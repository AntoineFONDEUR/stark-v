//! Typed execution of the recursion V2 Fiat-Shamir program.
//!
//! The trusted verifier plan owns transcript order. Each transcript-affecting
//! step absorbs one fixed-width header containing its sequence, tag, arity,
//! and zero-filled arguments before any private payload. Draw operations then
//! derive one full rate block. This shared driver feeds either the native or
//! recording backend, so witness generation cannot define a second transcript
//! schedule.

use core::fmt;

use air::digest::{Digest8, M31Word, ProtocolId};

use super::kernel::{VerifierControlPlan, VerifierStep};
use super::protocol::CanonicalWords;
use super::statement::SpanStatement;
use super::transcript::{TranscriptBackend, TranscriptError, TranscriptKernel, encode_u64_words};
use super::wire::{FixedStarkProofWire, Qm31Wire};

const TRANSCRIPT_OPERATION_TAG: u16 = 0x5452;
const TRANSCRIPT_HEADER_WORDS: usize = 8;
const TRANSCRIPT_DRAW_WORDS: usize = 8;

/// How one trusted verifier step changes the Fiat-Shamir transcript.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TranscriptEffect {
    Mix,
    Draw,
    Pow,
}

impl TranscriptEffect {
    const fn hash_count(self) -> u32 {
        match self {
            Self::Mix => 1,
            Self::Draw | Self::Pow => 2,
        }
    }
}

impl VerifierStep {
    /// Classifies the transcript work owned by this verifier operation.
    pub const fn transcript_effect(self) -> Option<TranscriptEffect> {
        match self {
            Self::BindProtocol
            | Self::BindStatement
            | Self::BindPcsParameters
            | Self::AbsorbTraceCommitment { .. }
            | Self::AbsorbPublicClaim
            | Self::AbsorbClaimedSums { .. }
            | Self::AbsorbSampledValues { .. }
            | Self::AbsorbFriCommitment { .. }
            | Self::AbsorbLastLayerCoefficients { .. } => Some(TranscriptEffect::Mix),
            Self::DrawRelationChallenge { .. }
            | Self::DrawCompositionRandomness
            | Self::DrawOodsPoint
            | Self::DrawDeepRandomness
            | Self::DrawFriAlpha { .. }
            | Self::DrawQueryBlock { .. } => Some(TranscriptEffect::Draw),
            Self::VerifyAndAbsorbInteractionPow { .. } | Self::VerifyAndAbsorbPcsPow { .. } => {
                Some(TranscriptEffect::Pow)
            }
            Self::AccumulatePublicLogupTerm { .. }
            | Self::AssertGlobalLogupZero
            | Self::EvaluateAirInstruction { .. }
            | Self::AssertComposition { .. }
            | Self::VerifyTraceMerklePath { .. }
            | Self::EvaluateDeepQuotient { .. }
            | Self::VerifyFriMerklePath { .. }
            | Self::FoldFri { .. }
            | Self::VerifyLastLayer { .. }
            | Self::CloseRelation { .. }
            | Self::Complete => None,
        }
    }
}

/// Exact frame and call range produced by one transcript operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TranscriptOperationTrace {
    sequence: u32,
    step: VerifierStep,
    first_hash_id: u32,
    hash_count: u32,
    first_call_id: u32,
    call_count: u32,
    draw: Option<[M31Word; TRANSCRIPT_DRAW_WORDS]>,
}

impl TranscriptOperationTrace {
    pub const fn sequence(&self) -> u32 {
        self.sequence
    }

    pub const fn step(&self) -> VerifierStep {
        self.step
    }

    pub const fn first_hash_id(&self) -> u32 {
        self.first_hash_id
    }

    pub const fn hash_count(&self) -> u32 {
        self.hash_count
    }

    pub const fn first_call_id(&self) -> u32 {
        self.first_call_id
    }

    pub const fn call_count(&self) -> u32 {
        self.call_count
    }

    pub const fn draw(&self) -> Option<[M31Word; TRANSCRIPT_DRAW_WORDS]> {
        self.draw
    }
}

/// Result of executing one complete child-verifier transcript.
#[derive(Clone, Debug)]
pub struct VerifierTranscriptExecution<B> {
    kernel: TranscriptKernel<B>,
    operations: Vec<TranscriptOperationTrace>,
}

impl<B> VerifierTranscriptExecution<B>
where
    B: TranscriptBackend,
    B::Error: From<TranscriptError>,
{
    pub fn operations(&self) -> &[TranscriptOperationTrace] {
        &self.operations
    }

    pub const fn final_digest(&self) -> Digest8 {
        self.kernel.digest()
    }

    pub const fn final_draw_count(&self) -> u32 {
        self.kernel.draw_count()
    }

    pub const fn backend(&self) -> &B {
        self.kernel.backend()
    }

    pub fn into_backend(self) -> B {
        self.kernel.into_backend()
    }
}

/// Executes every transcript step over one exact fixed proof wire.
pub fn execute_fixed_transcript<
    B,
    const N_COMMITMENTS: usize,
    const N_CLAIMED_SUMS: usize,
    const N_SAMPLED_VALUES: usize,
    const N_QUERY_VALUES: usize,
    const N_TRACE_PATHS: usize,
    const N_FRI_LAYERS: usize,
    const N_QUERIES: usize,
    const FOLD_WIDTH: usize,
    const N_LAST_LAYER_COEFFICIENTS: usize,
    const MAX_MERKLE_DEPTH: usize,
>(
    backend: B,
    plan: &VerifierControlPlan,
    protocol_id: ProtocolId,
    statement: &SpanStatement,
    proof: &FixedStarkProofWire<
        N_COMMITMENTS,
        N_CLAIMED_SUMS,
        N_SAMPLED_VALUES,
        N_QUERY_VALUES,
        N_TRACE_PATHS,
        N_FRI_LAYERS,
        N_QUERIES,
        FOLD_WIDTH,
        N_LAST_LAYER_COEFFICIENTS,
        MAX_MERKLE_DEPTH,
    >,
) -> Result<VerifierTranscriptExecution<B>, TranscriptProgramError>
where
    B: TranscriptBackend<Error = TranscriptError>,
{
    validate_input_counts(plan, proof)?;

    let mut kernel = TranscriptKernel::new(backend);
    let mut operations = Vec::new();
    for (sequence, step) in plan.steps().iter().copied().enumerate() {
        let sequence = u32::try_from(sequence)
            .map_err(|_| TranscriptProgramError::SequenceOutOfRange { sequence })?;
        let before = kernel.position();
        let draw = execute_step(
            &mut kernel,
            sequence,
            step,
            protocol_id,
            statement,
            plan,
            proof,
        )?;
        let after = kernel.position();
        let Some(effect) = step.transcript_effect() else {
            if before != after {
                return Err(TranscriptProgramError::UnexpectedTranscriptTransition { sequence });
            }
            continue;
        };
        let expected_draw = effect == TranscriptEffect::Draw;
        if draw.is_some() != expected_draw {
            return Err(TranscriptProgramError::DrawOutputMismatch {
                sequence,
                expected: expected_draw,
                actual: draw.is_some(),
            });
        }
        let hash_count = monotonic_delta(before.next_hash_id(), after.next_hash_id());
        if hash_count != effect.hash_count() {
            return Err(TranscriptProgramError::HashCountMismatch {
                sequence,
                expected: effect.hash_count(),
                actual: hash_count,
            });
        }
        operations.push(TranscriptOperationTrace {
            sequence,
            step,
            first_hash_id: before.next_hash_id(),
            hash_count,
            first_call_id: before.next_call_id(),
            call_count: monotonic_delta(before.next_call_id(), after.next_call_id()),
            draw,
        });
    }

    Ok(VerifierTranscriptExecution { kernel, operations })
}

fn execute_step<
    B,
    const N_COMMITMENTS: usize,
    const N_CLAIMED_SUMS: usize,
    const N_SAMPLED_VALUES: usize,
    const N_QUERY_VALUES: usize,
    const N_TRACE_PATHS: usize,
    const N_FRI_LAYERS: usize,
    const N_QUERIES: usize,
    const FOLD_WIDTH: usize,
    const N_LAST_LAYER_COEFFICIENTS: usize,
    const MAX_MERKLE_DEPTH: usize,
>(
    kernel: &mut TranscriptKernel<B>,
    sequence: u32,
    step: VerifierStep,
    protocol_id: ProtocolId,
    statement: &SpanStatement,
    plan: &VerifierControlPlan,
    proof: &FixedStarkProofWire<
        N_COMMITMENTS,
        N_CLAIMED_SUMS,
        N_SAMPLED_VALUES,
        N_QUERY_VALUES,
        N_TRACE_PATHS,
        N_FRI_LAYERS,
        N_QUERIES,
        FOLD_WIDTH,
        N_LAST_LAYER_COEFFICIENTS,
        MAX_MERKLE_DEPTH,
    >,
) -> Result<Option<[M31Word; TRANSCRIPT_DRAW_WORDS]>, TranscriptProgramError>
where
    B: TranscriptBackend<Error = TranscriptError>,
{
    match step {
        VerifierStep::BindProtocol => {
            absorb_operation(kernel, sequence, step, protocol_id.digest().words())?;
        }
        VerifierStep::BindStatement => {
            absorb_operation(kernel, sequence, step, &statement.canonical_words())?;
        }
        VerifierStep::BindPcsParameters => {
            absorb_operation(
                kernel,
                sequence,
                step,
                &plan.pcs_parameters().canonical_words(),
            )?;
        }
        VerifierStep::AbsorbTraceCommitment { tree, .. } => {
            let commitment = proof.commitments.get(index("commitment", tree)?).ok_or(
                TranscriptProgramError::IndexOutOfRange {
                    field: "commitment",
                    index: tree,
                    len: N_COMMITMENTS,
                },
            )?;
            absorb_operation(kernel, sequence, step, commitment.words())?;
        }
        VerifierStep::AbsorbPublicClaim => {
            // BindStatement owns the complete common public input. This header
            // marks the schema-specific claim phase without a second encoding.
            absorb_operation(kernel, sequence, step, &[])?;
        }
        VerifierStep::VerifyAndAbsorbInteractionPow { bits } => {
            absorb_operation(
                kernel,
                sequence,
                step,
                &encode_u64_words(proof.interaction_pow),
            )?;
            kernel.verify_pow_from_current_digest(proof.interaction_pow, bits)?;
        }
        VerifierStep::DrawRelationChallenge { .. }
        | VerifierStep::DrawCompositionRandomness
        | VerifierStep::DrawOodsPoint
        | VerifierStep::DrawDeepRandomness
        | VerifierStep::DrawFriAlpha { .. }
        | VerifierStep::DrawQueryBlock { .. } => {
            absorb_operation(kernel, sequence, step, &[])?;
            return Ok(Some(kernel.draw_block()?));
        }
        VerifierStep::AbsorbClaimedSums { .. } => {
            absorb_operation(kernel, sequence, step, &qm31_words(&proof.claimed_sums))?;
        }
        VerifierStep::AbsorbSampledValues { .. } => {
            absorb_operation(kernel, sequence, step, &qm31_words(&proof.sampled_values))?;
        }
        VerifierStep::AbsorbFriCommitment { layer } => {
            let commitment = proof
                .fri_layers
                .get(index("FRI layer", layer)?)
                .ok_or(TranscriptProgramError::IndexOutOfRange {
                    field: "FRI layer",
                    index: layer,
                    len: N_FRI_LAYERS,
                })?
                .commitment();
            absorb_operation(kernel, sequence, step, commitment.words())?;
        }
        VerifierStep::AbsorbLastLayerCoefficients { .. } => {
            absorb_operation(
                kernel,
                sequence,
                step,
                &qm31_words(&proof.last_layer_coefficients),
            )?;
        }
        VerifierStep::VerifyAndAbsorbPcsPow { bits } => {
            absorb_operation(kernel, sequence, step, &encode_u64_words(proof.pcs_pow))?;
            kernel.verify_pow_from_current_digest(proof.pcs_pow, bits)?;
        }
        VerifierStep::AccumulatePublicLogupTerm { .. }
        | VerifierStep::AssertGlobalLogupZero
        | VerifierStep::EvaluateAirInstruction { .. }
        | VerifierStep::AssertComposition { .. }
        | VerifierStep::VerifyTraceMerklePath { .. }
        | VerifierStep::EvaluateDeepQuotient { .. }
        | VerifierStep::VerifyFriMerklePath { .. }
        | VerifierStep::FoldFri { .. }
        | VerifierStep::VerifyLastLayer { .. }
        | VerifierStep::CloseRelation { .. }
        | VerifierStep::Complete => {}
    }
    Ok(None)
}

fn absorb_operation<B: TranscriptBackend<Error = TranscriptError>>(
    kernel: &mut TranscriptKernel<B>,
    sequence: u32,
    step: VerifierStep,
    payload: &[M31Word],
) -> Result<(), TranscriptProgramError> {
    let mut words = Vec::with_capacity(TRANSCRIPT_HEADER_WORDS + payload.len());
    words.extend(operation_header(sequence, step)?);
    words.extend_from_slice(payload);
    kernel.absorb_m31_words(&words)?;
    Ok(())
}

pub(crate) fn operation_header(
    sequence: u32,
    step: VerifierStep,
) -> Result<[M31Word; TRANSCRIPT_HEADER_WORDS], TranscriptProgramError> {
    let encoded = step.encode();
    let [arg_0, arg_1, arg_2, arg_3] = encoded.args();
    Ok([
        M31Word::from(TRANSCRIPT_OPERATION_TAG),
        header_word("sequence", sequence)?,
        header_word("tag", encoded.tag())?,
        M31Word::from(u16::from(encoded.arity())),
        header_word("argument", arg_0)?,
        header_word("argument", arg_1)?,
        header_word("argument", arg_2)?,
        header_word("argument", arg_3)?,
    ])
}

fn header_word(field: &'static str, value: u32) -> Result<M31Word, TranscriptProgramError> {
    M31Word::try_from(value)
        .map_err(|_| TranscriptProgramError::ControlWordOutOfRange { field, value })
}

fn qm31_words<const N: usize>(values: &[Qm31Wire; N]) -> Vec<M31Word> {
    values
        .iter()
        .flat_map(|value| value.words().iter().copied())
        .collect()
}

fn index(field: &'static str, value: u32) -> Result<usize, TranscriptProgramError> {
    usize::try_from(value).map_err(|_| TranscriptProgramError::IndexOutOfRange {
        field,
        index: value,
        len: usize::MAX,
    })
}

fn monotonic_delta(before: u32, after: u32) -> u32 {
    after
        .checked_sub(before)
        .expect("transcript identifiers only advance")
}

fn validate_input_counts<
    const N_COMMITMENTS: usize,
    const N_CLAIMED_SUMS: usize,
    const N_SAMPLED_VALUES: usize,
    const N_QUERY_VALUES: usize,
    const N_TRACE_PATHS: usize,
    const N_FRI_LAYERS: usize,
    const N_QUERIES: usize,
    const FOLD_WIDTH: usize,
    const N_LAST_LAYER_COEFFICIENTS: usize,
    const MAX_MERKLE_DEPTH: usize,
>(
    plan: &VerifierControlPlan,
    _proof: &FixedStarkProofWire<
        N_COMMITMENTS,
        N_CLAIMED_SUMS,
        N_SAMPLED_VALUES,
        N_QUERY_VALUES,
        N_TRACE_PATHS,
        N_FRI_LAYERS,
        N_QUERIES,
        FOLD_WIDTH,
        N_LAST_LAYER_COEFFICIENTS,
        MAX_MERKLE_DEPTH,
    >,
) -> Result<(), TranscriptProgramError> {
    let commitment_count = plan
        .steps()
        .iter()
        .filter(|step| matches!(step, VerifierStep::AbsorbTraceCommitment { .. }))
        .count();
    require_count("commitments", commitment_count, N_COMMITMENTS)?;
    let fri_layer_count = plan
        .steps()
        .iter()
        .filter(|step| matches!(step, VerifierStep::AbsorbFriCommitment { .. }))
        .count();
    require_count("FRI layers", fri_layer_count, N_FRI_LAYERS)?;

    for step in plan.steps() {
        match *step {
            VerifierStep::AbsorbClaimedSums { count } => {
                require_count(
                    "claimed sums",
                    index("claimed sums", count)?,
                    N_CLAIMED_SUMS,
                )?;
            }
            VerifierStep::AbsorbSampledValues { count } => {
                require_count(
                    "sampled values",
                    index("sampled values", count)?,
                    N_SAMPLED_VALUES,
                )?;
            }
            VerifierStep::AbsorbLastLayerCoefficients { count } => {
                require_count(
                    "last-layer coefficients",
                    index("last-layer coefficients", count)?,
                    N_LAST_LAYER_COEFFICIENTS,
                )?;
            }
            _ => {}
        }
    }
    let query_count = plan
        .steps()
        .iter()
        .filter_map(|step| match step {
            VerifierStep::DrawQueryBlock { query_count, .. } => Some(*query_count),
            _ => None,
        })
        .try_fold(0_u32, |total, count| total.checked_add(count))
        .ok_or(TranscriptProgramError::QueryCountOverflow)?;
    require_count("raw queries", index("raw queries", query_count)?, N_QUERIES)
}

fn require_count(
    field: &'static str,
    expected: usize,
    actual: usize,
) -> Result<(), TranscriptProgramError> {
    if expected != actual {
        return Err(TranscriptProgramError::InputCountMismatch {
            field,
            expected,
            actual,
        });
    }
    Ok(())
}

/// Invalid fixed input or impossible transition in the typed transcript program.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TranscriptProgramError {
    Transcript(TranscriptError),
    SequenceOutOfRange {
        sequence: usize,
    },
    ControlWordOutOfRange {
        field: &'static str,
        value: u32,
    },
    InputCountMismatch {
        field: &'static str,
        expected: usize,
        actual: usize,
    },
    IndexOutOfRange {
        field: &'static str,
        index: u32,
        len: usize,
    },
    QueryCountOverflow,
    UnexpectedTranscriptTransition {
        sequence: u32,
    },
    DrawOutputMismatch {
        sequence: u32,
        expected: bool,
        actual: bool,
    },
    HashCountMismatch {
        sequence: u32,
        expected: u32,
        actual: u32,
    },
}

impl From<TranscriptError> for TranscriptProgramError {
    fn from(value: TranscriptError) -> Self {
        Self::Transcript(value)
    }
}

impl fmt::Display for TranscriptProgramError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Transcript(error) => write!(formatter, "transcript execution failed: {error}"),
            Self::SequenceOutOfRange { sequence } => {
                write!(formatter, "verifier sequence {sequence} does not fit u32")
            }
            Self::ControlWordOutOfRange { field, value } => {
                write!(formatter, "transcript {field} {value} is not canonical M31")
            }
            Self::InputCountMismatch {
                field,
                expected,
                actual,
            } => write!(
                formatter,
                "transcript expects {expected} {field}, fixed wire has {actual}"
            ),
            Self::IndexOutOfRange { field, index, len } => {
                write!(
                    formatter,
                    "transcript {field} index {index} exceeds length {len}"
                )
            }
            Self::QueryCountOverflow => write!(formatter, "raw query count overflowed u32"),
            Self::UnexpectedTranscriptTransition { sequence } => write!(
                formatter,
                "non-transcript verifier step {sequence} changed transcript coordinates"
            ),
            Self::DrawOutputMismatch {
                sequence,
                expected,
                actual,
            } => write!(
                formatter,
                "transcript step {sequence} draw output presence is {actual}, expected {expected}"
            ),
            Self::HashCountMismatch {
                sequence,
                expected,
                actual,
            } => write!(
                formatter,
                "transcript step {sequence} produced {actual} hash frames, expected {expected}"
            ),
        }
    }
}

impl std::error::Error for TranscriptProgramError {}

#[cfg(test)]
mod tests {
    use air::digest::{IoDigest, MemoryDigest, ProgramDigest};
    use rstest::rstest;
    use stwo::core::pcs::TreeVec;
    use stwo::core::poly::circle::CanonicCoset;
    use stwo_constraint_framework::{FrameworkEval, assert_constraints_on_polys};

    use super::*;
    use crate::v2::control_air::ControlRelations;
    use crate::v2::kernel::{VerifierProgramSpec, VerifierSchema};
    use crate::v2::protocol::{FixedProofShape, OptionalM31Word, PcsParameters};
    use crate::v2::statement::{
        CompleteExecutionStatement, JobContext, MachineState, SpanStatement,
    };
    use crate::v2::transcript::{NativeTranscriptBackend, RecordingTranscriptBackend};
    use crate::v2::transcript_air::TranscriptAirRelations;
    use crate::v2::transcript_binding_air::{
        Eval as TranscriptBindingEval, TranscriptBindingRelations, TranscriptCallBindingTable,
        TranscriptCallPreprocessed, UniversalTranscriptWitness,
        gen_interaction_trace as gen_binding_interaction_trace, push_call_bindings,
    };
    use crate::v2::transcript_layout::TranscriptLayout;
    use crate::v2::transcript_state_air::{
        Eval as TranscriptStateEval, TranscriptFrameStateTable, TranscriptStatePreprocessed,
        TranscriptStateRelations, gen_interaction_trace as gen_state_interaction_trace,
        push_frame_states,
    };
    use crate::v2::transcript_word_air::{
        Eval as TranscriptWordEval, TranscriptWordPreprocessed, TranscriptWordRelations,
        TranscriptWordTable, gen_interaction_trace as gen_word_interaction_trace,
        push_transcript_words,
    };
    use crate::v2::wire::{FriLayerWire, FriQueryWire, MerklePathWire, ProofKind};

    type TestProof = FixedStarkProofWire<4, 1, 1, 1, 4, 2, 1, 4, 1, 4>;

    #[derive(Clone, Copy)]
    enum FrameStateTamper {
        None,
        InitialDigest,
        InactiveValue,
    }

    #[derive(Clone, Copy)]
    enum WordTamper {
        None,
        FixedValue,
        InactiveValue,
    }

    fn word(value: u16) -> M31Word {
        M31Word::from(value)
    }

    fn canonical(value: u32) -> M31Word {
        M31Word::try_from(value).expect("conformance word is canonical M31")
    }

    fn digest(seed: u16) -> Digest8 {
        Digest8::new(core::array::from_fn(|offset| word(seed + offset as u16)))
    }

    fn qm31(seed: u16) -> Qm31Wire {
        Qm31Wire::new(core::array::from_fn(|offset| word(seed + offset as u16)))
    }

    fn pcs() -> PcsParameters {
        PcsParameters {
            interaction_pow_bits: M31Word::ZERO,
            pow_bits: M31Word::ZERO,
            fri_log_blowup_factor: word(1),
            fri_n_queries: word(1),
            fri_log_last_layer_degree_bound: M31Word::ZERO,
            fri_fold_step: word(2),
            lifting_log_size: OptionalM31Word::Some(word(4)),
        }
    }

    fn shape(claimed_sum_count: u16) -> FixedProofShape<1, 4, 2> {
        FixedProofShape {
            claimed_sum_count: word(claimed_sum_count),
            sampled_value_count: word(1),
            queried_value_count: word(1),
            trace_path_count: word(4),
            raw_query_count: word(1),
            last_layer_coefficient_count: word(1),
            table_log_sizes: [word(3)],
            tree_heights: [word(4); 4],
            fri_layer_fold_widths: [word(4), word(2)],
            fri_layer_tree_heights: [word(2), word(2)],
        }
    }

    fn plan_for_schema(schema: VerifierSchema, claimed_sum_count: u16) -> VerifierControlPlan {
        let spec = VerifierProgramSpec::new(schema, 1, 1, 1, 1)
            .expect("fixture program has every verifier phase");
        VerifierControlPlan::new(spec, pcs(), &shape(claimed_sum_count))
            .expect("fixture geometry matches its PCS profile")
    }

    fn plan(claimed_sum_count: u16) -> VerifierControlPlan {
        plan_for_schema(VerifierSchema::Vm, claimed_sum_count)
    }

    fn state(seed: u16) -> MachineState {
        let mut registers = [0_u32; 32];
        registers[1] = u32::from(seed);
        MachineState::new(
            u32::from(seed) * 4,
            registers,
            MemoryDigest::from(digest(seed + 10)),
            IoDigest::from(digest(seed + 20)),
        )
        .expect("fixture keeps the zero register immutable")
    }

    fn statement(seed: u16) -> SpanStatement {
        let complete = CompleteExecutionStatement::new(
            ProtocolId::from(digest(1)),
            ProgramDigest::from(digest(2)),
            state(0),
            state(seed),
            IoDigest::from(digest(3)),
            IoDigest::from(digest(4)),
            12,
        )
        .expect("fixture execution has cycles");
        let job = JobContext::new(complete, 3).expect("fixture job has three segments");
        SpanStatement::empty_leaf(job, 3).expect("slot three is canonical suffix padding")
    }

    fn proof() -> TestProof {
        let trace_path =
            MerklePathWire::new(4, [digest(30); 4]).expect("trace path fills the fixed depth");
        let fri_path =
            MerklePathWire::new(2, [digest(40), digest(41), Digest8::ZERO, Digest8::ZERO])
                .expect("FRI path uses canonical suffix padding");
        let first_query = FriQueryWire::new([qm31(50), qm31(54), qm31(58), qm31(62)], fri_path);
        let last_query = FriQueryWire::new(
            [qm31(70), qm31(74), Qm31Wire::ZERO, Qm31Wire::ZERO],
            fri_path,
        );
        FixedStarkProofWire {
            commitments: [digest(80), digest(90), digest(100), digest(110)],
            claimed_sums: [qm31(120)],
            sampled_values: [qm31(130)],
            queried_values: [word(140)],
            trace_paths: [trace_path; 4],
            fri_layers: [
                FriLayerWire::new(4, digest(150), [first_query])
                    .expect("first FRI layer uses its full fold width"),
                FriLayerWire::new(2, digest(160), [last_query])
                    .expect("last FRI layer zero-pads inactive values"),
            ],
            last_layer_coefficients: [qm31(170)],
            interaction_pow: 0x1122_3344_5566_7788,
            pcs_pow: 0x8877_6655_4433_2211,
        }
    }

    fn recording_execution()
    -> VerifierTranscriptExecution<crate::v2::transcript::RecordingTranscriptBackend> {
        recording_execution_for(&plan(1), 1)
    }

    fn recording_execution_for(
        plan: &VerifierControlPlan,
        statement_seed: u16,
    ) -> VerifierTranscriptExecution<crate::v2::transcript::RecordingTranscriptBackend> {
        execute_fixed_transcript(
            RecordingTranscriptBackend::default(),
            plan,
            ProtocolId::from(digest(9)),
            &statement(statement_seed),
            &proof(),
        )
        .expect("fixture executes the complete typed transcript")
    }

    fn assert_call_binding_constraints(kind: ProofKind, tamper_enabler: bool) {
        let vm_plan = plan_for_schema(VerifierSchema::Vm, 1);
        let recursion_plan = plan_for_schema(VerifierSchema::Recursion, 1);
        let preprocessing = TranscriptCallPreprocessed::new(&vm_plan, &recursion_plan)
            .expect("fixture plans occupy their canonical transcript lanes");
        let segment = recording_execution_for(&vm_plan, 1);
        let left = recording_execution_for(&recursion_plan, 1);
        let right = recording_execution_for(&recursion_plan, 2);
        let witness = match kind {
            ProofKind::SegmentLeaf => UniversalTranscriptWitness::Segment(&segment),
            ProofKind::BinaryNode => UniversalTranscriptWitness::Binary {
                left: &left,
                right: &right,
            },
            ProofKind::EmptyLeaf => UniversalTranscriptWitness::Empty,
        };
        let mut table = TranscriptCallBindingTable::new();
        push_call_bindings(&mut table, &preprocessing, witness)
            .expect("validated transcript executions materialize");
        if tamper_enabler {
            table.enabler[0] = 0;
        }

        let control_relations = ControlRelations::dummy();
        let transcript_relations = TranscriptAirRelations::dummy();
        let binding_relations = TranscriptBindingRelations::dummy();
        let preprocessed = preprocessing.gen_columns();
        let trace = table.into_witness();
        let (interaction, claimed_sum) = gen_binding_interaction_trace(
            &trace,
            &preprocessed,
            kind,
            &control_relations,
            &transcript_relations,
            &binding_relations,
        );
        let traces = TreeVec::new(vec![preprocessed, trace, interaction]);
        let trace_polys = traces.map_cols(|column| column.interpolate());
        let eval = TranscriptBindingEval {
            log_size: preprocessing.log_size(),
            proof_kind: kind,
            control_relations,
            transcript_relations,
            binding_relations,
        };
        assert_constraints_on_polys(
            &trace_polys,
            CanonicCoset::new(preprocessing.log_size()),
            |row| {
                eval.evaluate(row);
            },
            claimed_sum,
        );
    }

    fn assert_frame_state_constraints(kind: ProofKind, tamper: FrameStateTamper) {
        let vm_plan = plan_for_schema(VerifierSchema::Vm, 1);
        let recursion_plan = plan_for_schema(VerifierSchema::Recursion, 1);
        let calls = TranscriptCallPreprocessed::new(&vm_plan, &recursion_plan)
            .expect("fixture plans occupy their canonical transcript lanes");
        let preprocessing = TranscriptStatePreprocessed::new(&calls)
            .expect("trusted call layout has canonical digest transitions");
        let segment = recording_execution_for(&vm_plan, 1);
        let left = recording_execution_for(&recursion_plan, 1);
        let right = recording_execution_for(&recursion_plan, 2);
        let witness = match kind {
            ProofKind::SegmentLeaf => UniversalTranscriptWitness::Segment(&segment),
            ProofKind::BinaryNode => UniversalTranscriptWitness::Binary {
                left: &left,
                right: &right,
            },
            ProofKind::EmptyLeaf => UniversalTranscriptWitness::Empty,
        };
        let mut table = TranscriptFrameStateTable::new();
        push_frame_states(&mut table, &preprocessing, witness)
            .expect("validated transcript frames materialize");
        match tamper {
            FrameStateTamper::None => {}
            FrameStateTamper::InitialDigest | FrameStateTamper::InactiveValue => {
                table.input_0[0] = 1;
            }
        }

        let binding_relations = TranscriptBindingRelations::dummy();
        let state_relations = TranscriptStateRelations::dummy();
        let preprocessed = preprocessing.gen_columns();
        let trace = table.into_witness();
        let (interaction, claimed_sum) = gen_state_interaction_trace(
            &trace,
            &preprocessed,
            kind,
            &binding_relations,
            &state_relations,
        );
        let traces = TreeVec::new(vec![preprocessed, trace, interaction]);
        let trace_polys = traces.map_cols(|column| column.interpolate());
        let eval = TranscriptStateEval {
            log_size: preprocessing.log_size(),
            proof_kind: kind,
            binding_relations,
            state_relations,
        };
        assert_constraints_on_polys(
            &trace_polys,
            CanonicCoset::new(preprocessing.log_size()),
            |row| {
                eval.evaluate(row);
            },
            claimed_sum,
        );
    }

    fn assert_word_constraints(kind: ProofKind, tamper: WordTamper) {
        let vm_plan = plan_for_schema(VerifierSchema::Vm, 1);
        let recursion_plan = plan_for_schema(VerifierSchema::Recursion, 1);
        let calls = TranscriptCallPreprocessed::new(&vm_plan, &recursion_plan)
            .expect("fixture plans occupy their canonical transcript lanes");
        let preprocessing = TranscriptWordPreprocessed::new(&calls)
            .expect("trusted call layout has canonical word ownership");
        let segment = recording_execution_for(&vm_plan, 1);
        let left = recording_execution_for(&recursion_plan, 1);
        let right = recording_execution_for(&recursion_plan, 2);
        let witness = match kind {
            ProofKind::SegmentLeaf => UniversalTranscriptWitness::Segment(&segment),
            ProofKind::BinaryNode => UniversalTranscriptWitness::Binary {
                left: &left,
                right: &right,
            },
            ProofKind::EmptyLeaf => UniversalTranscriptWitness::Empty,
        };
        let mut table = TranscriptWordTable::new();
        push_transcript_words(&mut table, &preprocessing, witness)
            .expect("validated transcript words materialize");
        match tamper {
            WordTamper::None => {}
            WordTamper::FixedValue | WordTamper::InactiveValue => {
                table.value[0] = 1;
            }
        }

        let binding_relations = TranscriptBindingRelations::dummy();
        let word_relations = TranscriptWordRelations::dummy();
        let preprocessed = preprocessing.gen_columns();
        let trace = table.into_witness();
        let (interaction, claimed_sum) = gen_word_interaction_trace(
            &trace,
            &preprocessed,
            kind,
            &binding_relations,
            &word_relations,
        );
        let traces = TreeVec::new(vec![preprocessed, trace, interaction]);
        let trace_polys = traces.map_cols(|column| column.interpolate());
        let eval = TranscriptWordEval {
            log_size: preprocessing.log_size(),
            proof_kind: kind,
            binding_relations,
            word_relations,
        };
        assert_constraints_on_polys(
            &trace_polys,
            CanonicCoset::new(preprocessing.log_size()),
            |row| {
                eval.evaluate(row);
            },
            claimed_sum,
        );
    }

    #[rstest]
    #[case::segment(ProofKind::SegmentLeaf)]
    #[case::binary(ProofKind::BinaryNode)]
    #[case::empty(ProofKind::EmptyLeaf)]
    fn every_universal_mode_satisfies_the_transcript_call_binding(#[case] kind: ProofKind) {
        assert_call_binding_constraints(kind, false);
    }

    #[rstest]
    #[case::segment(ProofKind::SegmentLeaf, 144)]
    #[case::binary(ProofKind::BinaryNode, 288)]
    #[case::empty(ProofKind::EmptyLeaf, 0)]
    fn proof_kind_activates_only_its_transcript_calls(
        #[case] kind: ProofKind,
        #[case] expected: usize,
    ) {
        let preprocessing = TranscriptCallPreprocessed::new(
            &plan_for_schema(VerifierSchema::Vm, 1),
            &plan_for_schema(VerifierSchema::Recursion, 1),
        )
        .expect("fixture plans occupy their canonical transcript lanes");
        assert_eq!(preprocessing.active_call_count(kind), expected);
    }

    #[rstest]
    #[should_panic]
    fn transcript_call_rows_cannot_disable_trusted_preprocessing() {
        assert_call_binding_constraints(ProofKind::SegmentLeaf, true);
    }

    #[rstest]
    fn transcript_call_binding_constraint_profile_stays_cubic() {
        use stwo_constraint_framework::expr::ExprEvaluator;

        let eval = TranscriptBindingEval {
            log_size: 4,
            proof_kind: ProofKind::SegmentLeaf,
            control_relations: ControlRelations::dummy(),
            transcript_relations: TranscriptAirRelations::dummy(),
            binding_relations: TranscriptBindingRelations::dummy(),
        };
        let degrees = eval
            .evaluate(ExprEvaluator::new())
            .constraint_degree_bounds();
        assert_eq!((degrees.len(), degrees.into_iter().max()), (32, Some(3)));
    }

    #[rstest]
    #[case::segment(ProofKind::SegmentLeaf)]
    #[case::binary(ProofKind::BinaryNode)]
    #[case::empty(ProofKind::EmptyLeaf)]
    fn every_universal_mode_satisfies_the_transcript_state_chain(#[case] kind: ProofKind) {
        assert_frame_state_constraints(kind, FrameStateTamper::None);
    }

    #[rstest]
    #[case::segment(ProofKind::SegmentLeaf, 31)]
    #[case::binary(ProofKind::BinaryNode, 62)]
    #[case::empty(ProofKind::EmptyLeaf, 0)]
    fn proof_kind_activates_only_its_transcript_frames(
        #[case] kind: ProofKind,
        #[case] expected: usize,
    ) {
        let calls = TranscriptCallPreprocessed::new(
            &plan_for_schema(VerifierSchema::Vm, 1),
            &plan_for_schema(VerifierSchema::Recursion, 1),
        )
        .expect("fixture plans occupy their canonical transcript lanes");
        let preprocessing = TranscriptStatePreprocessed::new(&calls)
            .expect("trusted call layout has canonical digest transitions");
        assert_eq!(preprocessing.active_frame_count(kind), expected);
    }

    #[rstest]
    #[should_panic]
    fn first_transcript_digest_must_be_zero() {
        assert_frame_state_constraints(ProofKind::SegmentLeaf, FrameStateTamper::InitialDigest);
    }

    #[rstest]
    #[should_panic]
    fn inactive_transcript_state_values_must_be_zero() {
        assert_frame_state_constraints(ProofKind::EmptyLeaf, FrameStateTamper::InactiveValue);
    }

    #[rstest]
    fn transcript_state_constraint_profile_stays_cubic() {
        use stwo_constraint_framework::expr::ExprEvaluator;

        let eval = TranscriptStateEval {
            log_size: 4,
            proof_kind: ProofKind::SegmentLeaf,
            binding_relations: TranscriptBindingRelations::dummy(),
            state_relations: TranscriptStateRelations::dummy(),
        };
        let degrees = eval
            .evaluate(ExprEvaluator::new())
            .constraint_degree_bounds();
        assert_eq!((degrees.len(), degrees.into_iter().max()), (31, Some(3)));
    }

    #[rstest]
    #[case::segment(ProofKind::SegmentLeaf)]
    #[case::binary(ProofKind::BinaryNode)]
    #[case::empty(ProofKind::EmptyLeaf)]
    fn every_universal_mode_satisfies_the_transcript_word_component(#[case] kind: ProofKind) {
        assert_word_constraints(kind, WordTamper::None);
    }

    #[rstest]
    #[case::segment(ProofKind::SegmentLeaf, 904, 504)]
    #[case::binary(ProofKind::BinaryNode, 1_808, 1_008)]
    #[case::empty(ProofKind::EmptyLeaf, 0, 0)]
    fn proof_kind_activates_only_its_typed_transcript_words(
        #[case] kind: ProofKind,
        #[case] expected_words: usize,
        #[case] expected_payloads: usize,
    ) {
        let calls = TranscriptCallPreprocessed::new(
            &plan_for_schema(VerifierSchema::Vm, 1),
            &plan_for_schema(VerifierSchema::Recursion, 1),
        )
        .expect("fixture plans occupy their canonical transcript lanes");
        let preprocessing = TranscriptWordPreprocessed::new(&calls)
            .expect("trusted call layout has canonical word ownership");
        assert_eq!(
            (
                preprocessing.active_word_count(kind),
                preprocessing.active_payload_count(kind),
            ),
            (expected_words, expected_payloads)
        );
    }

    #[rstest]
    #[should_panic]
    fn fixed_transcript_words_cannot_be_replaced_by_committed_values() {
        assert_word_constraints(ProofKind::SegmentLeaf, WordTamper::FixedValue);
    }

    #[rstest]
    #[should_panic]
    fn inactive_transcript_word_values_must_be_zero() {
        assert_word_constraints(ProofKind::EmptyLeaf, WordTamper::InactiveValue);
    }

    #[rstest]
    fn transcript_word_constraint_profile_stays_cubic() {
        use stwo_constraint_framework::expr::ExprEvaluator;

        let eval = TranscriptWordEval {
            log_size: 4,
            proof_kind: ProofKind::SegmentLeaf,
            binding_relations: TranscriptBindingRelations::dummy(),
            word_relations: TranscriptWordRelations::dummy(),
        };
        let degrees = eval
            .evaluate(ExprEvaluator::new())
            .constraint_degree_bounds();
        assert_eq!((degrees.len(), degrees.into_iter().max()), (4, Some(3)));
    }

    #[rstest]
    fn every_transcript_step_has_one_operation_record() {
        let plan = plan(1);
        let execution = execute_fixed_transcript(
            RecordingTranscriptBackend::default(),
            &plan,
            ProtocolId::from(digest(9)),
            &statement(1),
            &proof(),
        )
        .expect("fixture executes the complete typed transcript");
        assert_eq!(
            execution.operations().len(),
            plan.steps()
                .iter()
                .filter(|step| step.transcript_effect().is_some())
                .count()
        );
    }

    #[rstest]
    fn operation_ranges_cover_every_recorded_hash_frame() {
        let execution = recording_execution();
        let first = execution
            .operations()
            .first()
            .expect("program has operations");
        let last = execution
            .operations()
            .last()
            .expect("program has operations");
        assert_eq!(
            (
                first.first_hash_id(),
                last.first_hash_id() + last.hash_count()
            ),
            (0, execution.backend().trace().hash_frames.len() as u32)
        );
    }

    #[rstest]
    fn recorded_program_passes_complete_frame_validation() {
        let execution = recording_execution();
        assert_eq!(
            execution
                .backend()
                .trace()
                .sponge_rows()
                .map(|rows| rows.len()),
            Ok(execution.backend().trace().poseidon_calls.len())
        );
    }

    #[rstest]
    fn trusted_layout_matches_the_recording_backend() {
        let plan = plan(1);
        let execution = execute_fixed_transcript(
            RecordingTranscriptBackend::default(),
            &plan,
            ProtocolId::from(digest(9)),
            &statement(1),
            &proof(),
        )
        .expect("fixture executes the complete typed transcript");
        let layout = TranscriptLayout::new(&plan).expect("trusted plan has a finite layout");
        assert_eq!(
            layout.validate_execution(execution.operations(), execution.backend().trace()),
            Ok(())
        );
    }

    #[rstest]
    fn trusted_layout_has_stable_preprocessed_dimensions() {
        let layout = TranscriptLayout::new(&plan(1)).expect("fixture plan has a finite layout");
        assert_eq!(
            (
                layout.operations().len(),
                layout.frames().len(),
                layout.calls().len(),
            ),
            (22, 31, 144)
        );
    }

    #[rstest]
    fn native_and_recording_backends_reach_the_same_transcript_state() {
        let plan = plan(1);
        let statement = statement(1);
        let proof = proof();
        let native = execute_fixed_transcript(
            NativeTranscriptBackend,
            &plan,
            ProtocolId::from(digest(9)),
            &statement,
            &proof,
        )
        .expect("native transcript accepts the fixture");
        let recording = execute_fixed_transcript(
            RecordingTranscriptBackend::default(),
            &plan,
            ProtocolId::from(digest(9)),
            &statement,
            &proof,
        )
        .expect("recording transcript accepts the fixture");
        assert_eq!(
            (
                native.final_digest(),
                native.final_draw_count(),
                native.operations()
            ),
            (
                recording.final_digest(),
                recording.final_draw_count(),
                recording.operations()
            )
        );
    }

    #[rstest]
    fn changing_the_bound_statement_changes_the_final_digest() {
        let plan = plan(1);
        let proof = proof();
        let first = execute_fixed_transcript(
            NativeTranscriptBackend,
            &plan,
            ProtocolId::from(digest(9)),
            &statement(1),
            &proof,
        )
        .expect("first statement executes");
        let second = execute_fixed_transcript(
            NativeTranscriptBackend,
            &plan,
            ProtocolId::from(digest(9)),
            &statement(2),
            &proof,
        )
        .expect("second statement executes");
        assert_ne!(first.final_digest(), second.final_digest());
    }

    #[rstest]
    fn typed_transcript_matches_its_conformance_digest() {
        assert_eq!(
            recording_execution().final_digest(),
            Digest8::new([
                canonical(1_263_169_743),
                canonical(139_866_038),
                canonical(2_063_857_902),
                canonical(1_318_105_051),
                canonical(1_148_619_615),
                canonical(1_748_000_098),
                canonical(2_038_110_020),
                canonical(2_118_719_565),
            ])
        );
    }

    #[rstest]
    fn operation_header_has_one_fixed_control_encoding() {
        assert_eq!(
            operation_header(
                7,
                VerifierStep::DrawQueryBlock {
                    block: 1,
                    first_query: 8,
                    query_count: 1,
                },
            ),
            Ok([
                word(TRANSCRIPT_OPERATION_TAG),
                word(7),
                word(21),
                word(3),
                word(1),
                word(8),
                word(1),
                M31Word::ZERO,
            ])
        );
    }

    #[rstest]
    fn public_claim_phase_has_no_second_statement_payload() {
        let execution = recording_execution();
        let operation = execution
            .operations()
            .iter()
            .find(|operation| operation.step() == VerifierStep::AbsorbPublicClaim)
            .expect("plan contains the public claim phase");
        let frame = &execution.backend().trace().hash_frames[operation.first_hash_id() as usize];
        assert_eq!(frame.words.len(), 2 * TRANSCRIPT_HEADER_WORDS);
    }

    #[rstest]
    fn fixed_wire_count_mismatch_is_rejected_before_transcript_execution() {
        assert_eq!(
            execute_fixed_transcript(
                RecordingTranscriptBackend::default(),
                &plan(2),
                ProtocolId::from(digest(9)),
                &statement(1),
                &proof(),
            )
            .map(|_| ()),
            Err(TranscriptProgramError::InputCountMismatch {
                field: "claimed sums",
                expected: 2,
                actual: 1,
            })
        );
    }
}
