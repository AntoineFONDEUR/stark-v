//! Proof-of-work predicate AIR for recursion V2.
//!
//! Each enabled row consumes a
//! `(verifier_id, kind, call_id, bits, word)` transcript-frame tuple and proves
//! that the requested low-order bits of the canonical M31 word are zero. The
//! invocation and operation-kind coordinates prevent otherwise identical
//! checks from being exchanged between child slots or between the interaction
//! and PCS proof-of-work rounds.

use core::fmt;

use stwo::core::ColumnVec;
use stwo::core::channel::Channel;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::QM31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, RelationEntry, relation,
};
use stwo_macros::define_component_tables;

use super::transcript::PowCheck;
use super::transcript_binding_air::TranscriptBindingRelations;

const M31_BITS: usize = 31;

define_component_tables! {
    pow_check: {
        committed: {
            verifier_id, pow_kind, call_id, bits, word,
            word_bit_0, word_bit_1, word_bit_2, word_bit_3,
            word_bit_4, word_bit_5, word_bit_6, word_bit_7,
            word_bit_8, word_bit_9, word_bit_10, word_bit_11,
            word_bit_12, word_bit_13, word_bit_14, word_bit_15,
            word_bit_16, word_bit_17, word_bit_18, word_bit_19,
            word_bit_20, word_bit_21, word_bit_22, word_bit_23,
            word_bit_24, word_bit_25, word_bit_26, word_bit_27,
            word_bit_28, word_bit_29, word_bit_30,
            active_0, active_1, active_2, active_3,
            active_4, active_5, active_6, active_7,
            active_8, active_9, active_10, active_11,
            active_12, active_13, active_14, active_15,
            active_16, active_17, active_18, active_19,
            active_20, active_21, active_22, active_23,
            active_24, active_25, active_26, active_27,
            active_28, active_29, active_30,
        },
        constraints: {
            word_bit_0 * (1 - word_bit_0),
            word_bit_1 * (1 - word_bit_1),
            word_bit_2 * (1 - word_bit_2),
            word_bit_3 * (1 - word_bit_3),
            word_bit_4 * (1 - word_bit_4),
            word_bit_5 * (1 - word_bit_5),
            word_bit_6 * (1 - word_bit_6),
            word_bit_7 * (1 - word_bit_7),
            word_bit_8 * (1 - word_bit_8),
            word_bit_9 * (1 - word_bit_9),
            word_bit_10 * (1 - word_bit_10),
            word_bit_11 * (1 - word_bit_11),
            word_bit_12 * (1 - word_bit_12),
            word_bit_13 * (1 - word_bit_13),
            word_bit_14 * (1 - word_bit_14),
            word_bit_15 * (1 - word_bit_15),
            word_bit_16 * (1 - word_bit_16),
            word_bit_17 * (1 - word_bit_17),
            word_bit_18 * (1 - word_bit_18),
            word_bit_19 * (1 - word_bit_19),
            word_bit_20 * (1 - word_bit_20),
            word_bit_21 * (1 - word_bit_21),
            word_bit_22 * (1 - word_bit_22),
            word_bit_23 * (1 - word_bit_23),
            word_bit_24 * (1 - word_bit_24),
            word_bit_25 * (1 - word_bit_25),
            word_bit_26 * (1 - word_bit_26),
            word_bit_27 * (1 - word_bit_27),
            word_bit_28 * (1 - word_bit_28),
            word_bit_29 * (1 - word_bit_29),
            word_bit_30 * (1 - word_bit_30),
            active_0 * (1 - active_0),
            active_1 * (1 - active_1),
            active_2 * (1 - active_2),
            active_3 * (1 - active_3),
            active_4 * (1 - active_4),
            active_5 * (1 - active_5),
            active_6 * (1 - active_6),
            active_7 * (1 - active_7),
            active_8 * (1 - active_8),
            active_9 * (1 - active_9),
            active_10 * (1 - active_10),
            active_11 * (1 - active_11),
            active_12 * (1 - active_12),
            active_13 * (1 - active_13),
            active_14 * (1 - active_14),
            active_15 * (1 - active_15),
            active_16 * (1 - active_16),
            active_17 * (1 - active_17),
            active_18 * (1 - active_18),
            active_19 * (1 - active_19),
            active_20 * (1 - active_20),
            active_21 * (1 - active_21),
            active_22 * (1 - active_22),
            active_23 * (1 - active_23),
            active_24 * (1 - active_24),
            active_25 * (1 - active_25),
            active_26 * (1 - active_26),
            active_27 * (1 - active_27),
            active_28 * (1 - active_28),
            active_29 * (1 - active_29),
            active_30 * (1 - active_30),
            word - (
                word_bit_0 + 2 * word_bit_1 + 4 * word_bit_2 + 8 * word_bit_3
                + 16 * word_bit_4 + 32 * word_bit_5 + 64 * word_bit_6
                + 128 * word_bit_7 + 256 * word_bit_8 + 512 * word_bit_9
                + 1024 * word_bit_10 + 2048 * word_bit_11 + 4096 * word_bit_12
                + 8192 * word_bit_13 + 16384 * word_bit_14 + 32768 * word_bit_15
                + 65536 * word_bit_16 + 131072 * word_bit_17
                + 262144 * word_bit_18 + 524288 * word_bit_19
                + 1048576 * word_bit_20 + 2097152 * word_bit_21
                + 4194304 * word_bit_22 + 8388608 * word_bit_23
                + 16777216 * word_bit_24 + 33554432 * word_bit_25
                + 67108864 * word_bit_26 + 134217728 * word_bit_27
                + 268435456 * word_bit_28 + 536870912 * word_bit_29
                + 1073741824 * word_bit_30
            ),
            (1 - active_0) * active_1,
            (1 - active_1) * active_2,
            (1 - active_2) * active_3,
            (1 - active_3) * active_4,
            (1 - active_4) * active_5,
            (1 - active_5) * active_6,
            (1 - active_6) * active_7,
            (1 - active_7) * active_8,
            (1 - active_8) * active_9,
            (1 - active_9) * active_10,
            (1 - active_10) * active_11,
            (1 - active_11) * active_12,
            (1 - active_12) * active_13,
            (1 - active_13) * active_14,
            (1 - active_14) * active_15,
            (1 - active_15) * active_16,
            (1 - active_16) * active_17,
            (1 - active_17) * active_18,
            (1 - active_18) * active_19,
            (1 - active_19) * active_20,
            (1 - active_20) * active_21,
            (1 - active_21) * active_22,
            (1 - active_22) * active_23,
            (1 - active_23) * active_24,
            (1 - active_24) * active_25,
            (1 - active_25) * active_26,
            (1 - active_26) * active_27,
            (1 - active_27) * active_28,
            (1 - active_28) * active_29,
            (1 - active_29) * active_30,
            bits - (
                active_0 + active_1 + active_2 + active_3 + active_4
                + active_5 + active_6 + active_7 + active_8 + active_9
                + active_10 + active_11 + active_12 + active_13 + active_14
                + active_15 + active_16 + active_17 + active_18 + active_19
                + active_20 + active_21 + active_22 + active_23 + active_24
                + active_25 + active_26 + active_27 + active_28 + active_29
                + active_30
            ),
            active_0 * word_bit_0,
            active_1 * word_bit_1,
            active_2 * word_bit_2,
            active_3 * word_bit_3,
            active_4 * word_bit_4,
            active_5 * word_bit_5,
            active_6 * word_bit_6,
            active_7 * word_bit_7,
            active_8 * word_bit_8,
            active_9 * word_bit_9,
            active_10 * word_bit_10,
            active_11 * word_bit_11,
            active_12 * word_bit_12,
            active_13 * word_bit_13,
            active_14 * word_bit_14,
            active_15 * word_bit_15,
            active_16 * word_bit_16,
            active_17 * word_bit_17,
            active_18 * word_bit_18,
            active_19 * word_bit_19,
            active_20 * word_bit_20,
            active_21 * word_bit_21,
            active_22 * word_bit_22,
            active_23 * word_bit_23,
            active_24 * word_bit_24,
            active_25 * word_bit_25,
            active_26 * word_bit_26,
            active_27 * word_bit_27,
            active_28 * word_bit_28,
            active_29 * word_bit_29,
            active_30 * word_bit_30,
        },
    },
    pow_frame: {
        committed: {
            verifier_id, sequence, pow_kind, hash_id, call_id, bits,
            word_0, word_1, word_2, word_3,
            word_4, word_5, word_6, word_7,
        },
        constraints: {
            // Only the two protocol-owned PoW rounds are representable.
            enabler * (pow_kind - 1) * (pow_kind - 2),
        },
    },
}

use prover_columns::{PowCheckColumns, PowFrameColumns};

relation!(PowCheckRelation, 5);

/// Domain tag for the two proof-of-work rounds in one verifier transcript.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum PowKind {
    Interaction = 1,
    Pcs = 2,
}

impl PowKind {
    const fn as_u32(self) -> u32 {
        self as u32
    }
}

/// V2 relations used to connect arithmetic checks to transcript frames.
#[derive(Clone)]
pub struct PowRelations {
    pub check: PowCheckRelation,
}

impl PowRelations {
    pub fn dummy() -> Self {
        Self {
            check: PowCheckRelation::dummy(),
        }
    }

    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            check: PowCheckRelation::draw(channel),
        }
    }
}

pub type Component = FrameworkComponent<Eval>;
pub type FrameComponent = FrameworkComponent<FrameEval>;

#[derive(Clone)]
pub struct Eval {
    pub log_size: u32,
    pub relations: PowRelations,
}

impl FrameworkEval for Eval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let cols = PowCheckColumns::from_eval(&mut eval);
        for constraint in cols.constraints() {
            eval.add_constraint(constraint);
        }
        eval.add_to_relation(RelationEntry::new(
            &self.relations.check,
            -E::EF::from(cols.enabler.clone()),
            &[
                cols.verifier_id.clone(),
                cols.pow_kind.clone(),
                cols.call_id.clone(),
                cols.bits.clone(),
                cols.word.clone(),
            ],
        ));
        eval.finalize_logup();
        eval
    }
}

/// Connects one transcript-owned PoW frame to the arithmetic predicate.
#[derive(Clone)]
pub struct FrameEval {
    pub log_size: u32,
    pub pow_relations: PowRelations,
    pub binding_relations: TranscriptBindingRelations,
}

impl FrameworkEval for FrameEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let cols = PowFrameColumns::from_eval(&mut eval);
        for constraint in cols.constraints() {
            eval.add_constraint(constraint);
        }
        let pow_tag = cols.pow_kind.clone() * BaseField::from(14) - E::F::from(BaseField::from(8));
        eval.add_to_relation(RelationEntry::new(
            &self.binding_relations.pow_frame,
            -E::EF::from(cols.enabler.clone()),
            &[
                cols.verifier_id.clone(),
                cols.sequence.clone(),
                pow_tag,
                cols.hash_id.clone(),
                cols.call_id.clone(),
                cols.bits.clone(),
                cols.word_0.clone(),
                cols.word_1.clone(),
                cols.word_2.clone(),
                cols.word_3.clone(),
                cols.word_4.clone(),
                cols.word_5.clone(),
                cols.word_6.clone(),
                cols.word_7.clone(),
            ],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.pow_relations.check,
            E::EF::from(cols.enabler.clone()),
            &[
                cols.verifier_id.clone(),
                cols.pow_kind.clone(),
                cols.call_id.clone(),
                cols.bits.clone(),
                cols.word_0.clone(),
            ],
        ));
        eval.finalize_logup_in_pairs();
        eval
    }
}

/// Generates the consumer-side LogUp trace for proof-of-work checks.
pub fn gen_interaction_trace(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    relations: &PowRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    let cols = PowCheckColumns::from_iter(trace.iter().map(|eval| &eval.values.data));
    let log_size = trace[0].domain.log_size();
    let denominator = combine!(
        relations.check,
        [
            cols.verifier_id,
            cols.pow_kind,
            cols.call_id,
            cols.bits,
            cols.word
        ]
    );
    let numerator: Vec<PackedQM31> = cols
        .enabler
        .iter()
        .map(|&enabled| -PackedQM31::from(enabled))
        .collect();
    let mut logup_gen = LogupTraceGenerator::new(log_size);
    write_col!(&numerator, &denominator, logup_gen);
    logup_gen.finalize_last()
}

/// Generates the transcript-frame/check binding interaction trace.
pub fn gen_frame_interaction_trace(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    pow_relations: &PowRelations,
    binding_relations: &TranscriptBindingRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    let cols = PowFrameColumns::from_iter(trace.iter().map(|eval| &eval.values.data));
    let log_size = trace[0].domain.log_size();
    let enabled: Vec<PackedQM31> = cols
        .enabler
        .iter()
        .map(|&value| PackedQM31::from(value))
        .collect();
    let neg_enabled: Vec<PackedQM31> = enabled.iter().map(|&value| -value).collect();
    let fourteen = stwo::prover::backend::simd::m31::PackedM31::broadcast(BaseField::from(14));
    let eight = stwo::prover::backend::simd::m31::PackedM31::broadcast(BaseField::from(8));
    let pow_tag: Vec<_> = (0..cols.enabler.len())
        .map(|row| cols.pow_kind[row] * fourteen - eight)
        .collect();
    let frame_denom = combine!(
        binding_relations.pow_frame,
        [
            cols.verifier_id,
            cols.sequence,
            &pow_tag,
            cols.hash_id,
            cols.call_id,
            cols.bits,
            cols.word_0,
            cols.word_1,
            cols.word_2,
            cols.word_3,
            cols.word_4,
            cols.word_5,
            cols.word_6,
            cols.word_7
        ]
    );
    let check_denom = combine!(
        pow_relations.check,
        [
            cols.verifier_id,
            cols.pow_kind,
            cols.call_id,
            cols.bits,
            cols.word_0
        ]
    );
    let mut logup_gen = LogupTraceGenerator::new(log_size);
    write_pair!(
        &neg_enabled,
        &frame_denom,
        &enabled,
        &check_denom,
        logup_gen
    );
    logup_gen.finalize_last()
}

/// Records one arithmetic PoW check for a fixed verifier invocation.
pub fn push_pow_check(
    table: &mut PowCheckTable,
    verifier_id: u32,
    kind: PowKind,
    check: PowCheck,
) -> Result<(), PowWitnessError> {
    if check.bits > M31_BITS as u32 {
        return Err(PowWitnessError::BitsOutOfRange { bits: check.bits });
    }

    // push_row keeps the generated table declaration as the canonical column order.
    let mut row = Vec::with_capacity(1 + 5 + 2 * M31_BITS);
    row.extend([
        1,
        verifier_id,
        kind.as_u32(),
        check.call_id,
        check.bits,
        check.word.as_u32(),
    ]);
    row.extend((0..M31_BITS).map(|bit| (check.word.as_u32() >> bit) & 1));
    row.extend((0..M31_BITS).map(|bit| u32::from(bit < check.bits as usize)));
    debug_assert_eq!(row.len(), 1 + 5 + 2 * M31_BITS);
    table.push_row(&row);
    Ok(())
}

/// Records all PoW frame bindings in their verifier-program order.
pub fn push_pow_frames(
    table: &mut PowFrameTable,
    verifier_id: u32,
    plan: &super::kernel::VerifierControlPlan,
    trace: &super::transcript::TranscriptTrace,
) -> Result<(), PowFrameError> {
    trace.sponge_rows().map_err(PowFrameError::Transcript)?;
    let schedule = plan
        .steps()
        .iter()
        .copied()
        .enumerate()
        .filter_map(|(sequence, step)| match step {
            super::kernel::VerifierStep::VerifyAndAbsorbInteractionPow { bits } => {
                Some((sequence, PowKind::Interaction, bits))
            }
            super::kernel::VerifierStep::VerifyAndAbsorbPcsPow { bits } => {
                Some((sequence, PowKind::Pcs, bits))
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    if schedule.len() != trace.pow_checks.len() {
        return Err(PowFrameError::KindCountMismatch {
            expected: trace.pow_checks.len(),
            actual: schedule.len(),
        });
    }
    for ((sequence, kind, bits), check) in schedule.into_iter().zip(&trace.pow_checks) {
        if bits != check.bits {
            return Err(PowFrameError::BitsMismatch {
                call_id: check.call_id,
                expected: bits,
                actual: check.bits,
            });
        }
        let frame = trace
            .hash_frames
            .iter()
            .find(|frame| {
                frame.purpose == super::transcript::HashPurpose::Draw
                    && frame.final_call_id() == Some(check.call_id)
            })
            .ok_or(PowFrameError::DrawFrameMissing {
                call_id: check.call_id,
            })?;
        let output = frame.output.map(air::digest::M31Word::as_u32);
        table.push(
            verifier_id,
            u32::try_from(sequence).map_err(|_| PowFrameError::SequenceOutOfRange { sequence })?,
            kind.as_u32(),
            frame.hash_id,
            check.call_id,
            check.bits,
            output[0],
            output[1],
            output[2],
            output[3],
            output[4],
            output[5],
            output[6],
            output[7],
        );
    }
    Ok(())
}

/// Invalid witness metadata that cannot be represented by the M31 predicate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PowWitnessError {
    BitsOutOfRange { bits: u32 },
}

impl fmt::Display for PowWitnessError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BitsOutOfRange { bits } => {
                write!(
                    formatter,
                    "PoW difficulty {bits} exceeds the 31-bit M31 word"
                )
            }
        }
    }
}

impl std::error::Error for PowWitnessError {}

/// Invalid linkage between recorded PoW checks and transcript frames.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PowFrameError {
    Transcript(super::transcript::TranscriptError),
    KindCountMismatch {
        expected: usize,
        actual: usize,
    },
    SequenceOutOfRange {
        sequence: usize,
    },
    BitsMismatch {
        call_id: u32,
        expected: u32,
        actual: u32,
    },
    DrawFrameMissing {
        call_id: u32,
    },
}

impl fmt::Display for PowFrameError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Transcript(error) => write!(formatter, "invalid transcript trace: {error}"),
            Self::KindCountMismatch { expected, actual } => write!(
                formatter,
                "PoW frame has {actual} kind tags, expected {expected}"
            ),
            Self::SequenceOutOfRange { sequence } => {
                write!(
                    formatter,
                    "PoW control sequence {sequence} does not fit u32"
                )
            }
            Self::BitsMismatch {
                call_id,
                expected,
                actual,
            } => write!(
                formatter,
                "PoW call {call_id} checks {actual} bits, control requires {expected}"
            ),
            Self::DrawFrameMissing { call_id } => write!(
                formatter,
                "PoW check call {call_id} has no final draw frame"
            ),
        }
    }
}

impl std::error::Error for PowFrameError {}

#[cfg(test)]
mod tests {
    use air::digest::M31Word;
    use rstest::rstest;
    use stwo::core::channel::Channel;
    use stwo::core::pcs::TreeVec;
    use stwo::core::poly::circle::CanonicCoset;
    use stwo::core::proof_of_work::GrindOps;
    use stwo::prover::backend::simd::SimdBackend;
    use stwo_constraint_framework::assert_constraints_on_polys;

    use prover::poseidon2_channel::Poseidon2M31Channel;

    use super::*;
    use crate::v2::kernel::{VerifierControlPlan, VerifierProgramSpec, VerifierSchema};
    use crate::v2::protocol::{FixedProofShape, OptionalM31Word, PcsParameters};
    use crate::v2::transcript::{RecordingTranscriptBackend, TranscriptKernel, TranscriptTrace};

    fn check(bits: u32, word: u32) -> PowCheck {
        PowCheck {
            call_id: 17,
            nonce: 0x1122_3344_5566_7788,
            bits,
            word: M31Word::try_from(word).expect("test word is canonical M31"),
        }
    }

    fn assert_table_satisfies_constraints(table: PowCheckTable) {
        let relations = PowRelations::dummy();
        let trace = table.into_witness();
        let log_size = trace
            .first()
            .map(|column| column.domain.log_size())
            .expect("generated table has columns");
        let (interaction, claimed_sum) = gen_interaction_trace(&trace, &relations);
        let traces = TreeVec::new(vec![vec![], trace, interaction]);
        let trace_polys = traces.map_cols(|column| column.interpolate());
        let eval = Eval {
            log_size,
            relations,
        };
        assert_constraints_on_polys(
            &trace_polys,
            CanonicCoset::new(log_size),
            |row| {
                eval.evaluate(row);
            },
            claimed_sum,
        );
    }

    fn pow_trace() -> TranscriptTrace {
        let mut reference = Poseidon2M31Channel::default();
        reference.mix_u32s(&[1, 2, 3]);
        let mut kernel = TranscriptKernel::<RecordingTranscriptBackend>::default();
        kernel
            .absorb_u32s(&[1, 2, 3])
            .expect("fixture words are accepted");
        for bits in [8, 10] {
            let nonce = <SimdBackend as GrindOps<Poseidon2M31Channel>>::grind(&reference, bits);
            kernel
                .verify_and_absorb_pow(nonce, bits)
                .expect("ground nonce satisfies the fixture challenge");
            reference.mix_u64(nonce);
        }
        kernel.into_backend().into_trace()
    }

    fn plan() -> VerifierControlPlan {
        let pcs = PcsParameters {
            interaction_pow_bits: M31Word::from(8),
            pow_bits: M31Word::from(10),
            fri_log_blowup_factor: M31Word::from(1),
            fri_n_queries: M31Word::from(9),
            fri_log_last_layer_degree_bound: M31Word::ZERO,
            fri_fold_step: M31Word::from(2),
            lifting_log_size: OptionalM31Word::Some(M31Word::from(8)),
        };
        let shape = FixedProofShape {
            claimed_sum_count: M31Word::from(7),
            sampled_value_count: M31Word::from(8),
            queried_value_count: M31Word::from(36),
            trace_path_count: M31Word::from(36),
            raw_query_count: M31Word::from(9),
            last_layer_coefficient_count: M31Word::from(1),
            table_log_sizes: [M31Word::from(5), M31Word::from(6)],
            tree_heights: [M31Word::from(8); 4],
            fri_layer_fold_widths: [
                M31Word::from(4),
                M31Word::from(4),
                M31Word::from(4),
                M31Word::from(2),
            ],
            fri_layer_tree_heights: [
                M31Word::from(6),
                M31Word::from(4),
                M31Word::from(2),
                M31Word::from(2),
            ],
        };
        let spec = VerifierProgramSpec::new(VerifierSchema::Vm, 3, 5, 7, 4)
            .expect("fixture program has every mandatory phase");
        VerifierControlPlan::new(spec, pcs, &shape).expect("fixture shape matches the PCS profile")
    }

    fn assert_frame_table_satisfies_constraints(table: PowFrameTable) {
        let pow_relations = PowRelations::dummy();
        let binding_relations = TranscriptBindingRelations::dummy();
        let trace = table.into_witness();
        let log_size = trace
            .first()
            .map(|column| column.domain.log_size())
            .expect("generated table has columns");
        let (interaction, claimed_sum) =
            gen_frame_interaction_trace(&trace, &pow_relations, &binding_relations);
        let traces = TreeVec::new(vec![vec![], trace, interaction]);
        let trace_polys = traces.map_cols(|column| column.interpolate());
        let eval = FrameEval {
            log_size,
            pow_relations,
            binding_relations,
        };
        assert_constraints_on_polys(
            &trace_polys,
            CanonicCoset::new(log_size),
            |row| {
                eval.evaluate(row);
            },
            claimed_sum,
        );
    }

    #[rstest]
    #[case::zero_difficulty(0, 1)]
    #[case::five_zero_bits(5, 0b10_0000)]
    #[case::full_m31_difficulty(31, 0)]
    fn valid_pow_predicate_satisfies_constraints(#[case] bits: u32, #[case] word: u32) {
        let mut table = PowCheckTable::new();
        push_pow_check(&mut table, 1, PowKind::Pcs, check(bits, word)).expect("valid witness");
        assert_table_satisfies_constraints(table);
    }

    #[test]
    #[should_panic]
    fn set_low_bit_is_rejected() {
        let mut table = PowCheckTable::new();
        push_pow_check(&mut table, 0, PowKind::Interaction, check(5, 1))
            .expect("representable witness");
        assert_table_satisfies_constraints(table);
    }

    #[test]
    #[should_panic]
    fn wrong_word_decomposition_is_rejected() {
        let mut table = PowCheckTable::new();
        push_pow_check(&mut table, 0, PowKind::Interaction, check(5, 0b10_0000))
            .expect("representable witness");
        table.word_bit_6[0] = 1;
        assert_table_satisfies_constraints(table);
    }

    #[test]
    #[should_panic]
    fn non_prefix_difficulty_mask_is_rejected() {
        let mut table = PowCheckTable::new();
        push_pow_check(&mut table, 0, PowKind::Interaction, check(5, 0))
            .expect("representable witness");
        table.active_0[0] = 0;
        table.active_5[0] = 1;
        assert_table_satisfies_constraints(table);
    }

    #[test]
    fn out_of_range_difficulty_is_rejected_before_witness_indexing() {
        let error = push_pow_check(&mut PowCheckTable::new(), 0, PowKind::Pcs, check(32, 0));
        assert_eq!(error, Err(PowWitnessError::BitsOutOfRange { bits: 32 }));
    }

    #[test]
    fn constraint_profile_stays_quadratic() {
        use stwo_constraint_framework::expr::ExprEvaluator;

        let eval = Eval {
            log_size: 4,
            relations: PowRelations::dummy(),
        };
        let degrees = eval
            .evaluate(ExprEvaluator::new())
            .constraint_degree_bounds();
        assert_eq!((degrees.len(), degrees.into_iter().max()), (127, Some(2)));
    }

    #[rstest]
    fn recorded_draw_frame_satisfies_the_pow_binding_air() {
        let mut table = PowFrameTable::new();
        push_pow_frames(&mut table, 1, &plan(), &pow_trace())
            .expect("recorded PoW frame is canonical");
        assert_frame_table_satisfies_constraints(table);
    }

    #[rstest]
    #[should_panic]
    fn pow_frame_rejects_an_unknown_round_kind() {
        let mut table = PowFrameTable::new();
        push_pow_frames(&mut table, 1, &plan(), &pow_trace())
            .expect("recorded PoW frame is canonical");
        table.pow_kind[0] = 3;
        assert_frame_table_satisfies_constraints(table);
    }

    #[rstest]
    fn pow_frame_requires_one_kind_per_recorded_check() {
        let mut trace = pow_trace();
        trace.pow_checks.pop();
        let result = push_pow_frames(&mut PowFrameTable::new(), 1, &plan(), &trace);
        assert_eq!(
            result,
            Err(PowFrameError::KindCountMismatch {
                expected: 1,
                actual: 2,
            })
        );
    }

    #[rstest]
    fn pow_frame_uses_the_plan_difficulty() {
        let mut trace = pow_trace();
        trace.pow_checks[0].bits = 7;
        let call_id = trace.pow_checks[0].call_id;
        let result = push_pow_frames(&mut PowFrameTable::new(), 1, &plan(), &trace);
        assert_eq!(
            result,
            Err(PowFrameError::BitsMismatch {
                call_id,
                expected: 8,
                actual: 7,
            })
        );
    }

    #[rstest]
    fn pow_frame_constraint_profile_stays_cubic() {
        use stwo_constraint_framework::expr::ExprEvaluator;

        let eval = FrameEval {
            log_size: 4,
            pow_relations: PowRelations::dummy(),
            binding_relations: TranscriptBindingRelations::dummy(),
        };
        let degrees = eval
            .evaluate(ExprEvaluator::new())
            .constraint_degree_bounds();
        assert_eq!((degrees.len(), degrees.into_iter().max()), (3, Some(3)));
    }
}
