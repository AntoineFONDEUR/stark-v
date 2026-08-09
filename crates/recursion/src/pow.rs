//! Proof-of-work predicate AIR for recursion.
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
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo_constraint_framework::relation;

use super::transcript::PowCheck;
use super::transcript_binding_air::TranscriptBindingRelations;

const M31_BITS: usize = 31;

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

/// current protocol relations used to connect arithmetic checks to transcript frames.
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

mod pow_check_dsl {
    stwo_macros::define_air_fns! {
        max_degree: 3,
        embedded: [],
        embedded_component: true,
        embedded_relations: crate::pow::PowRelations,
        logup_batch: 1,

        relation check(5);

        fn pow_check(
            verifier_id, pow_kind, call_id, bits, word,
            word_bit: [felt; 31],
            active: [felt; 31],
        ) {
            for bit in 0..31 {
                constrain word_bit[bit] * (1 - word_bit[bit]);
                constrain active[bit] * (1 - active[bit]);
                constrain active[bit] * word_bit[bit];
            }
            for bit in 0..30 {
                constrain (1 - active[bit]) * active[bit + 1];
            }
            constrain word - (
                word_bit[0] + 2 * word_bit[1] + 4 * word_bit[2] + 8 * word_bit[3]
                + 16 * word_bit[4] + 32 * word_bit[5] + 64 * word_bit[6]
                + 128 * word_bit[7] + 256 * word_bit[8] + 512 * word_bit[9]
                + 1024 * word_bit[10] + 2048 * word_bit[11] + 4096 * word_bit[12]
                + 8192 * word_bit[13] + 16384 * word_bit[14] + 32768 * word_bit[15]
                + 65536 * word_bit[16] + 131072 * word_bit[17]
                + 262144 * word_bit[18] + 524288 * word_bit[19]
                + 1048576 * word_bit[20] + 2097152 * word_bit[21]
                + 4194304 * word_bit[22] + 8388608 * word_bit[23]
                + 16777216 * word_bit[24] + 33554432 * word_bit[25]
                + 67108864 * word_bit[26] + 134217728 * word_bit[27]
                + 268435456 * word_bit[28] + 536870912 * word_bit[29]
                + 1073741824 * word_bit[30]
            );
            constrain bits - sum(bit, 0..31, active[bit]);

            consume(enabler) check(verifier_id, pow_kind, call_id, bits, word);

            return word;
        }
    }
}

/// Relation instances shared by the transcript-frame and arithmetic PoW AIRs.
#[derive(Clone)]
pub struct PowFrameRelations {
    pub check: PowCheckRelation,
    pub pow_frame: super::transcript_binding_air::TranscriptPowFrameRelation,
}

impl PowFrameRelations {
    /// Combine the PoW predicate and transcript-frame relation instances.
    pub fn new(
        pow_relations: &PowRelations,
        binding_relations: &TranscriptBindingRelations,
    ) -> Self {
        Self {
            check: pow_relations.check.clone(),
            pow_frame: binding_relations.pow_frame.clone(),
        }
    }
}

mod pow_frame_dsl {
    stwo_macros::define_air_fns! {
        max_degree: 3,
        embedded: [],
        embedded_component: true,
        embedded_relations: crate::pow::PowFrameRelations,
        logup_batch: 2,

        relation pow_frame(14);
        relation check(5);

        fn pow_frame(
            verifier_id, sequence, pow_kind, hash_id, call_id, bits,
            word_0, word_1, word_2, word_3,
            word_4, word_5, word_6, word_7,
        ) {
            let pow_tag = pow_kind * 14 - 8;

            constrain enabler * (pow_kind - 1) * (pow_kind - 2);

            consume(enabler) pow_frame(
                verifier_id, sequence, pow_tag, hash_id, call_id, bits,
                word_0, word_1, word_2, word_3,
                word_4, word_5, word_6, word_7,
            );
            emit(enabler) check(verifier_id, pow_kind, call_id, bits, word_0);

            return word_0;
        }
    }
}

pub use pow_check_dsl::PowCheckTable;
pub use pow_check_dsl::component::air::{Component, Eval};
pub use pow_frame_dsl::PowFrameTable;
pub use pow_frame_dsl::component::air::{Component as FrameComponent, Eval as FrameEval};

/// Construct the frame evaluator with both shared relation bundles.
pub fn frame_eval(
    log_size: u32,
    pow_relations: &PowRelations,
    binding_relations: &TranscriptBindingRelations,
) -> FrameEval {
    FrameEval {
        log_size,
        relations: PowFrameRelations::new(pow_relations, binding_relations),
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
    pow_check_dsl::component::witness::gen_interaction_trace(trace, relations)
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
    pow_frame_dsl::component::witness::gen_interaction_trace(
        trace,
        &PowFrameRelations::new(pow_relations, binding_relations),
    )
}

/// Records one arithmetic PoW check for a fixed verifier invocation.
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
    use stwo_constraint_framework::{FrameworkEval, assert_constraints_on_polys};

    use prover::poseidon2_channel::Poseidon2M31Channel;

    use super::*;
    use crate::kernel::{VerifierControlPlan, VerifierProgramSpec, VerifierSchema};
    use crate::protocol::{FixedProofShape, OptionalM31Word, PcsParameters};
    use crate::transcript::{RecordingTranscriptBackend, TranscriptKernel, TranscriptTrace};

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
        let eval = frame_eval(log_size, &pow_relations, &binding_relations);
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

        let eval = frame_eval(
            4,
            &PowRelations::dummy(),
            &TranscriptBindingRelations::dummy(),
        );
        let degrees = eval
            .evaluate(ExprEvaluator::new())
            .constraint_degree_bounds();
        assert_eq!((degrees.len(), degrees.into_iter().max()), (3, Some(3)));
    }
}
