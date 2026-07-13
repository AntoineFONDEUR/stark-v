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
}

use prover_columns::PowCheckColumns;

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

#[cfg(test)]
mod tests {
    use air::digest::M31Word;
    use rstest::rstest;
    use stwo::core::pcs::TreeVec;
    use stwo::core::poly::circle::CanonicCoset;
    use stwo_constraint_framework::assert_constraints_on_polys;

    use super::*;

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
}
