//! Control-step consumer for VM public-LogUp verification.
//!
//! Verifier preprocessing extracts the exact sequential public-term steps and
//! the following global-zero assertion from the trusted VM plan. Segment mode
//! consumes those control tuples; binary and empty modes leave this VM-only
//! component inactive.

use core::fmt;

use simd::AlignedVec;
use stwo::core::ColumnVec;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::QM31;
use stwo::core::poly::circle::CanonicCoset;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, RelationEntry,
};

use super::control_air::{ControlRelations, SEGMENT_VERIFIER_ID};
use super::kernel::{VerifierControlPlan, VerifierSchema, VerifierStep};
use super::wire::ProofKind;

const MIN_LOG_SIZE: u32 = 4;
const MAX_LOG_SIZE: u32 = 30;

const ROW_MASK_COLUMN: usize = 0;
const SEQUENCE_COLUMN: usize = 1;
const TAG_COLUMN: usize = 2;
const ARG_0_COLUMN: usize = 3;
const ARG_1_COLUMN: usize = 4;
const ARG_2_COLUMN: usize = 5;
const ARG_3_COLUMN: usize = 6;
const PREPROCESSED_COLUMN_COUNT: usize = 7;

const PREPROCESSED_COLUMN_IDS: [&str; PREPROCESSED_COLUMN_COUNT] = [
    "recursion_vm_public_logup_control_row_mask",
    "recursion_vm_public_logup_control_sequence",
    "recursion_vm_public_logup_control_tag",
    "recursion_vm_public_logup_control_arg_0",
    "recursion_vm_public_logup_control_arg_1",
    "recursion_vm_public_logup_control_arg_2",
    "recursion_vm_public_logup_control_arg_3",
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PreprocessedRow {
    sequence: u32,
    tag: u32,
    args: [u32; 4],
}

/// Trusted VM public-LogUp control rows for one fixed term count.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VmPublicLogupControlPreprocessed {
    log_size: u32,
    rows: Vec<PreprocessedRow>,
    public_term_count: u32,
}

impl VmPublicLogupControlPreprocessed {
    pub fn new(
        plan: &VerifierControlPlan,
        public_term_count: u32,
    ) -> Result<Self, VmPublicLogupControlError> {
        if plan.schema() != VerifierSchema::Vm {
            return Err(VmPublicLogupControlError::SchemaMismatch {
                actual: plan.schema(),
            });
        }
        let mut rows = Vec::new();
        let mut expected_term = 0_u32;
        let mut assert_sequence = None;
        for (sequence, step) in plan.steps().iter().copied().enumerate() {
            match step {
                VerifierStep::AccumulatePublicLogupTerm { term } => {
                    if assert_sequence.is_some() {
                        return Err(VmPublicLogupControlError::TermAfterGlobalAssertion { term });
                    }
                    if term != expected_term {
                        return Err(VmPublicLogupControlError::NonCanonicalTermIndex {
                            expected: expected_term,
                            actual: term,
                        });
                    }
                    rows.push(encoded_row(sequence, step)?);
                    expected_term = expected_term
                        .checked_add(1)
                        .ok_or(VmPublicLogupControlError::TermCountOverflow)?;
                }
                VerifierStep::AssertGlobalLogupZero => {
                    if assert_sequence.is_some() {
                        return Err(VmPublicLogupControlError::DuplicateGlobalAssertion);
                    }
                    if expected_term != public_term_count {
                        return Err(VmPublicLogupControlError::TermCountMismatch {
                            expected: public_term_count,
                            actual: expected_term,
                        });
                    }
                    let sequence_u32 = u32::try_from(sequence)
                        .map_err(|_| VmPublicLogupControlError::SequenceOutOfRange { sequence })?;
                    assert_sequence = Some(sequence_u32);
                    rows.push(encoded_row(sequence, step)?);
                }
                _ => {}
            }
        }
        if expected_term != public_term_count {
            return Err(VmPublicLogupControlError::TermCountMismatch {
                expected: public_term_count,
                actual: expected_term,
            });
        }
        if assert_sequence.is_none() {
            return Err(VmPublicLogupControlError::GlobalAssertionMissing);
        }
        let padded_rows = rows
            .len()
            .checked_next_power_of_two()
            .ok_or(VmPublicLogupControlError::RowCountOverflow)?
            .max(1 << MIN_LOG_SIZE);
        let log_size = padded_rows.ilog2();
        if log_size > MAX_LOG_SIZE {
            return Err(VmPublicLogupControlError::LogSizeOutOfRange { log_size });
        }
        Ok(Self {
            log_size,
            rows,
            public_term_count,
        })
    }

    pub const fn log_size(&self) -> u32 {
        self.log_size
    }

    pub const fn public_term_count(&self) -> u32 {
        self.public_term_count
    }

    pub fn row_count(&self) -> usize {
        self.rows.len()
    }

    pub fn column_ids() -> Vec<PreProcessedColumnId> {
        PREPROCESSED_COLUMN_IDS
            .iter()
            .map(|id| PreProcessedColumnId { id: (*id).into() })
            .collect()
    }

    pub fn gen_columns(
        &self,
    ) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
        let size = 1_usize << self.log_size;
        let mut columns = (0..PREPROCESSED_COLUMN_COUNT)
            .map(|_| {
                let mut column = AlignedVec::with_capacity(size);
                column.resize(size, 0);
                column
            })
            .collect::<Vec<_>>();
        for (index, row) in self.rows.iter().copied().enumerate() {
            columns[ROW_MASK_COLUMN][index] = 1;
            columns[SEQUENCE_COLUMN][index] = row.sequence;
            columns[TAG_COLUMN][index] = row.tag;
            columns[ARG_0_COLUMN][index] = row.args[0];
            columns[ARG_1_COLUMN][index] = row.args[1];
            columns[ARG_2_COLUMN][index] = row.args[2];
            columns[ARG_3_COLUMN][index] = row.args[3];
        }
        let domain = CanonicCoset::new(self.log_size).circle_domain();
        columns
            .into_iter()
            .map(|column| CircleEvaluation::new(domain, BaseColumn::from(column)))
            .collect()
    }
}

fn encoded_row(
    sequence: usize,
    step: VerifierStep,
) -> Result<PreprocessedRow, VmPublicLogupControlError> {
    let sequence = u32::try_from(sequence)
        .map_err(|_| VmPublicLogupControlError::SequenceOutOfRange { sequence })?;
    let encoded = step.encode();
    Ok(PreprocessedRow {
        sequence,
        tag: encoded.tag(),
        args: encoded.args(),
    })
}

pub type Component = FrameworkComponent<Eval>;

#[derive(Clone)]
pub struct Eval {
    pub log_size: u32,
    pub proof_kind: ProofKind,
    pub control_relations: ControlRelations,
}

impl FrameworkEval for Eval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let ids = VmPublicLogupControlPreprocessed::column_ids();
        let row_mask = eval.get_preprocessed_column(ids[ROW_MASK_COLUMN].clone());
        let sequence = eval.get_preprocessed_column(ids[SEQUENCE_COLUMN].clone());
        let tag = eval.get_preprocessed_column(ids[TAG_COLUMN].clone());
        let arg_0 = eval.get_preprocessed_column(ids[ARG_0_COLUMN].clone());
        let arg_1 = eval.get_preprocessed_column(ids[ARG_1_COLUMN].clone());
        let arg_2 = eval.get_preprocessed_column(ids[ARG_2_COLUMN].clone());
        let arg_3 = eval.get_preprocessed_column(ids[ARG_3_COLUMN].clone());
        let segment = BaseField::from(u32::from(self.proof_kind == ProofKind::SegmentLeaf));
        eval.add_to_relation(RelationEntry::new(
            &self.control_relations.step,
            -E::EF::from(row_mask * segment),
            &[
                E::F::from(BaseField::from(SEGMENT_VERIFIER_ID)),
                sequence,
                tag,
                arg_0,
                arg_1,
                arg_2,
                arg_3,
            ],
        ));
        eval.finalize_logup();
        eval
    }
}

/// Generates the negative control-step fractions for segment mode.
pub fn gen_interaction_trace(
    preprocessed: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    proof_kind: ProofKind,
    control_relations: &ControlRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    let columns = preprocessed
        .iter()
        .map(|column| &column.values.data)
        .collect::<Vec<_>>();
    let segment = BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf));
    let numerator = (0..columns[ROW_MASK_COLUMN].len())
        .map(|row| -PackedQM31::from(columns[ROW_MASK_COLUMN][row] * segment))
        .collect::<Vec<_>>();
    let verifier_id = vec![
        stwo::prover::backend::simd::m31::PackedM31::broadcast(BaseField::from(
            SEGMENT_VERIFIER_ID,
        ));
        columns[ROW_MASK_COLUMN].len()
    ];
    let denominator = combine!(
        control_relations.step,
        [
            verifier_id,
            columns[SEQUENCE_COLUMN],
            columns[TAG_COLUMN],
            columns[ARG_0_COLUMN],
            columns[ARG_1_COLUMN],
            columns[ARG_2_COLUMN],
            columns[ARG_3_COLUMN]
        ]
    );
    let mut logup_gen = LogupTraceGenerator::new(preprocessed[0].domain.log_size());
    write_col!(&numerator, &denominator, logup_gen);
    logup_gen.finalize_last()
}

/// Invalid VM public-LogUp control slice.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VmPublicLogupControlError {
    SchemaMismatch { actual: VerifierSchema },
    RowCountOverflow,
    LogSizeOutOfRange { log_size: u32 },
    SequenceOutOfRange { sequence: usize },
    NonCanonicalTermIndex { expected: u32, actual: u32 },
    TermCountOverflow,
    TermCountMismatch { expected: u32, actual: u32 },
    TermAfterGlobalAssertion { term: u32 },
    DuplicateGlobalAssertion,
    GlobalAssertionMissing,
}

impl fmt::Display for VmPublicLogupControlError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for VmPublicLogupControlError {}

#[cfg(test)]
mod tests {
    use num_traits::Zero;
    use prover::poseidon2_channel::Poseidon2M31Channel;
    use rstest::rstest;
    use stwo::core::fields::FieldExpOps;
    use stwo::core::fields::m31::M31;
    use stwo::core::pcs::TreeVec;
    use stwo_constraint_framework::{Relation, assert_constraints_on_polys};

    use super::*;
    use crate::kernel::VerifierProgramSpec;
    use crate::protocol::{FixedProofShape, OptionalM31Word, PcsParameters};

    const TERM_COUNT: u32 = 5;

    fn word(value: u16) -> air::digest::M31Word {
        air::digest::M31Word::from(value)
    }

    fn plan() -> VerifierControlPlan {
        let pcs = PcsParameters {
            interaction_pow_bits: word(8),
            pow_bits: word(10),
            fri_log_blowup_factor: word(1),
            fri_n_queries: word(9),
            fri_log_last_layer_degree_bound: air::digest::M31Word::ZERO,
            fri_fold_step: word(2),
            lifting_log_size: OptionalM31Word::Some(word(8)),
        };
        let shape = FixedProofShape {
            claimed_sum_count: word(7),
            sampled_value_count: word(8),
            queried_value_count: word(36),
            trace_path_count: word(36),
            raw_query_count: word(9),
            last_layer_coefficient_count: word(1),
            table_log_sizes: [word(5), word(6)],
            tree_heights: [word(8); 4],
            fri_layer_fold_widths: [word(4), word(4), word(4), word(2)],
            fri_layer_tree_heights: [word(6), word(4), word(2), word(2)],
        };
        let spec = VerifierProgramSpec::new(VerifierSchema::Vm, 4, TERM_COUNT, 7, 3)
            .expect("fixture VM program has every phase");
        VerifierControlPlan::new(spec, pcs, &shape).expect("fixture shape matches its PCS profile")
    }

    fn assert_constraints(kind: ProofKind) {
        let preprocessing = VmPublicLogupControlPreprocessed::new(&plan(), TERM_COUNT)
            .expect("fixture public control slice is exact");
        let control_relations = ControlRelations::dummy();
        let preprocessed = preprocessing.gen_columns();
        let (interaction, claimed_sum) =
            gen_interaction_trace(&preprocessed, kind, &control_relations);
        let traces = TreeVec::new(vec![preprocessed, vec![], interaction]);
        let trace_polys = traces.map_cols(|column| column.interpolate());
        let eval = Eval {
            log_size: preprocessing.log_size(),
            proof_kind: kind,
            control_relations,
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

    fn bridge_sum() -> QM31 {
        let preprocessing = VmPublicLogupControlPreprocessed::new(&plan(), TERM_COUNT)
            .expect("fixture public control slice is exact");
        let mut channel = Poseidon2M31Channel::default();
        let relations = ControlRelations::draw(&mut channel);
        let (_, consumer_sum) = gen_interaction_trace(
            &preprocessing.gen_columns(),
            ProofKind::SegmentLeaf,
            &relations,
        );
        preprocessing.rows.iter().fold(consumer_sum, |sum, row| {
            let denominator: QM31 = relations.step.combine(&[
                M31::from(SEGMENT_VERIFIER_ID),
                M31::from(row.sequence),
                M31::from(row.tag),
                M31::from(row.args[0]),
                M31::from(row.args[1]),
                M31::from(row.args[2]),
                M31::from(row.args[3]),
            ]);
            sum + denominator.inverse()
        })
    }

    #[rstest]
    #[case::segment(ProofKind::SegmentLeaf)]
    #[case::binary(ProofKind::BinaryNode)]
    #[case::empty(ProofKind::EmptyLeaf)]
    fn every_universal_mode_satisfies_vm_public_control_constraints(#[case] kind: ProofKind) {
        assert_constraints(kind);
    }

    #[rstest]
    fn public_logup_control_steps_close_exactly() {
        assert!(bridge_sum().is_zero());
    }

    #[rstest]
    fn mismatched_public_term_count_is_rejected() {
        assert_eq!(
            VmPublicLogupControlPreprocessed::new(&plan(), TERM_COUNT - 1),
            Err(VmPublicLogupControlError::TermCountMismatch {
                expected: TERM_COUNT - 1,
                actual: TERM_COUNT,
            })
        );
    }
}
