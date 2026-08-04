//! Trusted universal control program for recursion.
//!
//! The preprocessed trace contains one VM verifier lane and two recursion
//! verifier lanes. Public proof-kind constants activate only the segment lane
//! or both binary lanes; an empty leaf activates none. Every active row emits
//! its exact `(verifier, sequence, tag, args)` tuple, so downstream gadgets
//! must discharge every mandatory verifier step without proof-selected
//! control flow.

use core::fmt;

use simd::AlignedVec;
use stwo::core::ColumnVec;
use stwo::core::channel::Channel;
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
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, RelationEntry, relation,
};

use super::kernel::{VerifierControlPlan, VerifierSchema};
use super::wire::ProofKind;

pub const SEGMENT_VERIFIER_ID: u32 = 0;
pub const LEFT_RECURSION_VERIFIER_ID: u32 = 1;
pub const RIGHT_RECURSION_VERIFIER_ID: u32 = 2;

const MIN_LOG_SIZE: u32 = 4;
const MAX_LOG_SIZE: u32 = 30;
const CONTROL_COLUMN_COUNT: usize = 9;
const SEGMENT_MASK_COLUMN: usize = 0;
const BINARY_MASK_COLUMN: usize = 1;
const VERIFIER_ID_COLUMN: usize = 2;
const SEQUENCE_COLUMN: usize = 3;
const TAG_COLUMN: usize = 4;
const ARG_0_COLUMN: usize = 5;
const ARG_1_COLUMN: usize = 6;
const ARG_2_COLUMN: usize = 7;
const ARG_3_COLUMN: usize = 8;

const CONTROL_COLUMN_IDS: [&str; CONTROL_COLUMN_COUNT] = [
    "recursion_control_segment_mask",
    "recursion_control_binary_mask",
    "recursion_control_verifier_id",
    "recursion_control_sequence",
    "recursion_control_tag",
    "recursion_control_arg_0",
    "recursion_control_arg_1",
    "recursion_control_arg_2",
    "recursion_control_arg_3",
];

relation!(VerifierStepRelation, 7);

#[derive(Clone)]
pub struct ControlRelations {
    pub step: VerifierStepRelation,
}

impl ControlRelations {
    pub fn dummy() -> Self {
        Self {
            step: VerifierStepRelation::dummy(),
        }
    }

    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            step: VerifierStepRelation::draw(channel),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ControlRow {
    segment_mask: u32,
    binary_mask: u32,
    verifier_id: u32,
    sequence: u32,
    tag: u32,
    args: [u32; 4],
}

/// Preprocessed control columns derived only from the two trusted verifier plans.
#[derive(Clone, Debug)]
pub struct ControlPreprocessed {
    log_size: u32,
    rows: Vec<ControlRow>,
    vm_step_count: usize,
    recursion_step_count: usize,
}

impl ControlPreprocessed {
    pub fn new(
        vm: &VerifierControlPlan,
        recursion: &VerifierControlPlan,
    ) -> Result<Self, ControlLayoutError> {
        if vm.schema() != VerifierSchema::Vm {
            return Err(ControlLayoutError::SchemaMismatch {
                lane: "segment",
                expected: VerifierSchema::Vm,
                actual: vm.schema(),
            });
        }
        if recursion.schema() != VerifierSchema::Recursion {
            return Err(ControlLayoutError::SchemaMismatch {
                lane: "binary",
                expected: VerifierSchema::Recursion,
                actual: recursion.schema(),
            });
        }

        let row_count = vm
            .steps()
            .len()
            .checked_add(
                recursion
                    .steps()
                    .len()
                    .checked_mul(2)
                    .ok_or(ControlLayoutError::RowCountOverflow)?,
            )
            .ok_or(ControlLayoutError::RowCountOverflow)?;
        let padded_rows = row_count
            .checked_next_power_of_two()
            .ok_or(ControlLayoutError::RowCountOverflow)?
            .max(1 << MIN_LOG_SIZE);
        let log_size = padded_rows.ilog2();
        if log_size > MAX_LOG_SIZE {
            return Err(ControlLayoutError::LogSizeOutOfRange { log_size });
        }

        let mut rows = Vec::with_capacity(row_count);
        append_plan_rows(&mut rows, vm, SEGMENT_VERIFIER_ID, 1, 0)?;
        append_plan_rows(&mut rows, recursion, LEFT_RECURSION_VERIFIER_ID, 0, 1)?;
        append_plan_rows(&mut rows, recursion, RIGHT_RECURSION_VERIFIER_ID, 0, 1)?;
        Ok(Self {
            log_size,
            rows,
            vm_step_count: vm.steps().len(),
            recursion_step_count: recursion.steps().len(),
        })
    }

    pub const fn log_size(&self) -> u32 {
        self.log_size
    }

    pub fn column_ids() -> Vec<PreProcessedColumnId> {
        CONTROL_COLUMN_IDS
            .iter()
            .map(|id| PreProcessedColumnId { id: (*id).into() })
            .collect()
    }

    pub fn gen_columns(
        &self,
    ) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
        let size = 1_usize << self.log_size;
        let mut columns = (0..CONTROL_COLUMN_COUNT)
            .map(|_| {
                let mut column = AlignedVec::with_capacity(size);
                column.resize(size, 0);
                column
            })
            .collect::<Vec<_>>();
        for (index, row) in self.rows.iter().copied().enumerate() {
            columns[SEGMENT_MASK_COLUMN][index] = row.segment_mask;
            columns[BINARY_MASK_COLUMN][index] = row.binary_mask;
            columns[VERIFIER_ID_COLUMN][index] = row.verifier_id;
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

    pub const fn active_step_count(&self, kind: ProofKind) -> usize {
        match kind {
            ProofKind::SegmentLeaf => self.vm_step_count,
            ProofKind::BinaryNode => 2 * self.recursion_step_count,
            ProofKind::EmptyLeaf => 0,
        }
    }
}

fn append_plan_rows(
    rows: &mut Vec<ControlRow>,
    plan: &VerifierControlPlan,
    verifier_id: u32,
    segment_mask: u32,
    binary_mask: u32,
) -> Result<(), ControlLayoutError> {
    for (sequence, step) in plan.steps().iter().copied().enumerate() {
        let sequence = u32::try_from(sequence)
            .map_err(|_| ControlLayoutError::SequenceOutOfRange { sequence })?;
        let encoded = step.encode();
        rows.push(ControlRow {
            segment_mask,
            binary_mask,
            verifier_id,
            sequence,
            tag: encoded.tag(),
            args: encoded.args(),
        });
    }
    Ok(())
}

pub type Component = FrameworkComponent<Eval>;

#[derive(Clone)]
pub struct Eval {
    pub log_size: u32,
    pub proof_kind: ProofKind,
    pub relations: ControlRelations,
}

impl FrameworkEval for Eval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let column_ids = ControlPreprocessed::column_ids();
        let segment_mask = eval.get_preprocessed_column(column_ids[SEGMENT_MASK_COLUMN].clone());
        let binary_mask = eval.get_preprocessed_column(column_ids[BINARY_MASK_COLUMN].clone());
        let verifier_id = eval.get_preprocessed_column(column_ids[VERIFIER_ID_COLUMN].clone());
        let sequence = eval.get_preprocessed_column(column_ids[SEQUENCE_COLUMN].clone());
        let tag = eval.get_preprocessed_column(column_ids[TAG_COLUMN].clone());
        let arg_0 = eval.get_preprocessed_column(column_ids[ARG_0_COLUMN].clone());
        let arg_1 = eval.get_preprocessed_column(column_ids[ARG_1_COLUMN].clone());
        let arg_2 = eval.get_preprocessed_column(column_ids[ARG_2_COLUMN].clone());
        let arg_3 = eval.get_preprocessed_column(column_ids[ARG_3_COLUMN].clone());
        let segment_active = BaseField::from(u32::from(self.proof_kind == ProofKind::SegmentLeaf));
        let binary_active = BaseField::from(u32::from(self.proof_kind == ProofKind::BinaryNode));
        let enabled = segment_mask * segment_active + binary_mask * binary_active;
        eval.add_to_relation(RelationEntry::new(
            &self.relations.step,
            E::EF::from(enabled),
            &[verifier_id, sequence, tag, arg_0, arg_1, arg_2, arg_3],
        ));
        eval.finalize_logup();
        eval
    }
}

/// Generates the interaction trace for the proof-kind-selected control lanes.
pub fn gen_interaction_trace(
    preprocessed: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    proof_kind: ProofKind,
    relations: &ControlRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    let columns = preprocessed
        .iter()
        .map(|column| &column.values.data)
        .collect::<Vec<_>>();
    let segment_active = BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf));
    let binary_active = BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode));
    let numerator: Vec<PackedQM31> = (0..columns[SEGMENT_MASK_COLUMN].len())
        .map(|row| {
            PackedQM31::from(
                columns[SEGMENT_MASK_COLUMN][row] * segment_active
                    + columns[BINARY_MASK_COLUMN][row] * binary_active,
            )
        })
        .collect();
    let denominator = combine!(
        relations.step,
        [
            columns[VERIFIER_ID_COLUMN],
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ControlLayoutError {
    SchemaMismatch {
        lane: &'static str,
        expected: VerifierSchema,
        actual: VerifierSchema,
    },
    RowCountOverflow,
    LogSizeOutOfRange {
        log_size: u32,
    },
    SequenceOutOfRange {
        sequence: usize,
    },
}

impl fmt::Display for ControlLayoutError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SchemaMismatch {
                lane,
                expected,
                actual,
            } => write!(
                formatter,
                "{lane} control lane requires {expected:?}, got {actual:?}"
            ),
            Self::RowCountOverflow => write!(formatter, "control row count overflowed"),
            Self::LogSizeOutOfRange { log_size } => write!(
                formatter,
                "control log size {log_size} exceeds the supported maximum {MAX_LOG_SIZE}"
            ),
            Self::SequenceOutOfRange { sequence } => {
                write!(formatter, "control sequence {sequence} does not fit u32")
            }
        }
    }
}

impl std::error::Error for ControlLayoutError {}

#[cfg(test)]
mod tests {
    use air::digest::M31Word;
    use rstest::rstest;
    use stwo::core::pcs::TreeVec;
    use stwo_constraint_framework::assert_constraints_on_polys;

    use super::*;
    use crate::kernel::{VerifierProgramSpec, VerifierStep};
    use crate::protocol::{FixedProofShape, OptionalM31Word, PcsParameters};

    fn word(value: u16) -> M31Word {
        M31Word::from(value)
    }

    fn pcs() -> PcsParameters {
        PcsParameters {
            interaction_pow_bits: word(8),
            pow_bits: word(10),
            fri_log_blowup_factor: word(1),
            fri_n_queries: word(9),
            fri_log_last_layer_degree_bound: M31Word::ZERO,
            fri_fold_step: word(2),
            lifting_log_size: OptionalM31Word::Some(word(8)),
        }
    }

    fn shape() -> FixedProofShape<2, 4, 4> {
        FixedProofShape {
            claimed_sum_count: word(7),
            sampled_value_count: word(8),
            queried_value_count: word(36),
            trace_path_count: word(36),
            raw_query_count: word(9),
            last_layer_coefficient_count: word(1),
            table_log_sizes: [word(5), word(6)],
            tree_heights: [word(8), word(8), word(8), word(8)],
            fri_layer_fold_widths: [word(4), word(4), word(4), word(2)],
            fri_layer_tree_heights: [word(6), word(4), word(2), word(2)],
        }
    }

    fn plan(schema: VerifierSchema) -> VerifierControlPlan {
        let spec = VerifierProgramSpec::new(schema, 3, 5, 7, 4)
            .expect("fixture program has every mandatory phase");
        VerifierControlPlan::new(spec, pcs(), &shape())
            .expect("fixture shape matches the PCS profile")
    }

    fn preprocessing() -> ControlPreprocessed {
        ControlPreprocessed::new(&plan(VerifierSchema::Vm), &plan(VerifierSchema::Recursion))
            .expect("fixture plans occupy their canonical lanes")
    }

    fn assert_control_constraints(kind: ProofKind) {
        let preprocessing = preprocessing();
        let relations = ControlRelations::dummy();
        let preprocessed = preprocessing.gen_columns();
        let (interaction, claimed_sum) = gen_interaction_trace(&preprocessed, kind, &relations);
        let traces = TreeVec::new(vec![preprocessed, vec![], interaction]);
        let trace_polys = traces.map_cols(|column| column.interpolate());
        let eval = Eval {
            log_size: preprocessing.log_size(),
            proof_kind: kind,
            relations,
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
    fn every_universal_mode_satisfies_the_control_component(#[case] kind: ProofKind) {
        assert_control_constraints(kind);
    }

    #[rstest]
    #[case::segment(ProofKind::SegmentLeaf, 1)]
    #[case::binary(ProofKind::BinaryNode, 2)]
    #[case::empty(ProofKind::EmptyLeaf, 0)]
    fn proof_kind_activates_only_its_verifier_lanes(
        #[case] kind: ProofKind,
        #[case] lane_multiplier: usize,
    ) {
        let vm = plan(VerifierSchema::Vm);
        let recursion = plan(VerifierSchema::Recursion);
        let preprocessing =
            ControlPreprocessed::new(&vm, &recursion).expect("fixture lanes are valid");
        let expected = match kind {
            ProofKind::SegmentLeaf => lane_multiplier * vm.steps().len(),
            ProofKind::BinaryNode => lane_multiplier * recursion.steps().len(),
            ProofKind::EmptyLeaf => 0,
        };
        assert_eq!(preprocessing.active_step_count(kind), expected);
    }

    #[rstest]
    fn control_rows_use_fixed_zero_filled_step_arguments() {
        let vm = plan(VerifierSchema::Vm);
        assert!(vm.steps().iter().copied().all(|step| {
            let encoded = step.encode();
            encoded.arity() <= 4
                && encoded.args()[encoded.arity() as usize..]
                    .iter()
                    .all(|value| *value == 0)
        }));
    }

    #[rstest]
    fn control_layout_rejects_swapped_schema_lanes() {
        let vm = plan(VerifierSchema::Vm);
        let result = ControlPreprocessed::new(&vm, &vm);
        assert!(matches!(
            result,
            Err(ControlLayoutError::SchemaMismatch {
                lane: "binary",
                expected: VerifierSchema::Recursion,
                actual: VerifierSchema::Vm,
            })
        ));
    }

    #[rstest]
    fn complete_step_keeps_the_last_control_tag() {
        assert_eq!(VerifierStep::Complete.encode().tag(), 28);
    }
}
