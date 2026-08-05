//! Control-step consumer for universal public-LogUp verification.
//!
//! Verifier preprocessing extracts the exact sequential public-term steps and
//! the following global-zero assertion from both trusted verifier plans.
//! Segment mode consumes the VM lane, binary mode consumes both recursion
//! assertions, and empty mode consumes neither lane.

use core::fmt;

use simd::AlignedVec;
use stwo::core::ColumnVec;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::QM31;
use stwo::core::poly::circle::CanonicCoset;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;

use super::control_air::ControlRelations;
use super::kernel::{VerifierControlPlan, VerifierSchema, VerifierStep};
use super::wire::ProofKind;

const MIN_LOG_SIZE: u32 = 4;
const MAX_LOG_SIZE: u32 = 30;

const ROW_MASK_COLUMN: usize = 0;
const SEGMENT_MASK_COLUMN: usize = 1;
const VERIFIER_ID_COLUMN: usize = 2;
const SEQUENCE_COLUMN: usize = 3;
const TAG_COLUMN: usize = 4;
const ARG_0_COLUMN: usize = 5;
const ARG_1_COLUMN: usize = 6;
const ARG_2_COLUMN: usize = 7;
const ARG_3_COLUMN: usize = 8;
const PREPROCESSED_COLUMN_COUNT: usize = 9;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PreprocessedRow {
    segment_mask: u32,
    verifier_id: u32,
    sequence: u32,
    tag: u32,
    args: [u32; 4],
}

/// Trusted universal public-LogUp control rows for fixed term counts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VmPublicLogupControlPreprocessed {
    log_size: u32,
    rows: Vec<PreprocessedRow>,
    vm_public_term_count: u32,
    recursion_public_term_count: u32,
}

impl VmPublicLogupControlPreprocessed {
    pub fn new(
        vm_plan: &VerifierControlPlan,
        vm_public_term_count: u32,
        recursion_plan: &VerifierControlPlan,
        recursion_public_term_count: u32,
    ) -> Result<Self, VmPublicLogupControlError> {
        if vm_plan.schema() != VerifierSchema::Vm {
            return Err(VmPublicLogupControlError::SchemaMismatch {
                lane: "segment",
                expected: VerifierSchema::Vm,
                actual: vm_plan.schema(),
            });
        }
        if recursion_plan.schema() != VerifierSchema::Recursion {
            return Err(VmPublicLogupControlError::SchemaMismatch {
                lane: "binary",
                expected: VerifierSchema::Recursion,
                actual: recursion_plan.schema(),
            });
        }
        let mut rows = validated_rows(
            vm_plan,
            vm_public_term_count,
            super::control_air::SEGMENT_VERIFIER_ID,
        )?;
        rows.extend(validated_rows(
            recursion_plan,
            recursion_public_term_count,
            super::control_air::LEFT_RECURSION_VERIFIER_ID,
        )?);
        rows.extend(validated_rows(
            recursion_plan,
            recursion_public_term_count,
            super::control_air::RIGHT_RECURSION_VERIFIER_ID,
        )?);
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
            vm_public_term_count,
            recursion_public_term_count,
        })
    }

    pub const fn log_size(&self) -> u32 {
        self.log_size
    }

    pub const fn vm_public_term_count(&self) -> u32 {
        self.vm_public_term_count
    }

    pub const fn recursion_public_term_count(&self) -> u32 {
        self.recursion_public_term_count
    }

    pub fn row_count(&self) -> usize {
        self.rows.len()
    }

    pub fn column_ids() -> Vec<PreProcessedColumnId> {
        preprocessed_column_ids()
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
            columns[SEGMENT_MASK_COLUMN][index] = row.segment_mask;
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
}

fn validated_rows(
    plan: &VerifierControlPlan,
    public_term_count: u32,
    verifier_id: u32,
) -> Result<Vec<PreprocessedRow>, VmPublicLogupControlError> {
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
                rows.push(encoded_row(sequence, step, verifier_id)?);
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
                rows.push(encoded_row(sequence, step, verifier_id)?);
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
    Ok(rows)
}

fn encoded_row(
    sequence: usize,
    step: VerifierStep,
    verifier_id: u32,
) -> Result<PreprocessedRow, VmPublicLogupControlError> {
    let sequence = u32::try_from(sequence)
        .map_err(|_| VmPublicLogupControlError::SequenceOutOfRange { sequence })?;
    let encoded = step.encode();
    Ok(PreprocessedRow {
        segment_mask: u32::from(verifier_id == super::control_air::SEGMENT_VERIFIER_ID),
        verifier_id,
        sequence,
        tag: encoded.tag(),
        args: encoded.args(),
    })
}

stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [],
    embedded_component: true,
    embedded_relations: crate::control_air::ControlRelations,
    embedded_preprocessed: {
        row_mask: "recursion_vm_public_logup_control_row_mask",
        segment_mask: "recursion_vm_public_logup_control_segment_mask",
        verifier_id: "recursion_vm_public_logup_control_verifier_id",
        sequence: "recursion_vm_public_logup_control_sequence",
        tag: "recursion_vm_public_logup_control_tag",
        arg_0: "recursion_vm_public_logup_control_arg_0",
        arg_1: "recursion_vm_public_logup_control_arg_1",
        arg_2: "recursion_vm_public_logup_control_arg_2",
        arg_3: "recursion_vm_public_logup_control_arg_3",
    },
    embedded_params: [segment_active, binary_active],

    relation step(7);

    fn vm_public_logup_control(
        row_mask,
        segment_mask,
        verifier_id,
        sequence,
        tag,
        arg_0,
        arg_1,
        arg_2,
        arg_3,
        segment_active,
        binary_active,
    ) {
        let binary_mask = 1 - segment_mask;
        let active = row_mask
            * (segment_mask * segment_active + binary_mask * binary_active);
        consume(active) step(
            verifier_id,
            sequence,
            tag,
            arg_0,
            arg_1,
            arg_2,
            arg_3,
        );
        return sequence;
    }
}

pub use component::air::{Component, Eval};

/// Construct the generated consumer with verifier-owned proof-kind selectors.
pub fn eval_for_proof_kind(
    log_size: u32,
    proof_kind: ProofKind,
    control_relations: ControlRelations,
) -> Eval {
    Eval {
        log_size,
        segment_active: BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        binary_active: BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode)),
        relations: control_relations,
    }
}

/// Generates the negative control-step fractions for the active verifier lanes.
pub fn gen_interaction_trace(
    preprocessed: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    proof_kind: ProofKind,
    control_relations: &ControlRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    component::witness::gen_interaction_trace(
        preprocessed,
        BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode)),
        control_relations,
    )
}

/// Invalid universal public-LogUp control slice.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VmPublicLogupControlError {
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
    NonCanonicalTermIndex {
        expected: u32,
        actual: u32,
    },
    TermCountOverflow,
    TermCountMismatch {
        expected: u32,
        actual: u32,
    },
    TermAfterGlobalAssertion {
        term: u32,
    },
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
    use stwo_constraint_framework::{FrameworkEval, Relation, assert_constraints_on_polys};

    use super::*;
    use crate::control_air::SEGMENT_VERIFIER_ID;
    use crate::kernel::VerifierProgramSpec;
    use crate::protocol::{FixedProofShape, OptionalM31Word, PcsParameters};

    const TERM_COUNT: u32 = 5;

    fn word(value: u16) -> air::digest::M31Word {
        air::digest::M31Word::from(value)
    }

    fn plan(schema: VerifierSchema, public_term_count: u32) -> VerifierControlPlan {
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
        let spec = VerifierProgramSpec::new(schema, 4, public_term_count, 7, 3)
            .expect("fixture verifier program has every phase");
        VerifierControlPlan::new(spec, pcs, &shape).expect("fixture shape matches its PCS profile")
    }

    fn preprocessing() -> VmPublicLogupControlPreprocessed {
        VmPublicLogupControlPreprocessed::new(
            &plan(VerifierSchema::Vm, TERM_COUNT),
            TERM_COUNT,
            &plan(VerifierSchema::Recursion, 0),
            0,
        )
        .expect("fixture public control slices are exact")
    }

    fn assert_constraints(kind: ProofKind) {
        let preprocessing = preprocessing();
        let control_relations = ControlRelations::dummy();
        let preprocessed = preprocessing.gen_columns();
        let (interaction, claimed_sum) =
            gen_interaction_trace(&preprocessed, kind, &control_relations);
        let traces = TreeVec::new(vec![preprocessed, vec![], interaction]);
        let trace_polys = traces.map_cols(|column| column.interpolate());
        let eval = eval_for_proof_kind(preprocessing.log_size(), kind, control_relations);
        assert_constraints_on_polys(
            &trace_polys,
            CanonicCoset::new(preprocessing.log_size()),
            |row| {
                eval.evaluate(row);
            },
            claimed_sum,
        );
    }

    fn bridge_sum(kind: ProofKind) -> QM31 {
        let preprocessing = preprocessing();
        let mut channel = Poseidon2M31Channel::default();
        let relations = ControlRelations::draw(&mut channel);
        let (_, consumer_sum) =
            gen_interaction_trace(&preprocessing.gen_columns(), kind, &relations);
        preprocessing
            .rows
            .iter()
            .filter(|row| match kind {
                ProofKind::SegmentLeaf => row.verifier_id == SEGMENT_VERIFIER_ID,
                ProofKind::BinaryNode => row.verifier_id != SEGMENT_VERIFIER_ID,
                ProofKind::EmptyLeaf => false,
            })
            .fold(consumer_sum, |sum, row| {
                let denominator: QM31 = relations.step.combine(&[
                    M31::from(row.verifier_id),
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
    fn every_universal_mode_satisfies_public_control_constraints(#[case] kind: ProofKind) {
        assert_constraints(kind);
    }

    #[rstest]
    #[case::segment(ProofKind::SegmentLeaf)]
    #[case::binary(ProofKind::BinaryNode)]
    #[case::empty(ProofKind::EmptyLeaf)]
    fn public_logup_control_steps_close_exactly(#[case] kind: ProofKind) {
        assert!(bridge_sum(kind).is_zero());
    }

    #[rstest]
    fn mismatched_public_term_count_is_rejected() {
        assert_eq!(
            VmPublicLogupControlPreprocessed::new(
                &plan(VerifierSchema::Vm, TERM_COUNT),
                TERM_COUNT - 1,
                &plan(VerifierSchema::Recursion, 0),
                0,
            ),
            Err(VmPublicLogupControlError::TermCountMismatch {
                expected: TERM_COUNT - 1,
                actual: TERM_COUNT,
            })
        );
    }
}
