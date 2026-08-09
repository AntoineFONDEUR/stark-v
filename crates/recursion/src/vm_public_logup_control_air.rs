//! Public-LogUp control and joint segment-proof binding.
//!
//! Verifier preprocessing extracts the exact sequential public-term steps and
//! the relation assertions that follow them from both trusted verifier plans.
//! Segment mode consumes the VM shared-relation assertions, binary mode
//! consumes both recursion zero-sum assertions, and empty mode consumes none.
//! Segment-only rows also bind both interaction seeds and nonces and constrain
//! the VM shared-relation sum to cancel the Poseidon2 claimed sum.

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

use super::control_air::{
    ControlRelations, POSEIDON2_VERIFIER_ID, SEGMENT_VERIFIER_ID, VerifierStepRelation,
};
use super::kernel::{VerifierControlPlan, VerifierSchema, VerifierStep};
use super::transcript_payload_air::VerifierInputWordRelation;
use super::transcript_payload_air::{VerifierInputKind, VerifierInputRelations};
use super::verifier_randomness_air::{
    VerifierRandomnessKind, VerifierRandomnessRelations, VerifierRandomnessWordRelation,
};
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
const CONTROL_MASK_COLUMN: usize = 9;
const SEED_MASK_COLUMN: usize = 10;
const NONCE_MASK_COLUMN: usize = 11;
const CANCELLATION_MASK_COLUMN: usize = 12;
const ITEM_INDEX_COLUMN: usize = 13;
const LIMB_INDEX_COLUMN: usize = 14;
const PREPROCESSED_COLUMN_COUNT: usize = 15;
const VM_ASSERTIONS: [VerifierStep; 2] = [
    VerifierStep::AssertVmSharedRelation,
    VerifierStep::AssertSegmentSharedRelationZero,
];
const RECURSION_ASSERTIONS: [VerifierStep; 1] = [VerifierStep::AssertGlobalLogupZero];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PreprocessedRow {
    segment_mask: u32,
    verifier_id: u32,
    sequence: u32,
    tag: u32,
    args: [u32; 4],
    binder: BinderKind,
    item_index: u32,
    limb_index: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BinderKind {
    None,
    Seed,
    Nonce,
    Cancellation,
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
        append_segment_binder_rows(&mut rows);
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
            columns[CONTROL_MASK_COLUMN][index] = u32::from(row.binder == BinderKind::None);
            columns[SEED_MASK_COLUMN][index] = u32::from(row.binder == BinderKind::Seed);
            columns[NONCE_MASK_COLUMN][index] = u32::from(row.binder == BinderKind::Nonce);
            columns[CANCELLATION_MASK_COLUMN][index] =
                u32::from(row.binder == BinderKind::Cancellation);
            columns[ITEM_INDEX_COLUMN][index] = row.item_index;
            columns[LIMB_INDEX_COLUMN][index] = row.limb_index;
        }
        let domain = CanonicCoset::new(self.log_size).circle_domain();
        columns
            .into_iter()
            .map(|column| CircleEvaluation::new(domain, BaseColumn::from(column)))
            .collect()
    }
}

fn append_segment_binder_rows(rows: &mut Vec<PreprocessedRow>) {
    for item_index in 0..2 {
        for limb_index in 0..4 {
            rows.push(binder_row(BinderKind::Seed, item_index, limb_index));
        }
    }
    for limb_index in 0..4 {
        rows.push(binder_row(BinderKind::Nonce, 0, limb_index));
    }
    for limb_index in 0..4 {
        rows.push(binder_row(BinderKind::Cancellation, 0, limb_index));
    }
}

const fn binder_row(binder: BinderKind, item_index: u32, limb_index: u32) -> PreprocessedRow {
    PreprocessedRow {
        segment_mask: 1,
        verifier_id: 0,
        sequence: 0,
        tag: 0,
        args: [0; 4],
        binder,
        item_index,
        limb_index,
    }
}

fn validated_rows(
    plan: &VerifierControlPlan,
    public_term_count: u32,
    verifier_id: u32,
) -> Result<Vec<PreprocessedRow>, VmPublicLogupControlError> {
    let mut rows = Vec::new();
    let mut expected_term = 0_u32;
    let mut assertion_index = 0_usize;
    let expected_assertions = match plan.schema() {
        VerifierSchema::Vm => VM_ASSERTIONS.as_slice(),
        VerifierSchema::Recursion => RECURSION_ASSERTIONS.as_slice(),
        VerifierSchema::Poseidon2 => {
            return Err(VmPublicLogupControlError::SchemaMismatch {
                lane: "public LogUp",
                expected: VerifierSchema::Vm,
                actual: VerifierSchema::Poseidon2,
            });
        }
    };
    for (sequence, step) in plan.steps().iter().copied().enumerate() {
        match step {
            VerifierStep::AccumulatePublicLogupTerm { term } => {
                if assertion_index != 0 {
                    return Err(VmPublicLogupControlError::TermAfterAssertion { term });
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
            VerifierStep::AssertVmSharedRelation
            | VerifierStep::AssertSegmentSharedRelationZero
            | VerifierStep::AssertGlobalLogupZero => {
                if expected_term != public_term_count {
                    return Err(VmPublicLogupControlError::TermCountMismatch {
                        expected: public_term_count,
                        actual: expected_term,
                    });
                }
                let expected = expected_assertions
                    .get(assertion_index)
                    .copied()
                    .ok_or(VmPublicLogupControlError::UnexpectedAssertion { actual: step })?;
                if step != expected {
                    return Err(VmPublicLogupControlError::AssertionMismatch {
                        expected,
                        actual: step,
                    });
                }
                rows.push(encoded_row(sequence, step, verifier_id)?);
                assertion_index += 1;
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
    if assertion_index != expected_assertions.len() {
        return Err(VmPublicLogupControlError::AssertionMissing {
            expected: expected_assertions[assertion_index],
        });
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
        binder: BinderKind::None,
        item_index: 0,
        limb_index: 0,
    })
}

/// Relations shared by the public-LogUp control and segment binder rows.
#[derive(Clone)]
pub struct VmPublicLogupControlRelations {
    pub step: VerifierStepRelation,
    pub verifier_input_word: VerifierInputWordRelation,
    pub randomness_word: VerifierRandomnessWordRelation,
}

impl VmPublicLogupControlRelations {
    pub fn new(
        control_relations: &ControlRelations,
        input_relations: &VerifierInputRelations,
        randomness_relations: &VerifierRandomnessRelations,
    ) -> Self {
        Self {
            step: control_relations.step.clone(),
            verifier_input_word: input_relations.input_word.clone(),
            randomness_word: randomness_relations.word.clone(),
        }
    }
}

stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [],
    embedded_component: true,
    embedded_enabler_boolean: false,
    embedded_relations: crate::vm_public_logup_control_air::VmPublicLogupControlRelations,
    logup_batch: 2,
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
        control_mask: "recursion_vm_public_logup_control_control_mask",
        seed_mask: "recursion_vm_public_logup_control_seed_mask",
        nonce_mask: "recursion_vm_public_logup_control_nonce_mask",
        cancellation_mask: "recursion_vm_public_logup_control_cancellation_mask",
        item_index: "recursion_vm_public_logup_control_item_index",
        limb_index: "recursion_vm_public_logup_control_limb_index",
    },
    embedded_params: [
        segment_active, binary_active, vm_id, poseidon2_id, joint_seed_kind,
        interaction_nonce_kind, shared_sum_kind, claimed_sum_kind,
        interaction_seed_kind,
    ],

    relation step(7);
    relation verifier_input_word(5);
    relation randomness_word(5);

    fn vm_public_logup_control(
        value_a,
        value_b,
        row_mask,
        segment_mask,
        verifier_id,
        sequence,
        tag,
        arg_0,
        arg_1,
        arg_2,
        arg_3,
        control_mask,
        seed_mask,
        nonce_mask,
        cancellation_mask,
        item_index,
        limb_index,
        segment_active,
        binary_active,
        vm_id,
        poseidon2_id,
        joint_seed_kind,
        interaction_nonce_kind,
        shared_sum_kind,
        claimed_sum_kind,
        interaction_seed_kind,
    ) {
        let binary_mask = 1 - segment_mask;
        let control_active = control_mask
            * (segment_mask * segment_active + binary_mask * binary_active);
        let binder_active = segment_active
            * (seed_mask + nonce_mask + cancellation_mask);

        constrain enabler - row_mask;
        constrain (1 - binder_active) * value_a;
        constrain (1 - binder_active) * value_b;
        constrain segment_active * cancellation_mask * (value_a + value_b);

        consume(control_active) step(
            verifier_id,
            sequence,
            tag,
            arg_0,
            arg_1,
            arg_2,
            arg_3,
        );
        consume(segment_active * seed_mask) randomness_word(
            item_index, interaction_seed_kind, 0, limb_index, value_a,
        );
        consume(segment_active * seed_mask) verifier_input_word(
            vm_id, joint_seed_kind, item_index, limb_index, value_a,
        );
        consume(segment_active * seed_mask) verifier_input_word(
            poseidon2_id, joint_seed_kind, item_index, limb_index, value_a,
        );
        consume(segment_active * nonce_mask) verifier_input_word(
            vm_id, interaction_nonce_kind, 0, limb_index, value_a,
        );
        consume(segment_active * nonce_mask) verifier_input_word(
            poseidon2_id, interaction_nonce_kind, 0, limb_index, value_a,
        );
        consume(segment_active * cancellation_mask) verifier_input_word(
            vm_id, shared_sum_kind, 0, limb_index, value_a,
        );
        consume(segment_active * cancellation_mask) verifier_input_word(
            poseidon2_id, claimed_sum_kind, 0, limb_index, value_b,
        );
        return (value_a, value_b);
    }
}

pub use component::air::{Component, Eval};

/// Construct the generated consumer with verifier-owned proof-kind selectors.
pub fn eval_for_proof_kind(
    log_size: u32,
    proof_kind: ProofKind,
    control_relations: &ControlRelations,
    input_relations: &VerifierInputRelations,
    randomness_relations: &VerifierRandomnessRelations,
) -> Eval {
    Eval {
        log_size,
        segment_active: BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        binary_active: BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode)),
        vm_id: BaseField::from(SEGMENT_VERIFIER_ID),
        poseidon2_id: BaseField::from(POSEIDON2_VERIFIER_ID),
        joint_seed_kind: BaseField::from(VerifierInputKind::JointInteractionSeed.as_u32()),
        interaction_nonce_kind: BaseField::from(VerifierInputKind::InteractionPowNonce.as_u32()),
        shared_sum_kind: BaseField::from(VerifierInputKind::SharedRelationSum.as_u32()),
        claimed_sum_kind: BaseField::from(VerifierInputKind::ClaimedSum.as_u32()),
        interaction_seed_kind: BaseField::from(VerifierRandomnessKind::InteractionSeed.as_u32()),
        relations: VmPublicLogupControlRelations::new(
            control_relations,
            input_relations,
            randomness_relations,
        ),
    }
}

/// Generates the active control and joint segment-binding fractions.
pub fn gen_interaction_trace(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    preprocessed: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    proof_kind: ProofKind,
    control_relations: &ControlRelations,
    input_relations: &VerifierInputRelations,
    randomness_relations: &VerifierRandomnessRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    component::witness::gen_interaction_trace(
        trace,
        preprocessed,
        BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode)),
        BaseField::from(SEGMENT_VERIFIER_ID),
        BaseField::from(POSEIDON2_VERIFIER_ID),
        BaseField::from(VerifierInputKind::JointInteractionSeed.as_u32()),
        BaseField::from(VerifierInputKind::InteractionPowNonce.as_u32()),
        BaseField::from(VerifierInputKind::SharedRelationSum.as_u32()),
        BaseField::from(VerifierInputKind::ClaimedSum.as_u32()),
        BaseField::from(VerifierRandomnessKind::InteractionSeed.as_u32()),
        &VmPublicLogupControlRelations::new(
            control_relations,
            input_relations,
            randomness_relations,
        ),
    )
}

/// Segment-only values that tie the VM and Poseidon2 proof transcripts together.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SegmentJointBindingWitness {
    pub interaction_seeds: [QM31; 2],
    pub interaction_pow: u64,
    pub shared_relation_sum: QM31,
    pub poseidon2_claimed_sum: QM31,
}

/// Materializes control placeholders and active joint segment-binding values.
pub fn push_vm_public_logup_control(
    table: &mut VmPublicLogupControlTable,
    preprocessed: &VmPublicLogupControlPreprocessed,
    proof_kind: ProofKind,
    segment: Option<SegmentJointBindingWitness>,
) -> Result<(), VmPublicLogupControlError> {
    let segment = match (proof_kind, segment) {
        (ProofKind::SegmentLeaf, Some(segment)) => Some(segment),
        (ProofKind::SegmentLeaf, None) => {
            return Err(VmPublicLogupControlError::MissingSegmentBinding);
        }
        (ProofKind::BinaryNode | ProofKind::EmptyLeaf, None) => None,
        (ProofKind::BinaryNode | ProofKind::EmptyLeaf, Some(_)) => {
            return Err(VmPublicLogupControlError::UnexpectedSegmentBinding);
        }
    };
    for row in &preprocessed.rows {
        let (value_a, value_b) = match (row.binder, segment) {
            (BinderKind::Seed, Some(segment)) => (
                segment.interaction_seeds[row.item_index as usize].to_m31_array()
                    [row.limb_index as usize]
                    .0,
                0,
            ),
            (BinderKind::Nonce, Some(segment)) => (
                crate::transcript::encode_u64_words(segment.interaction_pow)
                    [row.limb_index as usize]
                    .as_u32(),
                0,
            ),
            (BinderKind::Cancellation, Some(segment)) => (
                segment.shared_relation_sum.to_m31_array()[row.limb_index as usize].0,
                segment.poseidon2_claimed_sum.to_m31_array()[row.limb_index as usize].0,
            ),
            (BinderKind::None, _) | (_, None) => (0, 0),
        };
        table.push(value_a, value_b);
    }
    Ok(())
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
    TermAfterAssertion {
        term: u32,
    },
    UnexpectedAssertion {
        actual: VerifierStep,
    },
    AssertionMismatch {
        expected: VerifierStep,
        actual: VerifierStep,
    },
    AssertionMissing {
        expected: VerifierStep,
    },
    MissingSegmentBinding,
    UnexpectedSegmentBinding,
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
        assert_constraints_with_binding(
            kind,
            (kind == ProofKind::SegmentLeaf).then_some(SegmentJointBindingWitness {
                interaction_seeds: [QM31::zero(); 2],
                interaction_pow: 0,
                shared_relation_sum: QM31::zero(),
                poseidon2_claimed_sum: QM31::zero(),
            }),
        );
    }

    fn assert_constraints_with_binding(
        kind: ProofKind,
        segment_binding: Option<SegmentJointBindingWitness>,
    ) {
        let preprocessing = preprocessing();
        let control_relations = ControlRelations::dummy();
        let input_relations = VerifierInputRelations::dummy();
        let randomness_relations = VerifierRandomnessRelations::dummy();
        let preprocessed = preprocessing.gen_columns();
        let mut table = VmPublicLogupControlTable::new();
        push_vm_public_logup_control(&mut table, &preprocessing, kind, segment_binding)
            .expect("fixture control and binder values match their mode");
        let trace = table.into_witness();
        let (interaction, claimed_sum) = gen_interaction_trace(
            &trace,
            &preprocessed,
            kind,
            &control_relations,
            &input_relations,
            &randomness_relations,
        );
        let traces = TreeVec::new(vec![preprocessed, trace, interaction]);
        let trace_polys = traces.map_cols(|column| column.interpolate());
        let eval = eval_for_proof_kind(
            preprocessing.log_size(),
            kind,
            &control_relations,
            &input_relations,
            &randomness_relations,
        );
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
        relation_sum(
            kind,
            (kind == ProofKind::SegmentLeaf).then_some(SegmentJointBindingWitness {
                interaction_seeds: [QM31::zero(); 2],
                interaction_pow: 0,
                shared_relation_sum: QM31::zero(),
                poseidon2_claimed_sum: QM31::zero(),
            }),
        )
    }

    fn relation_sum(kind: ProofKind, segment_binding: Option<SegmentJointBindingWitness>) -> QM31 {
        let preprocessing = preprocessing();
        let mut channel = Poseidon2M31Channel::default();
        let control_relations = ControlRelations::draw(&mut channel);
        let input_relations = VerifierInputRelations::draw(&mut channel);
        let randomness_relations = VerifierRandomnessRelations::draw(&mut channel);
        let mut table = VmPublicLogupControlTable::new();
        push_vm_public_logup_control(&mut table, &preprocessing, kind, segment_binding)
            .expect("fixture control and binder values match their mode");
        let trace = table.into_witness();
        let (_, consumer_sum) = gen_interaction_trace(
            &trace,
            &preprocessing.gen_columns(),
            kind,
            &control_relations,
            &input_relations,
            &randomness_relations,
        );
        let control_sum = preprocessing
            .rows
            .iter()
            .filter(|row| match (kind, row.binder) {
                (ProofKind::SegmentLeaf, BinderKind::None) => {
                    row.verifier_id == SEGMENT_VERIFIER_ID
                }
                (ProofKind::BinaryNode, BinderKind::None) => row.verifier_id != SEGMENT_VERIFIER_ID,
                _ => false,
            })
            .fold(consumer_sum, |sum, row| {
                let denominator: QM31 = control_relations.step.combine(&[
                    M31::from(row.verifier_id),
                    M31::from(row.sequence),
                    M31::from(row.tag),
                    M31::from(row.args[0]),
                    M31::from(row.args[1]),
                    M31::from(row.args[2]),
                    M31::from(row.args[3]),
                ]);
                sum + denominator.inverse()
            });
        if kind != ProofKind::SegmentLeaf {
            return control_sum;
        }
        let segment_binding = segment_binding.expect("segment mode carries binding values");
        preprocessing.rows.iter().fold(control_sum, |sum, row| {
            let (value_a, value_b) = match row.binder {
                BinderKind::Seed => (
                    segment_binding.interaction_seeds[row.item_index as usize].to_m31_array()
                        [row.limb_index as usize],
                    M31::zero(),
                ),
                BinderKind::Nonce => (
                    M31::from(
                        crate::transcript::encode_u64_words(segment_binding.interaction_pow)
                            [row.limb_index as usize],
                    ),
                    M31::zero(),
                ),
                BinderKind::Cancellation => (
                    segment_binding.shared_relation_sum.to_m31_array()[row.limb_index as usize],
                    segment_binding.poseidon2_claimed_sum.to_m31_array()[row.limb_index as usize],
                ),
                BinderKind::None => (M31::zero(), M31::zero()),
            };
            match row.binder {
                BinderKind::Seed => {
                    let randomness: QM31 = randomness_relations.word.combine(&[
                        M31::from(row.item_index),
                        M31::from(VerifierRandomnessKind::InteractionSeed.as_u32()),
                        M31::zero(),
                        M31::from(row.limb_index),
                        value_a,
                    ]);
                    [SEGMENT_VERIFIER_ID, POSEIDON2_VERIFIER_ID]
                        .into_iter()
                        .fold(sum + randomness.inverse(), |sum, verifier_id| {
                            let input: QM31 = input_relations.input_word.combine(&[
                                M31::from(verifier_id),
                                M31::from(VerifierInputKind::JointInteractionSeed.as_u32()),
                                M31::from(row.item_index),
                                M31::from(row.limb_index),
                                value_a,
                            ]);
                            sum + input.inverse()
                        })
                }
                BinderKind::Nonce => [SEGMENT_VERIFIER_ID, POSEIDON2_VERIFIER_ID]
                    .into_iter()
                    .fold(sum, |sum, verifier_id| {
                        let input: QM31 = input_relations.input_word.combine(&[
                            M31::from(verifier_id),
                            M31::from(VerifierInputKind::InteractionPowNonce.as_u32()),
                            M31::zero(),
                            M31::from(row.limb_index),
                            value_a,
                        ]);
                        sum + input.inverse()
                    }),
                BinderKind::Cancellation => [
                    (
                        SEGMENT_VERIFIER_ID,
                        VerifierInputKind::SharedRelationSum,
                        value_a,
                    ),
                    (
                        POSEIDON2_VERIFIER_ID,
                        VerifierInputKind::ClaimedSum,
                        value_b,
                    ),
                ]
                .into_iter()
                .fold(sum, |sum, (verifier_id, kind, value)| {
                    let input: QM31 = input_relations.input_word.combine(&[
                        M31::from(verifier_id),
                        M31::from(kind.as_u32()),
                        M31::zero(),
                        M31::from(row.limb_index),
                        value,
                    ]);
                    sum + input.inverse()
                }),
                BinderKind::None => sum,
            }
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
    fn nonzero_joint_seed_binding_closes_exactly() {
        assert!(
            relation_sum(
                ProofKind::SegmentLeaf,
                Some(SegmentJointBindingWitness {
                    interaction_seeds: [QM31::from(M31::from(11)), QM31::from(M31::from(19))],
                    interaction_pow: 0,
                    shared_relation_sum: QM31::zero(),
                    poseidon2_claimed_sum: QM31::zero(),
                }),
            )
            .is_zero()
        );
    }

    #[rstest]
    fn nonzero_joint_nonce_binding_closes_exactly() {
        assert!(
            relation_sum(
                ProofKind::SegmentLeaf,
                Some(SegmentJointBindingWitness {
                    interaction_seeds: [QM31::zero(); 2],
                    interaction_pow: 0x1122_3344_5566_7788,
                    shared_relation_sum: QM31::zero(),
                    poseidon2_claimed_sum: QM31::zero(),
                }),
            )
            .is_zero()
        );
    }

    #[rstest]
    fn nonzero_shared_sum_cancellation_closes_exactly() {
        let shared_relation_sum = QM31::from(M31::from(23));
        assert!(
            relation_sum(
                ProofKind::SegmentLeaf,
                Some(SegmentJointBindingWitness {
                    interaction_seeds: [QM31::zero(); 2],
                    interaction_pow: 0,
                    shared_relation_sum,
                    poseidon2_claimed_sum: -shared_relation_sum,
                }),
            )
            .is_zero()
        );
    }

    #[rstest]
    fn mismatched_segment_relation_sums_violate_constraints() {
        let result = std::panic::catch_unwind(|| {
            assert_constraints_with_binding(
                ProofKind::SegmentLeaf,
                Some(SegmentJointBindingWitness {
                    interaction_seeds: [QM31::zero(); 2],
                    interaction_pow: 0,
                    shared_relation_sum: QM31::from(M31::from(23)),
                    poseidon2_claimed_sum: QM31::zero(),
                }),
            );
        });
        assert!(result.is_err());
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
