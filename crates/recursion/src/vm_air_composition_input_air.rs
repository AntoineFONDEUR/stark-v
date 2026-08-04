//! AIR ownership for VM AIR composition-circuit inputs.
//!
//! Verifier preprocessing assigns every circuit input to one sampled-value
//! limb, claimed-sum limb, relation-challenge word, typed randomness word, or
//! the public segment selector. Each transcript source is consumed once and
//! each circuit wire is emitted with its exact fixed use count.

use core::fmt;
use std::collections::HashSet;

use air::digest::M31Word;
use simd::AlignedVec;
use stwo::core::ColumnVec;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::QM31;
use stwo::core::poly::circle::{CanonicCoset, MAX_CIRCLE_DOMAIN_LOG_SIZE};
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;

use super::control_air::SEGMENT_VERIFIER_ID;
use super::relation_challenge_air::{AIR_EVALUATION_CHALLENGE_SCOPE, RelationChallengeRelations};
use super::transcript_payload_air::{VerifierInputKind, VerifierInputRelations};
use super::verifier_randomness_air::{VerifierRandomnessKind, VerifierRandomnessRelations};
use super::vm_air_composition_circuit::{
    SECURE_VALUE_WORD_COUNT, VmAirCompositionCircuit, VmAirCompositionInputSource,
};
use super::wire::ProofKind;
use crate::circuit::use_counts_for_outputs;
use crate::recorder::Op;
use crate::relations::RecursionRelations;

const MIN_LOG_SIZE: u32 = 4;
const RELATION_CHALLENGE_WORD_COUNT_U32: u32 = 8;
const SECURE_VALUE_WORD_COUNT_U32: u32 = 4;

const ROW_MASK_COLUMN: usize = 0;
const SAMPLED_VALUE_MASK_COLUMN: usize = 1;
const CLAIMED_SUM_MASK_COLUMN: usize = 2;
const CHALLENGE_MASK_COLUMN: usize = 3;
const COMPOSITION_RANDOMNESS_MASK_COLUMN: usize = 4;
const OODS_POINT_MASK_COLUMN: usize = 5;
const SELECTOR_MASK_COLUMN: usize = 6;
const CIRCUIT_ID_COLUMN: usize = 7;
const NODE_ID_COLUMN: usize = 8;
const USE_COUNT_COLUMN: usize = 9;
const SOURCE_INDEX_0_COLUMN: usize = 10;
const SOURCE_INDEX_1_COLUMN: usize = 11;
const PREPROCESSED_COLUMN_COUNT: usize = 12;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PreprocessedRow {
    source: VmAirCompositionInputSource,
    circuit_id: u32,
    node_id: u32,
    use_count: u32,
    source_index_0: u32,
    source_index_1: u32,
}

/// Verifier-owned input-node layout for one fixed VM composition circuit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VmAirCompositionInputPreprocessed {
    log_size: u32,
    rows: Vec<PreprocessedRow>,
}

impl VmAirCompositionInputPreprocessed {
    pub fn new(
        reference: &VmAirCompositionCircuit,
        circuit_id: u32,
    ) -> Result<Self, VmAirCompositionInputError> {
        M31Word::try_from(circuit_id)
            .map_err(|_| VmAirCompositionInputError::CircuitIdNotCanonical { circuit_id })?;
        let arena = reference.circuit().arena();
        let uses = use_counts_for_outputs(&arena, reference.circuit().outputs());
        let mut sources = HashSet::with_capacity(reference.input_bindings().len());
        let mut selector_count = 0_usize;
        let mut rows = Vec::with_capacity(reference.input_bindings().len());
        for binding in reference.input_bindings() {
            if !sources.insert(binding.source) {
                return Err(VmAirCompositionInputError::DuplicateInputSource {
                    source: binding.source,
                });
            }
            M31Word::try_from(binding.node_id).map_err(|_| {
                VmAirCompositionInputError::NodeIdNotCanonical {
                    node_id: binding.node_id,
                }
            })?;
            let node_id = usize::try_from(binding.node_id).map_err(|_| {
                VmAirCompositionInputError::NodeIdDoesNotFitUsize {
                    node_id: binding.node_id,
                }
            })?;
            let node = arena
                .nodes
                .get(node_id)
                .ok_or(VmAirCompositionInputError::NodeMissing {
                    node_id: binding.node_id,
                })?;
            if node.op != Op::Input {
                return Err(VmAirCompositionInputError::BindingTargetsNonInput {
                    node_id: binding.node_id,
                });
            }
            let use_count = uses[node_id];
            M31Word::try_from(use_count).map_err(|_| {
                VmAirCompositionInputError::UseCountNotCanonical {
                    node_id: binding.node_id,
                    use_count,
                }
            })?;
            let (source_index_0, source_index_1) =
                validate_source(binding.source, reference, &mut selector_count)?;
            rows.push(PreprocessedRow {
                source: binding.source,
                circuit_id,
                node_id: binding.node_id,
                use_count,
                source_index_0,
                source_index_1,
            });
        }
        if selector_count != 1 {
            return Err(VmAirCompositionInputError::SelectorCountMismatch {
                actual: selector_count,
            });
        }
        let expected_inputs = expected_input_count(reference)?;
        if rows.len() != expected_inputs {
            return Err(VmAirCompositionInputError::InputCountMismatch {
                expected: expected_inputs,
                actual: rows.len(),
            });
        }
        drop(arena);
        let padded_rows = rows
            .len()
            .checked_next_power_of_two()
            .ok_or(VmAirCompositionInputError::RowCountOverflow)?
            .max(1 << MIN_LOG_SIZE);
        let log_size = padded_rows.ilog2();
        if log_size > MAX_CIRCLE_DOMAIN_LOG_SIZE {
            return Err(VmAirCompositionInputError::LogSizeOutOfRange { log_size });
        }
        Ok(Self { log_size, rows })
    }

    pub const fn log_size(&self) -> u32 {
        self.log_size
    }

    pub fn input_count(&self) -> usize {
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
            columns[SAMPLED_VALUE_MASK_COLUMN][index] = u32::from(matches!(
                row.source,
                VmAirCompositionInputSource::SampledValueWord { .. }
            ));
            columns[CLAIMED_SUM_MASK_COLUMN][index] = u32::from(matches!(
                row.source,
                VmAirCompositionInputSource::ClaimedSumWord { .. }
            ));
            columns[CHALLENGE_MASK_COLUMN][index] = u32::from(matches!(
                row.source,
                VmAirCompositionInputSource::RelationChallengeWord { .. }
            ));
            columns[COMPOSITION_RANDOMNESS_MASK_COLUMN][index] = u32::from(matches!(
                row.source,
                VmAirCompositionInputSource::CompositionRandomnessWord { .. }
            ));
            columns[OODS_POINT_MASK_COLUMN][index] = u32::from(matches!(
                row.source,
                VmAirCompositionInputSource::OodsPointWord { .. }
            ));
            columns[SELECTOR_MASK_COLUMN][index] =
                u32::from(row.source == VmAirCompositionInputSource::SegmentSelector);
            columns[CIRCUIT_ID_COLUMN][index] = row.circuit_id;
            columns[NODE_ID_COLUMN][index] = row.node_id;
            columns[USE_COUNT_COLUMN][index] = row.use_count;
            columns[SOURCE_INDEX_0_COLUMN][index] = row.source_index_0;
            columns[SOURCE_INDEX_1_COLUMN][index] = row.source_index_1;
        }
        let domain = CanonicCoset::new(self.log_size).circle_domain();
        columns
            .into_iter()
            .map(|column| CircleEvaluation::new(domain, BaseColumn::from(column)))
            .collect()
    }
}

fn validate_source(
    source: VmAirCompositionInputSource,
    reference: &VmAirCompositionCircuit,
    selector_count: &mut usize,
) -> Result<(u32, u32), VmAirCompositionInputError> {
    let profile = reference.profile();
    match source {
        VmAirCompositionInputSource::SampledValueWord {
            item_index,
            word_index,
        } => {
            validate_secure_coordinate(
                VmAirCompositionInputKind::SampledValue,
                item_index,
                word_index,
                profile.sampled_value_count(),
            )?;
            Ok((item_index, word_index))
        }
        VmAirCompositionInputSource::ClaimedSumWord {
            item_index,
            word_index,
        } => {
            validate_secure_coordinate(
                VmAirCompositionInputKind::ClaimedSum,
                item_index,
                word_index,
                profile.claimed_sum_count(),
            )?;
            Ok((item_index, word_index))
        }
        VmAirCompositionInputSource::RelationChallengeWord {
            challenge,
            word_index,
        } => {
            if challenge >= profile.relation_challenge_count() {
                return Err(VmAirCompositionInputError::ChallengeIndexOutOfRange { challenge });
            }
            if word_index >= RELATION_CHALLENGE_WORD_COUNT_U32 {
                return Err(VmAirCompositionInputError::ChallengeWordOutOfRange { word_index });
            }
            Ok((challenge, word_index))
        }
        VmAirCompositionInputSource::CompositionRandomnessWord { word_index } => {
            validate_randomness_word(VerifierRandomnessKind::CompositionRandomness, word_index)?;
            Ok((0, word_index))
        }
        VmAirCompositionInputSource::OodsPointWord { word_index } => {
            validate_randomness_word(VerifierRandomnessKind::OodsPoint, word_index)?;
            Ok((0, word_index))
        }
        VmAirCompositionInputSource::SegmentSelector => {
            *selector_count = selector_count
                .checked_add(1)
                .ok_or(VmAirCompositionInputError::RowCountOverflow)?;
            Ok((0, 0))
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VmAirCompositionInputKind {
    SampledValue,
    ClaimedSum,
}

fn validate_secure_coordinate(
    kind: VmAirCompositionInputKind,
    item_index: u32,
    word_index: u32,
    item_count: u32,
) -> Result<(), VmAirCompositionInputError> {
    if item_index >= item_count {
        return Err(VmAirCompositionInputError::SecureItemIndexOutOfRange {
            kind,
            item_index,
            item_count,
        });
    }
    if word_index >= SECURE_VALUE_WORD_COUNT_U32 {
        return Err(VmAirCompositionInputError::SecureWordIndexOutOfRange { kind, word_index });
    }
    Ok(())
}

fn validate_randomness_word(
    kind: VerifierRandomnessKind,
    word_index: u32,
) -> Result<(), VmAirCompositionInputError> {
    if word_index >= SECURE_VALUE_WORD_COUNT_U32 {
        return Err(VmAirCompositionInputError::RandomnessWordOutOfRange { kind, word_index });
    }
    Ok(())
}

fn expected_input_count(
    reference: &VmAirCompositionCircuit,
) -> Result<usize, VmAirCompositionInputError> {
    let profile = reference.profile();
    let sampled = usize::try_from(profile.sampled_value_count())
        .ok()
        .and_then(|count| count.checked_mul(SECURE_VALUE_WORD_COUNT))
        .ok_or(VmAirCompositionInputError::RowCountOverflow)?;
    let claimed = usize::try_from(profile.claimed_sum_count())
        .ok()
        .and_then(|count| count.checked_mul(SECURE_VALUE_WORD_COUNT))
        .ok_or(VmAirCompositionInputError::RowCountOverflow)?;
    let challenges = usize::try_from(profile.relation_challenge_count())
        .ok()
        .and_then(|count| count.checked_mul(RELATION_CHALLENGE_WORD_COUNT_U32 as usize))
        .ok_or(VmAirCompositionInputError::RowCountOverflow)?;
    sampled
        .checked_add(claimed)
        .and_then(|count| count.checked_add(challenges))
        .and_then(|count| count.checked_add(2 * SECURE_VALUE_WORD_COUNT))
        .and_then(|count| count.checked_add(1))
        .ok_or(VmAirCompositionInputError::RowCountOverflow)
}

/// Relations used by the macro-generated VM composition input component.
#[derive(Clone)]
pub struct VmAirCompositionInputComponentRelations {
    pub verifier_input_word: super::transcript_payload_air::VerifierInputWordRelation,
    pub challenge_word: super::relation_challenge_air::RelationChallengeWordRelation,
    pub randomness_word: super::verifier_randomness_air::VerifierRandomnessWordRelation,
    pub wire: crate::relations::WireRelation,
}

impl VmAirCompositionInputComponentRelations {
    /// Combine every transcript source with the shared arithmetic wire relation.
    pub fn new(
        challenge_relations: &RelationChallengeRelations,
        verifier_input_relations: &VerifierInputRelations,
        randomness_relations: &VerifierRandomnessRelations,
        circuit_relations: &RecursionRelations,
    ) -> Self {
        Self {
            verifier_input_word: verifier_input_relations.input_word.clone(),
            challenge_word: challenge_relations.word.clone(),
            randomness_word: randomness_relations.word.clone(),
            wire: circuit_relations.wire.clone(),
        }
    }
}

stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [],
    embedded_component: true,
    embedded_enabler_boolean: false,
    embedded_relations:
        crate::vm_air_composition_input_air::VmAirCompositionInputComponentRelations,
    logup_batch: 2,
    embedded_preprocessed: {
        row_mask: "recursion_vm_air_composition_input_row_mask",
        sampled_value_mask: "recursion_vm_air_composition_input_sampled_value_mask",
        claimed_sum_mask: "recursion_vm_air_composition_input_claimed_sum_mask",
        challenge_mask: "recursion_vm_air_composition_input_challenge_mask",
        composition_randomness_mask:
            "recursion_vm_air_composition_input_composition_randomness_mask",
        oods_point_mask: "recursion_vm_air_composition_input_oods_point_mask",
        selector_mask: "recursion_vm_air_composition_input_selector_mask",
        circuit_id: "recursion_vm_air_composition_input_circuit_id",
        node_id: "recursion_vm_air_composition_input_node_id",
        use_count: "recursion_vm_air_composition_input_use_count",
        source_index_0: "recursion_vm_air_composition_input_source_index_0",
        source_index_1: "recursion_vm_air_composition_input_source_index_1",
    },
    embedded_params: [
        segment_active, verifier_id, sampled_value_kind, claimed_sum_kind,
        challenge_scope, composition_randomness_kind, oods_point_kind,
    ],

    relation verifier_input_word(5);
    relation challenge_word(5);
    relation randomness_word(5);
    relation wire(6);

    fn vm_air_composition_input(
        value,
        row_mask, sampled_value_mask, claimed_sum_mask, challenge_mask,
        composition_randomness_mask, oods_point_mask, selector_mask,
        circuit_id, node_id, use_count, source_index_0, source_index_1,
        segment_active, verifier_id, sampled_value_kind, claimed_sum_kind,
        challenge_scope, composition_randomness_kind, oods_point_kind,
    ) {
        let witness_mask = row_mask - selector_mask;

        constrain enabler - row_mask;
        constrain witness_mask * (1 - segment_active) * value;
        constrain selector_mask * (value - segment_active);

        consume(segment_active * sampled_value_mask) verifier_input_word(
            verifier_id, sampled_value_kind, source_index_0, source_index_1, value,
        );
        consume(segment_active * claimed_sum_mask) verifier_input_word(
            verifier_id, claimed_sum_kind, source_index_0, source_index_1, value,
        );
        consume(segment_active * challenge_mask) challenge_word(
            verifier_id, challenge_scope, source_index_0, source_index_1, value,
        );
        consume(segment_active * composition_randomness_mask) randomness_word(
            verifier_id, composition_randomness_kind, source_index_0, source_index_1, value,
        );
        consume(segment_active * oods_point_mask) randomness_word(
            verifier_id, oods_point_kind, source_index_0, source_index_1, value,
        );
        emit(row_mask * use_count) wire(circuit_id, node_id, value, 0, 0, 0);

        return value;
    }
}

pub use component::air::{Component, Eval};

/// Construct the generated evaluator for the selected universal proof kind.
pub fn eval_for_proof_kind(
    log_size: u32,
    proof_kind: ProofKind,
    challenge_relations: &RelationChallengeRelations,
    verifier_input_relations: &VerifierInputRelations,
    randomness_relations: &VerifierRandomnessRelations,
    circuit_relations: &RecursionRelations,
) -> Eval {
    Eval {
        log_size,
        segment_active: BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        verifier_id: BaseField::from(SEGMENT_VERIFIER_ID),
        sampled_value_kind: BaseField::from(VerifierInputKind::SampledValue.as_u32()),
        claimed_sum_kind: BaseField::from(VerifierInputKind::VmAirClaimedSum.as_u32()),
        challenge_scope: BaseField::from(AIR_EVALUATION_CHALLENGE_SCOPE),
        composition_randomness_kind: BaseField::from(
            VerifierRandomnessKind::CompositionRandomness.as_u32(),
        ),
        oods_point_kind: BaseField::from(VerifierRandomnessKind::OodsPoint.as_u32()),
        relations: VmAirCompositionInputComponentRelations::new(
            challenge_relations,
            verifier_input_relations,
            randomness_relations,
            circuit_relations,
        ),
    }
}

/// Generate source consumers and exact circuit-wire producers.
pub fn gen_interaction_trace(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    preprocessed: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    proof_kind: ProofKind,
    challenge_relations: &RelationChallengeRelations,
    verifier_input_relations: &VerifierInputRelations,
    randomness_relations: &VerifierRandomnessRelations,
    circuit_relations: &RecursionRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    component::witness::gen_interaction_trace(
        trace,
        preprocessed,
        BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        BaseField::from(SEGMENT_VERIFIER_ID),
        BaseField::from(VerifierInputKind::SampledValue.as_u32()),
        BaseField::from(VerifierInputKind::VmAirClaimedSum.as_u32()),
        BaseField::from(AIR_EVALUATION_CHALLENGE_SCOPE),
        BaseField::from(VerifierRandomnessKind::CompositionRandomness.as_u32()),
        BaseField::from(VerifierRandomnessKind::OodsPoint.as_u32()),
        &VmAirCompositionInputComponentRelations::new(
            challenge_relations,
            verifier_input_relations,
            randomness_relations,
            circuit_relations,
        ),
    )
}

/// Materializes input values after checking the fixed circuit layout.
pub fn push_vm_air_composition_inputs(
    table: &mut VmAirCompositionInputTable,
    preprocessed: &VmAirCompositionInputPreprocessed,
    reference: &VmAirCompositionCircuit,
    witness: &VmAirCompositionCircuit,
    proof_kind: ProofKind,
) -> Result<(), VmAirCompositionInputError> {
    if reference.profile() != witness.profile()
        || reference.input_bindings() != witness.input_bindings()
        || reference.circuit().outputs() != witness.circuit().outputs()
    {
        return Err(VmAirCompositionInputError::InputLayoutMismatch);
    }
    if witness.input_bindings().len() != preprocessed.rows.len() {
        return Err(VmAirCompositionInputError::InputCountMismatch {
            expected: preprocessed.rows.len(),
            actual: witness.input_bindings().len(),
        });
    }
    let arena = witness.circuit().arena();
    let active = proof_kind == ProofKind::SegmentLeaf;
    for (row, binding) in preprocessed.rows.iter().zip(witness.input_bindings()) {
        if row.node_id != binding.node_id || row.source != binding.source {
            return Err(VmAirCompositionInputError::InputCoordinateMismatch {
                node_id: binding.node_id,
            });
        }
        let node_id = usize::try_from(binding.node_id).map_err(|_| {
            VmAirCompositionInputError::NodeIdDoesNotFitUsize {
                node_id: binding.node_id,
            }
        })?;
        let node = arena
            .nodes
            .get(node_id)
            .ok_or(VmAirCompositionInputError::NodeMissing {
                node_id: binding.node_id,
            })?;
        if node.op != Op::Input {
            return Err(VmAirCompositionInputError::BindingTargetsNonInput {
                node_id: binding.node_id,
            });
        }
        let limbs = node.value.to_m31_array();
        if limbs[1..].iter().any(|limb| limb.0 != 0) {
            return Err(VmAirCompositionInputError::InputIsNotBaseField {
                node_id: binding.node_id,
            });
        }
        let expected = if binding.source == VmAirCompositionInputSource::SegmentSelector {
            u32::from(active)
        } else if active {
            limbs[0].0
        } else {
            0
        };
        if limbs[0].0 != expected {
            return Err(VmAirCompositionInputError::InactiveInputIsNonZero {
                node_id: binding.node_id,
            });
        }
        table.push(expected);
    }
    Ok(())
}

/// Invalid composition input layout, coordinate, or mode assignment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VmAirCompositionInputError {
    CircuitIdNotCanonical {
        circuit_id: u32,
    },
    RowCountOverflow,
    LogSizeOutOfRange {
        log_size: u32,
    },
    NodeIdNotCanonical {
        node_id: u32,
    },
    NodeIdDoesNotFitUsize {
        node_id: u32,
    },
    NodeMissing {
        node_id: u32,
    },
    BindingTargetsNonInput {
        node_id: u32,
    },
    UseCountNotCanonical {
        node_id: u32,
        use_count: u32,
    },
    DuplicateInputSource {
        source: VmAirCompositionInputSource,
    },
    SecureItemIndexOutOfRange {
        kind: VmAirCompositionInputKind,
        item_index: u32,
        item_count: u32,
    },
    SecureWordIndexOutOfRange {
        kind: VmAirCompositionInputKind,
        word_index: u32,
    },
    ChallengeIndexOutOfRange {
        challenge: u32,
    },
    ChallengeWordOutOfRange {
        word_index: u32,
    },
    RandomnessWordOutOfRange {
        kind: VerifierRandomnessKind,
        word_index: u32,
    },
    SelectorCountMismatch {
        actual: usize,
    },
    InputCountMismatch {
        expected: usize,
        actual: usize,
    },
    InputLayoutMismatch,
    InputCoordinateMismatch {
        node_id: u32,
    },
    InputIsNotBaseField {
        node_id: u32,
    },
    InactiveInputIsNonZero {
        node_id: u32,
    },
}

impl fmt::Display for VmAirCompositionInputError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for VmAirCompositionInputError {}

#[cfg(test)]
mod tests {
    use num_traits::Zero;
    use prover::components::{COMPONENT_COUNT, COMPONENT_NAMES};
    use prover::relations::Relations;
    use rstest::rstest;
    use stwo::core::fields::qm31::SecureField;
    use stwo::core::pcs::TreeVec;
    use stwo_constraint_framework::{FrameworkEval, assert_constraints_on_polys};

    use super::*;
    use crate::air_relation_parameters::RELATION_CHALLENGE_WORD_COUNT;
    use crate::vm_air_composition_circuit::{
        VmAirCompositionWitness, build_vm_air_composition_circuit,
        build_vm_air_composition_reference,
    };
    use crate::vm_air_program::VmAirProgram;

    const CIRCUIT_ID: u32 = 43;

    fn component_log_sizes() -> [u32; COMPONENT_COUNT] {
        core::array::from_fn(|index| match COMPONENT_NAMES[index] {
            "bitwise" => 18,
            "range_check_20" | "range_check_8_8_4" => 20,
            "range_check_8_11" => 19,
            "range_check_8_8" => 16,
            "range_check_m31" => 15,
            _ => 6,
        })
    }

    fn circuits(kind: ProofKind) -> (VmAirCompositionCircuit, VmAirCompositionCircuit) {
        let reference = build_vm_air_composition_reference(component_log_sizes())
            .expect("fixture reference is constructible");
        let program = VmAirProgram::new(component_log_sizes()).expect("fixture profile is valid");
        let samples = vec![SecureField::zero(); program.sample_coordinates().len()];
        let claimed_sums = vec![SecureField::zero(); COMPONENT_COUNT];
        let challenges =
            vec![[M31Word::ZERO; RELATION_CHALLENGE_WORD_COUNT]; Relations::DESCRIPTORS.len()];
        let witness = build_vm_air_composition_circuit(
            component_log_sizes(),
            VmAirCompositionWitness {
                segment_selector: kind == ProofKind::SegmentLeaf,
                sampled_values: &samples,
                claimed_sums: &claimed_sums,
                relation_challenges: &challenges,
                composition_randomness: [M31Word::ZERO; SECURE_VALUE_WORD_COUNT],
                oods_point: [M31Word::ZERO; SECURE_VALUE_WORD_COUNT],
            },
        )
        .expect("zero fixture has fixed composition structure");
        (reference, witness)
    }

    fn assert_constraints(kind: ProofKind) {
        let (reference, witness) = circuits(kind);
        let preprocessing = VmAirCompositionInputPreprocessed::new(&reference, CIRCUIT_ID)
            .expect("reference owns every input once");
        let mut table = VmAirCompositionInputTable::new();
        push_vm_air_composition_inputs(&mut table, &preprocessing, &reference, &witness, kind)
            .expect("mode assignment matches its selector");
        let trace = table.into_witness();
        let preprocessed = preprocessing.gen_columns();
        let challenge_relations = RelationChallengeRelations::dummy();
        let verifier_input_relations = VerifierInputRelations::dummy();
        let randomness_relations = VerifierRandomnessRelations::dummy();
        let circuit_relations = RecursionRelations::dummy();
        let (interaction, claimed_sum) = gen_interaction_trace(
            &trace,
            &preprocessed,
            kind,
            &challenge_relations,
            &verifier_input_relations,
            &randomness_relations,
            &circuit_relations,
        );
        let traces = TreeVec::new(vec![preprocessed, trace, interaction]);
        let trace_polys = traces.map_cols(|column| column.interpolate());
        let eval = eval_for_proof_kind(
            preprocessing.log_size(),
            kind,
            &challenge_relations,
            &verifier_input_relations,
            &randomness_relations,
            &circuit_relations,
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

    #[rstest]
    #[case::segment(ProofKind::SegmentLeaf)]
    #[case::binary(ProofKind::BinaryNode)]
    #[case::empty(ProofKind::EmptyLeaf)]
    fn every_universal_mode_satisfies_composition_input_constraints(#[case] kind: ProofKind) {
        assert_constraints(kind);
    }

    #[test]
    fn preprocessing_owns_every_tracked_input_once() {
        let (reference, _) = circuits(ProofKind::EmptyLeaf);
        let preprocessing = VmAirCompositionInputPreprocessed::new(&reference, CIRCUIT_ID)
            .expect("reference owns every input once");
        assert_eq!(
            preprocessing.input_count(),
            reference.input_bindings().len()
        );
    }

    #[test]
    fn active_selector_cannot_be_reused_in_binary_mode() {
        let (reference, active) = circuits(ProofKind::SegmentLeaf);
        let preprocessing = VmAirCompositionInputPreprocessed::new(&reference, CIRCUIT_ID)
            .expect("reference owns every input once");
        let result = push_vm_air_composition_inputs(
            &mut VmAirCompositionInputTable::new(),
            &preprocessing,
            &reference,
            &active,
            ProofKind::BinaryNode,
        );
        assert!(matches!(
            result,
            Err(VmAirCompositionInputError::InactiveInputIsNonZero { .. })
        ));
    }
}
