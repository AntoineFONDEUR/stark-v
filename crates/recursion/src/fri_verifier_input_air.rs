//! AIR ownership for fixed FRI-verifier circuit inputs.
//!
//! Trusted preprocessing assigns every tracked base-field input node to one
//! verifier lane and semantic source. Active lanes consume the DEEP answer,
//! authenticated FRI words, transcript alphas and coefficients, canonical
//! query bits, and routed positions. Every input then emits its exact circuit
//! wire multiplicity into the shared arithmetic relations.

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
use stwo_constraint_framework::relation;

use super::control_air::{
    LEFT_RECURSION_VERIFIER_ID, RIGHT_RECURSION_VERIFIER_ID, SEGMENT_VERIFIER_ID,
};
use super::fri_merkle_air::FriMerkleRelations;
use super::fri_verifier_circuit::{FriVerifierCircuit, FriVerifierInputSource, FriVerifierProfile};
use super::pcs_deep_input_air::PcsDeepRelations;
use super::query_position_air::{QueryPositionKind, QueryPositionRelations};
use super::transcript_payload_air::{VerifierInputKind, VerifierInputRelations};
use super::verifier_randomness_air::{VerifierRandomnessKind, VerifierRandomnessRelations};
use super::wire::ProofKind;
use crate::circuit::use_counts_for_outputs;
use crate::recorder::Op;
use crate::relations::RecursionRelations;

const MIN_LOG_SIZE: u32 = 4;
const SECURE_WORD_COUNT: usize = 4;
const M31_BITS: usize = 31;

const ROW_MASK_COLUMN: usize = 0;
const SEGMENT_MASK_COLUMN: usize = 1;
const BINARY_MASK_COLUMN: usize = 2;
const DEEP_ANSWER_MASK_COLUMN: usize = 3;
const AUTHENTICATED_VALUE_MASK_COLUMN: usize = 4;
const FRI_ALPHA_MASK_COLUMN: usize = 5;
const QUERY_BIT_MASK_COLUMN: usize = 6;
const FRI_POSITION_MASK_COLUMN: usize = 7;
const FRI_OFFSET_MASK_COLUMN: usize = 8;
const LAST_POSITION_MASK_COLUMN: usize = 9;
const COEFFICIENT_MASK_COLUMN: usize = 10;
const SELECTOR_MASK_COLUMN: usize = 11;
const VERIFIER_ID_COLUMN: usize = 12;
const CIRCUIT_ID_COLUMN: usize = 13;
const NODE_ID_COLUMN: usize = 14;
const USE_COUNT_COLUMN: usize = 15;
const SOURCE_INDEX_0_COLUMN: usize = 16;
const SOURCE_INDEX_1_COLUMN: usize = 17;
const SOURCE_INDEX_2_COLUMN: usize = 18;
const SOURCE_INDEX_3_COLUMN: usize = 19;
const PREPROCESSED_COLUMN_COUNT: usize = 20;

/// Scalar fields exported by the trusted FRI route adapter.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum FriVerifierRouteField {
    Position = 1,
    Offset = 2,
}

impl FriVerifierRouteField {
    pub const fn as_u32(self) -> u32 {
        self as u32
    }
}

// Routed scalar: verifier, query-purpose, item, query, field, value.
relation!(FriVerifierRouteWordRelation, 6);

/// Relations exported by the FRI control and route adapter.
#[derive(Clone)]
pub struct FriVerifierRouteRelations {
    pub word: FriVerifierRouteWordRelation,
}

impl FriVerifierRouteRelations {
    pub fn dummy() -> Self {
        Self {
            word: FriVerifierRouteWordRelation::dummy(),
        }
    }

    pub fn draw(channel: &mut impl stwo::core::channel::Channel) -> Self {
        Self {
            word: FriVerifierRouteWordRelation::draw(channel),
        }
    }
}

/// One fixed verifier lane and its circuit namespace.
#[derive(Clone, Copy)]
pub struct FriVerifierCircuitLane<'a> {
    pub verifier_id: u32,
    pub circuit_id: u32,
    pub circuit: &'a FriVerifierCircuit,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PreprocessedRow {
    source: FriVerifierInputSource,
    lane: usize,
    binding: usize,
    segment_mask: u32,
    binary_mask: u32,
    verifier_id: u32,
    circuit_id: u32,
    node_id: u32,
    use_count: u32,
    source_indices: [u32; 4],
}

/// Verifier-owned FRI input-node layout for the VM lane and two child lanes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FriVerifierInputPreprocessed {
    log_size: u32,
    rows: Vec<PreprocessedRow>,
}

impl FriVerifierInputPreprocessed {
    pub fn new(lanes: [FriVerifierCircuitLane<'_>; 3]) -> Result<Self, FriVerifierInputError> {
        validate_lane_order(&lanes)?;
        let mut circuit_ids = HashSet::with_capacity(lanes.len());
        let mut rows = Vec::new();
        for (lane_index, lane) in lanes.iter().copied().enumerate() {
            M31Word::try_from(lane.circuit_id).map_err(|_| {
                FriVerifierInputError::CircuitIdNotCanonical {
                    circuit_id: lane.circuit_id,
                }
            })?;
            if !circuit_ids.insert(lane.circuit_id) {
                return Err(FriVerifierInputError::DuplicateCircuitId {
                    circuit_id: lane.circuit_id,
                });
            }
            let (segment_mask, binary_mask) = lane_masks(lane.verifier_id)?;
            let arena = lane.circuit.circuit().arena();
            let uses = use_counts_for_outputs(&arena, lane.circuit.circuit().outputs());
            let mut sources = HashSet::with_capacity(lane.circuit.input_bindings().len());
            let mut selector_count = 0_usize;
            for (binding_index, binding) in lane.circuit.input_bindings().iter().enumerate() {
                if !sources.insert(binding.source) {
                    return Err(FriVerifierInputError::DuplicateInputSource {
                        verifier_id: lane.verifier_id,
                        source: binding.source,
                    });
                }
                M31Word::try_from(binding.node_id).map_err(|_| {
                    FriVerifierInputError::NodeIdNotCanonical {
                        node_id: binding.node_id,
                    }
                })?;
                let node_index = usize::try_from(binding.node_id).map_err(|_| {
                    FriVerifierInputError::NodeIdDoesNotFitUsize {
                        node_id: binding.node_id,
                    }
                })?;
                let node =
                    arena
                        .nodes
                        .get(node_index)
                        .ok_or(FriVerifierInputError::NodeMissing {
                            node_id: binding.node_id,
                        })?;
                if node.op != Op::Input {
                    return Err(FriVerifierInputError::BindingTargetsNonInput {
                        node_id: binding.node_id,
                    });
                }
                let use_count = uses[node_index];
                M31Word::try_from(use_count).map_err(|_| {
                    FriVerifierInputError::UseCountNotCanonical {
                        node_id: binding.node_id,
                        use_count,
                    }
                })?;
                let source_indices =
                    validate_source(binding.source, lane.circuit.profile(), &mut selector_count)?;
                rows.push(PreprocessedRow {
                    source: binding.source,
                    lane: lane_index,
                    binding: binding_index,
                    segment_mask,
                    binary_mask,
                    verifier_id: lane.verifier_id,
                    circuit_id: lane.circuit_id,
                    node_id: binding.node_id,
                    use_count,
                    source_indices,
                });
            }
            if selector_count != 1 {
                return Err(FriVerifierInputError::SelectorCountMismatch {
                    verifier_id: lane.verifier_id,
                    actual: selector_count,
                });
            }
            let expected = expected_input_count(lane.circuit.profile())?;
            if sources.len() != expected {
                return Err(FriVerifierInputError::InputCountMismatch {
                    verifier_id: lane.verifier_id,
                    expected,
                    actual: sources.len(),
                });
            }
        }
        let padded_rows = rows
            .len()
            .checked_next_power_of_two()
            .ok_or(FriVerifierInputError::RowCountOverflow)?
            .max(1 << MIN_LOG_SIZE);
        let log_size = padded_rows.ilog2();
        if log_size > MAX_CIRCLE_DOMAIN_LOG_SIZE {
            return Err(FriVerifierInputError::LogSizeOutOfRange { log_size });
        }
        Ok(Self { log_size, rows })
    }

    pub const fn log_size(&self) -> u32 {
        self.log_size
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
        let mut columns = zero_columns(PREPROCESSED_COLUMN_COUNT, size);
        for (index, row) in self.rows.iter().copied().enumerate() {
            columns[ROW_MASK_COLUMN][index] = 1;
            columns[SEGMENT_MASK_COLUMN][index] = row.segment_mask;
            columns[BINARY_MASK_COLUMN][index] = row.binary_mask;
            columns[source_mask_column(row.source)][index] = 1;
            columns[VERIFIER_ID_COLUMN][index] = row.verifier_id;
            columns[CIRCUIT_ID_COLUMN][index] = row.circuit_id;
            columns[NODE_ID_COLUMN][index] = row.node_id;
            columns[USE_COUNT_COLUMN][index] = row.use_count;
            columns[SOURCE_INDEX_0_COLUMN][index] = row.source_indices[0];
            columns[SOURCE_INDEX_1_COLUMN][index] = row.source_indices[1];
            columns[SOURCE_INDEX_2_COLUMN][index] = row.source_indices[2];
            columns[SOURCE_INDEX_3_COLUMN][index] = row.source_indices[3];
        }
        into_evaluations(columns, self.log_size)
    }
}

fn source_mask_column(source: FriVerifierInputSource) -> usize {
    match source {
        FriVerifierInputSource::ActiveSelector => SELECTOR_MASK_COLUMN,
        FriVerifierInputSource::DeepAnswerWord { .. } => DEEP_ANSWER_MASK_COLUMN,
        FriVerifierInputSource::AuthenticatedValueWord { .. } => AUTHENTICATED_VALUE_MASK_COLUMN,
        FriVerifierInputSource::FriAlphaWord { .. } => FRI_ALPHA_MASK_COLUMN,
        FriVerifierInputSource::QueryBit { .. } => QUERY_BIT_MASK_COLUMN,
        FriVerifierInputSource::FriPosition { .. } => FRI_POSITION_MASK_COLUMN,
        FriVerifierInputSource::FriOffset { .. } => FRI_OFFSET_MASK_COLUMN,
        FriVerifierInputSource::LastLayerPosition { .. } => LAST_POSITION_MASK_COLUMN,
        FriVerifierInputSource::LastLayerCoefficientWord { .. } => COEFFICIENT_MASK_COLUMN,
    }
}

fn validate_lane_order(
    lanes: &[FriVerifierCircuitLane<'_>; 3],
) -> Result<(), FriVerifierInputError> {
    for (lane, expected) in lanes.iter().zip([
        SEGMENT_VERIFIER_ID,
        LEFT_RECURSION_VERIFIER_ID,
        RIGHT_RECURSION_VERIFIER_ID,
    ]) {
        if lane.verifier_id != expected {
            return Err(FriVerifierInputError::VerifierLaneOrderMismatch {
                expected,
                actual: lane.verifier_id,
            });
        }
    }
    Ok(())
}

fn lane_masks(verifier_id: u32) -> Result<(u32, u32), FriVerifierInputError> {
    match verifier_id {
        SEGMENT_VERIFIER_ID => Ok((1, 0)),
        LEFT_RECURSION_VERIFIER_ID | RIGHT_RECURSION_VERIFIER_ID => Ok((0, 1)),
        _ => Err(FriVerifierInputError::UnknownVerifierId { verifier_id }),
    }
}

fn validate_source(
    source: FriVerifierInputSource,
    profile: &FriVerifierProfile,
    selector_count: &mut usize,
) -> Result<[u32; 4], FriVerifierInputError> {
    match source {
        FriVerifierInputSource::ActiveSelector => {
            *selector_count = selector_count
                .checked_add(1)
                .ok_or(FriVerifierInputError::RowCountOverflow)?;
            Ok([0; 4])
        }
        FriVerifierInputSource::DeepAnswerWord { query, word } => {
            validate_index("query", query, profile.query_count())?;
            validate_word(word)?;
            Ok([query, word, 0, 0])
        }
        FriVerifierInputSource::AuthenticatedValueWord {
            layer,
            query,
            offset,
            word,
        } => {
            let layer_index = validate_index("FRI layer", layer, profile.layer_count())?;
            validate_index("query", query, profile.query_count())?;
            validate_index("FRI offset", offset, profile.fold_widths()[layer_index])?;
            validate_word(word)?;
            Ok([layer, query, offset, word])
        }
        FriVerifierInputSource::FriAlphaWord { layer, word } => {
            validate_index("FRI layer", layer, profile.layer_count())?;
            validate_word(word)?;
            Ok([layer, word, 0, 0])
        }
        FriVerifierInputSource::QueryBit { query, bit } => {
            validate_index("query", query, profile.query_count())?;
            validate_index("query bit", bit, M31_BITS)?;
            Ok([query, bit, 0, 0])
        }
        FriVerifierInputSource::FriPosition { layer, query }
        | FriVerifierInputSource::FriOffset { layer, query } => {
            validate_index("FRI layer", layer, profile.layer_count())?;
            validate_index("query", query, profile.query_count())?;
            Ok([layer, query, 0, 0])
        }
        FriVerifierInputSource::LastLayerPosition { query } => {
            validate_index("query", query, profile.query_count())?;
            Ok([query, 0, 0, 0])
        }
        FriVerifierInputSource::LastLayerCoefficientWord { coefficient, word } => {
            validate_index(
                "last-layer coefficient",
                coefficient,
                profile.last_layer_coefficient_count(),
            )?;
            validate_word(word)?;
            Ok([coefficient, word, 0, 0])
        }
    }
}

fn validate_index(
    field: &'static str,
    value: u32,
    count: usize,
) -> Result<usize, FriVerifierInputError> {
    let index = usize::try_from(value)
        .map_err(|_| FriVerifierInputError::SourceIndexDoesNotFitUsize { field, value })?;
    if index >= count {
        Err(FriVerifierInputError::SourceIndexOutOfRange {
            field,
            value,
            count,
        })
    } else {
        Ok(index)
    }
}

fn validate_word(word: u32) -> Result<(), FriVerifierInputError> {
    validate_index("secure word", word, SECURE_WORD_COUNT).map(|_| ())
}

fn expected_input_count(profile: &FriVerifierProfile) -> Result<usize, FriVerifierInputError> {
    let secure = |count: usize| {
        count
            .checked_mul(SECURE_WORD_COUNT)
            .ok_or(FriVerifierInputError::RowCountOverflow)
    };
    let authenticated = profile
        .fold_widths()
        .iter()
        .try_fold(0_usize, |sum, width| {
            profile
                .query_count()
                .checked_mul(*width)
                .and_then(|count| count.checked_mul(SECURE_WORD_COUNT))
                .and_then(|count| sum.checked_add(count))
                .ok_or(FriVerifierInputError::RowCountOverflow)
        })?;
    1_usize
        .checked_add(secure(profile.query_count())?)
        .and_then(|count| count.checked_add(authenticated))
        .and_then(|count| {
            secure(profile.layer_count())
                .ok()
                .and_then(|v| count.checked_add(v))
        })
        .and_then(|count| {
            profile
                .query_count()
                .checked_mul(M31_BITS)
                .and_then(|v| count.checked_add(v))
        })
        .and_then(|count| {
            profile
                .layer_count()
                .checked_mul(profile.query_count())
                .and_then(|v| v.checked_mul(2))
                .and_then(|v| count.checked_add(v))
        })
        .and_then(|count| count.checked_add(profile.query_count()))
        .and_then(|count| {
            secure(profile.last_layer_coefficient_count())
                .ok()
                .and_then(|v| count.checked_add(v))
        })
        .ok_or(FriVerifierInputError::RowCountOverflow)
}

fn zero_columns(count: usize, size: usize) -> Vec<AlignedVec<u32>> {
    (0..count)
        .map(|_| {
            let mut column = AlignedVec::with_capacity(size);
            column.resize(size, 0);
            column
        })
        .collect()
}

fn into_evaluations(
    columns: Vec<AlignedVec<u32>>,
    log_size: u32,
) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    let domain = CanonicCoset::new(log_size).circle_domain();
    columns
        .into_iter()
        .map(|column| CircleEvaluation::new(domain, BaseColumn::from(column)))
        .collect()
}

/// Relations used by the macro-generated FRI verifier input component.
#[derive(Clone)]
pub struct FriVerifierInputComponentRelations {
    pub verifier_input_word: super::transcript_payload_air::VerifierInputWordRelation,
    pub randomness_word: super::verifier_randomness_air::VerifierRandomnessWordRelation,
    pub query_bit_value: super::query_position_air::QueryBitValueRelation,
    pub deep_answer_word: super::pcs_deep_input_air::PcsDeepAnswerWordRelation,
    pub fri_value_word: super::fri_merkle_air::FriMerkleValueWordRelation,
    pub route_word: FriVerifierRouteWordRelation,
    pub wire: crate::relations::WireRelation,
}

impl FriVerifierInputComponentRelations {
    /// Combine every semantic input source with its exact circuit-wire use.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        verifier_input_relations: &VerifierInputRelations,
        randomness_relations: &VerifierRandomnessRelations,
        query_relations: &QueryPositionRelations,
        deep_relations: &PcsDeepRelations,
        fri_merkle_relations: &FriMerkleRelations,
        route_relations: &FriVerifierRouteRelations,
        circuit_relations: &RecursionRelations,
    ) -> Self {
        Self {
            verifier_input_word: verifier_input_relations.input_word.clone(),
            randomness_word: randomness_relations.word.clone(),
            query_bit_value: query_relations.bit_value.clone(),
            deep_answer_word: deep_relations.answer_word.clone(),
            fri_value_word: fri_merkle_relations.value_word.clone(),
            route_word: route_relations.word.clone(),
            wire: circuit_relations.wire.clone(),
        }
    }
}

stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [],
    embedded_component: true,
    embedded_enabler_boolean: false,
    embedded_relations: crate::fri_verifier_input_air::FriVerifierInputComponentRelations,
    logup_batch: 2,
    embedded_preprocessed: {
        row_mask: "recursion_fri_verifier_input_row_mask",
        segment_mask: "recursion_fri_verifier_input_segment_mask",
        binary_mask: "recursion_fri_verifier_input_binary_mask",
        deep_answer_mask: "recursion_fri_verifier_input_deep_answer_mask",
        authenticated_value_mask: "recursion_fri_verifier_input_authenticated_value_mask",
        alpha_mask: "recursion_fri_verifier_input_alpha_mask",
        query_bit_mask: "recursion_fri_verifier_input_query_bit_mask",
        fri_position_mask: "recursion_fri_verifier_input_fri_position_mask",
        fri_offset_mask: "recursion_fri_verifier_input_fri_offset_mask",
        last_position_mask: "recursion_fri_verifier_input_last_position_mask",
        coefficient_mask: "recursion_fri_verifier_input_coefficient_mask",
        selector_mask: "recursion_fri_verifier_input_selector_mask",
        verifier_id: "recursion_fri_verifier_input_verifier_id",
        circuit_id: "recursion_fri_verifier_input_circuit_id",
        node_id: "recursion_fri_verifier_input_node_id",
        use_count: "recursion_fri_verifier_input_use_count",
        source_index_0: "recursion_fri_verifier_input_source_index_0",
        source_index_1: "recursion_fri_verifier_input_source_index_1",
        source_index_2: "recursion_fri_verifier_input_source_index_2",
        source_index_3: "recursion_fri_verifier_input_source_index_3",
    },
    embedded_params: [
        segment_active, binary_active, fri_alpha_kind, fri_fold_kind,
        last_layer_kind, position_field, offset_field, coefficient_kind,
    ],

    relation verifier_input_word(5);
    relation randomness_word(5);
    relation query_bit_value(4);
    relation deep_answer_word(4);
    relation fri_value_word(6);
    relation route_word(6);
    relation wire(6);

    fn fri_verifier_input(
        value,
        row_mask, segment_mask, binary_mask, deep_answer_mask,
        authenticated_value_mask, alpha_mask, query_bit_mask, fri_position_mask,
        fri_offset_mask, last_position_mask, coefficient_mask, selector_mask,
        verifier_id, circuit_id, node_id, use_count,
        source_index_0, source_index_1, source_index_2, source_index_3,
        segment_active, binary_active, fri_alpha_kind, fri_fold_kind,
        last_layer_kind, position_field, offset_field, coefficient_kind,
    ) {
        let active = segment_mask * segment_active + binary_mask * binary_active;
        let witness_mask = row_mask - selector_mask;

        constrain enabler - row_mask;
        constrain witness_mask * (1 - active) * value;
        constrain selector_mask * (value - active);

        consume(active * deep_answer_mask) deep_answer_word(
            verifier_id, source_index_0, source_index_1, value,
        );
        consume(active * authenticated_value_mask) fri_value_word(
            verifier_id, source_index_0, source_index_1,
            source_index_2, source_index_3, value,
        );
        consume(active * alpha_mask) randomness_word(
            verifier_id, fri_alpha_kind, source_index_0, source_index_1, value,
        );
        consume(active * query_bit_mask) query_bit_value(
            verifier_id, source_index_0, source_index_1, value,
        );
        consume(active * fri_position_mask) route_word(
            verifier_id, fri_fold_kind, source_index_0, source_index_1,
            position_field, value,
        );
        consume(active * fri_offset_mask) route_word(
            verifier_id, fri_fold_kind, source_index_0, source_index_1,
            offset_field, value,
        );
        consume(active * last_position_mask) route_word(
            verifier_id, last_layer_kind, 0, source_index_0, position_field, value,
        );
        consume(active * coefficient_mask) verifier_input_word(
            verifier_id, coefficient_kind, source_index_0, source_index_1, value,
        );
        emit(active * use_count) wire(circuit_id, node_id, value, 0, 0, 0);

        return value;
    }
}

pub use component::air::{Component, Eval};

/// Construct the generated FRI verifier input evaluator for the selected proof kind.
#[allow(clippy::too_many_arguments)]
pub fn eval_for_proof_kind(
    log_size: u32,
    proof_kind: ProofKind,
    verifier_input_relations: &VerifierInputRelations,
    randomness_relations: &VerifierRandomnessRelations,
    query_relations: &QueryPositionRelations,
    deep_relations: &PcsDeepRelations,
    fri_merkle_relations: &FriMerkleRelations,
    route_relations: &FriVerifierRouteRelations,
    circuit_relations: &RecursionRelations,
) -> Eval {
    Eval {
        log_size,
        segment_active: BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        binary_active: BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode)),
        fri_alpha_kind: BaseField::from(VerifierRandomnessKind::FriAlpha.as_u32()),
        fri_fold_kind: BaseField::from(QueryPositionKind::FriFold.as_u32()),
        last_layer_kind: BaseField::from(QueryPositionKind::LastLayer.as_u32()),
        position_field: BaseField::from(FriVerifierRouteField::Position.as_u32()),
        offset_field: BaseField::from(FriVerifierRouteField::Offset.as_u32()),
        coefficient_kind: BaseField::from(VerifierInputKind::LastLayerCoefficient.as_u32()),
        relations: FriVerifierInputComponentRelations::new(
            verifier_input_relations,
            randomness_relations,
            query_relations,
            deep_relations,
            fri_merkle_relations,
            route_relations,
            circuit_relations,
        ),
    }
}

/// Generate semantic consumers and circuit-wire producers.
#[allow(clippy::too_many_arguments)]
pub fn gen_interaction_trace(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    preprocessed: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    proof_kind: ProofKind,
    verifier_input_relations: &VerifierInputRelations,
    randomness_relations: &VerifierRandomnessRelations,
    query_relations: &QueryPositionRelations,
    deep_relations: &PcsDeepRelations,
    fri_merkle_relations: &FriMerkleRelations,
    route_relations: &FriVerifierRouteRelations,
    circuit_relations: &RecursionRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    component::witness::gen_interaction_trace(
        trace,
        preprocessed,
        BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode)),
        BaseField::from(VerifierRandomnessKind::FriAlpha.as_u32()),
        BaseField::from(QueryPositionKind::FriFold.as_u32()),
        BaseField::from(QueryPositionKind::LastLayer.as_u32()),
        BaseField::from(FriVerifierRouteField::Position.as_u32()),
        BaseField::from(FriVerifierRouteField::Offset.as_u32()),
        BaseField::from(VerifierInputKind::LastLayerCoefficient.as_u32()),
        &FriVerifierInputComponentRelations::new(
            verifier_input_relations,
            randomness_relations,
            query_relations,
            deep_relations,
            fri_merkle_relations,
            route_relations,
            circuit_relations,
        ),
    )
}

/// Materializes every lane after checking fixed circuit and mode assignments.
pub fn push_fri_verifier_inputs(
    table: &mut FriVerifierInputTable,
    preprocessed: &FriVerifierInputPreprocessed,
    references: [FriVerifierCircuitLane<'_>; 3],
    witnesses: [FriVerifierCircuitLane<'_>; 3],
    proof_kind: ProofKind,
) -> Result<(), FriVerifierInputError> {
    validate_lane_order(&references)?;
    validate_lane_order(&witnesses)?;
    for (reference, witness) in references.iter().zip(witnesses.iter()) {
        if reference.verifier_id != witness.verifier_id
            || reference.circuit_id != witness.circuit_id
            || reference.circuit.profile() != witness.circuit.profile()
            || reference.circuit.input_bindings() != witness.circuit.input_bindings()
            || reference.circuit.circuit().outputs() != witness.circuit.circuit().outputs()
        {
            return Err(FriVerifierInputError::InputLayoutMismatch {
                verifier_id: witness.verifier_id,
            });
        }
    }
    if preprocessed.rows.len()
        != references
            .iter()
            .map(|lane| lane.circuit.input_bindings().len())
            .sum()
    {
        return Err(FriVerifierInputError::PreprocessedInputCountMismatch);
    }
    for row in &preprocessed.rows {
        let reference = references[row.lane];
        let witness = witnesses[row.lane];
        if row.verifier_id != reference.verifier_id
            || row.circuit_id != reference.circuit_id
            || reference
                .circuit
                .input_bindings()
                .get(row.binding)
                .is_none()
        {
            return Err(FriVerifierInputError::PreprocessedCoordinateMismatch {
                verifier_id: row.verifier_id,
                node_id: row.node_id,
            });
        }
        let reference_binding = reference.circuit.input_bindings()[row.binding];
        let witness_binding = witness.circuit.input_bindings()[row.binding];
        if reference_binding != witness_binding
            || row.node_id != witness_binding.node_id
            || row.source != witness_binding.source
        {
            return Err(FriVerifierInputError::InputCoordinateMismatch {
                verifier_id: row.verifier_id,
                node_id: row.node_id,
            });
        }
        let node_index = usize::try_from(row.node_id).map_err(|_| {
            FriVerifierInputError::NodeIdDoesNotFitUsize {
                node_id: row.node_id,
            }
        })?;
        let arena = witness.circuit.circuit().arena();
        let node = arena
            .nodes
            .get(node_index)
            .ok_or(FriVerifierInputError::NodeMissing {
                node_id: row.node_id,
            })?;
        if node.op != Op::Input {
            return Err(FriVerifierInputError::BindingTargetsNonInput {
                node_id: row.node_id,
            });
        }
        let limbs = node.value.to_m31_array();
        if limbs[1..].iter().any(|limb| limb.0 != 0) {
            return Err(FriVerifierInputError::InputIsNotBaseField {
                node_id: row.node_id,
            });
        }
        let active = verifier_is_active(row.verifier_id, proof_kind)?;
        let expected = if row.source == FriVerifierInputSource::ActiveSelector {
            u32::from(active)
        } else if active {
            limbs[0].0
        } else {
            0
        };
        if limbs[0].0 != expected {
            return Err(FriVerifierInputError::InactiveInputIsNonZero {
                verifier_id: row.verifier_id,
                node_id: row.node_id,
            });
        }
        table.push(expected);
    }
    Ok(())
}

fn verifier_is_active(
    verifier_id: u32,
    proof_kind: ProofKind,
) -> Result<bool, FriVerifierInputError> {
    match verifier_id {
        SEGMENT_VERIFIER_ID => Ok(proof_kind == ProofKind::SegmentLeaf),
        LEFT_RECURSION_VERIFIER_ID | RIGHT_RECURSION_VERIFIER_ID => {
            Ok(proof_kind == ProofKind::BinaryNode)
        }
        _ => Err(FriVerifierInputError::UnknownVerifierId { verifier_id }),
    }
}

/// Invalid lane layout, source coordinate, or mode assignment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FriVerifierInputError {
    CircuitIdNotCanonical {
        circuit_id: u32,
    },
    DuplicateCircuitId {
        circuit_id: u32,
    },
    VerifierLaneOrderMismatch {
        expected: u32,
        actual: u32,
    },
    UnknownVerifierId {
        verifier_id: u32,
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
        verifier_id: u32,
        source: FriVerifierInputSource,
    },
    SelectorCountMismatch {
        verifier_id: u32,
        actual: usize,
    },
    SourceIndexDoesNotFitUsize {
        field: &'static str,
        value: u32,
    },
    SourceIndexOutOfRange {
        field: &'static str,
        value: u32,
        count: usize,
    },
    InputCountMismatch {
        verifier_id: u32,
        expected: usize,
        actual: usize,
    },
    PreprocessedInputCountMismatch,
    InputLayoutMismatch {
        verifier_id: u32,
    },
    PreprocessedCoordinateMismatch {
        verifier_id: u32,
        node_id: u32,
    },
    InputCoordinateMismatch {
        verifier_id: u32,
        node_id: u32,
    },
    InputIsNotBaseField {
        node_id: u32,
    },
    InactiveInputIsNonZero {
        verifier_id: u32,
        node_id: u32,
    },
}

impl fmt::Display for FriVerifierInputError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for FriVerifierInputError {}

#[cfg(test)]
mod tests {
    use num_traits::Zero;
    use rstest::rstest;
    use stwo::core::fields::qm31::SecureField;
    use stwo::core::pcs::TreeVec;
    use stwo_constraint_framework::{FrameworkEval, assert_constraints_on_polys};

    use super::*;
    use crate::fri_verifier_circuit::{
        FriVerifierProfile, FriVerifierWitness, build_fri_verifier_circuit,
        build_fri_verifier_reference,
    };

    const CIRCUIT_IDS: [u32; 3] = [301, 302, 303];

    struct CircuitSet {
        segment: FriVerifierCircuit,
        left: FriVerifierCircuit,
        right: FriVerifierCircuit,
    }

    impl CircuitSet {
        fn lanes(&self) -> [FriVerifierCircuitLane<'_>; 3] {
            [
                FriVerifierCircuitLane {
                    verifier_id: SEGMENT_VERIFIER_ID,
                    circuit_id: CIRCUIT_IDS[0],
                    circuit: &self.segment,
                },
                FriVerifierCircuitLane {
                    verifier_id: LEFT_RECURSION_VERIFIER_ID,
                    circuit_id: CIRCUIT_IDS[1],
                    circuit: &self.left,
                },
                FriVerifierCircuitLane {
                    verifier_id: RIGHT_RECURSION_VERIFIER_ID,
                    circuit_id: CIRCUIT_IDS[2],
                    circuit: &self.right,
                },
            ]
        }
    }

    fn profile() -> FriVerifierProfile {
        FriVerifierProfile::new(4, 1, 1, vec![4], 1).expect("fixture FRI profile is valid")
    }

    fn inactive_set(profile: &FriVerifierProfile) -> CircuitSet {
        CircuitSet {
            segment: build_fri_verifier_reference(profile).expect("segment reference is valid"),
            left: build_fri_verifier_reference(profile).expect("left reference is valid"),
            right: build_fri_verifier_reference(profile).expect("right reference is valid"),
        }
    }

    /// The all-zero assignment satisfies every fold identity, so it doubles
    /// as a valid active witness with the same arena as the reference.
    fn active_circuit(profile: &FriVerifierProfile) -> FriVerifierCircuit {
        let deep_answers = vec![SecureField::zero(); profile.query_count()];
        let authenticated_values = profile
            .fold_widths()
            .iter()
            .map(|width| vec![SecureField::zero(); profile.query_count() * width])
            .collect::<Vec<_>>();
        let fri_alphas = vec![SecureField::zero(); profile.layer_count()];
        let raw_queries = vec![M31Word::ZERO; profile.query_count()];
        let fri_positions = profile
            .fold_widths()
            .iter()
            .map(|_| vec![M31Word::ZERO; profile.query_count()])
            .collect::<Vec<_>>();
        let fri_offsets = fri_positions.clone();
        let last_layer_positions = vec![M31Word::ZERO; profile.query_count()];
        let last_layer_coefficients =
            vec![SecureField::zero(); profile.last_layer_coefficient_count()];
        build_fri_verifier_circuit(
            profile,
            FriVerifierWitness {
                active: true,
                deep_answers: &deep_answers,
                authenticated_values: &authenticated_values,
                fri_alphas: &fri_alphas,
                raw_queries: &raw_queries,
                fri_positions: &fri_positions,
                fri_offsets: &fri_offsets,
                last_layer_positions: &last_layer_positions,
                last_layer_coefficients: &last_layer_coefficients,
            },
        )
        .expect("zero assignment defines a valid active circuit")
    }

    fn witness_set(profile: &FriVerifierProfile, kind: ProofKind) -> CircuitSet {
        CircuitSet {
            segment: if kind == ProofKind::SegmentLeaf {
                active_circuit(profile)
            } else {
                build_fri_verifier_reference(profile).expect("segment reference is valid")
            },
            left: if kind == ProofKind::BinaryNode {
                active_circuit(profile)
            } else {
                build_fri_verifier_reference(profile).expect("left reference is valid")
            },
            right: if kind == ProofKind::BinaryNode {
                active_circuit(profile)
            } else {
                build_fri_verifier_reference(profile).expect("right reference is valid")
            },
        }
    }

    fn assert_constraints(kind: ProofKind) {
        let profile = profile();
        let references = inactive_set(&profile);
        let witnesses = witness_set(&profile, kind);
        let preprocessing = FriVerifierInputPreprocessed::new(references.lanes())
            .expect("fixture references own every input");
        let mut table = FriVerifierInputTable::new();
        push_fri_verifier_inputs(
            &mut table,
            &preprocessing,
            references.lanes(),
            witnesses.lanes(),
            kind,
        )
        .expect("fixture mode assignment is valid");
        let trace = table.into_witness();
        let preprocessed = preprocessing.gen_columns();
        let verifier_input_relations = VerifierInputRelations::dummy();
        let randomness_relations = VerifierRandomnessRelations::dummy();
        let query_relations = QueryPositionRelations::dummy();
        let deep_relations = PcsDeepRelations::dummy();
        let fri_merkle_relations = FriMerkleRelations::dummy();
        let route_relations = FriVerifierRouteRelations::dummy();
        let circuit_relations = RecursionRelations::dummy();
        let (interaction, claimed_sum) = gen_interaction_trace(
            &trace,
            &preprocessed,
            kind,
            &verifier_input_relations,
            &randomness_relations,
            &query_relations,
            &deep_relations,
            &fri_merkle_relations,
            &route_relations,
            &circuit_relations,
        );
        let traces = TreeVec::new(vec![preprocessed, trace, interaction]);
        let polys = traces.map_cols(|column| column.interpolate());
        let eval = eval_for_proof_kind(
            preprocessing.log_size(),
            kind,
            &verifier_input_relations,
            &randomness_relations,
            &query_relations,
            &deep_relations,
            &fri_merkle_relations,
            &route_relations,
            &circuit_relations,
        );
        assert_constraints_on_polys(
            &polys,
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
    fn every_universal_mode_satisfies_fri_input_constraints(#[case] kind: ProofKind) {
        assert_constraints(kind);
    }

    #[test]
    fn preprocessing_owns_every_tracked_input_once() {
        let profile = profile();
        let references = inactive_set(&profile);
        let preprocessing = FriVerifierInputPreprocessed::new(references.lanes())
            .expect("fixture references own every input");
        assert_eq!(
            preprocessing.row_count(),
            references
                .lanes()
                .iter()
                .map(|lane| lane.circuit.input_bindings().len())
                .sum()
        );
    }

    #[test]
    fn active_segment_inputs_cannot_be_reused_in_empty_mode() {
        let profile = profile();
        let references = inactive_set(&profile);
        let mut witnesses = inactive_set(&profile);
        witnesses.segment = active_circuit(&profile);
        let preprocessing = FriVerifierInputPreprocessed::new(references.lanes())
            .expect("fixture references own every input");
        let result = push_fri_verifier_inputs(
            &mut FriVerifierInputTable::new(),
            &preprocessing,
            references.lanes(),
            witnesses.lanes(),
            ProofKind::EmptyLeaf,
        );
        assert!(matches!(
            result,
            Err(FriVerifierInputError::InactiveInputIsNonZero {
                verifier_id: SEGMENT_VERIFIER_ID,
                ..
            })
        ));
    }

    #[test]
    fn authenticated_value_sources_are_typed_by_full_subset_coordinates() {
        let profile = profile();
        let references = inactive_set(&profile);
        let preprocessing = FriVerifierInputPreprocessed::new(references.lanes())
            .expect("fixture references own every input");
        let expected_per_lane: usize = profile
            .fold_widths()
            .iter()
            .map(|width| profile.query_count() * width * SECURE_WORD_COUNT)
            .sum();
        assert_eq!(
            preprocessing
                .rows
                .iter()
                .filter(|row| matches!(
                    row.source,
                    FriVerifierInputSource::AuthenticatedValueWord { .. }
                ))
                .count(),
            3 * expected_per_lane
        );
    }
}
