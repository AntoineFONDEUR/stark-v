//! AIR ownership for fixed PCS DEEP-circuit inputs and outputs.
//!
//! Trusted preprocessing assigns each tracked base-field node to one exact
//! verifier lane and semantic source. Active lanes consume transcript samples,
//! authenticated trace values, typed randomness, canonical query bits, and the
//! routed DEEP position. The claimed DEEP answer is exported word by word for
//! the first FRI fold, while every node emits its exact circuit-wire use count.

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
use super::pcs_deep_circuit::{PcsDeepCircuit, PcsDeepInputSource};
use super::query_position_air::{QueryPositionKind, QueryPositionRelations};
use super::trace_merkle_air::TraceMerkleRelations;
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
const SAMPLED_VALUE_MASK_COLUMN: usize = 3;
const QUERIED_VALUE_MASK_COLUMN: usize = 4;
const OODS_SEED_MASK_COLUMN: usize = 5;
const DEEP_RANDOMNESS_MASK_COLUMN: usize = 6;
const QUERY_BIT_MASK_COLUMN: usize = 7;
const QUERY_POSITION_MASK_COLUMN: usize = 8;
const ANSWER_MASK_COLUMN: usize = 9;
const SELECTOR_MASK_COLUMN: usize = 10;
const VERIFIER_ID_COLUMN: usize = 11;
const CIRCUIT_ID_COLUMN: usize = 12;
const NODE_ID_COLUMN: usize = 13;
const USE_COUNT_COLUMN: usize = 14;
const SOURCE_INDEX_0_COLUMN: usize = 15;
const SOURCE_INDEX_1_COLUMN: usize = 16;
const SOURCE_INDEX_2_COLUMN: usize = 17;
const PREPROCESSED_COLUMN_COUNT: usize = 18;

// The first FRI layer consumes each secure DEEP answer through four typed words.
relation!(PcsDeepAnswerWordRelation, 4);

/// Relations exported by the DEEP input and output boundary.
#[derive(Clone)]
pub struct PcsDeepRelations {
    pub answer_word: PcsDeepAnswerWordRelation,
}

impl PcsDeepRelations {
    pub fn dummy() -> Self {
        Self {
            answer_word: PcsDeepAnswerWordRelation::dummy(),
        }
    }

    pub fn draw(channel: &mut impl stwo::core::channel::Channel) -> Self {
        Self {
            answer_word: PcsDeepAnswerWordRelation::draw(channel),
        }
    }
}

/// One fixed verifier lane and its circuit namespace.
#[derive(Clone, Copy)]
pub struct PcsDeepCircuitLane<'a> {
    pub verifier_id: u32,
    pub circuit_id: u32,
    pub circuit: &'a PcsDeepCircuit,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PreprocessedRow {
    source: PcsDeepInputSource,
    lane: usize,
    binding: usize,
    segment_mask: u32,
    binary_mask: u32,
    verifier_id: u32,
    circuit_id: u32,
    node_id: u32,
    use_count: u32,
    source_indices: [u32; 3],
}

/// Verifier-owned input-node layout for the VM lane and two child lanes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PcsDeepInputPreprocessed {
    log_size: u32,
    rows: Vec<PreprocessedRow>,
}

impl PcsDeepInputPreprocessed {
    pub fn new(lanes: [PcsDeepCircuitLane<'_>; 3]) -> Result<Self, PcsDeepInputError> {
        validate_lane_order(&lanes)?;
        let mut circuit_ids = HashSet::with_capacity(lanes.len());
        let mut rows = Vec::new();
        for (lane_index, lane) in lanes.iter().copied().enumerate() {
            M31Word::try_from(lane.circuit_id).map_err(|_| {
                PcsDeepInputError::CircuitIdNotCanonical {
                    circuit_id: lane.circuit_id,
                }
            })?;
            if !circuit_ids.insert(lane.circuit_id) {
                return Err(PcsDeepInputError::DuplicateCircuitId {
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
                    return Err(PcsDeepInputError::DuplicateInputSource {
                        verifier_id: lane.verifier_id,
                        source: binding.source,
                    });
                }
                M31Word::try_from(binding.node_id).map_err(|_| {
                    PcsDeepInputError::NodeIdNotCanonical {
                        node_id: binding.node_id,
                    }
                })?;
                let node_index = usize::try_from(binding.node_id).map_err(|_| {
                    PcsDeepInputError::NodeIdDoesNotFitUsize {
                        node_id: binding.node_id,
                    }
                })?;
                let node = arena
                    .nodes
                    .get(node_index)
                    .ok_or(PcsDeepInputError::NodeMissing {
                        node_id: binding.node_id,
                    })?;
                if node.op != Op::Input {
                    return Err(PcsDeepInputError::BindingTargetsNonInput {
                        node_id: binding.node_id,
                    });
                }
                let use_count = uses[node_index];
                M31Word::try_from(use_count).map_err(|_| {
                    PcsDeepInputError::UseCountNotCanonical {
                        node_id: binding.node_id,
                        use_count,
                    }
                })?;
                let source_indices =
                    validate_source(binding.source, lane.circuit, &mut selector_count)?;
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
                return Err(PcsDeepInputError::SelectorCountMismatch {
                    verifier_id: lane.verifier_id,
                    actual: selector_count,
                });
            }
            let expected = expected_input_count(lane.circuit)?;
            if lane.circuit.input_bindings().len() != expected {
                return Err(PcsDeepInputError::InputCountMismatch {
                    verifier_id: lane.verifier_id,
                    expected,
                    actual: lane.circuit.input_bindings().len(),
                });
            }
        }
        let padded = rows
            .len()
            .checked_next_power_of_two()
            .ok_or(PcsDeepInputError::RowCountOverflow)?
            .max(1 << MIN_LOG_SIZE);
        let log_size = padded.ilog2();
        if log_size > MAX_CIRCLE_DOMAIN_LOG_SIZE {
            return Err(PcsDeepInputError::LogSizeOutOfRange { log_size });
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
        for (row_index, row) in self.rows.iter().copied().enumerate() {
            columns[ROW_MASK_COLUMN][row_index] = 1;
            columns[SEGMENT_MASK_COLUMN][row_index] = row.segment_mask;
            columns[BINARY_MASK_COLUMN][row_index] = row.binary_mask;
            columns[SAMPLED_VALUE_MASK_COLUMN][row_index] = u32::from(matches!(
                row.source,
                PcsDeepInputSource::SampledValueWord { .. }
            ));
            columns[QUERIED_VALUE_MASK_COLUMN][row_index] = u32::from(matches!(
                row.source,
                PcsDeepInputSource::QueriedValue { .. }
            ));
            columns[OODS_SEED_MASK_COLUMN][row_index] = u32::from(matches!(
                row.source,
                PcsDeepInputSource::OodsSeedWord { .. }
            ));
            columns[DEEP_RANDOMNESS_MASK_COLUMN][row_index] = u32::from(matches!(
                row.source,
                PcsDeepInputSource::DeepRandomnessWord { .. }
            ));
            columns[QUERY_BIT_MASK_COLUMN][row_index] =
                u32::from(matches!(row.source, PcsDeepInputSource::QueryBit { .. }));
            columns[QUERY_POSITION_MASK_COLUMN][row_index] = u32::from(matches!(
                row.source,
                PcsDeepInputSource::QueryPosition { .. }
            ));
            columns[ANSWER_MASK_COLUMN][row_index] =
                u32::from(matches!(row.source, PcsDeepInputSource::AnswerWord { .. }));
            columns[SELECTOR_MASK_COLUMN][row_index] =
                u32::from(row.source == PcsDeepInputSource::ActiveSelector);
            columns[VERIFIER_ID_COLUMN][row_index] = row.verifier_id;
            columns[CIRCUIT_ID_COLUMN][row_index] = row.circuit_id;
            columns[NODE_ID_COLUMN][row_index] = row.node_id;
            columns[USE_COUNT_COLUMN][row_index] = row.use_count;
            columns[SOURCE_INDEX_0_COLUMN][row_index] = row.source_indices[0];
            columns[SOURCE_INDEX_1_COLUMN][row_index] = row.source_indices[1];
            columns[SOURCE_INDEX_2_COLUMN][row_index] = row.source_indices[2];
        }
        let domain = CanonicCoset::new(self.log_size).circle_domain();
        columns
            .into_iter()
            .map(|column| CircleEvaluation::new(domain, BaseColumn::from(column)))
            .collect()
    }
}

fn validate_lane_order(lanes: &[PcsDeepCircuitLane<'_>; 3]) -> Result<(), PcsDeepInputError> {
    let expected = [
        SEGMENT_VERIFIER_ID,
        LEFT_RECURSION_VERIFIER_ID,
        RIGHT_RECURSION_VERIFIER_ID,
    ];
    for (lane, expected) in lanes.iter().zip(expected) {
        if lane.verifier_id != expected {
            return Err(PcsDeepInputError::VerifierLaneOrderMismatch {
                expected,
                actual: lane.verifier_id,
            });
        }
    }
    Ok(())
}

fn lane_masks(verifier_id: u32) -> Result<(u32, u32), PcsDeepInputError> {
    match verifier_id {
        SEGMENT_VERIFIER_ID => Ok((1, 0)),
        LEFT_RECURSION_VERIFIER_ID | RIGHT_RECURSION_VERIFIER_ID => Ok((0, 1)),
        _ => Err(PcsDeepInputError::UnknownVerifierId { verifier_id }),
    }
}

fn validate_source(
    source: PcsDeepInputSource,
    circuit: &PcsDeepCircuit,
    selector_count: &mut usize,
) -> Result<[u32; 3], PcsDeepInputError> {
    let profile = circuit.profile();
    match source {
        PcsDeepInputSource::ActiveSelector => {
            *selector_count = selector_count
                .checked_add(1)
                .ok_or(PcsDeepInputError::RowCountOverflow)?;
            Ok([0; 3])
        }
        PcsDeepInputSource::SampledValueWord { sample, word } => {
            validate_index("sample", sample, profile.sample_count())?;
            validate_word(word)?;
            Ok([sample, word, 0])
        }
        PcsDeepInputSource::QueriedValue {
            tree,
            column,
            query,
        } => {
            let tree_index = validate_index("tree", tree, profile.column_log_sizes().len())?;
            validate_index(
                "column",
                column,
                profile.column_log_sizes()[tree_index].len(),
            )?;
            validate_index("query", query, profile.query_count())?;
            Ok([tree, column, query])
        }
        PcsDeepInputSource::OodsSeedWord { word }
        | PcsDeepInputSource::DeepRandomnessWord { word } => {
            validate_word(word)?;
            Ok([0, word, 0])
        }
        PcsDeepInputSource::QueryBit { query, bit } => {
            validate_index("query", query, profile.query_count())?;
            validate_index("query bit", bit, M31_BITS)?;
            Ok([query, bit, 0])
        }
        PcsDeepInputSource::QueryPosition { query } => {
            validate_index("query", query, profile.query_count())?;
            Ok([query, 0, 0])
        }
        PcsDeepInputSource::AnswerWord { query, word } => {
            validate_index("query", query, profile.query_count())?;
            validate_word(word)?;
            Ok([query, word, 0])
        }
    }
}

fn validate_index(
    field: &'static str,
    value: u32,
    count: usize,
) -> Result<usize, PcsDeepInputError> {
    let index = usize::try_from(value)
        .map_err(|_| PcsDeepInputError::SourceIndexDoesNotFitUsize { field, value })?;
    if index >= count {
        Err(PcsDeepInputError::SourceIndexOutOfRange {
            field,
            value,
            count,
        })
    } else {
        Ok(index)
    }
}

fn validate_word(word: u32) -> Result<(), PcsDeepInputError> {
    validate_index("secure word", word, SECURE_WORD_COUNT).map(|_| ())
}

fn expected_input_count(circuit: &PcsDeepCircuit) -> Result<usize, PcsDeepInputError> {
    let profile = circuit.profile();
    profile
        .sample_count()
        .checked_mul(SECURE_WORD_COUNT)
        .and_then(|count| {
            profile
                .column_count()
                .checked_mul(profile.query_count())
                .and_then(|queried| count.checked_add(queried))
        })
        .and_then(|count| count.checked_add(2 * SECURE_WORD_COUNT))
        .and_then(|count| {
            profile
                .query_count()
                .checked_mul(M31_BITS)
                .and_then(|bits| count.checked_add(bits))
        })
        .and_then(|count| count.checked_add(profile.query_count()))
        .and_then(|count| {
            profile
                .query_count()
                .checked_mul(SECURE_WORD_COUNT)
                .and_then(|answers| count.checked_add(answers))
        })
        .and_then(|count| count.checked_add(1))
        .ok_or(PcsDeepInputError::RowCountOverflow)
}

/// Relations used by the macro-generated PCS DEEP boundary component.
#[derive(Clone)]
pub struct PcsDeepInputComponentRelations {
    pub verifier_input_word: super::transcript_payload_air::VerifierInputWordRelation,
    pub trace_value: super::trace_merkle_air::TraceQueryValueRelation,
    pub randomness_word: super::verifier_randomness_air::VerifierRandomnessWordRelation,
    pub query_bit_value: super::query_position_air::QueryBitValueRelation,
    pub query_position: super::query_position_air::QueryPositionRelation,
    pub answer_word: PcsDeepAnswerWordRelation,
    pub wire: crate::relations::WireRelation,
}

impl PcsDeepInputComponentRelations {
    /// Combine every authenticated source, answer export, and circuit wire.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        verifier_input_relations: &VerifierInputRelations,
        trace_relations: &TraceMerkleRelations,
        randomness_relations: &VerifierRandomnessRelations,
        query_relations: &QueryPositionRelations,
        deep_relations: &PcsDeepRelations,
        circuit_relations: &RecursionRelations,
    ) -> Self {
        Self {
            verifier_input_word: verifier_input_relations.input_word.clone(),
            trace_value: trace_relations.value.clone(),
            randomness_word: randomness_relations.word.clone(),
            query_bit_value: query_relations.bit_value.clone(),
            query_position: query_relations.position.clone(),
            answer_word: deep_relations.answer_word.clone(),
            wire: circuit_relations.wire.clone(),
        }
    }
}

stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [],
    embedded_component: true,
    embedded_enabler_boolean: false,
    embedded_relations: crate::pcs_deep_input_air::PcsDeepInputComponentRelations,
    logup_batch: 2,
    embedded_preprocessed: {
        row_mask: "recursion_pcs_deep_input_row_mask",
        segment_mask: "recursion_pcs_deep_input_segment_mask",
        binary_mask: "recursion_pcs_deep_input_binary_mask",
        sampled_value_mask: "recursion_pcs_deep_input_sampled_value_mask",
        queried_value_mask: "recursion_pcs_deep_input_queried_value_mask",
        oods_seed_mask: "recursion_pcs_deep_input_oods_seed_mask",
        deep_randomness_mask: "recursion_pcs_deep_input_deep_randomness_mask",
        query_bit_mask: "recursion_pcs_deep_input_query_bit_mask",
        query_position_mask: "recursion_pcs_deep_input_query_position_mask",
        answer_mask: "recursion_pcs_deep_input_answer_mask",
        selector_mask: "recursion_pcs_deep_input_selector_mask",
        verifier_id: "recursion_pcs_deep_input_verifier_id",
        circuit_id: "recursion_pcs_deep_input_circuit_id",
        node_id: "recursion_pcs_deep_input_node_id",
        use_count: "recursion_pcs_deep_input_use_count",
        source_index_0: "recursion_pcs_deep_input_source_index_0",
        source_index_1: "recursion_pcs_deep_input_source_index_1",
        source_index_2: "recursion_pcs_deep_input_source_index_2",
    },
    embedded_params: [
        segment_active, binary_active, sampled_value_kind, oods_point_kind,
        deep_randomness_kind, deep_position_kind,
    ],

    relation verifier_input_word(5);
    relation trace_value(5);
    relation randomness_word(5);
    relation query_bit_value(4);
    relation query_position(6);
    relation answer_word(4);
    relation wire(6);

    fn pcs_deep_input(
        value,
        row_mask, segment_mask, binary_mask, sampled_value_mask, queried_value_mask,
        oods_seed_mask, deep_randomness_mask, query_bit_mask, query_position_mask,
        answer_mask, selector_mask, verifier_id, circuit_id, node_id, use_count,
        source_index_0, source_index_1, source_index_2,
        segment_active, binary_active, sampled_value_kind, oods_point_kind,
        deep_randomness_kind, deep_position_kind,
    ) {
        let active = segment_mask * segment_active + binary_mask * binary_active;
        let witness_mask = row_mask - selector_mask;

        constrain enabler - row_mask;
        constrain witness_mask * (1 - active) * value;
        constrain selector_mask * (value - active);

        consume(active * sampled_value_mask) verifier_input_word(
            verifier_id, sampled_value_kind, source_index_0, source_index_1, value,
        );
        consume(active * queried_value_mask) trace_value(
            verifier_id, source_index_0, source_index_1, source_index_2, value,
        );
        consume(active * oods_seed_mask) randomness_word(
            verifier_id, oods_point_kind, source_index_0, source_index_1, value,
        );
        consume(active * deep_randomness_mask) randomness_word(
            verifier_id, deep_randomness_kind, source_index_0, source_index_1, value,
        );
        consume(active * query_bit_mask) query_bit_value(
            verifier_id, source_index_0, source_index_1, value,
        );
        consume(active * query_position_mask) query_position(
            verifier_id, deep_position_kind, 0, source_index_0, value, 0,
        );
        emit(active * answer_mask) answer_word(
            verifier_id, source_index_0, source_index_1, value,
        );
        emit(row_mask * use_count) wire(circuit_id, node_id, value, 0, 0, 0);

        return value;
    }
}

pub use component::air::{Component, Eval};

/// Construct the generated DEEP boundary evaluator for the selected proof kind.
#[allow(clippy::too_many_arguments)]
pub fn eval_for_proof_kind(
    log_size: u32,
    proof_kind: ProofKind,
    verifier_input_relations: &VerifierInputRelations,
    trace_relations: &TraceMerkleRelations,
    randomness_relations: &VerifierRandomnessRelations,
    query_relations: &QueryPositionRelations,
    deep_relations: &PcsDeepRelations,
    circuit_relations: &RecursionRelations,
) -> Eval {
    Eval {
        log_size,
        segment_active: BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        binary_active: BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode)),
        sampled_value_kind: BaseField::from(VerifierInputKind::SampledValue.as_u32()),
        oods_point_kind: BaseField::from(VerifierRandomnessKind::OodsPoint.as_u32()),
        deep_randomness_kind: BaseField::from(VerifierRandomnessKind::DeepRandomness.as_u32()),
        deep_position_kind: BaseField::from(QueryPositionKind::Deep.as_u32()),
        relations: PcsDeepInputComponentRelations::new(
            verifier_input_relations,
            trace_relations,
            randomness_relations,
            query_relations,
            deep_relations,
            circuit_relations,
        ),
    }
}

/// Generate semantic source consumers, answer producers, and circuit wires.
#[allow(clippy::too_many_arguments)]
pub fn gen_interaction_trace(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    preprocessed: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    proof_kind: ProofKind,
    verifier_input_relations: &VerifierInputRelations,
    trace_relations: &TraceMerkleRelations,
    randomness_relations: &VerifierRandomnessRelations,
    query_relations: &QueryPositionRelations,
    deep_relations: &PcsDeepRelations,
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
        BaseField::from(VerifierInputKind::SampledValue.as_u32()),
        BaseField::from(VerifierRandomnessKind::OodsPoint.as_u32()),
        BaseField::from(VerifierRandomnessKind::DeepRandomness.as_u32()),
        BaseField::from(QueryPositionKind::Deep.as_u32()),
        &PcsDeepInputComponentRelations::new(
            verifier_input_relations,
            trace_relations,
            randomness_relations,
            query_relations,
            deep_relations,
            circuit_relations,
        ),
    )
}

/// Materializes every lane after checking fixed circuit and mode assignments.
pub fn push_pcs_deep_inputs(
    table: &mut PcsDeepInputTable,
    preprocessed: &PcsDeepInputPreprocessed,
    references: [PcsDeepCircuitLane<'_>; 3],
    witnesses: [PcsDeepCircuitLane<'_>; 3],
    proof_kind: ProofKind,
) -> Result<(), PcsDeepInputError> {
    validate_lane_order(&references)?;
    validate_lane_order(&witnesses)?;
    for (reference, witness) in references.iter().zip(witnesses.iter()) {
        if reference.verifier_id != witness.verifier_id
            || reference.circuit_id != witness.circuit_id
            || reference.circuit.profile() != witness.circuit.profile()
            || reference.circuit.input_bindings() != witness.circuit.input_bindings()
            || reference.circuit.circuit().outputs() != witness.circuit.circuit().outputs()
        {
            return Err(PcsDeepInputError::InputLayoutMismatch {
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
        return Err(PcsDeepInputError::PreprocessedInputCountMismatch);
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
            return Err(PcsDeepInputError::PreprocessedCoordinateMismatch {
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
            return Err(PcsDeepInputError::InputCoordinateMismatch {
                verifier_id: row.verifier_id,
                node_id: row.node_id,
            });
        }
        let node_index =
            usize::try_from(row.node_id).map_err(|_| PcsDeepInputError::NodeIdDoesNotFitUsize {
                node_id: row.node_id,
            })?;
        let arena = witness.circuit.circuit().arena();
        let node = arena
            .nodes
            .get(node_index)
            .ok_or(PcsDeepInputError::NodeMissing {
                node_id: row.node_id,
            })?;
        if node.op != Op::Input {
            return Err(PcsDeepInputError::BindingTargetsNonInput {
                node_id: row.node_id,
            });
        }
        let limbs = node.value.to_m31_array();
        if limbs[1..].iter().any(|limb| limb.0 != 0) {
            return Err(PcsDeepInputError::InputIsNotBaseField {
                node_id: row.node_id,
            });
        }
        let active = verifier_is_active(row.verifier_id, proof_kind)?;
        let expected = if row.source == PcsDeepInputSource::ActiveSelector {
            u32::from(active)
        } else if active {
            limbs[0].0
        } else {
            0
        };
        if limbs[0].0 != expected {
            return Err(PcsDeepInputError::InactiveInputIsNonZero {
                verifier_id: row.verifier_id,
                node_id: row.node_id,
            });
        }
        table.push(expected);
    }
    Ok(())
}

fn verifier_is_active(verifier_id: u32, proof_kind: ProofKind) -> Result<bool, PcsDeepInputError> {
    match verifier_id {
        SEGMENT_VERIFIER_ID => Ok(proof_kind == ProofKind::SegmentLeaf),
        LEFT_RECURSION_VERIFIER_ID | RIGHT_RECURSION_VERIFIER_ID => {
            Ok(proof_kind == ProofKind::BinaryNode)
        }
        _ => Err(PcsDeepInputError::UnknownVerifierId { verifier_id }),
    }
}

/// Invalid lane layout, source coordinate, or mode assignment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PcsDeepInputError {
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
        source: PcsDeepInputSource,
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

impl fmt::Display for PcsDeepInputError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for PcsDeepInputError {}

#[cfg(test)]
mod tests {
    use num_traits::Zero;
    use rstest::rstest;
    use stwo::core::circle::CirclePointIndex;
    use stwo::core::fields::qm31::SecureField;
    use stwo::core::pcs::TreeVec;
    use stwo_constraint_framework::{FrameworkEval, assert_constraints_on_polys};

    use super::*;
    use crate::pcs_deep_circuit::{
        PcsDeepProfile, PcsDeepWitness, build_pcs_deep_circuit, build_pcs_deep_reference,
    };

    const CIRCUIT_IDS: [u32; 3] = [101, 102, 103];

    struct CircuitSet {
        segment: PcsDeepCircuit,
        left: PcsDeepCircuit,
        right: PcsDeepCircuit,
    }

    impl CircuitSet {
        fn lanes(&self) -> [PcsDeepCircuitLane<'_>; 3] {
            [
                PcsDeepCircuitLane {
                    verifier_id: SEGMENT_VERIFIER_ID,
                    circuit_id: CIRCUIT_IDS[0],
                    circuit: &self.segment,
                },
                PcsDeepCircuitLane {
                    verifier_id: LEFT_RECURSION_VERIFIER_ID,
                    circuit_id: CIRCUIT_IDS[1],
                    circuit: &self.left,
                },
                PcsDeepCircuitLane {
                    verifier_id: RIGHT_RECURSION_VERIFIER_ID,
                    circuit_id: CIRCUIT_IDS[2],
                    circuit: &self.right,
                },
            ]
        }
    }

    fn profile() -> PcsDeepProfile {
        PcsDeepProfile::new(
            vec![vec![4]],
            vec![vec![vec![CirclePointIndex::zero()]]],
            5,
            1,
        )
        .expect("fixture DEEP profile is valid")
    }

    fn inactive_set(profile: &PcsDeepProfile) -> CircuitSet {
        CircuitSet {
            segment: build_pcs_deep_reference(profile).expect("segment reference is valid"),
            left: build_pcs_deep_reference(profile).expect("left reference is valid"),
            right: build_pcs_deep_reference(profile).expect("right reference is valid"),
        }
    }

    fn active_circuit(profile: &PcsDeepProfile) -> PcsDeepCircuit {
        let sampled = [SecureField::zero()];
        let queried = [BaseField::zero()];
        let queries = [M31Word::from(3_u16)];
        let answers = [SecureField::zero()];
        build_pcs_deep_circuit(
            profile,
            PcsDeepWitness {
                active: true,
                sampled_values: &sampled,
                queried_values: &queried,
                oods_seed: [17_u32, 29, 43, 71]
                    .map(|word| M31Word::try_from(word).expect("fixture word is canonical")),
                deep_randomness: [
                    M31Word::from(1_u16),
                    M31Word::ZERO,
                    M31Word::ZERO,
                    M31Word::ZERO,
                ],
                raw_queries: &queries,
                answers: &answers,
            },
        )
        .expect("zero quotient defines a valid active circuit")
    }

    fn witness_set(profile: &PcsDeepProfile, kind: ProofKind) -> CircuitSet {
        CircuitSet {
            segment: if kind == ProofKind::SegmentLeaf {
                active_circuit(profile)
            } else {
                build_pcs_deep_reference(profile).expect("segment reference is valid")
            },
            left: if kind == ProofKind::BinaryNode {
                active_circuit(profile)
            } else {
                build_pcs_deep_reference(profile).expect("left reference is valid")
            },
            right: if kind == ProofKind::BinaryNode {
                active_circuit(profile)
            } else {
                build_pcs_deep_reference(profile).expect("right reference is valid")
            },
        }
    }

    fn assert_constraints(kind: ProofKind) {
        let profile = profile();
        let references = inactive_set(&profile);
        let witnesses = witness_set(&profile, kind);
        let preprocessing = PcsDeepInputPreprocessed::new(references.lanes())
            .expect("fixture references own every input");
        let mut table = PcsDeepInputTable::new();
        push_pcs_deep_inputs(
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
        let trace_relations = TraceMerkleRelations::dummy();
        let randomness_relations = VerifierRandomnessRelations::dummy();
        let query_relations = QueryPositionRelations::dummy();
        let deep_relations = PcsDeepRelations::dummy();
        let circuit_relations = RecursionRelations::dummy();
        let (interaction, claimed_sum) = gen_interaction_trace(
            &trace,
            &preprocessed,
            kind,
            &verifier_input_relations,
            &trace_relations,
            &randomness_relations,
            &query_relations,
            &deep_relations,
            &circuit_relations,
        );
        let traces = TreeVec::new(vec![preprocessed, trace, interaction]);
        let polys = traces.map_cols(|column| column.interpolate());
        let eval = eval_for_proof_kind(
            preprocessing.log_size(),
            kind,
            &verifier_input_relations,
            &trace_relations,
            &randomness_relations,
            &query_relations,
            &deep_relations,
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
    fn every_universal_mode_satisfies_deep_input_constraints(#[case] kind: ProofKind) {
        assert_constraints(kind);
    }

    #[test]
    fn preprocessing_owns_every_tracked_input_once() {
        let profile = profile();
        let references = inactive_set(&profile);
        let preprocessing = PcsDeepInputPreprocessed::new(references.lanes())
            .expect("fixture references own every input");
        assert_eq!(
            preprocessing.input_count(),
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
        let preprocessing = PcsDeepInputPreprocessed::new(references.lanes())
            .expect("fixture references own every input");
        let result = push_pcs_deep_inputs(
            &mut PcsDeepInputTable::new(),
            &preprocessing,
            references.lanes(),
            witnesses.lanes(),
            ProofKind::EmptyLeaf,
        );
        assert!(matches!(
            result,
            Err(PcsDeepInputError::InactiveInputIsNonZero {
                verifier_id: SEGMENT_VERIFIER_ID,
                ..
            })
        ));
    }

    #[test]
    fn answer_word_sources_are_typed_by_query_and_limb() {
        let profile = profile();
        let references = inactive_set(&profile);
        let preprocessing = PcsDeepInputPreprocessed::new(references.lanes())
            .expect("fixture references own every input");
        assert_eq!(
            preprocessing
                .rows
                .iter()
                .filter(|row| matches!(row.source, PcsDeepInputSource::AnswerWord { .. }))
                .count(),
            3 * SECURE_WORD_COUNT
        );
    }
}
