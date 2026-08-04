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
use stwo::prover::backend::simd::m31::PackedM31;
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, RelationEntry, relation,
};
use stwo_macros::define_component_tables;

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

const PREPROCESSED_COLUMN_IDS: [&str; PREPROCESSED_COLUMN_COUNT] = [
    "recursion_pcs_deep_input_row_mask",
    "recursion_pcs_deep_input_segment_mask",
    "recursion_pcs_deep_input_binary_mask",
    "recursion_pcs_deep_input_sampled_value_mask",
    "recursion_pcs_deep_input_queried_value_mask",
    "recursion_pcs_deep_input_oods_seed_mask",
    "recursion_pcs_deep_input_deep_randomness_mask",
    "recursion_pcs_deep_input_query_bit_mask",
    "recursion_pcs_deep_input_query_position_mask",
    "recursion_pcs_deep_input_answer_mask",
    "recursion_pcs_deep_input_selector_mask",
    "recursion_pcs_deep_input_verifier_id",
    "recursion_pcs_deep_input_circuit_id",
    "recursion_pcs_deep_input_node_id",
    "recursion_pcs_deep_input_use_count",
    "recursion_pcs_deep_input_source_index_0",
    "recursion_pcs_deep_input_source_index_1",
    "recursion_pcs_deep_input_source_index_2",
];

define_component_tables! {
    pcs_deep_input: {
        committed: { value },
        constraints: {},
    },
}

use prover_columns::PcsDeepInputColumns;

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

pub type Component = FrameworkComponent<Eval>;

/// Fixed input ownership constraints for all universal verifier lanes.
#[derive(Clone)]
pub struct Eval {
    pub log_size: u32,
    pub proof_kind: ProofKind,
    pub verifier_input_relations: VerifierInputRelations,
    pub trace_relations: TraceMerkleRelations,
    pub randomness_relations: VerifierRandomnessRelations,
    pub query_relations: QueryPositionRelations,
    pub deep_relations: PcsDeepRelations,
    pub circuit_relations: RecursionRelations,
}

impl FrameworkEval for Eval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let cols = PcsDeepInputColumns::from_eval(&mut eval);
        let ids = PcsDeepInputPreprocessed::column_ids();
        let pp = |eval: &mut E, column: usize| eval.get_preprocessed_column(ids[column].clone());
        let row_mask = pp(&mut eval, ROW_MASK_COLUMN);
        let segment_mask = pp(&mut eval, SEGMENT_MASK_COLUMN);
        let binary_mask = pp(&mut eval, BINARY_MASK_COLUMN);
        let sampled_mask = pp(&mut eval, SAMPLED_VALUE_MASK_COLUMN);
        let queried_mask = pp(&mut eval, QUERIED_VALUE_MASK_COLUMN);
        let oods_mask = pp(&mut eval, OODS_SEED_MASK_COLUMN);
        let randomness_mask = pp(&mut eval, DEEP_RANDOMNESS_MASK_COLUMN);
        let bit_mask = pp(&mut eval, QUERY_BIT_MASK_COLUMN);
        let position_mask = pp(&mut eval, QUERY_POSITION_MASK_COLUMN);
        let answer_mask = pp(&mut eval, ANSWER_MASK_COLUMN);
        let selector_mask = pp(&mut eval, SELECTOR_MASK_COLUMN);
        let verifier_id = pp(&mut eval, VERIFIER_ID_COLUMN);
        let circuit_id = pp(&mut eval, CIRCUIT_ID_COLUMN);
        let node_id = pp(&mut eval, NODE_ID_COLUMN);
        let use_count = pp(&mut eval, USE_COUNT_COLUMN);
        let source_0 = pp(&mut eval, SOURCE_INDEX_0_COLUMN);
        let source_1 = pp(&mut eval, SOURCE_INDEX_1_COLUMN);
        let source_2 = pp(&mut eval, SOURCE_INDEX_2_COLUMN);
        let segment = E::F::from(BaseField::from(u32::from(
            self.proof_kind == ProofKind::SegmentLeaf,
        )));
        let binary = E::F::from(BaseField::from(u32::from(
            self.proof_kind == ProofKind::BinaryNode,
        )));
        let active = segment_mask * segment + binary_mask * binary;
        let one = E::F::from(BaseField::from(1));

        eval.add_constraint(cols.enabler.clone() - row_mask.clone());
        eval.add_constraint(
            (row_mask.clone() - selector_mask.clone())
                * (one - active.clone())
                * cols.value.clone(),
        );
        eval.add_constraint(selector_mask * (cols.value.clone() - active.clone()));

        eval.add_to_relation(RelationEntry::new(
            &self.verifier_input_relations.input_word,
            -E::EF::from(active.clone() * sampled_mask),
            &[
                verifier_id.clone(),
                E::F::from(BaseField::from(VerifierInputKind::SampledValue.as_u32())),
                source_0.clone(),
                source_1.clone(),
                cols.value.clone(),
            ],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.trace_relations.value,
            -E::EF::from(active.clone() * queried_mask),
            &[
                verifier_id.clone(),
                source_0.clone(),
                source_1.clone(),
                source_2.clone(),
                cols.value.clone(),
            ],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.randomness_relations.word,
            -E::EF::from(active.clone() * oods_mask),
            &[
                verifier_id.clone(),
                E::F::from(BaseField::from(VerifierRandomnessKind::OodsPoint.as_u32())),
                source_0.clone(),
                source_1.clone(),
                cols.value.clone(),
            ],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.randomness_relations.word,
            -E::EF::from(active.clone() * randomness_mask),
            &[
                verifier_id.clone(),
                E::F::from(BaseField::from(
                    VerifierRandomnessKind::DeepRandomness.as_u32(),
                )),
                source_0.clone(),
                source_1.clone(),
                cols.value.clone(),
            ],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.query_relations.bit_value,
            -E::EF::from(active.clone() * bit_mask),
            &[
                verifier_id.clone(),
                source_0.clone(),
                source_1.clone(),
                cols.value.clone(),
            ],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.query_relations.position,
            -E::EF::from(active.clone() * position_mask),
            &[
                verifier_id.clone(),
                E::F::from(BaseField::from(QueryPositionKind::Deep.as_u32())),
                E::F::from(BaseField::from(0)),
                source_0.clone(),
                cols.value.clone(),
                E::F::from(BaseField::from(0)),
            ],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.deep_relations.answer_word,
            E::EF::from(active * answer_mask),
            &[verifier_id, source_0, source_1, cols.value.clone()],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.circuit_relations.wire,
            E::EF::from(row_mask * use_count),
            &[
                circuit_id,
                node_id,
                cols.value,
                E::F::from(BaseField::from(0)),
                E::F::from(BaseField::from(0)),
                E::F::from(BaseField::from(0)),
            ],
        ));
        eval.finalize_logup_in_pairs();
        eval
    }
}

/// Generates semantic source consumers, answer producers, and circuit wires.
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
    let cols = PcsDeepInputColumns::from_iter(trace.iter().map(|column| &column.values.data));
    let pp = preprocessed
        .iter()
        .map(|column| &column.values.data)
        .collect::<Vec<_>>();
    let size = cols.enabler.len();
    let segment = BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf));
    let binary = BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode));
    let active = (0..size)
        .map(|row| {
            PackedQM31::from(
                pp[SEGMENT_MASK_COLUMN][row] * segment + pp[BINARY_MASK_COLUMN][row] * binary,
            )
        })
        .collect::<Vec<_>>();
    let negative = |mask: usize| {
        (0..size)
            .map(|row| -active[row] * pp[mask][row])
            .collect::<Vec<_>>()
    };
    let sampled_numerator = negative(SAMPLED_VALUE_MASK_COLUMN);
    let queried_numerator = negative(QUERIED_VALUE_MASK_COLUMN);
    let oods_numerator = negative(OODS_SEED_MASK_COLUMN);
    let randomness_numerator = negative(DEEP_RANDOMNESS_MASK_COLUMN);
    let bit_numerator = negative(QUERY_BIT_MASK_COLUMN);
    let position_numerator = negative(QUERY_POSITION_MASK_COLUMN);
    let answer_numerator = (0..size)
        .map(|row| active[row] * pp[ANSWER_MASK_COLUMN][row])
        .collect::<Vec<_>>();
    let wire_numerator = (0..size)
        .map(|row| PackedQM31::from(pp[ROW_MASK_COLUMN][row] * pp[USE_COUNT_COLUMN][row]))
        .collect::<Vec<_>>();
    let zeros = vec![PackedM31::broadcast(BaseField::from(0)); size];
    let sampled_kind =
        vec![PackedM31::broadcast(BaseField::from(VerifierInputKind::SampledValue.as_u32())); size];
    let oods_kind =
        vec![
            PackedM31::broadcast(BaseField::from(VerifierRandomnessKind::OodsPoint.as_u32()));
            size
        ];
    let randomness_kind = vec![
        PackedM31::broadcast(BaseField::from(
            VerifierRandomnessKind::DeepRandomness.as_u32(),
        ));
        size
    ];
    let deep_kind =
        vec![PackedM31::broadcast(BaseField::from(QueryPositionKind::Deep.as_u32())); size];
    let sampled_denominator = combine!(
        verifier_input_relations.input_word,
        [
            pp[VERIFIER_ID_COLUMN],
            sampled_kind,
            pp[SOURCE_INDEX_0_COLUMN],
            pp[SOURCE_INDEX_1_COLUMN],
            cols.value
        ]
    );
    let queried_denominator = combine!(
        trace_relations.value,
        [
            pp[VERIFIER_ID_COLUMN],
            pp[SOURCE_INDEX_0_COLUMN],
            pp[SOURCE_INDEX_1_COLUMN],
            pp[SOURCE_INDEX_2_COLUMN],
            cols.value
        ]
    );
    let oods_denominator = combine!(
        randomness_relations.word,
        [
            pp[VERIFIER_ID_COLUMN],
            oods_kind,
            &zeros,
            pp[SOURCE_INDEX_1_COLUMN],
            cols.value
        ]
    );
    let randomness_denominator = combine!(
        randomness_relations.word,
        [
            pp[VERIFIER_ID_COLUMN],
            randomness_kind,
            &zeros,
            pp[SOURCE_INDEX_1_COLUMN],
            cols.value
        ]
    );
    let bit_denominator = combine!(
        query_relations.bit_value,
        [
            pp[VERIFIER_ID_COLUMN],
            pp[SOURCE_INDEX_0_COLUMN],
            pp[SOURCE_INDEX_1_COLUMN],
            cols.value
        ]
    );
    let position_denominator = combine!(
        query_relations.position,
        [
            pp[VERIFIER_ID_COLUMN],
            deep_kind,
            &zeros,
            pp[SOURCE_INDEX_0_COLUMN],
            cols.value,
            &zeros
        ]
    );
    let answer_denominator = combine!(
        deep_relations.answer_word,
        [
            pp[VERIFIER_ID_COLUMN],
            pp[SOURCE_INDEX_0_COLUMN],
            pp[SOURCE_INDEX_1_COLUMN],
            cols.value
        ]
    );
    let wire_denominator = combine!(
        circuit_relations.wire,
        [
            pp[CIRCUIT_ID_COLUMN],
            pp[NODE_ID_COLUMN],
            cols.value,
            &zeros,
            &zeros,
            zeros
        ]
    );

    let mut logup = LogupTraceGenerator::new(trace[0].domain.log_size());
    write_pair!(
        &sampled_numerator,
        &sampled_denominator,
        &queried_numerator,
        &queried_denominator,
        logup
    );
    write_pair!(
        &oods_numerator,
        &oods_denominator,
        &randomness_numerator,
        &randomness_denominator,
        logup
    );
    write_pair!(
        &bit_numerator,
        &bit_denominator,
        &position_numerator,
        &position_denominator,
        logup
    );
    write_pair!(
        &answer_numerator,
        &answer_denominator,
        &wire_numerator,
        &wire_denominator,
        logup
    );
    logup.finalize_last()
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
    use stwo_constraint_framework::assert_constraints_on_polys;

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
        let eval = Eval {
            log_size: preprocessing.log_size(),
            proof_kind: kind,
            verifier_input_relations,
            trace_relations,
            randomness_relations,
            query_relations,
            deep_relations,
            circuit_relations,
        };
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
