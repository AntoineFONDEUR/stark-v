//! AIR boundary from scoped statement words to the universal semantics circuit.
//!
//! Every arithmetic-circuit input has one preprocessed node id and use count.
//! Statement inputs consume their exact scoped word tuple, raw integer words
//! are decomposed into two bytes and checked by the shared `(8, 8)` lookup,
//! and all inputs emit their required circuit-wire multiplicity. Each mode
//! supplies only its active statement scopes and private witnesses.

use core::fmt;

use air::digest::M31Word;
use prover::relations::Relations;
use simd::AlignedVec;
use stwo::core::ColumnVec;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::QM31;
use stwo::core::poly::circle::CanonicCoset;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::m31::PackedM31;
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, RelationEntry,
};
use stwo_macros::define_component_tables;

use crate::circuit::use_counts_for_outputs;

use super::statement::canonical_layout;
use super::statement_input_air::StatementInputRelations;
use super::statement_semantics_circuit::{
    ProofKindSet, StatementCircuitInputSource, StatementSemanticsCircuit,
};
use super::wire::ProofKind;

const MIN_LOG_SIZE: u32 = 4;
const MAX_LOG_SIZE: u32 = 30;
const U16_BYTE_BASE: u32 = 1 << 8;

const ROW_MASK_COLUMN: usize = 0;
const STATEMENT_MASK_COLUMN: usize = 1;
const SELECTOR_MASK_COLUMN: usize = 2;
const PRIVATE_MASK_COLUMN: usize = 3;
const INTEGER_MASK_COLUMN: usize = 4;
const SEGMENT_ACTIVE_COLUMN: usize = 5;
const BINARY_ACTIVE_COLUMN: usize = 6;
const EMPTY_ACTIVE_COLUMN: usize = 7;
const CIRCUIT_ID_COLUMN: usize = 8;
const NODE_ID_COLUMN: usize = 9;
const USE_COUNT_COLUMN: usize = 10;
const STATEMENT_SCOPE_COLUMN: usize = 11;
const WORD_INDEX_COLUMN: usize = 12;
const PREPROCESSED_COLUMN_COUNT: usize = 13;

const PREPROCESSED_COLUMN_IDS: [&str; PREPROCESSED_COLUMN_COUNT] = [
    "recursion_statement_semantics_input_row_mask",
    "recursion_statement_semantics_input_statement_mask",
    "recursion_statement_semantics_input_selector_mask",
    "recursion_statement_semantics_input_private_mask",
    "recursion_statement_semantics_input_integer_mask",
    "recursion_statement_semantics_input_segment_active",
    "recursion_statement_semantics_input_binary_active",
    "recursion_statement_semantics_input_empty_active",
    "recursion_statement_semantics_input_circuit_id",
    "recursion_statement_semantics_input_node_id",
    "recursion_statement_semantics_input_use_count",
    "recursion_statement_semantics_input_scope",
    "recursion_statement_semantics_input_word_index",
];

define_component_tables! {
    statement_semantics_input: {
        committed: { value, low_byte, high_byte },
        constraints: {},
    },
}

use prover_columns::StatementSemanticsInputColumns;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum InputSource {
    Statement,
    Selector,
    Private,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PreprocessedRow {
    source: InputSource,
    integer: bool,
    active_kinds: ProofKindSet,
    circuit_id: u32,
    node_id: u32,
    use_count: u32,
    statement_scope: u32,
    word_index: u32,
}

/// Fixed input-node ownership for one universal statement circuit id.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StatementSemanticsInputPreprocessed {
    log_size: u32,
    rows: Vec<PreprocessedRow>,
}

impl StatementSemanticsInputPreprocessed {
    pub fn new(
        reference: &StatementSemanticsCircuit,
        circuit_id: u32,
    ) -> Result<Self, StatementSemanticsInputError> {
        M31Word::try_from(circuit_id)
            .map_err(|_| StatementSemanticsInputError::CircuitIdNotCanonical { circuit_id })?;
        let arena = reference.circuit().arena();
        let uses = use_counts_for_outputs(&arena, reference.circuit().outputs());
        let mut rows = Vec::with_capacity(reference.input_bindings().len());
        for binding in reference.input_bindings() {
            let node_id = usize::try_from(binding.node_id).map_err(|_| {
                StatementSemanticsInputError::NodeIdDoesNotFitUsize {
                    node_id: binding.node_id,
                }
            })?;
            let use_count =
                *uses
                    .get(node_id)
                    .ok_or(StatementSemanticsInputError::NodeMissing {
                        node_id: binding.node_id,
                    })?;
            M31Word::try_from(use_count).map_err(|_| {
                StatementSemanticsInputError::UseCountNotCanonical {
                    node_id: binding.node_id,
                    use_count,
                }
            })?;
            let (source, active_kinds, statement_scope, word_index, integer) = match binding.source
            {
                StatementCircuitInputSource::StatementWord {
                    scope,
                    index,
                    active_kinds,
                } => {
                    let index_usize = usize::try_from(index).map_err(|_| {
                        StatementSemanticsInputError::WordIndexDoesNotFitUsize { word_index: index }
                    })?;
                    (
                        InputSource::Statement,
                        active_kinds,
                        scope,
                        index,
                        canonical_layout::is_integer_word(index_usize),
                    )
                }
                StatementCircuitInputSource::ProofSelector { kind } => {
                    (InputSource::Selector, kind_set(kind), 0, 0, false)
                }
                StatementCircuitInputSource::PrivateWitness { active_kinds } => {
                    (InputSource::Private, active_kinds, 0, 0, false)
                }
            };
            rows.push(PreprocessedRow {
                source,
                integer,
                active_kinds,
                circuit_id,
                node_id: binding.node_id,
                use_count,
                statement_scope,
                word_index,
            });
        }
        drop(arena);

        let padded_rows = rows
            .len()
            .checked_next_power_of_two()
            .ok_or(StatementSemanticsInputError::RowCountOverflow)?
            .max(1 << MIN_LOG_SIZE);
        let log_size = padded_rows.ilog2();
        if log_size > MAX_LOG_SIZE {
            return Err(StatementSemanticsInputError::LogSizeOutOfRange { log_size });
        }
        Ok(Self { log_size, rows })
    }

    pub const fn log_size(&self) -> u32 {
        self.log_size
    }

    pub fn input_count(&self) -> usize {
        self.rows.len()
    }

    pub fn active_statement_count(&self, kind: ProofKind) -> usize {
        self.rows
            .iter()
            .filter(|row| row.source == InputSource::Statement && row.active_kinds.contains(kind))
            .count()
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
            columns[STATEMENT_MASK_COLUMN][index] = u32::from(row.source == InputSource::Statement);
            columns[SELECTOR_MASK_COLUMN][index] = u32::from(row.source == InputSource::Selector);
            columns[PRIVATE_MASK_COLUMN][index] = u32::from(row.source == InputSource::Private);
            columns[INTEGER_MASK_COLUMN][index] = u32::from(row.integer);
            let [segment, binary, empty] = row.active_kinds.selectors();
            columns[SEGMENT_ACTIVE_COLUMN][index] = u32::from(segment);
            columns[BINARY_ACTIVE_COLUMN][index] = u32::from(binary);
            columns[EMPTY_ACTIVE_COLUMN][index] = u32::from(empty);
            columns[CIRCUIT_ID_COLUMN][index] = row.circuit_id;
            columns[NODE_ID_COLUMN][index] = row.node_id;
            columns[USE_COUNT_COLUMN][index] = row.use_count;
            columns[STATEMENT_SCOPE_COLUMN][index] = row.statement_scope;
            columns[WORD_INDEX_COLUMN][index] = row.word_index;
        }
        let domain = CanonicCoset::new(self.log_size).circle_domain();
        columns
            .into_iter()
            .map(|column| CircleEvaluation::new(domain, BaseColumn::from(column)))
            .collect()
    }
}

pub type Component = FrameworkComponent<Eval>;

#[derive(Clone)]
pub struct Eval {
    pub log_size: u32,
    pub proof_kind: ProofKind,
    pub statement_relations: StatementInputRelations,
    pub circuit_relations: crate::relations::RecursionRelations,
    pub vm_relations: Relations,
}

impl FrameworkEval for Eval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let cols = StatementSemanticsInputColumns::from_eval(&mut eval);
        let ids = StatementSemanticsInputPreprocessed::column_ids();
        let row_mask = eval.get_preprocessed_column(ids[ROW_MASK_COLUMN].clone());
        let statement_mask = eval.get_preprocessed_column(ids[STATEMENT_MASK_COLUMN].clone());
        let selector_mask = eval.get_preprocessed_column(ids[SELECTOR_MASK_COLUMN].clone());
        let private_mask = eval.get_preprocessed_column(ids[PRIVATE_MASK_COLUMN].clone());
        let integer_mask = eval.get_preprocessed_column(ids[INTEGER_MASK_COLUMN].clone());
        let segment_active = eval.get_preprocessed_column(ids[SEGMENT_ACTIVE_COLUMN].clone());
        let binary_active = eval.get_preprocessed_column(ids[BINARY_ACTIVE_COLUMN].clone());
        let empty_active = eval.get_preprocessed_column(ids[EMPTY_ACTIVE_COLUMN].clone());
        let circuit_id = eval.get_preprocessed_column(ids[CIRCUIT_ID_COLUMN].clone());
        let node_id = eval.get_preprocessed_column(ids[NODE_ID_COLUMN].clone());
        let use_count = eval.get_preprocessed_column(ids[USE_COUNT_COLUMN].clone());
        let statement_scope = eval.get_preprocessed_column(ids[STATEMENT_SCOPE_COLUMN].clone());
        let word_index = eval.get_preprocessed_column(ids[WORD_INDEX_COLUMN].clone());
        eval.add_constraint(cols.enabler.clone() - row_mask.clone());

        let segment = BaseField::from(u32::from(self.proof_kind == ProofKind::SegmentLeaf));
        let binary = BaseField::from(u32::from(self.proof_kind == ProofKind::BinaryNode));
        let empty = BaseField::from(u32::from(self.proof_kind == ProofKind::EmptyLeaf));
        let one = E::F::from(BaseField::from(1));
        let active = segment_active * segment + binary_active * binary + empty_active * empty;
        let active_statement = statement_mask.clone() * active.clone();
        let active_integer = active_statement.clone() * integer_mask;
        let witness_input = statement_mask + private_mask;
        eval.add_constraint(witness_input * (one.clone() - active.clone()) * cols.value.clone());
        eval.add_constraint(selector_mask * (cols.value.clone() - active));
        eval.add_constraint(
            active_integer.clone()
                * (cols.value.clone()
                    - cols.low_byte.clone()
                    - cols.high_byte.clone() * BaseField::from(U16_BYTE_BASE)),
        );
        eval.add_constraint((one.clone() - active_integer.clone()) * cols.low_byte.clone());
        eval.add_constraint((one - active_integer.clone()) * cols.high_byte.clone());

        eval.add_to_relation(RelationEntry::new(
            &self.statement_relations.statement_word,
            -E::EF::from(active_statement),
            &[statement_scope, word_index, cols.value.clone()],
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
        eval.add_to_relation(RelationEntry::new(
            &self.vm_relations.range_check_8_8,
            -E::EF::from(active_integer),
            &[cols.low_byte, cols.high_byte],
        ));

        eval.finalize_logup_in_pairs();
        eval
    }
}

/// Generates statement, circuit-wire, and byte-range interaction fractions.
pub fn gen_interaction_trace(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    preprocessed: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    proof_kind: ProofKind,
    statement_relations: &StatementInputRelations,
    circuit_relations: &crate::relations::RecursionRelations,
    vm_relations: &Relations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    let cols = StatementSemanticsInputColumns::from_iter(
        trace.iter().map(|evaluation| &evaluation.values.data),
    );
    let pp = preprocessed
        .iter()
        .map(|column| &column.values.data)
        .collect::<Vec<_>>();
    let simd_size = cols.enabler.len();
    let log_size = trace[0].domain.log_size();
    let segment = BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf));
    let binary = BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode));
    let empty = BaseField::from(u32::from(proof_kind == ProofKind::EmptyLeaf));
    let active = (0..simd_size)
        .map(|row| {
            pp[SEGMENT_ACTIVE_COLUMN][row] * segment
                + pp[BINARY_ACTIVE_COLUMN][row] * binary
                + pp[EMPTY_ACTIVE_COLUMN][row] * empty
        })
        .collect::<Vec<_>>();
    let active_statement = (0..simd_size)
        .map(|row| PackedQM31::from(pp[STATEMENT_MASK_COLUMN][row] * active[row]))
        .collect::<Vec<_>>();
    let negative_statement = active_statement
        .iter()
        .map(|value| -*value)
        .collect::<Vec<_>>();
    let wire_multiplicity = (0..simd_size)
        .map(|row| PackedQM31::from(pp[ROW_MASK_COLUMN][row] * pp[USE_COUNT_COLUMN][row]))
        .collect::<Vec<_>>();
    let negative_integer = (0..simd_size)
        .map(|row| -active_statement[row] * PackedQM31::from(pp[INTEGER_MASK_COLUMN][row]))
        .collect::<Vec<_>>();
    let zeros = vec![PackedM31::broadcast(BaseField::from(0)); simd_size];

    let statement_denom = combine!(
        statement_relations.statement_word,
        [
            pp[STATEMENT_SCOPE_COLUMN],
            pp[WORD_INDEX_COLUMN],
            cols.value
        ]
    );
    let wire_denom = combine!(
        circuit_relations.wire,
        [
            pp[CIRCUIT_ID_COLUMN],
            pp[NODE_ID_COLUMN],
            cols.value,
            zeros,
            zeros,
            zeros
        ]
    );
    let range_denom = combine!(
        vm_relations.range_check_8_8,
        [cols.low_byte, cols.high_byte]
    );

    let mut logup_gen = LogupTraceGenerator::new(log_size);
    write_pair!(
        &negative_statement,
        &statement_denom,
        &wire_multiplicity,
        &wire_denom,
        logup_gen
    );
    write_col!(&negative_integer, &range_denom, logup_gen);
    logup_gen.finalize_last()
}

/// Registers the byte-pair consumers in the standard VM range table.
pub fn register_range_check_multiplicities(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    preprocessed: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    proof_kind: ProofKind,
    counters: &mut prover::relations::Counters,
) {
    let cols = StatementSemanticsInputColumns::from_iter(
        trace.iter().map(|evaluation| &evaluation.values.data),
    );
    let pp = preprocessed
        .iter()
        .map(|column| &column.values.data)
        .collect::<Vec<_>>();
    let simd_size = cols.enabler.len();
    let segment = BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf));
    let binary = BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode));
    let empty = BaseField::from(u32::from(proof_kind == ProofKind::EmptyLeaf));
    let multiplicities = (0..simd_size)
        .map(|row| {
            let active = pp[SEGMENT_ACTIVE_COLUMN][row] * segment
                + pp[BINARY_ACTIVE_COLUMN][row] * binary
                + pp[EMPTY_ACTIVE_COLUMN][row] * empty;
            -(pp[STATEMENT_MASK_COLUMN][row] * pp[INTEGER_MASK_COLUMN][row] * active)
        })
        .collect::<Vec<_>>();
    counters.range_check_8_8.register_many(
        &multiplicities,
        &[cols.low_byte.as_slice(), cols.high_byte.as_slice()],
    );
}

/// Generates exact circuit input values and their byte decompositions.
pub fn push_statement_semantics_inputs(
    table: &mut StatementSemanticsInputTable,
    preprocessed: &StatementSemanticsInputPreprocessed,
    circuit: &StatementSemanticsCircuit,
    proof_kind: ProofKind,
) -> Result<(), StatementSemanticsInputError> {
    if circuit.input_bindings().len() != preprocessed.rows.len() {
        return Err(StatementSemanticsInputError::InputCountMismatch {
            expected: preprocessed.rows.len(),
            actual: circuit.input_bindings().len(),
        });
    }
    let arena = circuit.circuit().arena();
    for (row, binding) in preprocessed.rows.iter().zip(circuit.input_bindings()) {
        if row.node_id != binding.node_id
            || row_source(binding.source) != row.source
            || source_active_kinds(binding.source) != row.active_kinds
        {
            return Err(StatementSemanticsInputError::InputLayoutMismatch {
                expected_node: row.node_id,
                actual_node: binding.node_id,
            });
        }
        if let StatementCircuitInputSource::StatementWord { scope, index, .. } = binding.source {
            if row.statement_scope != scope || row.word_index != index {
                return Err(StatementSemanticsInputError::StatementCoordinateMismatch {
                    node_id: row.node_id,
                });
            }
        }
        let node_id = usize::try_from(row.node_id).map_err(|_| {
            StatementSemanticsInputError::NodeIdDoesNotFitUsize {
                node_id: row.node_id,
            }
        })?;
        let value = arena
            .nodes
            .get(node_id)
            .ok_or(StatementSemanticsInputError::NodeMissing {
                node_id: row.node_id,
            })?
            .value
            .to_m31_array();
        if value[1..].iter().any(|limb| limb.0 != 0) {
            return Err(StatementSemanticsInputError::InputIsNotBaseField {
                node_id: row.node_id,
            });
        }
        let value = value[0].0;
        let active_integer = row.active_kinds.contains(proof_kind)
            && row.source == InputSource::Statement
            && row.integer;
        let (low_byte, high_byte) = if active_integer {
            let value = u16::try_from(value).map_err(|_| {
                StatementSemanticsInputError::IntegerWordOutOfRange {
                    node_id: row.node_id,
                    value,
                }
            })?;
            let [low_byte, high_byte] = value.to_le_bytes();
            (u32::from(low_byte), u32::from(high_byte))
        } else {
            (0, 0)
        };
        table.push(value, low_byte, high_byte);
    }
    Ok(())
}

fn row_source(source: StatementCircuitInputSource) -> InputSource {
    match source {
        StatementCircuitInputSource::StatementWord { .. } => InputSource::Statement,
        StatementCircuitInputSource::ProofSelector { .. } => InputSource::Selector,
        StatementCircuitInputSource::PrivateWitness { .. } => InputSource::Private,
    }
}

fn source_active_kinds(source: StatementCircuitInputSource) -> ProofKindSet {
    match source {
        StatementCircuitInputSource::StatementWord { active_kinds, .. }
        | StatementCircuitInputSource::PrivateWitness { active_kinds } => active_kinds,
        StatementCircuitInputSource::ProofSelector { kind } => kind_set(kind),
    }
}

const fn kind_set(kind: ProofKind) -> ProofKindSet {
    match kind {
        ProofKind::SegmentLeaf => ProofKindSet::SEGMENT,
        ProofKind::BinaryNode => ProofKindSet::BINARY,
        ProofKind::EmptyLeaf => ProofKindSet::EMPTY,
    }
}

/// Invalid statement-circuit preprocessing or input generation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StatementSemanticsInputError {
    CircuitIdNotCanonical {
        circuit_id: u32,
    },
    RowCountOverflow,
    LogSizeOutOfRange {
        log_size: u32,
    },
    NodeIdDoesNotFitUsize {
        node_id: u32,
    },
    NodeMissing {
        node_id: u32,
    },
    UseCountNotCanonical {
        node_id: u32,
        use_count: u32,
    },
    WordIndexDoesNotFitUsize {
        word_index: u32,
    },
    InputCountMismatch {
        expected: usize,
        actual: usize,
    },
    InputLayoutMismatch {
        expected_node: u32,
        actual_node: u32,
    },
    StatementCoordinateMismatch {
        node_id: u32,
    },
    InputIsNotBaseField {
        node_id: u32,
    },
    IntegerWordOutOfRange {
        node_id: u32,
        value: u32,
    },
}

impl fmt::Display for StatementSemanticsInputError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::CircuitIdNotCanonical { circuit_id } => {
                write!(
                    formatter,
                    "statement semantics circuit id {circuit_id} is not canonical M31"
                )
            }
            Self::RowCountOverflow => {
                write!(formatter, "statement semantics input row count overflowed")
            }
            Self::LogSizeOutOfRange { log_size } => write!(
                formatter,
                "statement semantics input log size {log_size} exceeds the supported maximum {MAX_LOG_SIZE}"
            ),
            Self::NodeIdDoesNotFitUsize { node_id } => {
                write!(formatter, "circuit node id {node_id} does not fit usize")
            }
            Self::NodeMissing { node_id } => write!(formatter, "circuit has no node {node_id}"),
            Self::UseCountNotCanonical { node_id, use_count } => write!(
                formatter,
                "circuit node {node_id} use count {use_count} is not canonical M31"
            ),
            Self::WordIndexDoesNotFitUsize { word_index } => write!(
                formatter,
                "statement word index {word_index} does not fit usize"
            ),
            Self::InputCountMismatch { expected, actual } => write!(
                formatter,
                "statement circuit has {actual} input bindings, expected {expected}"
            ),
            Self::InputLayoutMismatch {
                expected_node,
                actual_node,
            } => write!(
                formatter,
                "statement circuit input node is {actual_node}, expected {expected_node}"
            ),
            Self::StatementCoordinateMismatch { node_id } => write!(
                formatter,
                "fold circuit statement input {node_id} changed its scope or word index"
            ),
            Self::InputIsNotBaseField { node_id } => {
                write!(
                    formatter,
                    "fold circuit input {node_id} is not a base-field word"
                )
            }
            Self::IntegerWordOutOfRange { node_id, value } => write!(
                formatter,
                "statement circuit integer input {node_id} has non-u16 value {value}"
            ),
        }
    }
}

impl std::error::Error for StatementSemanticsInputError {}

#[cfg(test)]
mod tests {
    use num_traits::Zero;
    use prover::poseidon2_channel::Poseidon2M31Channel;
    use rstest::rstest;
    use stwo::core::channel::Channel;
    use stwo::core::fields::FieldExpOps;
    use stwo::core::fields::m31::M31;
    use stwo::core::pcs::TreeVec;
    use stwo_constraint_framework::{Relation, assert_constraints_on_polys};

    use super::*;
    use crate::relations::RecursionRelations;
    use crate::statement::SPAN_STATEMENT_CANONICAL_WORDS;
    use crate::statement_semantics_circuit::{
        StatementSemanticsCircuitWitness, StatementWords, build_statement_semantics_circuit,
    };

    fn zero_words() -> StatementWords {
        [M31Word::ZERO; SPAN_STATEMENT_CANONICAL_WORDS]
    }

    fn zero_circuit(selected_kind: Option<ProofKind>) -> StatementSemanticsCircuit {
        let segment = zero_words();
        let left = zero_words();
        let right = zero_words();
        let parent = zero_words();
        build_statement_semantics_circuit(StatementSemanticsCircuitWitness {
            segment_selector: selected_kind == Some(ProofKind::SegmentLeaf),
            binary_selector: selected_kind == Some(ProofKind::BinaryNode),
            empty_selector: selected_kind == Some(ProofKind::EmptyLeaf),
            segment: &segment,
            left: &left,
            right: &right,
            parent: &parent,
        })
    }

    fn preprocessing() -> StatementSemanticsInputPreprocessed {
        StatementSemanticsInputPreprocessed::new(&zero_circuit(None), 7)
            .expect("fixture circuit has canonical input ownership")
    }

    fn assert_constraints(kind: ProofKind, tamper: Option<usize>) {
        let preprocessing = preprocessing();
        let circuit = zero_circuit(Some(kind));
        let mut table = StatementSemanticsInputTable::new();
        push_statement_semantics_inputs(&mut table, &preprocessing, &circuit, kind)
            .expect("fixture circuit inputs are generated");
        if let Some(index) = tamper {
            table.value[index] += 1;
        }
        let statement_relations = StatementInputRelations::dummy();
        let circuit_relations = RecursionRelations::dummy();
        let vm_relations = Relations::dummy();
        let preprocessed = preprocessing.gen_columns();
        let trace = table.into_witness();
        let (interaction, claimed_sum) = gen_interaction_trace(
            &trace,
            &preprocessed,
            kind,
            &statement_relations,
            &circuit_relations,
            &vm_relations,
        );
        let traces = TreeVec::new(vec![preprocessed, trace, interaction]);
        let trace_polys = traces.map_cols(|column| column.interpolate());
        let eval = Eval {
            log_size: preprocessing.log_size(),
            proof_kind: kind,
            statement_relations,
            circuit_relations,
            vm_relations,
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

    fn manual_statement_terms(
        kind: ProofKind,
        relations: &StatementInputRelations,
        value: M31,
    ) -> QM31 {
        let mut total = QM31::zero();
        let scopes: &[u32] = match kind {
            ProofKind::SegmentLeaf => &[
                super::super::statement_input_air::SEGMENT_STATEMENT_SCOPE,
                super::super::statement_input_air::PARENT_STATEMENT_SCOPE,
            ],
            ProofKind::BinaryNode => &[
                super::super::statement_input_air::LEFT_STATEMENT_SCOPE,
                super::super::statement_input_air::RIGHT_STATEMENT_SCOPE,
                super::super::statement_input_air::PARENT_STATEMENT_SCOPE,
            ],
            ProofKind::EmptyLeaf => &[super::super::statement_input_air::PARENT_STATEMENT_SCOPE],
        };
        for scope in scopes {
            for index in 0..SPAN_STATEMENT_CANONICAL_WORDS {
                let index = u32::try_from(index).expect("statement word index fits u32");
                let denominator: QM31 =
                    relations
                        .statement_word
                        .combine(&[M31::from(*scope), M31::from(index), value]);
                total += denominator.inverse();
            }
        }
        total
    }

    fn statement_bridge_sum(kind: ProofKind, mut channel: Poseidon2M31Channel) -> QM31 {
        let preprocessing = preprocessing();
        let circuit = zero_circuit(Some(kind));
        let mut table = StatementSemanticsInputTable::new();
        push_statement_semantics_inputs(&mut table, &preprocessing, &circuit, kind)
            .expect("fixture circuit inputs are generated");
        let statement_relations = StatementInputRelations::draw(&mut channel);
        let (_, claimed_sum) = gen_interaction_trace(
            &table.into_witness(),
            &preprocessing.gen_columns(),
            kind,
            &statement_relations,
            &RecursionRelations::dummy(),
            &Relations::dummy(),
        );
        claimed_sum + manual_statement_terms(kind, &statement_relations, M31::from(0))
    }

    #[rstest]
    #[case::segment(ProofKind::SegmentLeaf)]
    #[case::binary(ProofKind::BinaryNode)]
    #[case::empty(ProofKind::EmptyLeaf)]
    fn every_universal_mode_satisfies_semantics_input_constraints(#[case] kind: ProofKind) {
        assert_constraints(kind, None);
    }

    #[rstest]
    #[should_panic]
    fn inactive_statement_selector_must_be_zero() {
        assert_constraints(ProofKind::EmptyLeaf, Some(0));
    }

    #[rstest]
    #[should_panic]
    fn active_integer_value_must_match_its_bytes() {
        let preprocessing = preprocessing();
        let integer_row = preprocessing
            .rows
            .iter()
            .position(|row| {
                row.integer
                    && row.source == InputSource::Statement
                    && row.active_kinds.contains(ProofKind::BinaryNode)
            })
            .expect("statement layout has integer words");
        assert_constraints(ProofKind::BinaryNode, Some(integer_row));
    }

    #[rstest]
    #[case::segment(ProofKind::SegmentLeaf, 2 * SPAN_STATEMENT_CANONICAL_WORDS)]
    #[case::binary(ProofKind::BinaryNode, 3 * SPAN_STATEMENT_CANONICAL_WORDS)]
    #[case::empty(ProofKind::EmptyLeaf, SPAN_STATEMENT_CANONICAL_WORDS)]
    fn each_mode_consumes_exactly_its_statement_scopes(
        #[case] kind: ProofKind,
        #[case] expected: usize,
    ) {
        assert_eq!(preprocessing().active_statement_count(kind), expected);
    }

    #[rstest]
    #[case::segment(ProofKind::SegmentLeaf)]
    #[case::binary(ProofKind::BinaryNode)]
    #[case::empty(ProofKind::EmptyLeaf)]
    fn active_integer_words_register_standard_range_multiplicities(#[case] kind: ProofKind) {
        use stwo::prover::backend::Column;

        let preprocessing = preprocessing();
        let circuit = zero_circuit(Some(kind));
        let mut table = StatementSemanticsInputTable::new();
        push_statement_semantics_inputs(&mut table, &preprocessing, &circuit, kind)
            .expect("fixture circuit inputs are generated");
        let trace = table.into_witness();
        let preprocessed = preprocessing.gen_columns();
        let mut counters = prover::relations::Counters::new();
        register_range_check_multiplicities(&trace, &preprocessed, kind, &mut counters);
        let registered = counters.range_check_8_8.into_trace()[0]
            .values
            .to_cpu()
            .into_iter()
            .fold(M31::zero(), |sum, value| sum + value);
        let expected_count = preprocessing
            .rows
            .iter()
            .filter(|row| {
                row.source == InputSource::Statement
                    && row.integer
                    && row.active_kinds.contains(kind)
            })
            .count();
        let expected_count =
            u32::try_from(expected_count).expect("active integer row count fits u32");
        assert_eq!(registered, -M31::from(expected_count));
    }

    #[rstest]
    #[case::segment(ProofKind::SegmentLeaf)]
    #[case::binary(ProofKind::BinaryNode)]
    #[case::empty(ProofKind::EmptyLeaf)]
    fn statement_scope_tuples_cancel_at_the_circuit_boundary(#[case] kind: ProofKind) {
        let baseline = statement_bridge_sum(kind, Poseidon2M31Channel::default());
        let mut changed = Poseidon2M31Channel::default();
        changed.mix_u32s(&[1]);
        assert_eq!(statement_bridge_sum(kind, changed), baseline);
    }

    #[rstest]
    fn input_generation_rejects_a_non_u16_integer_word() {
        let preprocessing = preprocessing();
        let segment = zero_words();
        let left = zero_words();
        let right = zero_words();
        let mut parent = zero_words();
        parent[canonical_layout::SLOT_HEIGHT] =
            M31Word::try_from(1_u32 << 16).expect("fixture word is canonical M31");
        let circuit = build_statement_semantics_circuit(StatementSemanticsCircuitWitness {
            segment_selector: false,
            binary_selector: true,
            empty_selector: false,
            segment: &segment,
            left: &left,
            right: &right,
            parent: &parent,
        });
        let mut table = StatementSemanticsInputTable::new();
        assert!(matches!(
            push_statement_semantics_inputs(
                &mut table,
                &preprocessing,
                &circuit,
                ProofKind::BinaryNode,
            ),
            Err(StatementSemanticsInputError::IntegerWordOutOfRange { .. })
        ));
    }

    #[rstest]
    fn semantics_input_constraint_profile_stays_cubic() {
        use stwo_constraint_framework::expr::ExprEvaluator;

        let eval = Eval {
            log_size: 4,
            proof_kind: ProofKind::BinaryNode,
            statement_relations: StatementInputRelations::dummy(),
            circuit_relations: RecursionRelations::dummy(),
            vm_relations: Relations::dummy(),
        };
        let degrees = eval
            .evaluate(ExprEvaluator::new())
            .constraint_degree_bounds();
        assert_eq!((degrees.len(), degrees.into_iter().max()), (8, Some(3)));
    }
}
