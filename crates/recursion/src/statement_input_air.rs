//! Statement-word boundary for the recursion verifier.
//!
//! Transcript payloads expose each verified proof's statement as indexed
//! words. This component consumes those verifier-input tuples and re-emits
//! them under segment, left-child, or right-child scopes. The statement
//! semantics AIR consumes those private scopes together with parent words
//! emitted by verifier-computed LogUp terms. No proof-dependent statement
//! value enters preprocessing.

use core::fmt;

use air::digest::M31Word;
use num_traits::Zero;
use simd::AlignedVec;
use stwo::core::ColumnVec;
use stwo::core::channel::Channel;
use stwo::core::fields::FieldExpOps;
use stwo::core::fields::m31::{BaseField, M31};
use stwo::core::fields::qm31::QM31;
use stwo::core::poly::circle::CanonicCoset;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{Relation, relation};

use super::control_air::{
    LEFT_RECURSION_VERIFIER_ID, POSEIDON2_VERIFIER_ID, RIGHT_RECURSION_VERIFIER_ID,
    SEGMENT_VERIFIER_ID,
};
use super::kernel::VerifierStep;
use super::protocol::CanonicalWords;
use super::statement::{SPAN_STATEMENT_CANONICAL_WORDS, SpanStatement};
use super::transcript_binding_air::TranscriptCallPreprocessed;
use super::transcript_layout::TranscriptLayout;
use super::transcript_payload_air::{VerifierInputKind, VerifierInputRelations};
use super::wire::ProofKind;

const MIN_LOG_SIZE: u32 = 4;
const MAX_LOG_SIZE: u32 = 30;

const ROW_MASK_COLUMN: usize = 0;
const SEGMENT_MASK_COLUMN: usize = 1;
const BINARY_MASK_COLUMN: usize = 2;
const VERIFIER_ID_COLUMN: usize = 3;
const STATEMENT_SCOPE_COLUMN: usize = 4;
const WORD_INDEX_COLUMN: usize = 5;
const STATEMENT_USE_COUNT_COLUMN: usize = 6;
const VM_CLAIM_MASK_COLUMN: usize = 7;
const PREPROCESSED_COLUMN_COUNT: usize = 8;

pub const SEGMENT_STATEMENT_SCOPE: u32 = 0;
pub const LEFT_STATEMENT_SCOPE: u32 = 1;
pub const RIGHT_STATEMENT_SCOPE: u32 = 2;
pub const PARENT_STATEMENT_SCOPE: u32 = 3;
pub const VM_CLAIM_STATEMENT_SCOPE: u32 = 4;

// One scoped canonical statement word: scope, word index, and value.
relation!(StatementWordRelation, 3);

/// Relations connecting transcript inputs, statement semantics, and public words.
#[derive(Clone)]
pub struct StatementInputRelations {
    pub statement_word: StatementWordRelation,
}

impl StatementInputRelations {
    pub fn dummy() -> Self {
        Self {
            statement_word: StatementWordRelation::dummy(),
        }
    }

    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            statement_word: StatementWordRelation::draw(channel),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PreprocessedRow {
    segment_mask: u32,
    binary_mask: u32,
    verifier_id: u32,
    statement_scope: u32,
    word_index: u32,
    statement_use_count: u32,
    vm_claim_mask: u32,
}

/// Fixed statement-word routing for two segment lanes and two recursion lanes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StatementInputPreprocessed {
    log_size: u32,
    rows: Vec<PreprocessedRow>,
}

impl StatementInputPreprocessed {
    pub fn new(calls: &TranscriptCallPreprocessed) -> Result<Self, StatementInputError> {
        validate_statement_layout("VM", calls.vm_layout())?;
        validate_statement_layout("Poseidon2", calls.poseidon2_layout())?;
        validate_statement_layout("recursion", calls.recursion_layout())?;

        let row_count = SPAN_STATEMENT_CANONICAL_WORDS
            .checked_mul(4)
            .ok_or(StatementInputError::RowCountOverflow)?;
        let padded_rows = row_count
            .checked_next_power_of_two()
            .ok_or(StatementInputError::RowCountOverflow)?
            .max(1 << MIN_LOG_SIZE);
        let log_size = padded_rows.ilog2();
        if log_size > MAX_LOG_SIZE {
            return Err(StatementInputError::LogSizeOutOfRange { log_size });
        }

        let mut rows = Vec::with_capacity(row_count);
        append_lane_rows(
            &mut rows,
            SEGMENT_VERIFIER_ID,
            SEGMENT_STATEMENT_SCOPE,
            1,
            0,
            1,
            1,
        )?;
        append_lane_rows(
            &mut rows,
            POSEIDON2_VERIFIER_ID,
            SEGMENT_STATEMENT_SCOPE,
            1,
            0,
            0,
            0,
        )?;
        append_lane_rows(
            &mut rows,
            LEFT_RECURSION_VERIFIER_ID,
            LEFT_STATEMENT_SCOPE,
            0,
            1,
            2,
            0,
        )?;
        append_lane_rows(
            &mut rows,
            RIGHT_RECURSION_VERIFIER_ID,
            RIGHT_STATEMENT_SCOPE,
            0,
            1,
            2,
            0,
        )?;
        Ok(Self { log_size, rows })
    }

    pub const fn log_size(&self) -> u32 {
        self.log_size
    }

    pub const fn active_word_count(kind: ProofKind) -> usize {
        match kind {
            ProofKind::SegmentLeaf => 2 * SPAN_STATEMENT_CANONICAL_WORDS,
            ProofKind::BinaryNode => 2 * SPAN_STATEMENT_CANONICAL_WORDS,
            ProofKind::EmptyLeaf => 0,
        }
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
            columns[BINARY_MASK_COLUMN][index] = row.binary_mask;
            columns[VERIFIER_ID_COLUMN][index] = row.verifier_id;
            columns[STATEMENT_SCOPE_COLUMN][index] = row.statement_scope;
            columns[WORD_INDEX_COLUMN][index] = row.word_index;
            columns[STATEMENT_USE_COUNT_COLUMN][index] = row.statement_use_count;
            columns[VM_CLAIM_MASK_COLUMN][index] = row.vm_claim_mask;
        }
        let domain = CanonicCoset::new(self.log_size).circle_domain();
        columns
            .into_iter()
            .map(|column| CircleEvaluation::new(domain, BaseColumn::from(column)))
            .collect()
    }
}

fn validate_statement_layout(
    schema: &'static str,
    layout: &TranscriptLayout,
) -> Result<(), StatementInputError> {
    let mut operations = layout
        .operations()
        .iter()
        .filter(|operation| operation.step() == VerifierStep::BindStatement);
    let operation = operations
        .next()
        .ok_or(StatementInputError::StatementBindingMissing { schema })?;
    if operations.next().is_some() {
        return Err(StatementInputError::StatementBindingDuplicated { schema });
    }
    let expected = u32::try_from(SPAN_STATEMENT_CANONICAL_WORDS)
        .map_err(|_| StatementInputError::WordCountOutOfRange)?;
    if operation.payload_word_count() != expected {
        return Err(StatementInputError::StatementWidthMismatch {
            schema,
            expected,
            actual: operation.payload_word_count(),
        });
    }
    Ok(())
}

fn append_lane_rows(
    rows: &mut Vec<PreprocessedRow>,
    verifier_id: u32,
    statement_scope: u32,
    segment_mask: u32,
    binary_mask: u32,
    statement_use_count: u32,
    vm_claim_mask: u32,
) -> Result<(), StatementInputError> {
    for word_index in 0..SPAN_STATEMENT_CANONICAL_WORDS {
        rows.push(PreprocessedRow {
            segment_mask,
            binary_mask,
            verifier_id,
            statement_scope,
            word_index: u32::try_from(word_index)
                .map_err(|_| StatementInputError::WordIndexOutOfRange { word_index })?,
            statement_use_count,
            vm_claim_mask,
        });
    }
    Ok(())
}

/// Relation instances used by the macro-generated statement input component.
#[derive(Clone)]
pub struct StatementInputComponentRelations {
    pub input_word: super::transcript_payload_air::VerifierInputWordRelation,
    pub statement_word: StatementWordRelation,
}

impl StatementInputComponentRelations {
    /// Combine verifier-input and scoped-statement relation instances.
    pub fn new(
        input_relations: &VerifierInputRelations,
        statement_relations: &StatementInputRelations,
    ) -> Self {
        Self {
            input_word: input_relations.input_word.clone(),
            statement_word: statement_relations.statement_word.clone(),
        }
    }
}

stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [],
    embedded_component: true,
    embedded_enabler_boolean: false,
    embedded_relations: crate::statement_input_air::StatementInputComponentRelations,
    logup_batch: 2,
    embedded_preprocessed: {
        row_mask: "recursion_statement_input_row_mask",
        segment_mask: "recursion_statement_input_segment_mask",
        binary_mask: "recursion_statement_input_binary_mask",
        verifier_id: "recursion_statement_input_verifier_id",
        statement_scope: "recursion_statement_input_scope",
        word_index: "recursion_statement_input_word_index",
        statement_use_count: "recursion_statement_input_statement_use_count",
        vm_claim_mask: "recursion_statement_input_vm_claim_mask",
    },
    embedded_params: [
        segment_active, binary_active, statement_input_kind, input_item, vm_claim_scope,
    ],

    relation input_word(5);
    relation statement_word(3);

    fn statement_input(
        value,
        row_mask, segment_mask, binary_mask, verifier_id, statement_scope, word_index,
        statement_use_count, vm_claim_mask,
        segment_active, binary_active, statement_input_kind, input_item, vm_claim_scope,
    ) {
        let active = segment_mask * segment_active + binary_mask * binary_active;

        constrain enabler - row_mask;
        constrain (row_mask - active) * value;

        consume(active) input_word(
            verifier_id, statement_input_kind, input_item, word_index, value,
        );
        emit(active * statement_use_count) statement_word(
            statement_scope, word_index, value,
        );
        emit(active * vm_claim_mask) statement_word(
            vm_claim_scope, word_index, value,
        );

        return value;
    }
}

pub use component::air::{Component, Eval};

/// Construct the generated evaluator with verifier-owned routing constants.
pub fn eval_for_proof_kind(
    log_size: u32,
    proof_kind: ProofKind,
    input_relations: &VerifierInputRelations,
    statement_relations: &StatementInputRelations,
) -> Eval {
    Eval {
        log_size,
        segment_active: BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        binary_active: BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode)),
        statement_input_kind: BaseField::from(VerifierInputKind::Statement.as_u32()),
        input_item: BaseField::from(0),
        vm_claim_scope: BaseField::from(VM_CLAIM_STATEMENT_SCOPE),
        relations: StatementInputComponentRelations::new(input_relations, statement_relations),
    }
}

/// Generate verifier-input consumers and scoped-statement producers.
pub fn gen_interaction_trace(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    preprocessed: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    proof_kind: ProofKind,
    input_relations: &VerifierInputRelations,
    statement_relations: &StatementInputRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    component::witness::gen_interaction_trace(
        trace,
        preprocessed,
        BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode)),
        BaseField::from(VerifierInputKind::Statement.as_u32()),
        BaseField::from(0),
        BaseField::from(VM_CLAIM_STATEMENT_SCOPE),
        &StatementInputComponentRelations::new(input_relations, statement_relations),
    )
}

/// Statement inputs needed by the selected universal verifier mode.
#[derive(Clone, Copy)]
pub enum StatementInputWitness<'a> {
    Segment(&'a SpanStatement),
    Binary {
        left: &'a SpanStatement,
        right: &'a SpanStatement,
    },
    Empty,
}

impl StatementInputWitness<'_> {
    pub const fn proof_kind(self) -> ProofKind {
        match self {
            Self::Segment(_) => ProofKind::SegmentLeaf,
            Self::Binary { .. } => ProofKind::BinaryNode,
            Self::Empty => ProofKind::EmptyLeaf,
        }
    }
}

/// Materializes active child statement words and zeroes every inactive lane.
pub fn push_statement_inputs(
    table: &mut StatementInputTable,
    preprocessed: &StatementInputPreprocessed,
    witness: StatementInputWitness<'_>,
) -> Result<(), StatementInputError> {
    let (segment, poseidon2, left, right) = match witness {
        StatementInputWitness::Segment(statement) => {
            let words = canonical_words(statement)?;
            (Some(words), Some(words), None, None)
        }
        StatementInputWitness::Binary { left, right } => (
            None,
            None,
            Some(canonical_words(left)?),
            Some(canonical_words(right)?),
        ),
        StatementInputWitness::Empty => (None, None, None, None),
    };

    for row in &preprocessed.rows {
        let words = match row.verifier_id {
            SEGMENT_VERIFIER_ID => segment.as_ref(),
            POSEIDON2_VERIFIER_ID => poseidon2.as_ref(),
            LEFT_RECURSION_VERIFIER_ID => left.as_ref(),
            RIGHT_RECURSION_VERIFIER_ID => right.as_ref(),
            verifier_id => return Err(StatementInputError::UnknownVerifierId { verifier_id }),
        };
        let value = if let Some(words) = words {
            let index = usize::try_from(row.word_index).map_err(|_| {
                StatementInputError::WordIndexDoesNotFitUsize {
                    word_index: row.word_index,
                }
            })?;
            words
                .get(index)
                .copied()
                .ok_or(StatementInputError::StatementWordMissing { index })?
                .as_u32()
        } else {
            0
        };
        table.push(value);
    }
    Ok(())
}

/// Verifier-owned contribution that emits every public parent statement word.
pub fn public_statement_terms(
    statement: &SpanStatement,
    relations: &StatementInputRelations,
) -> Result<QM31, StatementInputError> {
    statement_scope_terms(statement, PARENT_STATEMENT_SCOPE, relations)
}

fn statement_scope_terms(
    statement: &SpanStatement,
    scope: u32,
    relations: &StatementInputRelations,
) -> Result<QM31, StatementInputError> {
    let words = canonical_words(statement)?;
    let mut total = QM31::zero();
    for (index, word) in words.into_iter().enumerate() {
        let index = u32::try_from(index)
            .map_err(|_| StatementInputError::WordIndexOutOfRange { word_index: index })?;
        let denominator: QM31 = relations.statement_word.combine(&[
            M31::from(scope),
            M31::from(index),
            M31::from(word.as_u32()),
        ]);
        total += denominator.inverse();
    }
    Ok(total)
}

fn canonical_words(
    statement: &SpanStatement,
) -> Result<[M31Word; SPAN_STATEMENT_CANONICAL_WORDS], StatementInputError> {
    let words = statement.canonical_words();
    let actual = words.len();
    words
        .try_into()
        .map_err(|_| StatementInputError::CanonicalWordCountMismatch {
            expected: SPAN_STATEMENT_CANONICAL_WORDS,
            actual,
        })
}

/// Invalid statement-input preprocessing, witness, or canonical encoding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StatementInputError {
    RowCountOverflow,
    LogSizeOutOfRange {
        log_size: u32,
    },
    StatementBindingMissing {
        schema: &'static str,
    },
    StatementBindingDuplicated {
        schema: &'static str,
    },
    WordCountOutOfRange,
    StatementWidthMismatch {
        schema: &'static str,
        expected: u32,
        actual: u32,
    },
    WordIndexOutOfRange {
        word_index: usize,
    },
    WordIndexDoesNotFitUsize {
        word_index: u32,
    },
    UnknownVerifierId {
        verifier_id: u32,
    },
    StatementWordMissing {
        index: usize,
    },
    CanonicalWordCountMismatch {
        expected: usize,
        actual: usize,
    },
}

impl fmt::Display for StatementInputError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::RowCountOverflow => write!(formatter, "statement input row count overflowed"),
            Self::LogSizeOutOfRange { log_size } => write!(
                formatter,
                "statement input log size {log_size} exceeds the supported maximum {MAX_LOG_SIZE}"
            ),
            Self::StatementBindingMissing { schema } => {
                write!(formatter, "{schema} transcript has no statement binding")
            }
            Self::StatementBindingDuplicated { schema } => write!(
                formatter,
                "{schema} transcript has more than one statement binding"
            ),
            Self::WordCountOutOfRange => {
                write!(formatter, "canonical statement word count does not fit u32")
            }
            Self::StatementWidthMismatch {
                schema,
                expected,
                actual,
            } => write!(
                formatter,
                "{schema} statement binding has {actual} words, expected {expected}"
            ),
            Self::WordIndexOutOfRange { word_index } => {
                write!(
                    formatter,
                    "statement word index {word_index} does not fit u32"
                )
            }
            Self::WordIndexDoesNotFitUsize { word_index } => write!(
                formatter,
                "statement word index {word_index} does not fit usize"
            ),
            Self::UnknownVerifierId { verifier_id } => {
                write!(formatter, "unknown statement verifier id {verifier_id}")
            }
            Self::StatementWordMissing { index } => {
                write!(formatter, "canonical statement has no word {index}")
            }
            Self::CanonicalWordCountMismatch { expected, actual } => write!(
                formatter,
                "canonical statement has {actual} words, expected {expected}"
            ),
        }
    }
}

impl std::error::Error for StatementInputError {}

#[cfg(test)]
mod tests {
    use air::digest::{Digest8, IoDigest, MemoryDigest, ProgramDigest, ProtocolId};
    use prover::poseidon2_channel::Poseidon2M31Channel;
    use rstest::rstest;
    use stwo::core::pcs::TreeVec;
    use stwo_constraint_framework::{FrameworkEval, assert_constraints_on_polys};

    use super::*;
    use crate::kernel::{VerifierControlPlan, VerifierProgramSpec, VerifierSchema};
    use crate::protocol::{FixedProofShape, OptionalM31Word, PcsParameters};
    use crate::statement::{
        CompleteExecutionStatement, EdgeClaim, ExecutedSpan, JobContext, MachineState,
    };

    fn word(value: u16) -> M31Word {
        M31Word::from(value)
    }

    fn digest(seed: u16) -> Digest8 {
        Digest8::new(core::array::from_fn(|offset| word(seed + offset as u16)))
    }

    fn pcs() -> PcsParameters {
        PcsParameters {
            interaction_pow_bits: M31Word::ZERO,
            pow_bits: M31Word::ZERO,
            fri_log_blowup_factor: word(1),
            fri_n_queries: word(1),
            fri_log_last_layer_degree_bound: M31Word::ZERO,
            fri_fold_step: word(2),
            lifting_log_size: OptionalM31Word::Some(word(4)),
        }
    }

    fn shape() -> FixedProofShape<1, 4, 2> {
        FixedProofShape {
            claimed_sum_count: word(1),
            sampled_value_count: word(1),
            queried_value_count: word(1),
            trace_path_count: word(4),
            raw_query_count: word(1),
            last_layer_coefficient_count: word(1),
            table_log_sizes: [word(3)],
            tree_heights: [word(4); 4],
            fri_layer_fold_widths: [word(4), word(2)],
            fri_layer_tree_heights: [word(2), word(2)],
        }
    }

    fn plan(schema: VerifierSchema) -> VerifierControlPlan {
        let spec = VerifierProgramSpec::new(schema, 1, 1, 1, 1)
            .expect("fixture program has every verifier phase");
        VerifierControlPlan::new(spec, pcs(), &shape())
            .expect("fixture geometry matches its PCS profile")
    }

    fn preprocessing() -> StatementInputPreprocessed {
        let calls = TranscriptCallPreprocessed::new(
            &plan(VerifierSchema::Vm),
            &plan(VerifierSchema::Poseidon2),
            &plan(VerifierSchema::Recursion),
        )
        .expect("fixture plans occupy their canonical transcript lanes");
        StatementInputPreprocessed::new(&calls)
            .expect("fixture transcript layouts bind one canonical statement")
    }

    fn state(seed: u32) -> MachineState {
        let mut registers = [0_u32; 32];
        registers[1] = seed;
        MachineState::new(
            seed * 4,
            registers,
            MemoryDigest::from(digest(seed as u16 + 10)),
            IoDigest::from(digest(seed as u16 + 20)),
        )
        .expect("fixture keeps the zero register immutable")
    }

    fn child_statements() -> (SpanStatement, SpanStatement) {
        let complete = CompleteExecutionStatement::new(
            ProtocolId::from(digest(1)),
            ProgramDigest::from(digest(2)),
            state(0),
            state(2),
            IoDigest::from(digest(3)),
            IoDigest::from(digest(4)),
            10,
        )
        .expect("fixture execution is nonempty");
        let job = JobContext::new(complete, 2).expect("fixture job has two segments");
        let left_span = ExecutedSpan::new(
            0,
            1,
            0,
            4,
            state(0),
            state(1),
            EdgeClaim::present(complete.public_input()),
            EdgeClaim::absent(),
        )
        .expect("left fixture span is nonempty");
        let right_span = ExecutedSpan::new(
            1,
            1,
            4,
            6,
            state(1),
            state(2),
            EdgeClaim::absent(),
            EdgeClaim::present(complete.public_output()),
        )
        .expect("right fixture span is nonempty");
        (
            SpanStatement::segment_leaf(job, 0, left_span)
                .expect("left fixture statement covers slot zero"),
            SpanStatement::segment_leaf(job, 1, right_span)
                .expect("right fixture statement covers slot one"),
        )
    }

    fn assert_constraints(kind: ProofKind, tamper_inactive: bool) {
        let preprocessing = preprocessing();
        let (left, right) = child_statements();
        let witness = match kind {
            ProofKind::SegmentLeaf => StatementInputWitness::Segment(&left),
            ProofKind::BinaryNode => StatementInputWitness::Binary {
                left: &left,
                right: &right,
            },
            ProofKind::EmptyLeaf => StatementInputWitness::Empty,
        };
        let mut table = StatementInputTable::new();
        push_statement_inputs(&mut table, &preprocessing, witness)
            .expect("fixture statement words materialize");
        if tamper_inactive {
            table.value[0] = 1;
        }
        let input_relations = VerifierInputRelations::dummy();
        let statement_relations = StatementInputRelations::dummy();
        let preprocessed = preprocessing.gen_columns();
        let trace = table.into_witness();
        let (interaction, claimed_sum) = gen_interaction_trace(
            &trace,
            &preprocessed,
            kind,
            &input_relations,
            &statement_relations,
        );
        let traces = TreeVec::new(vec![preprocessed, trace, interaction]);
        let trace_polys = traces.map_cols(|column| column.interpolate());
        let eval = eval_for_proof_kind(
            preprocessing.log_size(),
            kind,
            &input_relations,
            &statement_relations,
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

    fn component_claimed_sum(
        witness: StatementInputWitness<'_>,
        input_relations: &VerifierInputRelations,
        statement_relations: &StatementInputRelations,
    ) -> QM31 {
        let preprocessing = preprocessing();
        let mut table = StatementInputTable::new();
        push_statement_inputs(&mut table, &preprocessing, witness)
            .expect("fixture statement words materialize");
        let (_, claimed_sum) = gen_interaction_trace(
            &table.into_witness(),
            &preprocessing.gen_columns(),
            witness.proof_kind(),
            input_relations,
            statement_relations,
        );
        claimed_sum
    }

    fn input_statement_terms(
        statement: &SpanStatement,
        verifier_id: u32,
        relations: &VerifierInputRelations,
    ) -> QM31 {
        let words = canonical_words(statement).expect("fixture statement width is canonical");
        let mut total = QM31::zero();
        for (index, word) in words.into_iter().enumerate() {
            let denominator: QM31 = relations.input_word.combine(&[
                M31::from(verifier_id),
                M31::from(VerifierInputKind::Statement.as_u32()),
                M31::from(0),
                M31::from(index as u32),
                M31::from(word.as_u32()),
            ]);
            total += denominator.inverse();
        }
        total
    }

    #[rstest]
    #[case::segment(ProofKind::SegmentLeaf)]
    #[case::binary(ProofKind::BinaryNode)]
    #[case::empty(ProofKind::EmptyLeaf)]
    fn every_universal_mode_satisfies_statement_input_routing(#[case] kind: ProofKind) {
        assert_constraints(kind, false);
    }

    #[rstest]
    #[case::segment(ProofKind::SegmentLeaf, SPAN_STATEMENT_CANONICAL_WORDS)]
    #[case::binary(ProofKind::BinaryNode, 2 * SPAN_STATEMENT_CANONICAL_WORDS)]
    #[case::empty(ProofKind::EmptyLeaf, 0)]
    fn proof_kind_activates_only_its_child_statement_words(
        #[case] kind: ProofKind,
        #[case] expected: usize,
    ) {
        assert_eq!(
            StatementInputPreprocessed::active_word_count(kind),
            expected
        );
    }

    #[rstest]
    #[should_panic]
    fn inactive_statement_input_values_must_be_zero() {
        assert_constraints(ProofKind::EmptyLeaf, true);
    }

    #[rstest]
    fn segment_statement_closes_into_the_leaf_semantics_scope() {
        let (statement, _) = child_statements();
        let mut channel = Poseidon2M31Channel::default();
        let input_relations = VerifierInputRelations::draw(&mut channel);
        let statement_relations = StatementInputRelations::draw(&mut channel);
        let component = component_claimed_sum(
            StatementInputWitness::Segment(&statement),
            &input_relations,
            &statement_relations,
        );
        let input = input_statement_terms(&statement, SEGMENT_VERIFIER_ID, &input_relations);
        let segment =
            statement_scope_terms(&statement, SEGMENT_STATEMENT_SCOPE, &statement_relations)
                .expect("fixture statement has canonical width");
        let vm_claim =
            statement_scope_terms(&statement, VM_CLAIM_STATEMENT_SCOPE, &statement_relations)
                .expect("fixture statement has canonical width");
        assert_eq!(component + input - segment - vm_claim, QM31::zero());
    }

    #[rstest]
    fn binary_statements_close_into_distinct_fold_scopes() {
        let (left, right) = child_statements();
        let mut channel = Poseidon2M31Channel::default();
        let input_relations = VerifierInputRelations::draw(&mut channel);
        let statement_relations = StatementInputRelations::draw(&mut channel);
        let component = component_claimed_sum(
            StatementInputWitness::Binary {
                left: &left,
                right: &right,
            },
            &input_relations,
            &statement_relations,
        );
        let inputs = input_statement_terms(&left, LEFT_RECURSION_VERIFIER_ID, &input_relations)
            + input_statement_terms(&right, RIGHT_RECURSION_VERIFIER_ID, &input_relations);
        let children = statement_scope_terms(&left, LEFT_STATEMENT_SCOPE, &statement_relations)
            .expect("left fixture statement has canonical width")
            + statement_scope_terms(&right, RIGHT_STATEMENT_SCOPE, &statement_relations)
                .expect("right fixture statement has canonical width");
        assert_eq!(component + inputs - children - children, QM31::zero());
    }

    #[rstest]
    fn statement_input_constraint_profile_stays_cubic() {
        use stwo_constraint_framework::expr::ExprEvaluator;

        let eval = eval_for_proof_kind(
            4,
            ProofKind::SegmentLeaf,
            &VerifierInputRelations::dummy(),
            &StatementInputRelations::dummy(),
        );
        let degrees = eval
            .evaluate(ExprEvaluator::new())
            .constraint_degree_bounds();
        assert_eq!((degrees.len(), degrees.into_iter().max()), (4, Some(3)));
    }
}
