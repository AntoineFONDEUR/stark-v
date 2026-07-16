//! Typed ownership for non-relation randomness drawn by V2 verifier transcripts.
//!
//! Each verifier operation consumes its complete eight-word transcript draw
//! atomically, then exports only the words used by that operation under a
//! verifier, semantic kind, item, and limb coordinate. Secure-field draws use
//! the first four words; query blocks export every verifier-planned raw query
//! word. Unused draw words remain constrained by the atomic transcript tuple.

use core::fmt;

use air::digest::M31Word;
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
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, RelationEntry, relation,
};
use stwo_macros::define_component_tables;

use super::control_air::{
    LEFT_RECURSION_VERIFIER_ID, RIGHT_RECURSION_VERIFIER_ID, SEGMENT_VERIFIER_ID,
};
use super::kernel::{VerifierControlPlan, VerifierSchema, VerifierStep};
use super::transcript::RecordingTranscriptBackend;
use super::transcript_binding_air::UniversalTranscriptWitness;
use super::transcript_program::VerifierTranscriptExecution;
use super::transcript_state_air::TranscriptStateRelations;
use super::wire::ProofKind;

const DRAW_WORDS: usize = 8;
const SECURE_FIELD_WORDS: u32 = 4;
const MIN_LOG_SIZE: u32 = 4;
const MAX_LOG_SIZE: u32 = 30;

const ROW_MASK_COLUMN: usize = 0;
const SEGMENT_MASK_COLUMN: usize = 1;
const BINARY_MASK_COLUMN: usize = 2;
const VERIFIER_ID_COLUMN: usize = 3;
const SEQUENCE_COLUMN: usize = 4;
const TAG_COLUMN: usize = 5;
const ARG_0_COLUMN: usize = 6;
const ARG_1_COLUMN: usize = 7;
const ARG_2_COLUMN: usize = 8;
const ARG_3_COLUMN: usize = 9;
const KIND_COLUMN: usize = 10;
const ITEM_BASE_COLUMN: usize = 11;
const QUERY_ITEMS_COLUMN: usize = 12;
const WORD_MASK_START_COLUMN: usize = 13;
const PREPROCESSED_COLUMN_COUNT: usize = WORD_MASK_START_COLUMN + DRAW_WORDS;

const PREPROCESSED_COLUMN_IDS: [&str; PREPROCESSED_COLUMN_COUNT] = [
    "recursion_v2_verifier_randomness_row_mask",
    "recursion_v2_verifier_randomness_segment_mask",
    "recursion_v2_verifier_randomness_binary_mask",
    "recursion_v2_verifier_randomness_verifier_id",
    "recursion_v2_verifier_randomness_sequence",
    "recursion_v2_verifier_randomness_tag",
    "recursion_v2_verifier_randomness_arg_0",
    "recursion_v2_verifier_randomness_arg_1",
    "recursion_v2_verifier_randomness_arg_2",
    "recursion_v2_verifier_randomness_arg_3",
    "recursion_v2_verifier_randomness_kind",
    "recursion_v2_verifier_randomness_item_base",
    "recursion_v2_verifier_randomness_query_items",
    "recursion_v2_verifier_randomness_word_0_mask",
    "recursion_v2_verifier_randomness_word_1_mask",
    "recursion_v2_verifier_randomness_word_2_mask",
    "recursion_v2_verifier_randomness_word_3_mask",
    "recursion_v2_verifier_randomness_word_4_mask",
    "recursion_v2_verifier_randomness_word_5_mask",
    "recursion_v2_verifier_randomness_word_6_mask",
    "recursion_v2_verifier_randomness_word_7_mask",
];

define_component_tables! {
    verifier_randomness: {
        committed: {
            output_0, output_1, output_2, output_3,
            output_4, output_5, output_6, output_7,
        },
        constraints: {},
    },
}

use prover_columns::VerifierRandomnessColumns;

// Typed word: verifier, semantic kind, item, word index, and value.
relation!(VerifierRandomnessWordRelation, 5);

/// Relation carrying transcript-derived randomness into verifier gadgets.
#[derive(Clone)]
pub struct VerifierRandomnessRelations {
    pub word: VerifierRandomnessWordRelation,
}

impl VerifierRandomnessRelations {
    pub fn dummy() -> Self {
        Self {
            word: VerifierRandomnessWordRelation::dummy(),
        }
    }

    pub fn draw(channel: &mut impl stwo::core::channel::Channel) -> Self {
        Self {
            word: VerifierRandomnessWordRelation::draw(channel),
        }
    }
}

/// Non-interchangeable semantic classes for verifier transcript draws.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
#[repr(u32)]
pub enum VerifierRandomnessKind {
    CompositionRandomness = 1,
    OodsPoint = 2,
    DeepRandomness = 3,
    FriAlpha = 4,
    RawQuery = 5,
}

impl VerifierRandomnessKind {
    pub const fn as_u32(self) -> u32 {
        self as u32
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct DrawDescriptor {
    kind: VerifierRandomnessKind,
    item_base: u32,
    query_items: bool,
    word_count: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PreprocessedRow {
    segment_mask: u32,
    binary_mask: u32,
    verifier_id: u32,
    sequence: u32,
    step: VerifierStep,
    tag: u32,
    args: [u32; 4],
    descriptor: DrawDescriptor,
}

/// Trusted non-relation draw operations for all three verifier lanes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifierRandomnessPreprocessed {
    log_size: u32,
    rows: Vec<PreprocessedRow>,
    vm_draw_count: u32,
    recursion_draw_count: u32,
}

impl VerifierRandomnessPreprocessed {
    pub fn new(
        vm: &VerifierControlPlan,
        recursion: &VerifierControlPlan,
    ) -> Result<Self, VerifierRandomnessError> {
        if vm.schema() != VerifierSchema::Vm {
            return Err(VerifierRandomnessError::SchemaMismatch {
                lane: "segment",
                expected: VerifierSchema::Vm,
                actual: vm.schema(),
            });
        }
        if recursion.schema() != VerifierSchema::Recursion {
            return Err(VerifierRandomnessError::SchemaMismatch {
                lane: "binary",
                expected: VerifierSchema::Recursion,
                actual: recursion.schema(),
            });
        }

        let mut rows = Vec::new();
        let vm_draw_count = append_plan_rows(&mut rows, vm, SEGMENT_VERIFIER_ID, 1, 0)?;
        let recursion_draw_count =
            append_plan_rows(&mut rows, recursion, LEFT_RECURSION_VERIFIER_ID, 0, 1)?;
        append_plan_rows(&mut rows, recursion, RIGHT_RECURSION_VERIFIER_ID, 0, 1)?;
        let padded_rows = rows
            .len()
            .checked_next_power_of_two()
            .ok_or(VerifierRandomnessError::RowCountOverflow)?
            .max(1 << MIN_LOG_SIZE);
        let log_size = padded_rows.ilog2();
        if log_size > MAX_LOG_SIZE {
            return Err(VerifierRandomnessError::LogSizeOutOfRange { log_size });
        }
        Ok(Self {
            log_size,
            rows,
            vm_draw_count,
            recursion_draw_count,
        })
    }

    pub const fn log_size(&self) -> u32 {
        self.log_size
    }

    pub const fn vm_draw_count(&self) -> u32 {
        self.vm_draw_count
    }

    pub const fn recursion_draw_count(&self) -> u32 {
        self.recursion_draw_count
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
            columns[SEGMENT_MASK_COLUMN][index] = row.segment_mask;
            columns[BINARY_MASK_COLUMN][index] = row.binary_mask;
            columns[VERIFIER_ID_COLUMN][index] = row.verifier_id;
            columns[SEQUENCE_COLUMN][index] = row.sequence;
            columns[TAG_COLUMN][index] = row.tag;
            columns[ARG_0_COLUMN][index] = row.args[0];
            columns[ARG_1_COLUMN][index] = row.args[1];
            columns[ARG_2_COLUMN][index] = row.args[2];
            columns[ARG_3_COLUMN][index] = row.args[3];
            columns[KIND_COLUMN][index] = row.descriptor.kind.as_u32();
            columns[ITEM_BASE_COLUMN][index] = row.descriptor.item_base;
            columns[QUERY_ITEMS_COLUMN][index] = u32::from(row.descriptor.query_items);
            for word in 0..DRAW_WORDS {
                columns[WORD_MASK_START_COLUMN + word][index] =
                    u32::from(word < row.descriptor.word_count as usize);
            }
        }
        let domain = CanonicCoset::new(self.log_size).circle_domain();
        columns
            .into_iter()
            .map(|column| CircleEvaluation::new(domain, BaseColumn::from(column)))
            .collect()
    }
}

fn append_plan_rows(
    rows: &mut Vec<PreprocessedRow>,
    plan: &VerifierControlPlan,
    verifier_id: u32,
    segment_mask: u32,
    binary_mask: u32,
) -> Result<u32, VerifierRandomnessError> {
    let mut draw_count = 0_u32;
    for (sequence, step) in plan.steps().iter().copied().enumerate() {
        let Some(descriptor) = draw_descriptor(step)? else {
            continue;
        };
        let sequence = u32::try_from(sequence)
            .map_err(|_| VerifierRandomnessError::SequenceOutOfRange { sequence })?;
        let encoded = step.encode();
        rows.push(PreprocessedRow {
            segment_mask,
            binary_mask,
            verifier_id,
            sequence,
            step,
            tag: encoded.tag(),
            args: encoded.args(),
            descriptor,
        });
        draw_count = draw_count
            .checked_add(1)
            .ok_or(VerifierRandomnessError::DrawCountOverflow)?;
    }
    if draw_count == 0 {
        return Err(VerifierRandomnessError::VerifierRandomnessMissing {
            schema: plan.schema(),
        });
    }
    Ok(draw_count)
}

fn draw_descriptor(step: VerifierStep) -> Result<Option<DrawDescriptor>, VerifierRandomnessError> {
    let secure = |kind, item_base| DrawDescriptor {
        kind,
        item_base,
        query_items: false,
        word_count: SECURE_FIELD_WORDS,
    };
    let descriptor = match step {
        VerifierStep::DrawCompositionRandomness => {
            secure(VerifierRandomnessKind::CompositionRandomness, 0)
        }
        VerifierStep::DrawOodsPoint => secure(VerifierRandomnessKind::OodsPoint, 0),
        VerifierStep::DrawDeepRandomness => secure(VerifierRandomnessKind::DeepRandomness, 0),
        VerifierStep::DrawFriAlpha { layer } => secure(VerifierRandomnessKind::FriAlpha, layer),
        VerifierStep::DrawQueryBlock {
            first_query,
            query_count,
            ..
        } => {
            if query_count == 0 || query_count > DRAW_WORDS as u32 {
                return Err(VerifierRandomnessError::QueryBlockWidthOutOfRange { query_count });
            }
            first_query
                .checked_add(query_count)
                .ok_or(VerifierRandomnessError::QueryIndexOverflow)?;
            DrawDescriptor {
                kind: VerifierRandomnessKind::RawQuery,
                item_base: first_query,
                query_items: true,
                word_count: query_count,
            }
        }
        VerifierStep::DrawRelationChallenge { .. }
        | VerifierStep::BindProtocol
        | VerifierStep::BindStatement
        | VerifierStep::BindPcsParameters
        | VerifierStep::AbsorbTraceCommitment { .. }
        | VerifierStep::AbsorbPublicClaim
        | VerifierStep::VerifyAndAbsorbInteractionPow { .. }
        | VerifierStep::AccumulatePublicLogupTerm { .. }
        | VerifierStep::AssertGlobalLogupZero
        | VerifierStep::AbsorbClaimedSums { .. }
        | VerifierStep::EvaluateAirInstruction { .. }
        | VerifierStep::AssertComposition { .. }
        | VerifierStep::AbsorbSampledValues { .. }
        | VerifierStep::AbsorbFriCommitment { .. }
        | VerifierStep::AbsorbLastLayerCoefficients { .. }
        | VerifierStep::VerifyAndAbsorbPcsPow { .. }
        | VerifierStep::VerifyTraceMerklePath { .. }
        | VerifierStep::EvaluateDeepQuotient { .. }
        | VerifierStep::VerifyFriMerklePath { .. }
        | VerifierStep::FoldFri { .. }
        | VerifierStep::VerifyLastLayer { .. }
        | VerifierStep::CloseRelation { .. }
        | VerifierStep::Complete => return Ok(None),
    };
    Ok(Some(descriptor))
}

pub type Component = FrameworkComponent<Eval>;

#[derive(Clone)]
pub struct Eval {
    pub log_size: u32,
    pub proof_kind: ProofKind,
    pub transcript_relations: TranscriptStateRelations,
    pub randomness_relations: VerifierRandomnessRelations,
}

impl FrameworkEval for Eval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let cols = VerifierRandomnessColumns::from_eval(&mut eval);
        let ids = VerifierRandomnessPreprocessed::column_ids();
        let row_mask = eval.get_preprocessed_column(ids[ROW_MASK_COLUMN].clone());
        let segment_mask = eval.get_preprocessed_column(ids[SEGMENT_MASK_COLUMN].clone());
        let binary_mask = eval.get_preprocessed_column(ids[BINARY_MASK_COLUMN].clone());
        let verifier_id = eval.get_preprocessed_column(ids[VERIFIER_ID_COLUMN].clone());
        let sequence = eval.get_preprocessed_column(ids[SEQUENCE_COLUMN].clone());
        let tag = eval.get_preprocessed_column(ids[TAG_COLUMN].clone());
        let arg_0 = eval.get_preprocessed_column(ids[ARG_0_COLUMN].clone());
        let arg_1 = eval.get_preprocessed_column(ids[ARG_1_COLUMN].clone());
        let arg_2 = eval.get_preprocessed_column(ids[ARG_2_COLUMN].clone());
        let arg_3 = eval.get_preprocessed_column(ids[ARG_3_COLUMN].clone());
        let kind = eval.get_preprocessed_column(ids[KIND_COLUMN].clone());
        let item_base = eval.get_preprocessed_column(ids[ITEM_BASE_COLUMN].clone());
        let query_items = eval.get_preprocessed_column(ids[QUERY_ITEMS_COLUMN].clone());
        let word_masks = core::array::from_fn::<_, DRAW_WORDS, _>(|word| {
            eval.get_preprocessed_column(ids[WORD_MASK_START_COLUMN + word].clone())
        });
        let output = output_columns(&cols);
        let segment = E::F::from(BaseField::from(u32::from(
            self.proof_kind == ProofKind::SegmentLeaf,
        )));
        let binary = E::F::from(BaseField::from(u32::from(
            self.proof_kind == ProofKind::BinaryNode,
        )));
        let active = row_mask * (segment_mask * segment + binary_mask * binary);
        let one = E::F::from(BaseField::from(1));
        eval.add_constraint(cols.enabler.clone() - active.clone());
        for value in &output {
            eval.add_constraint((one.clone() - active.clone()) * value.clone());
        }

        let mut draw_tuple = vec![
            verifier_id.clone(),
            sequence,
            tag,
            arg_0,
            arg_1,
            arg_2,
            arg_3,
        ];
        draw_tuple.extend(output.iter().cloned());
        eval.add_to_relation(RelationEntry::new(
            &self.transcript_relations.draw_output,
            -E::EF::from(active.clone()),
            &draw_tuple,
        ));
        for (word_index, value) in output.into_iter().enumerate() {
            let word = E::F::from(BaseField::from(
                u32::try_from(word_index).expect("draw word index fits u32"),
            ));
            let item = item_base.clone() + query_items.clone() * word.clone();
            let semantic_word_index = (one.clone() - query_items.clone()) * word;
            eval.add_to_relation(RelationEntry::new(
                &self.randomness_relations.word,
                E::EF::from(active.clone() * word_masks[word_index].clone()),
                &[
                    verifier_id.clone(),
                    kind.clone(),
                    item,
                    semantic_word_index,
                    value,
                ],
            ));
        }
        eval.finalize_logup_in_pairs();
        eval
    }
}

fn output_columns<F: Clone>(cols: &VerifierRandomnessColumns<F>) -> [F; DRAW_WORDS] {
    [
        cols.output_0.clone(),
        cols.output_1.clone(),
        cols.output_2.clone(),
        cols.output_3.clone(),
        cols.output_4.clone(),
        cols.output_5.clone(),
        cols.output_6.clone(),
        cols.output_7.clone(),
    ]
}

/// Generates atomic draw consumers and typed randomness-word producers.
pub fn gen_interaction_trace(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    preprocessed: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    proof_kind: ProofKind,
    transcript_relations: &TranscriptStateRelations,
    randomness_relations: &VerifierRandomnessRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    let cols = VerifierRandomnessColumns::from_iter(
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
    let active = (0..simd_size)
        .map(|row| {
            PackedQM31::from(
                pp[ROW_MASK_COLUMN][row]
                    * (pp[SEGMENT_MASK_COLUMN][row] * segment
                        + pp[BINARY_MASK_COLUMN][row] * binary),
            )
        })
        .collect::<Vec<_>>();
    let negative_active = active.iter().map(|value| -*value).collect::<Vec<_>>();
    let output = [
        cols.output_0,
        cols.output_1,
        cols.output_2,
        cols.output_3,
        cols.output_4,
        cols.output_5,
        cols.output_6,
        cols.output_7,
    ];
    let draw_denom = combine!(
        transcript_relations.draw_output,
        [
            pp[VERIFIER_ID_COLUMN],
            pp[SEQUENCE_COLUMN],
            pp[TAG_COLUMN],
            pp[ARG_0_COLUMN],
            pp[ARG_1_COLUMN],
            pp[ARG_2_COLUMN],
            pp[ARG_3_COLUMN],
            output[0],
            output[1],
            output[2],
            output[3],
            output[4],
            output[5],
            output[6],
            output[7]
        ]
    );
    let semantic_numerators = (0..DRAW_WORDS)
        .map(|word| {
            (0..simd_size)
                .map(|row| active[row] * PackedQM31::from(pp[WORD_MASK_START_COLUMN + word][row]))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let semantic_denoms = (0..DRAW_WORDS)
        .map(|word_index| {
            let word =
                BaseField::from(u32::try_from(word_index).expect("draw word index fits u32"));
            let item = (0..simd_size)
                .map(|row| {
                    pp[ITEM_BASE_COLUMN][row]
                        + pp[QUERY_ITEMS_COLUMN][row] * PackedM31::broadcast(word)
                })
                .collect::<Vec<_>>();
            let semantic_word_index = (0..simd_size)
                .map(|row| {
                    (PackedM31::broadcast(BaseField::from(1)) - pp[QUERY_ITEMS_COLUMN][row])
                        * PackedM31::broadcast(word)
                })
                .collect::<Vec<_>>();
            combine!(
                randomness_relations.word,
                [
                    pp[VERIFIER_ID_COLUMN],
                    pp[KIND_COLUMN],
                    item,
                    semantic_word_index,
                    output[word_index]
                ]
            )
        })
        .collect::<Vec<_>>();

    let mut logup_gen = LogupTraceGenerator::new(log_size);
    write_pair!(
        &negative_active,
        &draw_denom,
        &semantic_numerators[0],
        &semantic_denoms[0],
        logup_gen
    );
    write_pair!(
        &semantic_numerators[1],
        &semantic_denoms[1],
        &semantic_numerators[2],
        &semantic_denoms[2],
        logup_gen
    );
    write_pair!(
        &semantic_numerators[3],
        &semantic_denoms[3],
        &semantic_numerators[4],
        &semantic_denoms[4],
        logup_gen
    );
    write_pair!(
        &semantic_numerators[5],
        &semantic_denoms[5],
        &semantic_numerators[6],
        &semantic_denoms[6],
        logup_gen
    );
    write_col!(&semantic_numerators[7], &semantic_denoms[7], logup_gen);
    logup_gen.finalize_last()
}

/// Materializes the trusted non-relation draws for the selected verifier lanes.
pub fn push_verifier_randomness(
    table: &mut VerifierRandomnessTable,
    preprocessed: &VerifierRandomnessPreprocessed,
    witness: UniversalTranscriptWitness<'_>,
) -> Result<(), VerifierRandomnessError> {
    let (segment, left, right) = match witness {
        UniversalTranscriptWitness::Segment(execution) => (Some(execution), None, None),
        UniversalTranscriptWitness::Binary { left, right } => (None, Some(left), Some(right)),
        UniversalTranscriptWitness::Empty => (None, None, None),
    };
    for row in &preprocessed.rows {
        let execution = match row.verifier_id {
            SEGMENT_VERIFIER_ID => segment,
            LEFT_RECURSION_VERIFIER_ID => left,
            RIGHT_RECURSION_VERIFIER_ID => right,
            verifier_id => return Err(VerifierRandomnessError::UnknownVerifierId { verifier_id }),
        };
        let values = if let Some(execution) = execution {
            operation_draw(execution, row)?.map(M31Word::as_u32)
        } else {
            [0; DRAW_WORDS]
        };
        table.push_row_values(execution.is_some(), values);
    }
    Ok(())
}

fn operation_draw(
    execution: &VerifierTranscriptExecution<RecordingTranscriptBackend>,
    row: &PreprocessedRow,
) -> Result<[M31Word; DRAW_WORDS], VerifierRandomnessError> {
    let operation = execution
        .operations()
        .iter()
        .find(|operation| operation.sequence() == row.sequence)
        .ok_or(VerifierRandomnessError::OperationMissing {
            verifier_id: row.verifier_id,
            sequence: row.sequence,
        })?;
    if operation.step() != row.step {
        return Err(VerifierRandomnessError::OperationMismatch {
            verifier_id: row.verifier_id,
            sequence: row.sequence,
            expected: row.step,
            actual: operation.step(),
        });
    }
    operation
        .draw()
        .ok_or(VerifierRandomnessError::DrawMissing {
            verifier_id: row.verifier_id,
            sequence: row.sequence,
        })
}

impl VerifierRandomnessTable {
    fn push_row_values(&mut self, active: bool, values: [u32; DRAW_WORDS]) {
        self.push_row(&[
            u32::from(active),
            values[0],
            values[1],
            values[2],
            values[3],
            values[4],
            values[5],
            values[6],
            values[7],
        ]);
    }
}

/// Invalid trusted randomness layout or transcript witness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifierRandomnessError {
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
    DrawCountOverflow,
    VerifierRandomnessMissing {
        schema: VerifierSchema,
    },
    QueryBlockWidthOutOfRange {
        query_count: u32,
    },
    QueryIndexOverflow,
    UnknownVerifierId {
        verifier_id: u32,
    },
    OperationMissing {
        verifier_id: u32,
        sequence: u32,
    },
    OperationMismatch {
        verifier_id: u32,
        sequence: u32,
        expected: VerifierStep,
        actual: VerifierStep,
    },
    DrawMissing {
        verifier_id: u32,
        sequence: u32,
    },
}

impl fmt::Display for VerifierRandomnessError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for VerifierRandomnessError {}

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
    use crate::v2::kernel::VerifierProgramSpec;
    use crate::v2::protocol::{FixedProofShape, OptionalM31Word, PcsParameters};
    use crate::v2::relation_challenge_air::RelationChallengePreprocessed;
    use crate::v2::transcript_program::TranscriptEffect;
    use crate::v2::transcript_program::tests::{plan_for_schema, recording_execution_for};

    fn plans() -> (VerifierControlPlan, VerifierControlPlan) {
        (
            plan_for_schema(VerifierSchema::Vm, 1),
            plan_for_schema(VerifierSchema::Recursion, 1),
        )
    }

    fn plan_with_nine_queries(schema: VerifierSchema) -> VerifierControlPlan {
        let word = M31Word::from;
        let pcs = PcsParameters {
            interaction_pow_bits: M31Word::ZERO,
            pow_bits: M31Word::ZERO,
            fri_log_blowup_factor: word(1_u16),
            fri_n_queries: word(9_u16),
            fri_log_last_layer_degree_bound: M31Word::ZERO,
            fri_fold_step: word(2_u16),
            lifting_log_size: OptionalM31Word::Some(word(4_u16)),
        };
        let shape = FixedProofShape {
            claimed_sum_count: word(1_u16),
            sampled_value_count: word(9_u16),
            queried_value_count: word(9_u16),
            trace_path_count: word(36_u16),
            raw_query_count: word(9_u16),
            last_layer_coefficient_count: word(1_u16),
            table_log_sizes: [word(3_u16)],
            tree_heights: [word(4_u16); 4],
            fri_layer_fold_widths: [word(4_u16), word(2_u16)],
            fri_layer_tree_heights: [word(2_u16), word(2_u16)],
        };
        let spec = VerifierProgramSpec::new(schema, 1, 1, 1, 1)
            .expect("fixture program has every verifier phase");
        VerifierControlPlan::new(spec, pcs, &shape)
            .expect("nine-query fixture geometry is canonical")
    }

    fn assert_constraints(kind: ProofKind, tamper_inactive: bool) {
        let (vm, recursion) = plans();
        let preprocessing = VerifierRandomnessPreprocessed::new(&vm, &recursion)
            .expect("fixture plans have canonical verifier draws");
        let segment = recording_execution_for(&vm, 1);
        let left = recording_execution_for(&recursion, 1);
        let right = recording_execution_for(&recursion, 2);
        let witness = match kind {
            ProofKind::SegmentLeaf => UniversalTranscriptWitness::Segment(&segment),
            ProofKind::BinaryNode => UniversalTranscriptWitness::Binary {
                left: &left,
                right: &right,
            },
            ProofKind::EmptyLeaf => UniversalTranscriptWitness::Empty,
        };
        let mut table = VerifierRandomnessTable::new();
        push_verifier_randomness(&mut table, &preprocessing, witness)
            .expect("fixture verifier draws materialize");
        if tamper_inactive {
            table.output_0[0] = 1;
        }
        let transcript_relations = TranscriptStateRelations::dummy();
        let randomness_relations = VerifierRandomnessRelations::dummy();
        let preprocessed = preprocessing.gen_columns();
        let trace = table.into_witness();
        let (interaction, claimed_sum) = gen_interaction_trace(
            &trace,
            &preprocessed,
            kind,
            &transcript_relations,
            &randomness_relations,
        );
        let traces = TreeVec::new(vec![preprocessed, trace, interaction]);
        let trace_polys = traces.map_cols(|column| column.interpolate());
        let eval = Eval {
            log_size: preprocessing.log_size(),
            proof_kind: kind,
            transcript_relations,
            randomness_relations,
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

    fn bridge_sum(swap_verifier: bool, swap_kind: bool) -> QM31 {
        let (vm, recursion) = plans();
        let preprocessing = VerifierRandomnessPreprocessed::new(&vm, &recursion)
            .expect("fixture plans have canonical verifier draws");
        let execution = recording_execution_for(&vm, 1);
        let mut table = VerifierRandomnessTable::new();
        push_verifier_randomness(
            &mut table,
            &preprocessing,
            UniversalTranscriptWitness::Segment(&execution),
        )
        .expect("fixture verifier draws materialize");

        let mut channel = Poseidon2M31Channel::default();
        let transcript_relations = TranscriptStateRelations::draw(&mut channel);
        let randomness_relations = VerifierRandomnessRelations::draw(&mut channel);
        let (_, component_sum) = gen_interaction_trace(
            &table.into_witness(),
            &preprocessing.gen_columns(),
            ProofKind::SegmentLeaf,
            &transcript_relations,
            &randomness_relations,
        );
        component_sum
            + transcript_source_terms(&preprocessing, &execution, &transcript_relations)
            + randomness_consumer_terms(
                &preprocessing,
                &execution,
                &randomness_relations,
                swap_verifier,
                swap_kind,
            )
    }

    fn transcript_source_terms(
        preprocessing: &VerifierRandomnessPreprocessed,
        execution: &VerifierTranscriptExecution<RecordingTranscriptBackend>,
        relations: &TranscriptStateRelations,
    ) -> QM31 {
        preprocessing
            .rows
            .iter()
            .filter(|row| row.segment_mask == 1)
            .fold(QM31::zero(), |sum, row| {
                let draw =
                    operation_draw(execution, row).expect("fixture operation has a verifier draw");
                let mut tuple = vec![
                    M31::from(row.verifier_id),
                    M31::from(row.sequence),
                    M31::from(row.tag),
                    M31::from(row.args[0]),
                    M31::from(row.args[1]),
                    M31::from(row.args[2]),
                    M31::from(row.args[3]),
                ];
                tuple.extend(draw.map(|word| M31::from(word.as_u32())));
                let denominator: QM31 = relations.draw_output.combine(&tuple);
                sum + denominator.inverse()
            })
    }

    fn randomness_consumer_terms(
        preprocessing: &VerifierRandomnessPreprocessed,
        execution: &VerifierTranscriptExecution<RecordingTranscriptBackend>,
        relations: &VerifierRandomnessRelations,
        swap_verifier: bool,
        swap_kind: bool,
    ) -> QM31 {
        preprocessing
            .rows
            .iter()
            .filter(|row| row.segment_mask == 1)
            .flat_map(|row| {
                let draw =
                    operation_draw(execution, row).expect("fixture operation has a verifier draw");
                draw.into_iter()
                    .take(row.descriptor.word_count as usize)
                    .enumerate()
                    .map(move |(word_index, word)| {
                        let verifier_id = if swap_verifier {
                            LEFT_RECURSION_VERIFIER_ID
                        } else {
                            row.verifier_id
                        };
                        let kind = if swap_kind {
                            match row.descriptor.kind {
                                VerifierRandomnessKind::CompositionRandomness => {
                                    VerifierRandomnessKind::OodsPoint
                                }
                                VerifierRandomnessKind::OodsPoint => {
                                    VerifierRandomnessKind::CompositionRandomness
                                }
                                kind => kind,
                            }
                        } else {
                            row.descriptor.kind
                        };
                        let word_index =
                            u32::try_from(word_index).expect("draw word index fits u32");
                        let (item, semantic_word) = if row.descriptor.query_items {
                            (row.descriptor.item_base + word_index, 0)
                        } else {
                            (row.descriptor.item_base, word_index)
                        };
                        let denominator: QM31 = relations.word.combine(&[
                            M31::from(verifier_id),
                            M31::from(kind.as_u32()),
                            M31::from(item),
                            M31::from(semantic_word),
                            M31::from(word.as_u32()),
                        ]);
                        -denominator.inverse()
                    })
            })
            .fold(QM31::zero(), |sum, term| sum + term)
    }

    #[rstest]
    #[case::segment(ProofKind::SegmentLeaf)]
    #[case::binary(ProofKind::BinaryNode)]
    #[case::empty(ProofKind::EmptyLeaf)]
    fn every_universal_mode_satisfies_randomness_constraints(#[case] kind: ProofKind) {
        assert_constraints(kind, false);
    }

    #[rstest]
    #[should_panic]
    fn inactive_randomness_words_must_be_zero() {
        assert_constraints(ProofKind::EmptyLeaf, true);
    }

    #[rstest]
    fn transcript_draws_close_into_typed_randomness() {
        assert!(bridge_sum(false, false).is_zero());
    }

    #[rstest]
    fn randomness_kinds_cannot_be_swapped() {
        assert!(!bridge_sum(false, true).is_zero());
    }

    #[rstest]
    fn segment_randomness_cannot_move_to_a_recursion_lane() {
        assert!(!bridge_sum(true, false).is_zero());
    }

    #[rstest]
    fn fixture_plans_have_six_non_relation_draws_per_lane() {
        let (vm, recursion) = plans();
        let preprocessing = VerifierRandomnessPreprocessed::new(&vm, &recursion)
            .expect("fixture plans have canonical verifier draws");
        assert_eq!(
            (
                preprocessing.vm_draw_count(),
                preprocessing.recursion_draw_count()
            ),
            (6, 6)
        );
    }

    #[rstest]
    fn partial_query_block_exports_only_its_single_planned_word() {
        let vm = plan_with_nine_queries(VerifierSchema::Vm);
        let recursion = plan_with_nine_queries(VerifierSchema::Recursion);
        let preprocessing = VerifierRandomnessPreprocessed::new(&vm, &recursion)
            .expect("nine-query plans have canonical verifier draws");
        let query_rows = preprocessing
            .rows
            .iter()
            .filter(|row| {
                row.segment_mask == 1 && row.descriptor.kind == VerifierRandomnessKind::RawQuery
            })
            .map(|row| {
                (
                    row.descriptor.item_base,
                    row.descriptor.word_count,
                    row.descriptor.query_items,
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(query_rows, vec![(0, 8, true), (8, 1, true)]);
    }

    #[rstest]
    fn typed_draw_adapters_partition_every_transcript_draw() {
        let (vm, recursion) = plans();
        let relation = RelationChallengePreprocessed::new(&vm, &recursion)
            .expect("fixture relation draws are canonical");
        let randomness = VerifierRandomnessPreprocessed::new(&vm, &recursion)
            .expect("fixture verifier draws are canonical");
        let vm_draws = vm
            .steps()
            .iter()
            .filter(|step| step.transcript_effect() == Some(TranscriptEffect::Draw))
            .count();
        let recursion_draws = recursion
            .steps()
            .iter()
            .filter(|step| step.transcript_effect() == Some(TranscriptEffect::Draw))
            .count();
        assert_eq!(
            (
                relation.vm_challenge_count() as usize + randomness.vm_draw_count() as usize,
                relation.recursion_challenge_count() as usize
                    + randomness.recursion_draw_count() as usize,
            ),
            (vm_draws, recursion_draws)
        );
    }
}
