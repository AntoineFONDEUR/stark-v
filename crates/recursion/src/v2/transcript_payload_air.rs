//! Semantic payload adapter for the recursion V2 transcript.
//!
//! Each trusted payload slot has one fixed source class, item coordinate, and
//! limb coordinate. Protocol and PCS words are constrained directly from
//! verifier-owned constants. Statement and proof words are exported through
//! a scoped input relation so later verification gadgets must use the same
//! values that entered Fiat-Shamir.

use core::fmt;

use air::digest::{M31Word, ProtocolId};
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
use stwo_macros::define_component_tables;

use super::control_air::{
    LEFT_RECURSION_VERIFIER_ID, RIGHT_RECURSION_VERIFIER_ID, SEGMENT_VERIFIER_ID,
};
use super::kernel::{VerifierControlPlan, VerifierSchema, VerifierStep};
use super::protocol::CanonicalWords;
use super::transcript::{RecordingTranscriptBackend, TranscriptTrace};
use super::transcript_binding_air::{TranscriptCallPreprocessed, UniversalTranscriptWitness};
use super::transcript_layout::{TranscriptLayout, TranscriptLayoutError, TranscriptWordSource};
use super::transcript_program::VerifierTranscriptExecution;
use super::transcript_word_air::TranscriptWordRelations;
use super::wire::ProofKind;

const MIN_LOG_SIZE: u32 = 4;
const MAX_LOG_SIZE: u32 = 30;
const DIGEST_WORDS: usize = 8;
const QM31_WORDS: u32 = 4;

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
const PAYLOAD_INDEX_COLUMN: usize = 10;
const SOURCE_KIND_COLUMN: usize = 11;
const ITEM_INDEX_COLUMN: usize = 12;
const LIMB_INDEX_COLUMN: usize = 13;
const CONSTANT_MASK_COLUMN: usize = 14;
const INPUT_MASK_COLUMN: usize = 15;
const CONSTANT_COLUMN: usize = 16;
const VM_AIR_CLAIMED_SUM_MASK_COLUMN: usize = 17;
const PREPROCESSED_COLUMN_COUNT: usize = 18;

const PREPROCESSED_COLUMN_IDS: [&str; PREPROCESSED_COLUMN_COUNT] = [
    "recursion_v2_transcript_payload_row_mask",
    "recursion_v2_transcript_payload_segment_mask",
    "recursion_v2_transcript_payload_binary_mask",
    "recursion_v2_transcript_payload_verifier_id",
    "recursion_v2_transcript_payload_sequence",
    "recursion_v2_transcript_payload_tag",
    "recursion_v2_transcript_payload_arg_0",
    "recursion_v2_transcript_payload_arg_1",
    "recursion_v2_transcript_payload_arg_2",
    "recursion_v2_transcript_payload_arg_3",
    "recursion_v2_transcript_payload_index",
    "recursion_v2_transcript_payload_source_kind",
    "recursion_v2_transcript_payload_item_index",
    "recursion_v2_transcript_payload_limb_index",
    "recursion_v2_transcript_payload_constant_mask",
    "recursion_v2_transcript_payload_input_mask",
    "recursion_v2_transcript_payload_constant",
    "recursion_v2_transcript_payload_vm_air_claimed_sum_mask",
];

define_component_tables! {
    transcript_payload: {
        committed: { value },
        constraints: {},
    },
}

use prover_columns::TranscriptPayloadColumns;

// One shared verifier input word: verifier, source, item, limb, and value.
relation!(VerifierInputWordRelation, 5);

/// Relation connecting transcript payloads to public and proof input tables.
#[derive(Clone)]
pub struct VerifierInputRelations {
    pub input_word: VerifierInputWordRelation,
}

impl VerifierInputRelations {
    pub fn dummy() -> Self {
        Self {
            input_word: VerifierInputWordRelation::dummy(),
        }
    }

    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            input_word: VerifierInputWordRelation::draw(channel),
        }
    }
}

/// Non-interchangeable source classes for transcript payload words.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum VerifierInputKind {
    Protocol = 1,
    Statement = 2,
    PcsParameters = 3,
    Commitment = 4,
    ClaimedSum = 5,
    SampledValue = 6,
    FriCommitment = 7,
    LastLayerCoefficient = 8,
    InteractionPowNonce = 9,
    PcsPowNonce = 10,
    VmPublicClaimDigest = 11,
    VmAirClaimedSum = 12,
}

impl VerifierInputKind {
    pub const fn as_u32(self) -> u32 {
        self as u32
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PayloadSource {
    kind: VerifierInputKind,
    item_index: u32,
    limb_index: u32,
    constant: Option<M31Word>,
}

impl PayloadSource {
    const fn requires_input_relation(self) -> bool {
        matches!(
            self.kind,
            VerifierInputKind::Statement
                | VerifierInputKind::Commitment
                | VerifierInputKind::ClaimedSum
                | VerifierInputKind::SampledValue
                | VerifierInputKind::FriCommitment
                | VerifierInputKind::LastLayerCoefficient
                | VerifierInputKind::VmPublicClaimDigest
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PreprocessedRow {
    segment_mask: u32,
    binary_mask: u32,
    verifier_id: u32,
    sequence: u32,
    tag: u32,
    args: [u32; 4],
    payload_index: u32,
    source: PayloadSource,
    hash_id: u32,
    word_index: u32,
}

#[derive(Clone, Copy)]
struct LaneContext<'a> {
    plan: &'a VerifierControlPlan,
    protocol_words: &'a [M31Word; DIGEST_WORDS],
    verifier_id: u32,
    segment_mask: u32,
    binary_mask: u32,
}

/// Universal payload-source layout for one protocol and two verifier plans.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TranscriptPayloadPreprocessed {
    log_size: u32,
    rows: Vec<PreprocessedRow>,
    vm_layout: TranscriptLayout,
    recursion_layout: TranscriptLayout,
}

impl TranscriptPayloadPreprocessed {
    pub fn new(
        calls: &TranscriptCallPreprocessed,
        protocol_id: ProtocolId,
    ) -> Result<Self, TranscriptPayloadError> {
        let vm_layout = calls.vm_layout().clone();
        let recursion_layout = calls.recursion_layout().clone();
        let vm_count = payload_count(&vm_layout)?;
        let recursion_count = payload_count(&recursion_layout)?;
        let row_count = vm_count
            .checked_add(
                recursion_count
                    .checked_mul(2)
                    .ok_or(TranscriptPayloadError::RowCountOverflow)?,
            )
            .ok_or(TranscriptPayloadError::RowCountOverflow)?;
        let padded_rows = row_count
            .checked_next_power_of_two()
            .ok_or(TranscriptPayloadError::RowCountOverflow)?
            .max(1 << MIN_LOG_SIZE);
        let log_size = padded_rows.ilog2();
        if log_size > MAX_LOG_SIZE {
            return Err(TranscriptPayloadError::LogSizeOutOfRange { log_size });
        }

        let protocol_words = *protocol_id.digest().words();
        let mut rows = Vec::with_capacity(row_count);
        append_layout_rows(
            &mut rows,
            &vm_layout,
            LaneContext {
                plan: calls.vm_plan(),
                protocol_words: &protocol_words,
                verifier_id: SEGMENT_VERIFIER_ID,
                segment_mask: 1,
                binary_mask: 0,
            },
        )?;
        append_layout_rows(
            &mut rows,
            &recursion_layout,
            LaneContext {
                plan: calls.recursion_plan(),
                protocol_words: &protocol_words,
                verifier_id: LEFT_RECURSION_VERIFIER_ID,
                segment_mask: 0,
                binary_mask: 1,
            },
        )?;
        append_layout_rows(
            &mut rows,
            &recursion_layout,
            LaneContext {
                plan: calls.recursion_plan(),
                protocol_words: &protocol_words,
                verifier_id: RIGHT_RECURSION_VERIFIER_ID,
                segment_mask: 0,
                binary_mask: 1,
            },
        )?;
        Ok(Self {
            log_size,
            rows,
            vm_layout,
            recursion_layout,
        })
    }

    pub const fn log_size(&self) -> u32 {
        self.log_size
    }

    pub fn active_payload_count(&self, kind: ProofKind) -> usize {
        self.rows
            .iter()
            .filter(|row| match kind {
                ProofKind::SegmentLeaf => row.segment_mask == 1,
                ProofKind::BinaryNode => row.binary_mask == 1,
                ProofKind::EmptyLeaf => false,
            })
            .count()
    }

    pub fn active_input_count(&self, kind: ProofKind) -> usize {
        self.rows
            .iter()
            .filter(|row| {
                row.source.requires_input_relation()
                    && match kind {
                        ProofKind::SegmentLeaf => row.segment_mask == 1,
                        ProofKind::BinaryNode => row.binary_mask == 1,
                        ProofKind::EmptyLeaf => false,
                    }
            })
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
            columns[SEGMENT_MASK_COLUMN][index] = row.segment_mask;
            columns[BINARY_MASK_COLUMN][index] = row.binary_mask;
            columns[VERIFIER_ID_COLUMN][index] = row.verifier_id;
            columns[SEQUENCE_COLUMN][index] = row.sequence;
            columns[TAG_COLUMN][index] = row.tag;
            columns[ARG_0_COLUMN][index] = row.args[0];
            columns[ARG_1_COLUMN][index] = row.args[1];
            columns[ARG_2_COLUMN][index] = row.args[2];
            columns[ARG_3_COLUMN][index] = row.args[3];
            columns[PAYLOAD_INDEX_COLUMN][index] = row.payload_index;
            columns[SOURCE_KIND_COLUMN][index] = row.source.kind.as_u32();
            columns[ITEM_INDEX_COLUMN][index] = row.source.item_index;
            columns[LIMB_INDEX_COLUMN][index] = row.source.limb_index;
            columns[CONSTANT_MASK_COLUMN][index] = u32::from(row.source.constant.is_some());
            columns[INPUT_MASK_COLUMN][index] = u32::from(row.source.requires_input_relation());
            columns[CONSTANT_COLUMN][index] = row.source.constant.unwrap_or(M31Word::ZERO).as_u32();
            columns[VM_AIR_CLAIMED_SUM_MASK_COLUMN][index] = u32::from(
                row.verifier_id == SEGMENT_VERIFIER_ID
                    && row.source.kind == VerifierInputKind::ClaimedSum,
            );
        }
        let domain = CanonicCoset::new(self.log_size).circle_domain();
        columns
            .into_iter()
            .map(|column| CircleEvaluation::new(domain, BaseColumn::from(column)))
            .collect()
    }
}

fn payload_count(layout: &TranscriptLayout) -> Result<usize, TranscriptPayloadError> {
    layout
        .operations()
        .iter()
        .try_fold(0_usize, |total, operation| {
            let count = usize::try_from(operation.payload_word_count()).map_err(|_| {
                TranscriptPayloadError::PayloadCountOutOfRange {
                    count: operation.payload_word_count(),
                }
            })?;
            total
                .checked_add(count)
                .ok_or(TranscriptPayloadError::RowCountOverflow)
        })
}

fn append_layout_rows(
    rows: &mut Vec<PreprocessedRow>,
    layout: &TranscriptLayout,
    lane: LaneContext<'_>,
) -> Result<(), TranscriptPayloadError> {
    for operation in layout.operations() {
        let first_frame = usize::try_from(operation.first_hash_id()).map_err(|_| {
            TranscriptPayloadError::FrameIndexOutOfRange {
                hash_id: operation.first_hash_id(),
            }
        })?;
        let frame = layout.frames().get(first_frame).ok_or(
            TranscriptPayloadError::OperationFrameMissing {
                sequence: operation.sequence(),
            },
        )?;
        let encoded = operation.step().encode();
        let mut found = 0_u32;
        for (word_index, source) in frame.words().iter().copied().enumerate() {
            let TranscriptWordSource::Payload { index } = source else {
                continue;
            };
            if index != found {
                return Err(TranscriptPayloadError::PayloadIndexMismatch {
                    sequence: operation.sequence(),
                    expected: found,
                    actual: index,
                });
            }
            let word_index = u32::try_from(word_index)
                .map_err(|_| TranscriptPayloadError::WordIndexOutOfRange { word_index })?;
            rows.push(PreprocessedRow {
                segment_mask: lane.segment_mask,
                binary_mask: lane.binary_mask,
                verifier_id: lane.verifier_id,
                sequence: operation.sequence(),
                tag: encoded.tag(),
                args: encoded.args(),
                payload_index: index,
                source: payload_source(lane.plan, lane.protocol_words, operation.step(), index)?,
                hash_id: frame.hash_id(),
                word_index,
            });
            found = found
                .checked_add(1)
                .ok_or(TranscriptPayloadError::PayloadIndexOverflow)?;
        }
        if found != operation.payload_word_count() {
            return Err(TranscriptPayloadError::PayloadCountMismatch {
                sequence: operation.sequence(),
                expected: operation.payload_word_count(),
                actual: found,
            });
        }
    }
    Ok(())
}

fn payload_source(
    plan: &VerifierControlPlan,
    protocol_words: &[M31Word; DIGEST_WORDS],
    step: VerifierStep,
    payload_index: u32,
) -> Result<PayloadSource, TranscriptPayloadError> {
    let dynamic = |kind, item_index, limb_index| PayloadSource {
        kind,
        item_index,
        limb_index,
        constant: None,
    };
    let constant = |kind, value| PayloadSource {
        kind,
        item_index: 0,
        limb_index: payload_index,
        constant: Some(value),
    };
    let source = match step {
        VerifierStep::BindProtocol => constant(
            VerifierInputKind::Protocol,
            indexed_word("protocol", protocol_words, payload_index)?,
        ),
        VerifierStep::BindStatement => dynamic(VerifierInputKind::Statement, 0, payload_index),
        VerifierStep::BindPcsParameters => constant(
            VerifierInputKind::PcsParameters,
            indexed_word(
                "PCS parameters",
                &plan.pcs_parameters().canonical_words(),
                payload_index,
            )?,
        ),
        VerifierStep::AbsorbTraceCommitment { tree, .. } => {
            require_payload_width("commitment", payload_index, DIGEST_WORDS as u32)?;
            dynamic(VerifierInputKind::Commitment, tree, payload_index)
        }
        VerifierStep::VerifyAndAbsorbInteractionPow { .. } => {
            require_payload_width("interaction PoW nonce", payload_index, QM31_WORDS)?;
            dynamic(VerifierInputKind::InteractionPowNonce, 0, payload_index)
        }
        VerifierStep::AbsorbClaimedSums { count } => {
            indexed_qm31_source(VerifierInputKind::ClaimedSum, payload_index, count)?
        }
        VerifierStep::AbsorbSampledValues { count } => {
            indexed_qm31_source(VerifierInputKind::SampledValue, payload_index, count)?
        }
        VerifierStep::AbsorbFriCommitment { layer } => {
            require_payload_width("FRI commitment", payload_index, DIGEST_WORDS as u32)?;
            dynamic(VerifierInputKind::FriCommitment, layer, payload_index)
        }
        VerifierStep::AbsorbLastLayerCoefficients { count } => indexed_qm31_source(
            VerifierInputKind::LastLayerCoefficient,
            payload_index,
            count,
        )?,
        VerifierStep::VerifyAndAbsorbPcsPow { .. } => {
            require_payload_width("PCS PoW nonce", payload_index, QM31_WORDS)?;
            dynamic(VerifierInputKind::PcsPowNonce, 0, payload_index)
        }
        VerifierStep::AbsorbPublicClaim => {
            if plan.schema() != VerifierSchema::Vm {
                return Err(TranscriptPayloadError::UnexpectedPayload {
                    step,
                    payload_index,
                });
            }
            require_payload_width("VM public claim digest", payload_index, DIGEST_WORDS as u32)?;
            dynamic(VerifierInputKind::VmPublicClaimDigest, 0, payload_index)
        }
        VerifierStep::DrawRelationChallenge { .. }
        | VerifierStep::DrawCompositionRandomness
        | VerifierStep::DrawOodsPoint
        | VerifierStep::DrawDeepRandomness
        | VerifierStep::DrawFriAlpha { .. }
        | VerifierStep::DrawQueryBlock { .. }
        | VerifierStep::AccumulatePublicLogupTerm { .. }
        | VerifierStep::AssertGlobalLogupZero
        | VerifierStep::EvaluateAirInstruction { .. }
        | VerifierStep::AssertComposition { .. }
        | VerifierStep::VerifyTraceMerklePath { .. }
        | VerifierStep::EvaluateDeepQuotient { .. }
        | VerifierStep::VerifyFriMerklePath { .. }
        | VerifierStep::FoldFri { .. }
        | VerifierStep::VerifyLastLayer { .. }
        | VerifierStep::CloseRelation { .. }
        | VerifierStep::Complete => {
            return Err(TranscriptPayloadError::UnexpectedPayload {
                step,
                payload_index,
            });
        }
    };
    Ok(source)
}

fn indexed_qm31_source(
    kind: VerifierInputKind,
    payload_index: u32,
    item_count: u32,
) -> Result<PayloadSource, TranscriptPayloadError> {
    let payload_count = item_count
        .checked_mul(QM31_WORDS)
        .ok_or(TranscriptPayloadError::PayloadIndexOverflow)?;
    require_payload_width("QM31 array", payload_index, payload_count)?;
    Ok(PayloadSource {
        kind,
        item_index: payload_index / QM31_WORDS,
        limb_index: payload_index % QM31_WORDS,
        constant: None,
    })
}

fn indexed_word(
    field: &'static str,
    words: &[M31Word],
    index: u32,
) -> Result<M31Word, TranscriptPayloadError> {
    let index = usize::try_from(index)
        .map_err(|_| TranscriptPayloadError::PayloadIndexDoesNotFitUsize { index })?;
    words
        .get(index)
        .copied()
        .ok_or(TranscriptPayloadError::ConstantWordMissing {
            field,
            index,
            len: words.len(),
        })
}

fn require_payload_width(
    field: &'static str,
    index: u32,
    width: u32,
) -> Result<(), TranscriptPayloadError> {
    if index >= width {
        return Err(TranscriptPayloadError::PayloadWidthExceeded {
            field,
            index,
            width,
        });
    }
    Ok(())
}

pub type Component = FrameworkComponent<Eval>;

#[derive(Clone)]
pub struct Eval {
    pub log_size: u32,
    pub proof_kind: ProofKind,
    pub word_relations: TranscriptWordRelations,
    pub input_relations: VerifierInputRelations,
}

impl FrameworkEval for Eval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let cols = TranscriptPayloadColumns::from_eval(&mut eval);
        let column_ids = TranscriptPayloadPreprocessed::column_ids();
        let row_mask = eval.get_preprocessed_column(column_ids[ROW_MASK_COLUMN].clone());
        let segment_mask = eval.get_preprocessed_column(column_ids[SEGMENT_MASK_COLUMN].clone());
        let binary_mask = eval.get_preprocessed_column(column_ids[BINARY_MASK_COLUMN].clone());
        let verifier_id = eval.get_preprocessed_column(column_ids[VERIFIER_ID_COLUMN].clone());
        let sequence = eval.get_preprocessed_column(column_ids[SEQUENCE_COLUMN].clone());
        let tag = eval.get_preprocessed_column(column_ids[TAG_COLUMN].clone());
        let arg_0 = eval.get_preprocessed_column(column_ids[ARG_0_COLUMN].clone());
        let arg_1 = eval.get_preprocessed_column(column_ids[ARG_1_COLUMN].clone());
        let arg_2 = eval.get_preprocessed_column(column_ids[ARG_2_COLUMN].clone());
        let arg_3 = eval.get_preprocessed_column(column_ids[ARG_3_COLUMN].clone());
        let payload_index = eval.get_preprocessed_column(column_ids[PAYLOAD_INDEX_COLUMN].clone());
        let source_kind = eval.get_preprocessed_column(column_ids[SOURCE_KIND_COLUMN].clone());
        let item_index = eval.get_preprocessed_column(column_ids[ITEM_INDEX_COLUMN].clone());
        let limb_index = eval.get_preprocessed_column(column_ids[LIMB_INDEX_COLUMN].clone());
        let constant_mask = eval.get_preprocessed_column(column_ids[CONSTANT_MASK_COLUMN].clone());
        let input_mask = eval.get_preprocessed_column(column_ids[INPUT_MASK_COLUMN].clone());
        let constant = eval.get_preprocessed_column(column_ids[CONSTANT_COLUMN].clone());
        let vm_air_claimed_sum_mask =
            eval.get_preprocessed_column(column_ids[VM_AIR_CLAIMED_SUM_MASK_COLUMN].clone());
        eval.add_constraint(cols.enabler.clone() - row_mask.clone());

        let segment_active = BaseField::from(u32::from(self.proof_kind == ProofKind::SegmentLeaf));
        let binary_active = BaseField::from(u32::from(self.proof_kind == ProofKind::BinaryNode));
        let active = segment_mask * segment_active + binary_mask * binary_active;
        let shared_input = active.clone() * input_mask;
        eval.add_constraint((row_mask - active.clone()) * cols.value.clone());
        eval.add_constraint(active.clone() * constant_mask * (cols.value.clone() - constant));

        eval.add_to_relation(RelationEntry::new(
            &self.word_relations.payload_word,
            E::EF::from(active.clone()),
            &[
                verifier_id.clone(),
                sequence,
                tag,
                arg_0,
                arg_1,
                arg_2,
                arg_3,
                payload_index,
                cols.value.clone(),
            ],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.input_relations.input_word,
            E::EF::from(shared_input),
            &[
                verifier_id.clone(),
                source_kind,
                item_index.clone(),
                limb_index.clone(),
                cols.value.clone(),
            ],
        ));

        eval.add_to_relation(RelationEntry::new(
            &self.input_relations.input_word,
            E::EF::from(active * vm_air_claimed_sum_mask),
            &[
                verifier_id,
                E::F::from(BaseField::from(VerifierInputKind::VmAirClaimedSum.as_u32())),
                item_index,
                limb_index,
                cols.value,
            ],
        ));

        eval.finalize_logup_in_pairs();
        eval
    }
}

/// Generates all transcript-payload and dynamic-input relation fractions.
pub fn gen_interaction_trace(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    preprocessed: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    proof_kind: ProofKind,
    word_relations: &TranscriptWordRelations,
    input_relations: &VerifierInputRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    let cols =
        TranscriptPayloadColumns::from_iter(trace.iter().map(|evaluation| &evaluation.values.data));
    let pp = preprocessed
        .iter()
        .map(|column| &column.values.data)
        .collect::<Vec<_>>();
    let simd_size = cols.enabler.len();
    let log_size = trace[0].domain.log_size();
    let segment_active = BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf));
    let binary_active = BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode));
    let active: Vec<PackedQM31> = (0..simd_size)
        .map(|row| {
            PackedQM31::from(
                pp[SEGMENT_MASK_COLUMN][row] * segment_active
                    + pp[BINARY_MASK_COLUMN][row] * binary_active,
            )
        })
        .collect();
    let shared_input: Vec<PackedQM31> = (0..simd_size)
        .map(|row| active[row] * PackedQM31::from(pp[INPUT_MASK_COLUMN][row]))
        .collect();
    let vm_air_claimed_sum: Vec<PackedQM31> = (0..simd_size)
        .map(|row| active[row] * PackedQM31::from(pp[VM_AIR_CLAIMED_SUM_MASK_COLUMN][row]))
        .collect();

    let payload_denom = combine!(
        word_relations.payload_word,
        [
            pp[VERIFIER_ID_COLUMN],
            pp[SEQUENCE_COLUMN],
            pp[TAG_COLUMN],
            pp[ARG_0_COLUMN],
            pp[ARG_1_COLUMN],
            pp[ARG_2_COLUMN],
            pp[ARG_3_COLUMN],
            pp[PAYLOAD_INDEX_COLUMN],
            cols.value
        ]
    );
    let input_denom = combine!(
        input_relations.input_word,
        [
            pp[VERIFIER_ID_COLUMN],
            pp[SOURCE_KIND_COLUMN],
            pp[ITEM_INDEX_COLUMN],
            pp[LIMB_INDEX_COLUMN],
            cols.value
        ]
    );
    let vm_air_claimed_sum_kind = vec![
        stwo::prover::backend::simd::m31::PackedM31::broadcast(
            BaseField::from(VerifierInputKind::VmAirClaimedSum.as_u32(),)
        );
        simd_size
    ];
    let vm_air_claimed_sum_denom = combine!(
        input_relations.input_word,
        [
            pp[VERIFIER_ID_COLUMN],
            vm_air_claimed_sum_kind,
            pp[ITEM_INDEX_COLUMN],
            pp[LIMB_INDEX_COLUMN],
            cols.value
        ]
    );

    let mut logup_gen = LogupTraceGenerator::new(log_size);
    write_pair!(
        &active,
        &payload_denom,
        &shared_input,
        &input_denom,
        logup_gen
    );
    write_col!(&vm_air_claimed_sum, &vm_air_claimed_sum_denom, logup_gen);
    logup_gen.finalize_last()
}

/// Materializes active payload values from validated transcript executions.
pub fn push_transcript_payloads(
    table: &mut TranscriptPayloadTable,
    preprocessed: &TranscriptPayloadPreprocessed,
    witness: UniversalTranscriptWitness<'_>,
) -> Result<(), TranscriptPayloadError> {
    let (segment, left, right) = match witness {
        UniversalTranscriptWitness::Segment(execution) => (
            Some(validated_trace(&preprocessed.vm_layout, execution)?),
            None,
            None,
        ),
        UniversalTranscriptWitness::Binary { left, right } => (
            None,
            Some(validated_trace(&preprocessed.recursion_layout, left)?),
            Some(validated_trace(&preprocessed.recursion_layout, right)?),
        ),
        UniversalTranscriptWitness::Empty => (None, None, None),
    };

    for row in &preprocessed.rows {
        let trace = match row.verifier_id {
            SEGMENT_VERIFIER_ID => segment,
            LEFT_RECURSION_VERIFIER_ID => left,
            RIGHT_RECURSION_VERIFIER_ID => right,
            verifier_id => return Err(TranscriptPayloadError::UnknownVerifierId { verifier_id }),
        };
        let value = if let Some(trace) = trace {
            let frame_index = usize::try_from(row.hash_id).map_err(|_| {
                TranscriptPayloadError::FrameIndexOutOfRange {
                    hash_id: row.hash_id,
                }
            })?;
            let word_index = usize::try_from(row.word_index).map_err(|_| {
                TranscriptPayloadError::WordIndexDoesNotFitUsize {
                    word_index: row.word_index,
                }
            })?;
            trace
                .hash_frames
                .get(frame_index)
                .and_then(|frame| frame.words.get(word_index))
                .copied()
                .ok_or(TranscriptPayloadError::WordMissing {
                    verifier_id: row.verifier_id,
                    hash_id: row.hash_id,
                    word_index: row.word_index,
                })?
                .as_u32()
        } else {
            0
        };
        table.push(value);
    }
    Ok(())
}

fn validated_trace<'a>(
    layout: &TranscriptLayout,
    execution: &'a VerifierTranscriptExecution<RecordingTranscriptBackend>,
) -> Result<&'a TranscriptTrace, TranscriptPayloadError> {
    layout
        .validate_execution(execution.operations(), execution.backend().trace())
        .map_err(TranscriptPayloadError::Layout)?;
    Ok(execution.backend().trace())
}

/// Invalid payload preprocessing or witness materialization.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TranscriptPayloadError {
    Layout(TranscriptLayoutError),
    RowCountOverflow,
    LogSizeOutOfRange {
        log_size: u32,
    },
    PayloadCountOutOfRange {
        count: u32,
    },
    FrameIndexOutOfRange {
        hash_id: u32,
    },
    OperationFrameMissing {
        sequence: u32,
    },
    WordIndexOutOfRange {
        word_index: usize,
    },
    WordIndexDoesNotFitUsize {
        word_index: u32,
    },
    PayloadIndexMismatch {
        sequence: u32,
        expected: u32,
        actual: u32,
    },
    PayloadIndexOverflow,
    PayloadCountMismatch {
        sequence: u32,
        expected: u32,
        actual: u32,
    },
    PayloadIndexDoesNotFitUsize {
        index: u32,
    },
    ConstantWordMissing {
        field: &'static str,
        index: usize,
        len: usize,
    },
    PayloadWidthExceeded {
        field: &'static str,
        index: u32,
        width: u32,
    },
    UnexpectedPayload {
        step: VerifierStep,
        payload_index: u32,
    },
    UnknownVerifierId {
        verifier_id: u32,
    },
    WordMissing {
        verifier_id: u32,
        hash_id: u32,
        word_index: u32,
    },
}

impl fmt::Display for TranscriptPayloadError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Layout(error) => write!(formatter, "invalid transcript layout: {error}"),
            Self::RowCountOverflow => write!(formatter, "transcript payload row count overflowed"),
            Self::LogSizeOutOfRange { log_size } => write!(
                formatter,
                "transcript payload log size {log_size} exceeds the supported maximum {MAX_LOG_SIZE}"
            ),
            Self::PayloadCountOutOfRange { count } => {
                write!(
                    formatter,
                    "transcript payload count {count} does not fit usize"
                )
            }
            Self::FrameIndexOutOfRange { hash_id } => {
                write!(
                    formatter,
                    "transcript frame index {hash_id} does not fit usize"
                )
            }
            Self::OperationFrameMissing { sequence } => write!(
                formatter,
                "transcript operation {sequence} has no mix frame"
            ),
            Self::WordIndexOutOfRange { word_index } => {
                write!(
                    formatter,
                    "transcript word index {word_index} does not fit u32"
                )
            }
            Self::WordIndexDoesNotFitUsize { word_index } => write!(
                formatter,
                "transcript word index {word_index} does not fit usize"
            ),
            Self::PayloadIndexMismatch {
                sequence,
                expected,
                actual,
            } => write!(
                formatter,
                "transcript operation {sequence} payload index is {actual}, expected {expected}"
            ),
            Self::PayloadIndexOverflow => write!(formatter, "transcript payload index overflowed"),
            Self::PayloadCountMismatch {
                sequence,
                expected,
                actual,
            } => write!(
                formatter,
                "transcript operation {sequence} has {actual} payload words, expected {expected}"
            ),
            Self::PayloadIndexDoesNotFitUsize { index } => {
                write!(
                    formatter,
                    "transcript payload index {index} does not fit usize"
                )
            }
            Self::ConstantWordMissing { field, index, len } => write!(
                formatter,
                "{field} payload index {index} exceeds length {len}"
            ),
            Self::PayloadWidthExceeded {
                field,
                index,
                width,
            } => write!(
                formatter,
                "{field} payload index {index} exceeds width {width}"
            ),
            Self::UnexpectedPayload {
                step,
                payload_index,
            } => write!(
                formatter,
                "non-payload verifier step {step:?} has payload index {payload_index}"
            ),
            Self::UnknownVerifierId { verifier_id } => {
                write!(formatter, "unknown transcript verifier id {verifier_id}")
            }
            Self::WordMissing {
                verifier_id,
                hash_id,
                word_index,
            } => write!(
                formatter,
                "transcript verifier {verifier_id} frame {hash_id} has no word {word_index}"
            ),
        }
    }
}

impl std::error::Error for TranscriptPayloadError {}
