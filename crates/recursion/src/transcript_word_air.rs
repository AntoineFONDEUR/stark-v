//! Word-ownership AIR for the trusted recursion transcript layout.
//!
//! One universal row represents each padded frame word after the digest
//! prefix. Trusted preprocessing supplies headers, draw markers, delimiters,
//! and zero padding. Only declared payload slots use committed values, which
//! are delegated to semantic proof and public-input sources by an indexed
//! relation.

use core::fmt;

use simd::AlignedVec;
use stwo::core::ColumnVec;
use stwo::core::channel::Channel;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::QM31;
use stwo::core::poly::circle::CanonicCoset;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::relation;

use super::control_air::{
    LEFT_RECURSION_VERIFIER_ID, RIGHT_RECURSION_VERIFIER_ID, SEGMENT_VERIFIER_ID,
};
use super::transcript::{RecordingTranscriptBackend, TranscriptTrace};
use super::transcript_binding_air::{
    TranscriptBindingRelations, TranscriptCallPreprocessed, UniversalTranscriptWitness,
};
use super::transcript_layout::{TranscriptLayout, TranscriptLayoutError, TranscriptWordSource};
use super::transcript_program::VerifierTranscriptExecution;
use super::wire::ProofKind;

const DIGEST_WORDS: usize = 8;
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
const HASH_ID_COLUMN: usize = 10;
const WORD_INDEX_COLUMN: usize = 11;
const IS_PAYLOAD_COLUMN: usize = 12;
const PAYLOAD_INDEX_COLUMN: usize = 13;
const CONSTANT_COLUMN: usize = 14;
const PREPROCESSED_COLUMN_COUNT: usize = 15;

// One typed payload word scoped by verifier and exact control coordinates.
relation!(TranscriptPayloadWordRelation, 9);

/// Relation connecting frame payload slots to semantic input tables.
#[derive(Clone)]
pub struct TranscriptWordRelations {
    pub payload_word: TranscriptPayloadWordRelation,
}

impl TranscriptWordRelations {
    pub fn dummy() -> Self {
        Self {
            payload_word: TranscriptPayloadWordRelation::dummy(),
        }
    }

    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            payload_word: TranscriptPayloadWordRelation::draw(channel),
        }
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
    hash_id: u32,
    word_index: u32,
    is_payload: u32,
    payload_index: u32,
    constant: u32,
}

/// Universal non-digest word layout derived from the exact call preprocessing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TranscriptWordPreprocessed {
    log_size: u32,
    rows: Vec<PreprocessedRow>,
    vm_layout: TranscriptLayout,
    recursion_layout: TranscriptLayout,
}

impl TranscriptWordPreprocessed {
    pub fn new(calls: &TranscriptCallPreprocessed) -> Result<Self, TranscriptWordError> {
        let vm_layout = calls.vm_layout().clone();
        let recursion_layout = calls.recursion_layout().clone();
        let vm_word_count = non_digest_word_count(&vm_layout)?;
        let recursion_word_count = non_digest_word_count(&recursion_layout)?;
        let row_count = vm_word_count
            .checked_add(
                recursion_word_count
                    .checked_mul(2)
                    .ok_or(TranscriptWordError::RowCountOverflow)?,
            )
            .ok_or(TranscriptWordError::RowCountOverflow)?;
        let padded_rows = row_count
            .checked_next_power_of_two()
            .ok_or(TranscriptWordError::RowCountOverflow)?
            .max(1 << MIN_LOG_SIZE);
        let log_size = padded_rows.ilog2();
        if log_size > MAX_LOG_SIZE {
            return Err(TranscriptWordError::LogSizeOutOfRange { log_size });
        }

        let mut rows = Vec::with_capacity(row_count);
        append_layout_rows(&mut rows, &vm_layout, SEGMENT_VERIFIER_ID, 1, 0)?;
        append_layout_rows(
            &mut rows,
            &recursion_layout,
            LEFT_RECURSION_VERIFIER_ID,
            0,
            1,
        )?;
        append_layout_rows(
            &mut rows,
            &recursion_layout,
            RIGHT_RECURSION_VERIFIER_ID,
            0,
            1,
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

    pub fn active_word_count(&self, kind: ProofKind) -> usize {
        self.rows
            .iter()
            .filter(|row| match kind {
                ProofKind::SegmentLeaf => row.segment_mask == 1,
                ProofKind::BinaryNode => row.binary_mask == 1,
                ProofKind::EmptyLeaf => false,
            })
            .count()
    }

    pub fn active_payload_count(&self, kind: ProofKind) -> usize {
        self.rows
            .iter()
            .filter(|row| {
                row.is_payload == 1
                    && match kind {
                        ProofKind::SegmentLeaf => row.segment_mask == 1,
                        ProofKind::BinaryNode => row.binary_mask == 1,
                        ProofKind::EmptyLeaf => false,
                    }
            })
            .count()
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
            columns[SEQUENCE_COLUMN][index] = row.sequence;
            columns[TAG_COLUMN][index] = row.tag;
            columns[ARG_0_COLUMN][index] = row.args[0];
            columns[ARG_1_COLUMN][index] = row.args[1];
            columns[ARG_2_COLUMN][index] = row.args[2];
            columns[ARG_3_COLUMN][index] = row.args[3];
            columns[HASH_ID_COLUMN][index] = row.hash_id;
            columns[WORD_INDEX_COLUMN][index] = row.word_index;
            columns[IS_PAYLOAD_COLUMN][index] = row.is_payload;
            columns[PAYLOAD_INDEX_COLUMN][index] = row.payload_index;
            columns[CONSTANT_COLUMN][index] = row.constant;
        }
        let domain = CanonicCoset::new(self.log_size).circle_domain();
        columns
            .into_iter()
            .map(|column| CircleEvaluation::new(domain, BaseColumn::from(column)))
            .collect()
    }
}

fn non_digest_word_count(layout: &TranscriptLayout) -> Result<usize, TranscriptWordError> {
    layout.frames().iter().try_fold(0_usize, |total, frame| {
        let count = frame.words().len().checked_sub(DIGEST_WORDS).ok_or(
            TranscriptWordError::DigestPrefixMissing {
                hash_id: frame.hash_id(),
            },
        )?;
        total
            .checked_add(count)
            .ok_or(TranscriptWordError::RowCountOverflow)
    })
}

fn append_layout_rows(
    rows: &mut Vec<PreprocessedRow>,
    layout: &TranscriptLayout,
    verifier_id: u32,
    segment_mask: u32,
    binary_mask: u32,
) -> Result<(), TranscriptWordError> {
    for operation in layout.operations() {
        let first_frame = usize::try_from(operation.first_hash_id()).map_err(|_| {
            TranscriptWordError::FrameIndexOutOfRange {
                hash_id: operation.first_hash_id(),
            }
        })?;
        let frame_count = usize::try_from(operation.hash_count()).map_err(|_| {
            TranscriptWordError::FrameCountOutOfRange {
                count: operation.hash_count(),
            }
        })?;
        let frame_end = first_frame
            .checked_add(frame_count)
            .ok_or(TranscriptWordError::RowCountOverflow)?;
        let frames = layout.frames().get(first_frame..frame_end).ok_or(
            TranscriptWordError::OperationFrameRangeMissing {
                sequence: operation.sequence(),
            },
        )?;
        let encoded = operation.step().encode();
        let mut next_payload_index = 0_u32;
        for frame in frames {
            for limb in 0..DIGEST_WORDS {
                let expected_limb = u32::try_from(limb)
                    .map_err(|_| TranscriptWordError::WordIndexOutOfRange { word_index: limb })?;
                if frame.words().get(limb)
                    != Some(&TranscriptWordSource::Digest {
                        limb: expected_limb,
                    })
                {
                    return Err(TranscriptWordError::DigestPrefixMismatch {
                        hash_id: frame.hash_id(),
                        limb: expected_limb,
                    });
                }
            }
            for (word_index, source) in frame.words().iter().copied().enumerate().skip(DIGEST_WORDS)
            {
                let word_index_u32 = u32::try_from(word_index)
                    .map_err(|_| TranscriptWordError::WordIndexOutOfRange { word_index })?;
                let (is_payload, payload_index, constant) = match source {
                    TranscriptWordSource::Digest { .. } => {
                        return Err(TranscriptWordError::DigestOutsidePrefix {
                            hash_id: frame.hash_id(),
                            word_index: word_index_u32,
                        });
                    }
                    TranscriptWordSource::Payload { index } => {
                        if index != next_payload_index {
                            return Err(TranscriptWordError::PayloadIndexMismatch {
                                sequence: operation.sequence(),
                                expected: next_payload_index,
                                actual: index,
                            });
                        }
                        next_payload_index = next_payload_index
                            .checked_add(1)
                            .ok_or(TranscriptWordError::PayloadIndexOverflow)?;
                        (1, index, 0)
                    }
                    TranscriptWordSource::Constant(value) => (0, 0, value.as_u32()),
                };
                rows.push(PreprocessedRow {
                    segment_mask,
                    binary_mask,
                    verifier_id,
                    sequence: operation.sequence(),
                    tag: encoded.tag(),
                    args: encoded.args(),
                    hash_id: frame.hash_id(),
                    word_index: word_index_u32,
                    is_payload,
                    payload_index,
                    constant,
                });
            }
        }
        if next_payload_index != operation.payload_word_count() {
            return Err(TranscriptWordError::PayloadCountMismatch {
                sequence: operation.sequence(),
                expected: operation.payload_word_count(),
                actual: next_payload_index,
            });
        }
    }
    Ok(())
}

/// Relation instances used by the macro-generated transcript-word component.
#[derive(Clone)]
pub struct TranscriptWordComponentRelations {
    pub frame_word: super::transcript_binding_air::TranscriptFrameWordRelation,
    pub payload_word: TranscriptPayloadWordRelation,
}

impl TranscriptWordComponentRelations {
    /// Combine binding and payload-word relation instances.
    pub fn new(binding: &TranscriptBindingRelations, word: &TranscriptWordRelations) -> Self {
        Self {
            frame_word: binding.frame_word.clone(),
            payload_word: word.payload_word.clone(),
        }
    }
}

stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [],
    embedded_component: true,
    embedded_enabler_boolean: false,
    embedded_relations: crate::transcript_word_air::TranscriptWordComponentRelations,
    logup_batch: 2,
    embedded_preprocessed: {
        row_mask: "recursion_transcript_word_row_mask",
        segment_mask: "recursion_transcript_word_segment_mask",
        binary_mask: "recursion_transcript_word_binary_mask",
        verifier_id: "recursion_transcript_word_verifier_id",
        sequence: "recursion_transcript_word_sequence",
        tag: "recursion_transcript_word_tag",
        arg_0: "recursion_transcript_word_arg_0",
        arg_1: "recursion_transcript_word_arg_1",
        arg_2: "recursion_transcript_word_arg_2",
        arg_3: "recursion_transcript_word_arg_3",
        hash_id: "recursion_transcript_word_hash_id",
        word_index: "recursion_transcript_word_index",
        is_payload: "recursion_transcript_word_is_payload",
        payload_index: "recursion_transcript_word_payload_index",
        constant_value: "recursion_transcript_word_constant",
    },
    embedded_params: [segment_active, binary_active],

    relation frame_word(4);
    relation payload_word(9);

    fn transcript_word(
        value,
        row_mask, segment_mask, binary_mask, verifier_id,
        sequence, tag, arg_0, arg_1, arg_2, arg_3,
        hash_id, word_index, is_payload, payload_index, constant_value,
        segment_active, binary_active,
    ) {
        let active = segment_mask * segment_active + binary_mask * binary_active;
        let constant_mask = 1 - is_payload;

        constrain enabler - row_mask;
        constrain (row_mask - active) * value;
        constrain active * constant_mask * value;

        emit(active) frame_word(
            verifier_id,
            hash_id,
            word_index,
            value + constant_value,
        );
        consume(active * is_payload) payload_word(
            verifier_id, sequence, tag, arg_0, arg_1, arg_2, arg_3, payload_index, value,
        );

        return value;
    }
}

pub use component::air::{Component, Eval};

/// Construct the generated evaluator with verifier-owned mode selectors.
pub fn eval_for_proof_kind(
    log_size: u32,
    proof_kind: ProofKind,
    binding_relations: &TranscriptBindingRelations,
    word_relations: &TranscriptWordRelations,
) -> Eval {
    Eval {
        log_size,
        segment_active: BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        binary_active: BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode)),
        relations: TranscriptWordComponentRelations::new(binding_relations, word_relations),
    }
}

/// Generate fixed-word and payload-slot entries from the macro-defined frame.
pub fn gen_interaction_trace(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    preprocessed: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    proof_kind: ProofKind,
    binding_relations: &TranscriptBindingRelations,
    word_relations: &TranscriptWordRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    component::witness::gen_interaction_trace(
        trace,
        preprocessed,
        BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode)),
        &TranscriptWordComponentRelations::new(binding_relations, word_relations),
    )
}

/// Materializes only active payload words; fixed and inactive rows stay zero.
pub fn push_transcript_words(
    table: &mut TranscriptWordTable,
    preprocessed: &TranscriptWordPreprocessed,
    witness: UniversalTranscriptWitness<'_>,
) -> Result<(), TranscriptWordError> {
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
            verifier_id => return Err(TranscriptWordError::UnknownVerifierId { verifier_id }),
        };
        let value = if row.is_payload == 1 {
            if let Some(trace) = trace {
                let frame_index = usize::try_from(row.hash_id).map_err(|_| {
                    TranscriptWordError::FrameIndexOutOfRange {
                        hash_id: row.hash_id,
                    }
                })?;
                let word_index = usize::try_from(row.word_index).map_err(|_| {
                    TranscriptWordError::WordIndexDoesNotFitUsize {
                        word_index: row.word_index,
                    }
                })?;
                trace
                    .hash_frames
                    .get(frame_index)
                    .and_then(|frame| frame.words.get(word_index))
                    .copied()
                    .ok_or(TranscriptWordError::WordMissing {
                        verifier_id: row.verifier_id,
                        hash_id: row.hash_id,
                        word_index: row.word_index,
                    })?
                    .as_u32()
            } else {
                0
            }
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
) -> Result<&'a TranscriptTrace, TranscriptWordError> {
    layout
        .validate_execution(execution.operations(), execution.backend().trace())
        .map_err(TranscriptWordError::Layout)?;
    Ok(execution.backend().trace())
}

/// Invalid word preprocessing or witness materialization.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TranscriptWordError {
    Layout(TranscriptLayoutError),
    RowCountOverflow,
    LogSizeOutOfRange {
        log_size: u32,
    },
    DigestPrefixMissing {
        hash_id: u32,
    },
    DigestPrefixMismatch {
        hash_id: u32,
        limb: u32,
    },
    DigestOutsidePrefix {
        hash_id: u32,
        word_index: u32,
    },
    FrameIndexOutOfRange {
        hash_id: u32,
    },
    FrameCountOutOfRange {
        count: u32,
    },
    OperationFrameRangeMissing {
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
    UnknownVerifierId {
        verifier_id: u32,
    },
    WordMissing {
        verifier_id: u32,
        hash_id: u32,
        word_index: u32,
    },
}

impl fmt::Display for TranscriptWordError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Layout(error) => write!(formatter, "invalid transcript layout: {error}"),
            Self::RowCountOverflow => write!(formatter, "transcript word row count overflowed"),
            Self::LogSizeOutOfRange { log_size } => write!(
                formatter,
                "transcript word log size {log_size} exceeds the supported maximum {MAX_LOG_SIZE}"
            ),
            Self::DigestPrefixMissing { hash_id } => {
                write!(formatter, "transcript frame {hash_id} has no digest prefix")
            }
            Self::DigestPrefixMismatch { hash_id, limb } => write!(
                formatter,
                "transcript frame {hash_id} digest limb {limb} has the wrong source"
            ),
            Self::DigestOutsidePrefix {
                hash_id,
                word_index,
            } => write!(
                formatter,
                "transcript frame {hash_id} has digest source at word {word_index}"
            ),
            Self::FrameIndexOutOfRange { hash_id } => {
                write!(
                    formatter,
                    "transcript frame index {hash_id} does not fit usize"
                )
            }
            Self::FrameCountOutOfRange { count } => {
                write!(
                    formatter,
                    "transcript frame count {count} does not fit usize"
                )
            }
            Self::OperationFrameRangeMissing { sequence } => write!(
                formatter,
                "transcript operation {sequence} references missing frames"
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

impl std::error::Error for TranscriptWordError {}
