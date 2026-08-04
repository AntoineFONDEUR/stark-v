//! Digest-state AIR for the trusted recursion transcript layout.
//!
//! One universal row represents each fixed transcript frame. Mix outputs
//! advance the persistent digest, draw frames consume that digest without
//! changing it, and the first mix starts from zero. The component consumes
//! every verified frame output, supplies the first eight frame words, and
//! exposes only protocol draw outputs to downstream verifier gadgets.

use core::fmt;

use air::digest::M31Word;
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
use super::transcript::{HashPurpose, RecordingTranscriptBackend, TranscriptTrace};
use super::transcript_binding_air::{
    TranscriptBindingRelations, TranscriptCallPreprocessed, UniversalTranscriptWitness,
};
use super::transcript_layout::{TranscriptLayout, TranscriptLayoutError};
use super::transcript_program::{TranscriptEffect, VerifierTranscriptExecution};
use super::wire::ProofKind;

const RATE: usize = 8;
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
const INPUT_STATE_KEY_COLUMN: usize = 11;
const OUTPUT_STATE_KEY_COLUMN: usize = 12;
const INITIAL_MASK_COLUMN: usize = 13;
const STATE_CONSUME_MASK_COLUMN: usize = 14;
const STATE_PRODUCE_MULTIPLICITY_COLUMN: usize = 15;
const DRAW_OUTPUT_MASK_COLUMN: usize = 16;
const PREPROCESSED_COLUMN_COUNT: usize = 17;

// Persistent digest state: verifier, operation boundary, and eight words.
relation!(TranscriptDigestStateRelation, 10);
// One protocol draw: verifier, control coordinates, and eight output words.
relation!(TranscriptDrawOutputRelation, 15);

/// Relations connecting frame state to downstream verifier gadgets.
#[derive(Clone)]
pub struct TranscriptStateRelations {
    pub digest_state: TranscriptDigestStateRelation,
    pub draw_output: TranscriptDrawOutputRelation,
}

impl TranscriptStateRelations {
    pub fn dummy() -> Self {
        Self {
            digest_state: TranscriptDigestStateRelation::dummy(),
            draw_output: TranscriptDrawOutputRelation::dummy(),
        }
    }

    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            digest_state: TranscriptDigestStateRelation::draw(channel),
            draw_output: TranscriptDrawOutputRelation::draw(channel),
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
    input_state_key: u32,
    output_state_key: u32,
    initial_mask: u32,
    state_consume_mask: u32,
    state_produce_multiplicity: u32,
    draw_output_mask: u32,
}

/// Universal frame layout derived from the exact call preprocessing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TranscriptStatePreprocessed {
    log_size: u32,
    rows: Vec<PreprocessedRow>,
    vm_layout: TranscriptLayout,
    recursion_layout: TranscriptLayout,
}

impl TranscriptStatePreprocessed {
    pub fn new(calls: &TranscriptCallPreprocessed) -> Result<Self, TranscriptStateError> {
        let vm_layout = calls.vm_layout().clone();
        let recursion_layout = calls.recursion_layout().clone();
        let row_count = vm_layout
            .frames()
            .len()
            .checked_add(
                recursion_layout
                    .frames()
                    .len()
                    .checked_mul(2)
                    .ok_or(TranscriptStateError::RowCountOverflow)?,
            )
            .ok_or(TranscriptStateError::RowCountOverflow)?;
        let padded_rows = row_count
            .checked_next_power_of_two()
            .ok_or(TranscriptStateError::RowCountOverflow)?
            .max(1 << MIN_LOG_SIZE);
        let log_size = padded_rows.ilog2();
        if log_size > MAX_LOG_SIZE {
            return Err(TranscriptStateError::LogSizeOutOfRange { log_size });
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

    pub fn active_frame_count(&self, kind: ProofKind) -> usize {
        self.rows
            .iter()
            .filter(|row| match kind {
                ProofKind::SegmentLeaf => row.segment_mask == 1,
                ProofKind::BinaryNode => row.binary_mask == 1,
                ProofKind::EmptyLeaf => false,
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
            columns[INPUT_STATE_KEY_COLUMN][index] = row.input_state_key;
            columns[OUTPUT_STATE_KEY_COLUMN][index] = row.output_state_key;
            columns[INITIAL_MASK_COLUMN][index] = row.initial_mask;
            columns[STATE_CONSUME_MASK_COLUMN][index] = row.state_consume_mask;
            columns[STATE_PRODUCE_MULTIPLICITY_COLUMN][index] = row.state_produce_multiplicity;
            columns[DRAW_OUTPUT_MASK_COLUMN][index] = row.draw_output_mask;
        }
        let domain = CanonicCoset::new(self.log_size).circle_domain();
        columns
            .into_iter()
            .map(|column| CircleEvaluation::new(domain, BaseColumn::from(column)))
            .collect()
    }
}

fn append_layout_rows(
    rows: &mut Vec<PreprocessedRow>,
    layout: &TranscriptLayout,
    verifier_id: u32,
    segment_mask: u32,
    binary_mask: u32,
) -> Result<(), TranscriptStateError> {
    let operation_count = layout.operations().len();
    for (operation_index, operation) in layout.operations().iter().enumerate() {
        let expected_ordinal = u32::try_from(operation_index)
            .map_err(|_| TranscriptStateError::OperationIndexOutOfRange { operation_index })?;
        if operation.ordinal() != expected_ordinal {
            return Err(TranscriptStateError::OperationOrdinalMismatch {
                expected: expected_ordinal,
                actual: operation.ordinal(),
            });
        }
        let first_frame = usize::try_from(operation.first_hash_id()).map_err(|_| {
            TranscriptStateError::FrameIndexOutOfRange {
                hash_id: operation.first_hash_id(),
            }
        })?;
        let frame_count = usize::try_from(operation.hash_count()).map_err(|_| {
            TranscriptStateError::FrameCountOutOfRange {
                count: operation.hash_count(),
            }
        })?;
        let expected_frame_count = match operation.effect() {
            TranscriptEffect::Mix => 1,
            TranscriptEffect::Draw | TranscriptEffect::Pow => 2,
        };
        if frame_count != expected_frame_count {
            return Err(TranscriptStateError::OperationFrameCountMismatch {
                sequence: operation.sequence(),
                expected: expected_frame_count,
                actual: frame_count,
            });
        }
        let frame_end = first_frame
            .checked_add(frame_count)
            .ok_or(TranscriptStateError::RowCountOverflow)?;
        let frames = layout.frames().get(first_frame..frame_end).ok_or(
            TranscriptStateError::OperationFrameRangeMissing {
                sequence: operation.sequence(),
            },
        )?;
        let next_state_key = operation
            .ordinal()
            .checked_add(1)
            .ok_or(TranscriptStateError::StateKeyOverflow)?;
        let encoded = operation.step().encode();
        for (frame_offset, frame) in frames.iter().enumerate() {
            let expected_purpose = if frame_offset == 0 {
                HashPurpose::Mix
            } else {
                HashPurpose::Draw
            };
            if frame.purpose() != expected_purpose {
                return Err(TranscriptStateError::FramePurposeMismatch {
                    hash_id: frame.hash_id(),
                    expected: expected_purpose,
                    actual: frame.purpose(),
                });
            }
            let is_mix = frame_offset == 0;
            let has_draw = frame_count == 2;
            let has_next = operation_index + 1 < operation_count;
            rows.push(PreprocessedRow {
                segment_mask,
                binary_mask,
                verifier_id,
                sequence: operation.sequence(),
                tag: encoded.tag(),
                args: encoded.args(),
                hash_id: frame.hash_id(),
                input_state_key: if is_mix {
                    operation.ordinal()
                } else {
                    next_state_key
                },
                output_state_key: next_state_key,
                initial_mask: u32::from(is_mix && operation_index == 0),
                state_consume_mask: u32::from(!is_mix || operation_index > 0),
                state_produce_multiplicity: if is_mix {
                    u32::from(has_draw) + u32::from(has_next)
                } else {
                    0
                },
                draw_output_mask: u32::from(
                    !is_mix && operation.effect() == TranscriptEffect::Draw,
                ),
            });
        }
    }
    Ok(())
}

/// Relation instances used by the macro-generated frame-state component.
#[derive(Clone)]
pub struct TranscriptFrameStateRelations {
    pub frame_output: super::transcript_binding_air::TranscriptFrameOutputRelation,
    pub draw_output: TranscriptDrawOutputRelation,
    pub digest_state: TranscriptDigestStateRelation,
    pub frame_word: super::transcript_binding_air::TranscriptFrameWordRelation,
}

impl TranscriptFrameStateRelations {
    /// Combine binding and state relation instances for one universal proof.
    pub fn new(binding: &TranscriptBindingRelations, state: &TranscriptStateRelations) -> Self {
        Self {
            frame_output: binding.frame_output.clone(),
            draw_output: state.draw_output.clone(),
            digest_state: state.digest_state.clone(),
            frame_word: binding.frame_word.clone(),
        }
    }
}

stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [],
    embedded_component: true,
    embedded_enabler_boolean: false,
    embedded_relations: crate::transcript_state_air::TranscriptFrameStateRelations,
    logup_batch: 2,
    embedded_preprocessed: {
        row_mask: "recursion_transcript_state_row_mask",
        segment_mask: "recursion_transcript_state_segment_mask",
        binary_mask: "recursion_transcript_state_binary_mask",
        verifier_id: "recursion_transcript_state_verifier_id",
        sequence: "recursion_transcript_state_sequence",
        tag: "recursion_transcript_state_tag",
        arg_0: "recursion_transcript_state_arg_0",
        arg_1: "recursion_transcript_state_arg_1",
        arg_2: "recursion_transcript_state_arg_2",
        arg_3: "recursion_transcript_state_arg_3",
        hash_id: "recursion_transcript_state_hash_id",
        input_state_key: "recursion_transcript_state_input_key",
        output_state_key: "recursion_transcript_state_output_key",
        initial_mask: "recursion_transcript_state_initial_mask",
        state_consume_mask: "recursion_transcript_state_consume_mask",
        state_produce_multiplicity: "recursion_transcript_state_produce_multiplicity",
        draw_output_mask: "recursion_transcript_state_draw_output_mask",
    },
    embedded_params: [segment_active, binary_active],

    relation frame_output(10);
    relation draw_output(15);
    relation digest_state(10);
    relation frame_word(4);

    fn transcript_frame_state(
        input_0, input_1, input_2, input_3,
        input_4, input_5, input_6, input_7,
        output_0, output_1, output_2, output_3,
        output_4, output_5, output_6, output_7,
        row_mask, segment_mask, binary_mask, verifier_id,
        sequence, tag, arg_0, arg_1, arg_2, arg_3,
        hash_id, input_state_key, output_state_key, initial_mask,
        state_consume_mask, state_produce_multiplicity, draw_output_mask,
        segment_active, binary_active,
    ) {
        let active = segment_mask * segment_active + binary_mask * binary_active;
        let inactive = row_mask - active;

        constrain enabler - row_mask;
        constrain inactive * input_0;
        constrain inactive * input_1;
        constrain inactive * input_2;
        constrain inactive * input_3;
        constrain inactive * input_4;
        constrain inactive * input_5;
        constrain inactive * input_6;
        constrain inactive * input_7;
        constrain inactive * output_0;
        constrain inactive * output_1;
        constrain inactive * output_2;
        constrain inactive * output_3;
        constrain inactive * output_4;
        constrain inactive * output_5;
        constrain inactive * output_6;
        constrain inactive * output_7;
        constrain active * initial_mask * input_0;
        constrain active * initial_mask * input_1;
        constrain active * initial_mask * input_2;
        constrain active * initial_mask * input_3;
        constrain active * initial_mask * input_4;
        constrain active * initial_mask * input_5;
        constrain active * initial_mask * input_6;
        constrain active * initial_mask * input_7;

        consume(active) frame_output(
            verifier_id, hash_id,
            output_0, output_1, output_2, output_3,
            output_4, output_5, output_6, output_7,
        );
        emit(active * draw_output_mask) draw_output(
            verifier_id, sequence, tag, arg_0, arg_1, arg_2, arg_3,
            output_0, output_1, output_2, output_3,
            output_4, output_5, output_6, output_7,
        );
        consume(active * state_consume_mask) digest_state(
            verifier_id, input_state_key,
            input_0, input_1, input_2, input_3,
            input_4, input_5, input_6, input_7,
        );
        emit(active * state_produce_multiplicity) digest_state(
            verifier_id, output_state_key,
            output_0, output_1, output_2, output_3,
            output_4, output_5, output_6, output_7,
        );
        emit(active) frame_word(verifier_id, hash_id, 0, input_0);
        emit(active) frame_word(verifier_id, hash_id, 1, input_1);
        emit(active) frame_word(verifier_id, hash_id, 2, input_2);
        emit(active) frame_word(verifier_id, hash_id, 3, input_3);
        emit(active) frame_word(verifier_id, hash_id, 4, input_4);
        emit(active) frame_word(verifier_id, hash_id, 5, input_5);
        emit(active) frame_word(verifier_id, hash_id, 6, input_6);
        emit(active) frame_word(verifier_id, hash_id, 7, input_7);

        return (
            output_0, output_1, output_2, output_3,
            output_4, output_5, output_6, output_7,
        );
    }
}

pub use component::air::{Component, Eval};

/// Construct the generated evaluator with verifier-owned mode selectors.
pub fn eval_for_proof_kind(
    log_size: u32,
    proof_kind: ProofKind,
    binding_relations: &TranscriptBindingRelations,
    state_relations: &TranscriptStateRelations,
) -> Eval {
    Eval {
        log_size,
        segment_active: BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        binary_active: BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode)),
        relations: TranscriptFrameStateRelations::new(binding_relations, state_relations),
    }
}

/// Generate all frame-state interaction entries from the macro-defined frame.
pub fn gen_interaction_trace(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    preprocessed: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    proof_kind: ProofKind,
    binding_relations: &TranscriptBindingRelations,
    state_relations: &TranscriptStateRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    component::witness::gen_interaction_trace(
        trace,
        preprocessed,
        BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode)),
        &TranscriptFrameStateRelations::new(binding_relations, state_relations),
    )
}

/// Materializes frame inputs and verified rate outputs for the active lanes.
pub fn push_frame_states(
    table: &mut TranscriptFrameStateTable,
    preprocessed: &TranscriptStatePreprocessed,
    witness: UniversalTranscriptWitness<'_>,
) -> Result<(), TranscriptStateError> {
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
            verifier_id => return Err(TranscriptStateError::UnknownVerifierId { verifier_id }),
        };
        let (input, output) =
            if let Some(trace) = trace {
                let frame_index = usize::try_from(row.hash_id).map_err(|_| {
                    TranscriptStateError::FrameIndexOutOfRange {
                        hash_id: row.hash_id,
                    }
                })?;
                let frame = trace.hash_frames.get(frame_index).ok_or(
                    TranscriptStateError::FrameMissing {
                        verifier_id: row.verifier_id,
                        hash_id: row.hash_id,
                    },
                )?;
                let input: [M31Word; RATE] = frame
                    .words
                    .get(..RATE)
                    .ok_or(TranscriptStateError::DigestWordsMissing {
                        verifier_id: row.verifier_id,
                        hash_id: row.hash_id,
                    })?
                    .try_into()
                    .expect("digest prefix has eight words");
                let output: [M31Word; RATE] = frame.output[..RATE]
                    .try_into()
                    .expect("Poseidon rate has eight words");
                (input, output)
            } else {
                ([M31Word::ZERO; RATE], [M31Word::ZERO; RATE])
            };
        let input = input.map(M31Word::as_u32);
        let output = output.map(M31Word::as_u32);
        table.push(
            input[0], input[1], input[2], input[3], input[4], input[5], input[6], input[7],
            output[0], output[1], output[2], output[3], output[4], output[5], output[6], output[7],
        );
    }
    Ok(())
}

fn validated_trace<'a>(
    layout: &TranscriptLayout,
    execution: &'a VerifierTranscriptExecution<RecordingTranscriptBackend>,
) -> Result<&'a TranscriptTrace, TranscriptStateError> {
    layout
        .validate_execution(execution.operations(), execution.backend().trace())
        .map_err(TranscriptStateError::Layout)?;
    Ok(execution.backend().trace())
}

/// Invalid frame-state preprocessing or witness materialization.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TranscriptStateError {
    Layout(TranscriptLayoutError),
    RowCountOverflow,
    LogSizeOutOfRange {
        log_size: u32,
    },
    OperationIndexOutOfRange {
        operation_index: usize,
    },
    OperationOrdinalMismatch {
        expected: u32,
        actual: u32,
    },
    OperationFrameCountMismatch {
        sequence: u32,
        expected: usize,
        actual: usize,
    },
    OperationFrameRangeMissing {
        sequence: u32,
    },
    FrameIndexOutOfRange {
        hash_id: u32,
    },
    FrameCountOutOfRange {
        count: u32,
    },
    FramePurposeMismatch {
        hash_id: u32,
        expected: HashPurpose,
        actual: HashPurpose,
    },
    StateKeyOverflow,
    UnknownVerifierId {
        verifier_id: u32,
    },
    FrameMissing {
        verifier_id: u32,
        hash_id: u32,
    },
    DigestWordsMissing {
        verifier_id: u32,
        hash_id: u32,
    },
}

impl fmt::Display for TranscriptStateError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Layout(error) => write!(formatter, "invalid transcript layout: {error}"),
            Self::RowCountOverflow => write!(formatter, "transcript frame row count overflowed"),
            Self::LogSizeOutOfRange { log_size } => write!(
                formatter,
                "transcript frame log size {log_size} exceeds the supported maximum {MAX_LOG_SIZE}"
            ),
            Self::OperationIndexOutOfRange { operation_index } => write!(
                formatter,
                "transcript operation index {operation_index} does not fit u32"
            ),
            Self::OperationOrdinalMismatch { expected, actual } => write!(
                formatter,
                "transcript operation ordinal is {actual}, expected {expected}"
            ),
            Self::OperationFrameCountMismatch {
                sequence,
                expected,
                actual,
            } => write!(
                formatter,
                "transcript operation {sequence} has {actual} frames, expected {expected}"
            ),
            Self::OperationFrameRangeMissing { sequence } => write!(
                formatter,
                "transcript operation {sequence} references missing frames"
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
            Self::FramePurposeMismatch {
                hash_id,
                expected,
                actual,
            } => write!(
                formatter,
                "transcript frame {hash_id} has purpose {actual:?}, expected {expected:?}"
            ),
            Self::StateKeyOverflow => write!(formatter, "transcript digest-state key overflowed"),
            Self::UnknownVerifierId { verifier_id } => {
                write!(formatter, "unknown transcript verifier id {verifier_id}")
            }
            Self::FrameMissing {
                verifier_id,
                hash_id,
            } => write!(
                formatter,
                "transcript verifier {verifier_id} has no frame {hash_id}"
            ),
            Self::DigestWordsMissing {
                verifier_id,
                hash_id,
            } => write!(
                formatter,
                "transcript verifier {verifier_id} frame {hash_id} has no digest prefix"
            ),
        }
    }
}

impl std::error::Error for TranscriptStateError {}
