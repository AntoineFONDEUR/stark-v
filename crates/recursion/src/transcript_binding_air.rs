//! AIR binding between trusted transcript layout and atomic hash calls.
//!
//! Preprocessed columns fix every active verifier lane, control sequence,
//! frame boundary, and call coordinate. Committed columns contain only rate
//! chunks and final rate outputs. The component connects those values to the
//! hash-call AIR, consumes one trusted control step per transcript operation,
//! and exposes exact frame-word and verified-output relations for the state
//! and payload components.

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
    ControlRelations, LEFT_RECURSION_VERIFIER_ID, POSEIDON2_VERIFIER_ID,
    RIGHT_RECURSION_VERIFIER_ID, SEGMENT_VERIFIER_ID,
};
use super::kernel::{VerifierControlPlan, VerifierSchema};
use super::transcript::{HashPurpose, RecordingTranscriptBackend, SpongeRow, TranscriptError};
use super::transcript_air::TranscriptAirRelations;
use super::transcript_layout::{TranscriptLayout, TranscriptLayoutError};
use super::transcript_program::VerifierTranscriptExecution;
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
const CALL_ID_COLUMN: usize = 10;
const HASH_ID_COLUMN: usize = 11;
const HASH_STEP_COLUMN: usize = 12;
const IS_FIRST_COLUMN: usize = 13;
const IS_LAST_COLUMN: usize = 14;
const IS_DRAW_COLUMN: usize = 15;
const IS_OPERATION_FIRST_COLUMN: usize = 16;
const POW_FINAL_MASK_COLUMN: usize = 17;
const PREPROCESSED_COLUMN_COUNT: usize = 18;

// One padded frame word: verifier, hash session, word index, and value.
relation!(TranscriptFrameWordRelation, 4);
// One verified final rate output: verifier, hash session, and eight words.
relation!(TranscriptFrameOutputRelation, 10);
// One PoW operation: verifier, control coordinates, draw coordinates, and output.
relation!(TranscriptPowFrameRelation, 14);

/// Relations passed from call binding to transcript state and payload tables.
#[derive(Clone)]
pub struct TranscriptBindingRelations {
    pub frame_word: TranscriptFrameWordRelation,
    pub frame_output: TranscriptFrameOutputRelation,
    pub pow_frame: TranscriptPowFrameRelation,
}

impl TranscriptBindingRelations {
    pub fn dummy() -> Self {
        Self {
            frame_word: TranscriptFrameWordRelation::dummy(),
            frame_output: TranscriptFrameOutputRelation::dummy(),
            pow_frame: TranscriptPowFrameRelation::dummy(),
        }
    }

    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            frame_word: TranscriptFrameWordRelation::draw(channel),
            frame_output: TranscriptFrameOutputRelation::draw(channel),
            pow_frame: TranscriptPowFrameRelation::draw(channel),
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
    call_id: u32,
    hash_id: u32,
    hash_step: u32,
    is_first: u32,
    is_last: u32,
    is_draw: u32,
    is_operation_first: u32,
    pow_final_mask: u32,
}

/// Universal call layout derived from one VM plan and one recursion plan.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TranscriptCallPreprocessed {
    log_size: u32,
    rows: Vec<PreprocessedRow>,
    vm_plan: VerifierControlPlan,
    poseidon2_plan: VerifierControlPlan,
    recursion_plan: VerifierControlPlan,
    vm_layout: TranscriptLayout,
    poseidon2_layout: TranscriptLayout,
    recursion_layout: TranscriptLayout,
}

impl TranscriptCallPreprocessed {
    pub fn new(
        vm: &VerifierControlPlan,
        poseidon2: &VerifierControlPlan,
        recursion: &VerifierControlPlan,
    ) -> Result<Self, TranscriptBindingError> {
        if vm.schema() != VerifierSchema::Vm {
            return Err(TranscriptBindingError::SchemaMismatch {
                lane: "segment",
                expected: VerifierSchema::Vm,
                actual: vm.schema(),
            });
        }
        if poseidon2.schema() != VerifierSchema::Poseidon2 {
            return Err(TranscriptBindingError::SchemaMismatch {
                lane: "Poseidon2 segment",
                expected: VerifierSchema::Poseidon2,
                actual: poseidon2.schema(),
            });
        }
        if recursion.schema() != VerifierSchema::Recursion {
            return Err(TranscriptBindingError::SchemaMismatch {
                lane: "binary",
                expected: VerifierSchema::Recursion,
                actual: recursion.schema(),
            });
        }

        let vm_layout = TranscriptLayout::new(vm).map_err(TranscriptBindingError::Layout)?;
        let poseidon2_layout =
            TranscriptLayout::new(poseidon2).map_err(TranscriptBindingError::Layout)?;
        let recursion_layout =
            TranscriptLayout::new(recursion).map_err(TranscriptBindingError::Layout)?;
        let row_count = vm_layout
            .calls()
            .len()
            .checked_add(poseidon2_layout.calls().len())
            .ok_or(TranscriptBindingError::RowCountOverflow)?
            .checked_add(
                recursion_layout
                    .calls()
                    .len()
                    .checked_mul(2)
                    .ok_or(TranscriptBindingError::RowCountOverflow)?,
            )
            .ok_or(TranscriptBindingError::RowCountOverflow)?;
        let padded_rows = row_count
            .checked_next_power_of_two()
            .ok_or(TranscriptBindingError::RowCountOverflow)?
            .max(1 << MIN_LOG_SIZE);
        let log_size = padded_rows.ilog2();
        if log_size > MAX_LOG_SIZE {
            return Err(TranscriptBindingError::LogSizeOutOfRange { log_size });
        }

        let mut rows = Vec::with_capacity(row_count);
        append_layout_rows(&mut rows, &vm_layout, SEGMENT_VERIFIER_ID, 1, 0)?;
        append_layout_rows(&mut rows, &poseidon2_layout, POSEIDON2_VERIFIER_ID, 1, 0)?;
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
            vm_plan: vm.clone(),
            poseidon2_plan: poseidon2.clone(),
            recursion_plan: recursion.clone(),
            vm_layout,
            poseidon2_layout,
            recursion_layout,
        })
    }

    pub const fn log_size(&self) -> u32 {
        self.log_size
    }

    pub const fn vm_layout(&self) -> &TranscriptLayout {
        &self.vm_layout
    }

    pub const fn vm_plan(&self) -> &VerifierControlPlan {
        &self.vm_plan
    }

    pub const fn poseidon2_layout(&self) -> &TranscriptLayout {
        &self.poseidon2_layout
    }

    pub const fn poseidon2_plan(&self) -> &VerifierControlPlan {
        &self.poseidon2_plan
    }

    pub const fn recursion_layout(&self) -> &TranscriptLayout {
        &self.recursion_layout
    }

    pub const fn recursion_plan(&self) -> &VerifierControlPlan {
        &self.recursion_plan
    }

    pub fn active_call_count(&self, kind: ProofKind) -> usize {
        match kind {
            ProofKind::SegmentLeaf => {
                self.vm_layout.calls().len() + self.poseidon2_layout.calls().len()
            }
            ProofKind::BinaryNode => 2 * self.recursion_layout.calls().len(),
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
            columns[SEQUENCE_COLUMN][index] = row.sequence;
            columns[TAG_COLUMN][index] = row.tag;
            columns[ARG_0_COLUMN][index] = row.args[0];
            columns[ARG_1_COLUMN][index] = row.args[1];
            columns[ARG_2_COLUMN][index] = row.args[2];
            columns[ARG_3_COLUMN][index] = row.args[3];
            columns[CALL_ID_COLUMN][index] = row.call_id;
            columns[HASH_ID_COLUMN][index] = row.hash_id;
            columns[HASH_STEP_COLUMN][index] = row.hash_step;
            columns[IS_FIRST_COLUMN][index] = row.is_first;
            columns[IS_LAST_COLUMN][index] = row.is_last;
            columns[IS_DRAW_COLUMN][index] = row.is_draw;
            columns[IS_OPERATION_FIRST_COLUMN][index] = row.is_operation_first;
            columns[POW_FINAL_MASK_COLUMN][index] = row.pow_final_mask;
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
) -> Result<(), TranscriptBindingError> {
    for operation in layout.operations() {
        let encoded = operation.step().encode();
        let is_pow = matches!(
            operation.step(),
            super::kernel::VerifierStep::VerifyAndAbsorbInteractionPow { .. }
                | super::kernel::VerifierStep::VerifyAndAbsorbPcsPow { .. }
        );
        let first_call = usize::try_from(operation.first_call_id()).map_err(|_| {
            TranscriptBindingError::CallIndexOutOfRange {
                call_id: operation.first_call_id(),
            }
        })?;
        let call_count = usize::try_from(operation.call_count()).map_err(|_| {
            TranscriptBindingError::CallIndexOutOfRange {
                call_id: operation.call_count(),
            }
        })?;
        let end = first_call
            .checked_add(call_count)
            .ok_or(TranscriptBindingError::RowCountOverflow)?;
        for (offset, call) in layout.calls()[first_call..end].iter().enumerate() {
            let pow_final_mask = u32::from(is_pow && offset + 1 == call_count);
            if pow_final_mask == 1 && (!call.is_last() || call.purpose() != HashPurpose::Draw) {
                return Err(TranscriptBindingError::PowFrameMismatch {
                    sequence: operation.sequence(),
                });
            }
            rows.push(PreprocessedRow {
                segment_mask,
                binary_mask,
                verifier_id,
                sequence: operation.sequence(),
                tag: encoded.tag(),
                args: encoded.args(),
                call_id: call.call_id(),
                hash_id: call.hash_id(),
                hash_step: call.step(),
                is_first: u32::from(call.is_first()),
                is_last: u32::from(call.is_last()),
                is_draw: u32::from(call.purpose() == HashPurpose::Draw),
                is_operation_first: u32::from(offset == 0),
                pow_final_mask,
            });
        }
    }
    Ok(())
}

/// Relation instances used by the macro-generated call-binding component.
#[derive(Clone)]
pub struct TranscriptCallBindingRelations {
    pub hash_control: super::transcript_air::HashCallControlRelation,
    pub hash_data: super::transcript_air::HashDataRelation,
    pub hash_output: super::transcript_air::HashOutputRelation,
    pub frame_output: TranscriptFrameOutputRelation,
    pub pow_frame: TranscriptPowFrameRelation,
    pub step: super::control_air::VerifierStepRelation,
    pub frame_word: TranscriptFrameWordRelation,
}

impl TranscriptCallBindingRelations {
    /// Combine the control, hash-call, and binding relation instances.
    pub fn new(
        control: &ControlRelations,
        transcript: &TranscriptAirRelations,
        binding: &TranscriptBindingRelations,
    ) -> Self {
        Self {
            hash_control: transcript.control.clone(),
            hash_data: transcript.data.clone(),
            hash_output: transcript.output.clone(),
            frame_output: binding.frame_output.clone(),
            pow_frame: binding.pow_frame.clone(),
            step: control.step.clone(),
            frame_word: binding.frame_word.clone(),
        }
    }
}

stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [],
    embedded_component: true,
    embedded_enabler_boolean: false,
    embedded_relations: crate::transcript_binding_air::TranscriptCallBindingRelations,
    logup_batch: 2,
    embedded_preprocessed: {
        row_mask: "recursion_transcript_call_row_mask",
        segment_mask: "recursion_transcript_call_segment_mask",
        binary_mask: "recursion_transcript_call_binary_mask",
        verifier_id: "recursion_transcript_call_verifier_id",
        sequence: "recursion_transcript_call_sequence",
        tag: "recursion_transcript_call_tag",
        arg_0: "recursion_transcript_call_arg_0",
        arg_1: "recursion_transcript_call_arg_1",
        arg_2: "recursion_transcript_call_arg_2",
        arg_3: "recursion_transcript_call_arg_3",
        call_id: "recursion_transcript_call_call_id",
        hash_id: "recursion_transcript_call_hash_id",
        hash_step: "recursion_transcript_call_hash_step",
        is_first: "recursion_transcript_call_is_first",
        is_last: "recursion_transcript_call_is_last",
        is_draw: "recursion_transcript_call_is_draw",
        is_operation_first: "recursion_transcript_call_is_operation_first",
        pow_final_mask: "recursion_transcript_call_pow_final_mask",
    },
    embedded_params: [segment_active, binary_active],

    relation hash_control(7);
    relation hash_data(11);
    relation hash_output(12);
    relation frame_output(10);
    relation pow_frame(14);
    relation step(7);
    relation frame_word(4);

    fn transcript_call_binding(
        chunk_0, chunk_1, chunk_2, chunk_3,
        chunk_4, chunk_5, chunk_6, chunk_7,
        output_0, output_1, output_2, output_3,
        output_4, output_5, output_6, output_7,
        row_mask, segment_mask, binary_mask, verifier_id,
        sequence, tag, arg_0, arg_1, arg_2, arg_3,
        call_id, hash_id, hash_step, is_first, is_last, is_draw,
        is_operation_first, pow_final_mask,
        segment_active, binary_active,
    ) {
        let active = segment_mask * segment_active + binary_mask * binary_active;

        constrain enabler - row_mask;
        constrain (row_mask - active) * chunk_0;
        constrain (row_mask - active) * chunk_1;
        constrain (row_mask - active) * chunk_2;
        constrain (row_mask - active) * chunk_3;
        constrain (row_mask - active) * chunk_4;
        constrain (row_mask - active) * chunk_5;
        constrain (row_mask - active) * chunk_6;
        constrain (row_mask - active) * chunk_7;
        constrain (row_mask - is_last) * output_0;
        constrain (row_mask - is_last) * output_1;
        constrain (row_mask - is_last) * output_2;
        constrain (row_mask - is_last) * output_3;
        constrain (row_mask - is_last) * output_4;
        constrain (row_mask - is_last) * output_5;
        constrain (row_mask - is_last) * output_6;
        constrain (row_mask - is_last) * output_7;
        constrain (row_mask - active) * output_0;
        constrain (row_mask - active) * output_1;
        constrain (row_mask - active) * output_2;
        constrain (row_mask - active) * output_3;
        constrain (row_mask - active) * output_4;
        constrain (row_mask - active) * output_5;
        constrain (row_mask - active) * output_6;
        constrain (row_mask - active) * output_7;

        emit(active) hash_control(
            verifier_id, call_id, hash_id, hash_step, is_first, is_last, is_draw,
        );
        emit(active) hash_data(
            verifier_id, hash_id, hash_step,
            chunk_0, chunk_1, chunk_2, chunk_3,
            chunk_4, chunk_5, chunk_6, chunk_7,
        );
        consume(active * is_last) hash_output(
            verifier_id, hash_id, call_id, is_draw,
            output_0, output_1, output_2, output_3,
            output_4, output_5, output_6, output_7,
        );
        emit(active * is_last) frame_output(
            verifier_id, hash_id,
            output_0, output_1, output_2, output_3,
            output_4, output_5, output_6, output_7,
        );
        emit(active * pow_final_mask) pow_frame(
            verifier_id, sequence, tag, hash_id, call_id, arg_0,
            output_0, output_1, output_2, output_3,
            output_4, output_5, output_6, output_7,
        );
        consume(active * is_operation_first) step(
            verifier_id, sequence, tag, arg_0, arg_1, arg_2, arg_3,
        );
        consume(active) frame_word(verifier_id, hash_id, hash_step * 8, chunk_0);
        consume(active) frame_word(verifier_id, hash_id, hash_step * 8 + 1, chunk_1);
        consume(active) frame_word(verifier_id, hash_id, hash_step * 8 + 2, chunk_2);
        consume(active) frame_word(verifier_id, hash_id, hash_step * 8 + 3, chunk_3);
        consume(active) frame_word(verifier_id, hash_id, hash_step * 8 + 4, chunk_4);
        consume(active) frame_word(verifier_id, hash_id, hash_step * 8 + 5, chunk_5);
        consume(active) frame_word(verifier_id, hash_id, hash_step * 8 + 6, chunk_6);
        consume(active) frame_word(verifier_id, hash_id, hash_step * 8 + 7, chunk_7);

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
    control_relations: &ControlRelations,
    transcript_relations: &TranscriptAirRelations,
    binding_relations: &TranscriptBindingRelations,
) -> Eval {
    Eval {
        log_size,
        segment_active: BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        binary_active: BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode)),
        relations: TranscriptCallBindingRelations::new(
            control_relations,
            transcript_relations,
            binding_relations,
        ),
    }
}

/// Generate all call-binding interaction entries from the macro-defined frame.
pub fn gen_interaction_trace(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    preprocessed: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    proof_kind: ProofKind,
    control_relations: &ControlRelations,
    transcript_relations: &TranscriptAirRelations,
    binding_relations: &TranscriptBindingRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    component::witness::gen_interaction_trace(
        trace,
        preprocessed,
        BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode)),
        &TranscriptCallBindingRelations::new(
            control_relations,
            transcript_relations,
            binding_relations,
        ),
    )
}

/// Mode-indexed transcript executions accepted by the universal table.
#[derive(Clone, Copy)]
pub enum UniversalTranscriptWitness<'a> {
    Segment {
        vm: &'a VerifierTranscriptExecution<RecordingTranscriptBackend>,
        poseidon2: &'a VerifierTranscriptExecution<RecordingTranscriptBackend>,
    },
    Binary {
        left: &'a VerifierTranscriptExecution<RecordingTranscriptBackend>,
        right: &'a VerifierTranscriptExecution<RecordingTranscriptBackend>,
    },
    Empty,
}

impl UniversalTranscriptWitness<'_> {
    pub const fn proof_kind(&self) -> ProofKind {
        match self {
            Self::Segment { .. } => ProofKind::SegmentLeaf,
            Self::Binary { .. } => ProofKind::BinaryNode,
            Self::Empty => ProofKind::EmptyLeaf,
        }
    }
}

/// Materializes active call values and canonical zeroes for inactive lanes.
pub fn push_call_bindings(
    table: &mut TranscriptCallBindingTable,
    preprocessed: &TranscriptCallPreprocessed,
    witness: UniversalTranscriptWitness<'_>,
) -> Result<(), TranscriptBindingError> {
    let (segment, poseidon2, left, right) = match witness {
        UniversalTranscriptWitness::Segment { vm, poseidon2 } => (
            Some(validated_rows(&preprocessed.vm_layout, vm)?),
            Some(validated_rows(&preprocessed.poseidon2_layout, poseidon2)?),
            None,
            None,
        ),
        UniversalTranscriptWitness::Binary { left, right } => (
            None,
            None,
            Some(validated_rows(&preprocessed.recursion_layout, left)?),
            Some(validated_rows(&preprocessed.recursion_layout, right)?),
        ),
        UniversalTranscriptWitness::Empty => (None, None, None, None),
    };

    for row in &preprocessed.rows {
        let lane = match row.verifier_id {
            SEGMENT_VERIFIER_ID => segment.as_ref(),
            POSEIDON2_VERIFIER_ID => poseidon2.as_ref(),
            LEFT_RECURSION_VERIFIER_ID => left.as_ref(),
            RIGHT_RECURSION_VERIFIER_ID => right.as_ref(),
            verifier_id => {
                return Err(TranscriptBindingError::UnknownVerifierId { verifier_id });
            }
        };
        let (chunk, output) = if let Some(rows) = lane {
            let call_index = usize::try_from(row.call_id).map_err(|_| {
                TranscriptBindingError::CallIndexOutOfRange {
                    call_id: row.call_id,
                }
            })?;
            let call = rows
                .get(call_index)
                .ok_or(TranscriptBindingError::CallMissing {
                    verifier_id: row.verifier_id,
                    call_id: row.call_id,
                })?;
            let output = if row.is_last == 1 {
                call.output[..RATE]
                    .try_into()
                    .expect("rate slice has eight words")
            } else {
                [air::digest::M31Word::ZERO; RATE]
            };
            (call.chunk.map(air::digest::M31Word::as_u32), output)
        } else {
            ([0; RATE], [air::digest::M31Word::ZERO; RATE])
        };
        let output = output.map(air::digest::M31Word::as_u32);
        table.push(
            chunk[0], chunk[1], chunk[2], chunk[3], chunk[4], chunk[5], chunk[6], chunk[7],
            output[0], output[1], output[2], output[3], output[4], output[5], output[6], output[7],
        );
    }
    Ok(())
}

fn validated_rows(
    layout: &TranscriptLayout,
    execution: &VerifierTranscriptExecution<RecordingTranscriptBackend>,
) -> Result<Vec<SpongeRow>, TranscriptBindingError> {
    layout
        .validate_execution(execution.operations(), execution.backend().trace())
        .map_err(TranscriptBindingError::Layout)?;
    execution
        .backend()
        .trace()
        .sponge_rows()
        .map_err(TranscriptBindingError::Transcript)
}

/// Invalid universal preprocessing or transcript witness materialization.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TranscriptBindingError {
    SchemaMismatch {
        lane: &'static str,
        expected: VerifierSchema,
        actual: VerifierSchema,
    },
    Layout(TranscriptLayoutError),
    Transcript(TranscriptError),
    RowCountOverflow,
    LogSizeOutOfRange {
        log_size: u32,
    },
    CallIndexOutOfRange {
        call_id: u32,
    },
    UnknownVerifierId {
        verifier_id: u32,
    },
    CallMissing {
        verifier_id: u32,
        call_id: u32,
    },
    PowFrameMismatch {
        sequence: u32,
    },
}

impl fmt::Display for TranscriptBindingError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SchemaMismatch {
                lane,
                expected,
                actual,
            } => write!(
                formatter,
                "{lane} transcript lane requires {expected:?}, got {actual:?}"
            ),
            Self::Layout(error) => write!(formatter, "invalid transcript layout: {error}"),
            Self::Transcript(error) => write!(formatter, "invalid transcript trace: {error}"),
            Self::RowCountOverflow => write!(formatter, "transcript call row count overflowed"),
            Self::LogSizeOutOfRange { log_size } => write!(
                formatter,
                "transcript call log size {log_size} exceeds the supported maximum {MAX_LOG_SIZE}"
            ),
            Self::CallIndexOutOfRange { call_id } => {
                write!(
                    formatter,
                    "transcript call index {call_id} does not fit usize"
                )
            }
            Self::UnknownVerifierId { verifier_id } => {
                write!(formatter, "unknown transcript verifier id {verifier_id}")
            }
            Self::CallMissing {
                verifier_id,
                call_id,
            } => write!(
                formatter,
                "transcript verifier {verifier_id} has no call {call_id}"
            ),
            Self::PowFrameMismatch { sequence } => write!(
                formatter,
                "PoW operation {sequence} does not end at a draw frame boundary"
            ),
        }
    }
}

impl std::error::Error for TranscriptBindingError {}
