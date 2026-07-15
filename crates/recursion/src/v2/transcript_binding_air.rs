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
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, RelationEntry, relation,
};
use stwo_macros::define_component_tables;

use super::control_air::{
    ControlRelations, LEFT_RECURSION_VERIFIER_ID, RIGHT_RECURSION_VERIFIER_ID, SEGMENT_VERIFIER_ID,
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

const PREPROCESSED_COLUMN_IDS: [&str; PREPROCESSED_COLUMN_COUNT] = [
    "recursion_v2_transcript_call_row_mask",
    "recursion_v2_transcript_call_segment_mask",
    "recursion_v2_transcript_call_binary_mask",
    "recursion_v2_transcript_call_verifier_id",
    "recursion_v2_transcript_call_sequence",
    "recursion_v2_transcript_call_tag",
    "recursion_v2_transcript_call_arg_0",
    "recursion_v2_transcript_call_arg_1",
    "recursion_v2_transcript_call_arg_2",
    "recursion_v2_transcript_call_arg_3",
    "recursion_v2_transcript_call_call_id",
    "recursion_v2_transcript_call_hash_id",
    "recursion_v2_transcript_call_hash_step",
    "recursion_v2_transcript_call_is_first",
    "recursion_v2_transcript_call_is_last",
    "recursion_v2_transcript_call_is_draw",
    "recursion_v2_transcript_call_is_operation_first",
    "recursion_v2_transcript_call_pow_final_mask",
];

define_component_tables! {
    transcript_call_binding: {
        committed: {
            chunk_0, chunk_1, chunk_2, chunk_3,
            chunk_4, chunk_5, chunk_6, chunk_7,
            output_0, output_1, output_2, output_3,
            output_4, output_5, output_6, output_7,
        },
        constraints: {},
    },
}

use prover_columns::TranscriptCallBindingColumns;

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
    vm_layout: TranscriptLayout,
    recursion_layout: TranscriptLayout,
}

impl TranscriptCallPreprocessed {
    pub fn new(
        vm: &VerifierControlPlan,
        recursion: &VerifierControlPlan,
    ) -> Result<Self, TranscriptBindingError> {
        if vm.schema() != VerifierSchema::Vm {
            return Err(TranscriptBindingError::SchemaMismatch {
                lane: "segment",
                expected: VerifierSchema::Vm,
                actual: vm.schema(),
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
        let recursion_layout =
            TranscriptLayout::new(recursion).map_err(TranscriptBindingError::Layout)?;
        let row_count = vm_layout
            .calls()
            .len()
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

    pub const fn vm_layout(&self) -> &TranscriptLayout {
        &self.vm_layout
    }

    pub const fn recursion_layout(&self) -> &TranscriptLayout {
        &self.recursion_layout
    }

    pub fn active_call_count(&self, kind: ProofKind) -> usize {
        match kind {
            ProofKind::SegmentLeaf => self.vm_layout.calls().len(),
            ProofKind::BinaryNode => 2 * self.recursion_layout.calls().len(),
            ProofKind::EmptyLeaf => 0,
        }
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

pub type Component = FrameworkComponent<Eval>;

#[derive(Clone)]
pub struct Eval {
    pub log_size: u32,
    pub proof_kind: ProofKind,
    pub control_relations: ControlRelations,
    pub transcript_relations: TranscriptAirRelations,
    pub binding_relations: TranscriptBindingRelations,
}

impl FrameworkEval for Eval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let cols = TranscriptCallBindingColumns::from_eval(&mut eval);
        let column_ids = TranscriptCallPreprocessed::column_ids();
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
        let call_id = eval.get_preprocessed_column(column_ids[CALL_ID_COLUMN].clone());
        let hash_id = eval.get_preprocessed_column(column_ids[HASH_ID_COLUMN].clone());
        let hash_step = eval.get_preprocessed_column(column_ids[HASH_STEP_COLUMN].clone());
        let is_first = eval.get_preprocessed_column(column_ids[IS_FIRST_COLUMN].clone());
        let is_last = eval.get_preprocessed_column(column_ids[IS_LAST_COLUMN].clone());
        let is_draw = eval.get_preprocessed_column(column_ids[IS_DRAW_COLUMN].clone());
        let is_operation_first =
            eval.get_preprocessed_column(column_ids[IS_OPERATION_FIRST_COLUMN].clone());
        let pow_final_mask =
            eval.get_preprocessed_column(column_ids[POW_FINAL_MASK_COLUMN].clone());
        eval.add_constraint(cols.enabler.clone() - row_mask.clone());

        let segment_active = BaseField::from(u32::from(self.proof_kind == ProofKind::SegmentLeaf));
        let binary_active = BaseField::from(u32::from(self.proof_kind == ProofKind::BinaryNode));
        let active = segment_mask * segment_active + binary_mask * binary_active;
        let active_last = active.clone() * is_last.clone();
        let active_operation_first = active.clone() * is_operation_first;
        let active_pow_final = active.clone() * pow_final_mask;
        let chunk = [
            cols.chunk_0.clone(),
            cols.chunk_1.clone(),
            cols.chunk_2.clone(),
            cols.chunk_3.clone(),
            cols.chunk_4.clone(),
            cols.chunk_5.clone(),
            cols.chunk_6.clone(),
            cols.chunk_7.clone(),
        ];
        let output = [
            cols.output_0.clone(),
            cols.output_1.clone(),
            cols.output_2.clone(),
            cols.output_3.clone(),
            cols.output_4.clone(),
            cols.output_5.clone(),
            cols.output_6.clone(),
            cols.output_7.clone(),
        ];
        for value in &chunk {
            eval.add_constraint((row_mask.clone() - active.clone()) * value.clone());
        }
        for value in &output {
            eval.add_constraint((row_mask.clone() - is_last.clone()) * value.clone());
            eval.add_constraint((row_mask.clone() - active.clone()) * value.clone());
        }

        eval.add_to_relation(RelationEntry::new(
            &self.transcript_relations.control,
            E::EF::from(active.clone()),
            &[
                verifier_id.clone(),
                call_id.clone(),
                hash_id.clone(),
                hash_step.clone(),
                is_first,
                is_last.clone(),
                is_draw.clone(),
            ],
        ));
        let mut data_tuple = vec![verifier_id.clone(), hash_id.clone(), hash_step.clone()];
        data_tuple.extend(chunk.iter().cloned());
        eval.add_to_relation(RelationEntry::new(
            &self.transcript_relations.data,
            E::EF::from(active.clone()),
            &data_tuple,
        ));

        let mut hash_output_tuple = vec![
            verifier_id.clone(),
            hash_id.clone(),
            call_id.clone(),
            is_draw,
        ];
        hash_output_tuple.extend(output.iter().cloned());
        eval.add_to_relation(RelationEntry::new(
            &self.transcript_relations.output,
            -E::EF::from(active_last.clone()),
            &hash_output_tuple,
        ));
        let mut frame_output_tuple = vec![verifier_id.clone(), hash_id.clone()];
        frame_output_tuple.extend(output.iter().cloned());
        eval.add_to_relation(RelationEntry::new(
            &self.binding_relations.frame_output,
            E::EF::from(active_last),
            &frame_output_tuple,
        ));

        let mut pow_frame_tuple = vec![
            verifier_id.clone(),
            sequence.clone(),
            tag.clone(),
            hash_id.clone(),
            call_id,
            arg_0.clone(),
        ];
        pow_frame_tuple.extend(output.iter().cloned());
        eval.add_to_relation(RelationEntry::new(
            &self.binding_relations.pow_frame,
            E::EF::from(active_pow_final),
            &pow_frame_tuple,
        ));

        eval.add_to_relation(RelationEntry::new(
            &self.control_relations.step,
            -E::EF::from(active_operation_first),
            &[
                verifier_id.clone(),
                sequence,
                tag,
                arg_0,
                arg_1,
                arg_2,
                arg_3,
            ],
        ));

        let rate = E::F::from(BaseField::from(RATE as u32));
        for (slot, value) in chunk.into_iter().enumerate() {
            let word_index =
                hash_step.clone() * rate.clone() + E::F::from(BaseField::from(slot as u32));
            eval.add_to_relation(RelationEntry::new(
                &self.binding_relations.frame_word,
                -E::EF::from(active.clone()),
                &[verifier_id.clone(), hash_id.clone(), word_index, value],
            ));
        }

        eval.finalize_logup_in_pairs();
        eval
    }
}

/// Generates all call-binding relation fractions from fixed preprocessing.
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
    let cols = TranscriptCallBindingColumns::from_iter(
        trace.iter().map(|evaluation| &evaluation.values.data),
    );
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
    let neg_active: Vec<_> = active.iter().map(|value| -*value).collect();
    let active_last: Vec<PackedQM31> = (0..simd_size)
        .map(|row| active[row] * PackedQM31::from(pp[IS_LAST_COLUMN][row]))
        .collect();
    let neg_active_last: Vec<_> = active_last.iter().map(|value| -*value).collect();
    let active_pow_final: Vec<PackedQM31> = (0..simd_size)
        .map(|row| active[row] * PackedQM31::from(pp[POW_FINAL_MASK_COLUMN][row]))
        .collect();
    let neg_active_operation_first: Vec<PackedQM31> = (0..simd_size)
        .map(|row| -active[row] * PackedQM31::from(pp[IS_OPERATION_FIRST_COLUMN][row]))
        .collect();

    let call_control_denom = combine!(
        transcript_relations.control,
        [
            pp[VERIFIER_ID_COLUMN],
            pp[CALL_ID_COLUMN],
            pp[HASH_ID_COLUMN],
            pp[HASH_STEP_COLUMN],
            pp[IS_FIRST_COLUMN],
            pp[IS_LAST_COLUMN],
            pp[IS_DRAW_COLUMN]
        ]
    );
    let data_denom = combine!(
        transcript_relations.data,
        [
            pp[VERIFIER_ID_COLUMN],
            pp[HASH_ID_COLUMN],
            pp[HASH_STEP_COLUMN],
            cols.chunk_0,
            cols.chunk_1,
            cols.chunk_2,
            cols.chunk_3,
            cols.chunk_4,
            cols.chunk_5,
            cols.chunk_6,
            cols.chunk_7
        ]
    );
    let hash_output_denom = combine!(
        transcript_relations.output,
        [
            pp[VERIFIER_ID_COLUMN],
            pp[HASH_ID_COLUMN],
            pp[CALL_ID_COLUMN],
            pp[IS_DRAW_COLUMN],
            cols.output_0,
            cols.output_1,
            cols.output_2,
            cols.output_3,
            cols.output_4,
            cols.output_5,
            cols.output_6,
            cols.output_7
        ]
    );
    let frame_output_denom = combine!(
        binding_relations.frame_output,
        [
            pp[VERIFIER_ID_COLUMN],
            pp[HASH_ID_COLUMN],
            cols.output_0,
            cols.output_1,
            cols.output_2,
            cols.output_3,
            cols.output_4,
            cols.output_5,
            cols.output_6,
            cols.output_7
        ]
    );
    let pow_frame_denom = combine!(
        binding_relations.pow_frame,
        [
            pp[VERIFIER_ID_COLUMN],
            pp[SEQUENCE_COLUMN],
            pp[TAG_COLUMN],
            pp[HASH_ID_COLUMN],
            pp[CALL_ID_COLUMN],
            pp[ARG_0_COLUMN],
            cols.output_0,
            cols.output_1,
            cols.output_2,
            cols.output_3,
            cols.output_4,
            cols.output_5,
            cols.output_6,
            cols.output_7
        ]
    );
    let control_step_denom = combine!(
        control_relations.step,
        [
            pp[VERIFIER_ID_COLUMN],
            pp[SEQUENCE_COLUMN],
            pp[TAG_COLUMN],
            pp[ARG_0_COLUMN],
            pp[ARG_1_COLUMN],
            pp[ARG_2_COLUMN],
            pp[ARG_3_COLUMN]
        ]
    );

    let rate = stwo::prover::backend::simd::m31::PackedM31::broadcast(BaseField::from(RATE as u32));
    let word_indices = (0..RATE)
        .map(|slot| {
            let slot = stwo::prover::backend::simd::m31::PackedM31::broadcast(BaseField::from(
                slot as u32,
            ));
            (0..simd_size)
                .map(|row| pp[HASH_STEP_COLUMN][row] * rate + slot)
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let word_denoms = [
        cols.chunk_0,
        cols.chunk_1,
        cols.chunk_2,
        cols.chunk_3,
        cols.chunk_4,
        cols.chunk_5,
        cols.chunk_6,
        cols.chunk_7,
    ]
    .into_iter()
    .enumerate()
    .map(|(slot, values)| {
        combine!(
            binding_relations.frame_word,
            [
                pp[VERIFIER_ID_COLUMN],
                pp[HASH_ID_COLUMN],
                &word_indices[slot],
                values
            ]
        )
    })
    .collect::<Vec<_>>();

    let mut logup_gen = LogupTraceGenerator::new(log_size);
    write_pair!(
        &active,
        &call_control_denom,
        &active,
        &data_denom,
        logup_gen
    );
    write_pair!(
        &neg_active_last,
        &hash_output_denom,
        &active_last,
        &frame_output_denom,
        logup_gen
    );
    write_pair!(
        &active_pow_final,
        &pow_frame_denom,
        &neg_active_operation_first,
        &control_step_denom,
        logup_gen
    );
    write_pair!(
        &neg_active,
        &word_denoms[0],
        &neg_active,
        &word_denoms[1],
        logup_gen
    );
    write_pair!(
        &neg_active,
        &word_denoms[2],
        &neg_active,
        &word_denoms[3],
        logup_gen
    );
    write_pair!(
        &neg_active,
        &word_denoms[4],
        &neg_active,
        &word_denoms[5],
        logup_gen
    );
    write_pair!(
        &neg_active,
        &word_denoms[6],
        &neg_active,
        &word_denoms[7],
        logup_gen
    );
    logup_gen.finalize_last()
}

/// Mode-indexed transcript executions accepted by the universal table.
pub enum UniversalTranscriptWitness<'a> {
    Segment(&'a VerifierTranscriptExecution<RecordingTranscriptBackend>),
    Binary {
        left: &'a VerifierTranscriptExecution<RecordingTranscriptBackend>,
        right: &'a VerifierTranscriptExecution<RecordingTranscriptBackend>,
    },
    Empty,
}

impl UniversalTranscriptWitness<'_> {
    pub const fn proof_kind(&self) -> ProofKind {
        match self {
            Self::Segment(_) => ProofKind::SegmentLeaf,
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
    let (segment, left, right) = match witness {
        UniversalTranscriptWitness::Segment(execution) => (
            Some(validated_rows(&preprocessed.vm_layout, execution)?),
            None,
            None,
        ),
        UniversalTranscriptWitness::Binary { left, right } => (
            None,
            Some(validated_rows(&preprocessed.recursion_layout, left)?),
            Some(validated_rows(&preprocessed.recursion_layout, right)?),
        ),
        UniversalTranscriptWitness::Empty => (None, None, None),
    };

    for row in &preprocessed.rows {
        let lane = match row.verifier_id {
            SEGMENT_VERIFIER_ID => segment.as_ref(),
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
