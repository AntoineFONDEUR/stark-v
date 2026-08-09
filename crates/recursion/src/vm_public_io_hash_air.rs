//! Fixed Poseidon2 hashes for segment input and output semantics.
//!
//! Two verifier-owned lanes consume the canonical public-IO stream exported
//! from the VM claim. Each lane has a distinct capacity domain, full state
//! chaining, canonical end-marker padding, and one eight-word digest relation
//! consumed by the claim-to-statement semantic circuit.

use core::fmt;

use air::digest::M31Word;
use air::poseidon2::{T, poseidon2_traced_state};
use air::trace::Poseidon2Table;
use prover::public_data::PublicData;
use prover::relations::Relations;
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

use super::vm_public_claim::{
    VmPublicClaimError, VmPublicClaimShape, canonical_public_input_words_from_claim,
    canonical_public_output_words_from_claim, canonical_vm_public_claim_words,
    public_input_digest_from_claim, public_output_digest_from_claim,
};
#[cfg(test)]
use super::vm_public_claim::{
    canonical_public_input_words, canonical_public_output_words, public_input_digest,
    public_output_digest,
};
use super::vm_public_claim_input_air::{
    VM_PUBLIC_INPUT_KIND, VM_PUBLIC_OUTPUT_KIND, VmPublicClaimInputRelations,
};
use super::wire::ProofKind;

const RATE: usize = T / 2;
const PUBLIC_INPUT_HASH_DOMAIN: u32 = 0x5649;
const PUBLIC_OUTPUT_HASH_DOMAIN: u32 = 0x564f;
const MIN_LOG_SIZE: u32 = 4;
const MAX_LOG_SIZE: u32 = 30;

const ROW_MASK_COLUMN: usize = 0;
const IO_KIND_COLUMN: usize = 1;
const STEP_COLUMN: usize = 2;
const FIRST_MASK_COLUMN: usize = 3;
const LAST_MASK_COLUMN: usize = 4;
const DOMAIN_COLUMN: usize = 5;
const CHUNK_COLUMNS_START: usize = 6;
const CHUNK_COLUMNS_PER_WORD: usize = 3;
const PREPROCESSED_COLUMN_COUNT: usize = CHUNK_COLUMNS_START + RATE * CHUNK_COLUMNS_PER_WORD;

// Internal state tuple: IO kind, fixed step, and the complete state.
relation!(VmPublicIoHashStateRelation, 18);
// Final application digest tuple: IO kind, limb, and digest word.
relation!(VmPublicIoDigestRelation, 3);

/// State and final digest relations for both fixed IO hash lanes.
#[derive(Clone)]
pub struct VmPublicIoHashRelations {
    pub state: VmPublicIoHashStateRelation,
    pub digest: VmPublicIoDigestRelation,
}

impl VmPublicIoHashRelations {
    pub fn dummy() -> Self {
        Self {
            state: VmPublicIoHashStateRelation::dummy(),
            digest: VmPublicIoDigestRelation::dummy(),
        }
    }

    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            state: VmPublicIoHashStateRelation::draw(channel),
            digest: VmPublicIoDigestRelation::draw(channel),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ChunkSource {
    IoWord(u32),
    Constant(u32),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PreprocessedRow {
    io_kind: u32,
    step: u32,
    first: bool,
    last: bool,
    domain: u32,
    chunks: [ChunkSource; RATE],
}

/// Trusted two-lane sponge schedule for one claim capacity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VmPublicIoHashPreprocessed {
    shape: VmPublicClaimShape,
    log_size: u32,
    rows: Vec<PreprocessedRow>,
}

impl VmPublicIoHashPreprocessed {
    pub fn new(shape: VmPublicClaimShape) -> Result<Self, VmPublicIoHashError> {
        let mut rows = Vec::new();
        append_lane(
            &mut rows,
            VM_PUBLIC_INPUT_KIND,
            PUBLIC_INPUT_HASH_DOMAIN,
            9 + shape.max_input_words() as usize * 3,
        )?;
        append_lane(
            &mut rows,
            VM_PUBLIC_OUTPUT_KIND,
            PUBLIC_OUTPUT_HASH_DOMAIN,
            11 + shape.max_output_words() as usize * 5,
        )?;
        let padded_rows = rows
            .len()
            .checked_next_power_of_two()
            .ok_or(VmPublicIoHashError::RowCountOverflow)?
            .max(1 << MIN_LOG_SIZE);
        let log_size = padded_rows.ilog2();
        if log_size > MAX_LOG_SIZE {
            return Err(VmPublicIoHashError::LogSizeOutOfRange { log_size });
        }
        Ok(Self {
            shape,
            log_size,
            rows,
        })
    }

    pub const fn shape(&self) -> VmPublicClaimShape {
        self.shape
    }

    pub const fn log_size(&self) -> u32 {
        self.log_size
    }

    pub fn row_count(&self) -> usize {
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
            columns[IO_KIND_COLUMN][row_index] = row.io_kind;
            columns[STEP_COLUMN][row_index] = row.step;
            columns[FIRST_MASK_COLUMN][row_index] = u32::from(row.first);
            columns[LAST_MASK_COLUMN][row_index] = u32::from(row.last);
            columns[DOMAIN_COLUMN][row_index] = row.domain;
            for (slot, source) in row.chunks.into_iter().enumerate() {
                let start = chunk_column(slot);
                match source {
                    ChunkSource::IoWord(index) => {
                        columns[start][row_index] = 1;
                        columns[start + 1][row_index] = index;
                    }
                    ChunkSource::Constant(value) => columns[start + 2][row_index] = value,
                }
            }
        }
        let domain = CanonicCoset::new(self.log_size).circle_domain();
        columns
            .into_iter()
            .map(|column| CircleEvaluation::new(domain, BaseColumn::from(column)))
            .collect()
    }
}

fn append_lane(
    rows: &mut Vec<PreprocessedRow>,
    io_kind: u32,
    domain: u32,
    word_count: usize,
) -> Result<(), VmPublicIoHashError> {
    let padded_word_count = word_count
        .checked_add(1)
        .ok_or(VmPublicIoHashError::RowCountOverflow)?;
    let row_count = padded_word_count.div_ceil(RATE);
    for step in 0..row_count {
        let mut chunks = [ChunkSource::Constant(0); RATE];
        for (slot, source) in chunks.iter_mut().enumerate() {
            let index = step
                .checked_mul(RATE)
                .and_then(|start| start.checked_add(slot))
                .ok_or(VmPublicIoHashError::RowCountOverflow)?;
            *source = if index < 3 {
                ChunkSource::Constant(io_prefix_word(io_kind, word_count, index)?)
            } else if index < word_count {
                ChunkSource::IoWord(
                    u32::try_from(index)
                        .map_err(|_| VmPublicIoHashError::WordIndexOutOfRange { index })?,
                )
            } else if index == word_count {
                ChunkSource::Constant(1)
            } else {
                ChunkSource::Constant(0)
            };
        }
        rows.push(PreprocessedRow {
            io_kind,
            step: u32::try_from(step).map_err(|_| VmPublicIoHashError::StepOutOfRange { step })?,
            first: step == 0,
            last: step + 1 == row_count,
            domain,
            chunks,
        });
    }
    Ok(())
}

fn io_prefix_word(
    io_kind: u32,
    word_count: usize,
    index: usize,
) -> Result<u32, VmPublicIoHashError> {
    let capacity = match io_kind {
        VM_PUBLIC_INPUT_KIND => (word_count - 9) / 3,
        VM_PUBLIC_OUTPUT_KIND => (word_count - 11) / 5,
        _ => return Err(VmPublicIoHashError::UnknownIoKind { io_kind }),
    };
    let capacity = u32::try_from(capacity)
        .map_err(|_| VmPublicIoHashError::CapacityOutOfRange { capacity })?;
    Ok(match index {
        0 => match io_kind {
            VM_PUBLIC_INPUT_KIND => 20,
            VM_PUBLIC_OUTPUT_KIND => 21,
            _ => return Err(VmPublicIoHashError::UnknownIoKind { io_kind }),
        },
        1 => capacity & 0xffff,
        2 => capacity >> 16,
        _ => return Err(VmPublicIoHashError::PrefixIndexOutOfRange { index }),
    })
}

const fn chunk_column(slot: usize) -> usize {
    CHUNK_COLUMNS_START + slot * CHUNK_COLUMNS_PER_WORD
}

/// Relation instances used by the macro-generated public-IO hash component.
#[derive(Clone)]
pub struct VmPublicIoHashComponentRelations {
    pub poseidon2_io: air::relations::relation_types::poseidon2_io,
    pub io_word: super::vm_public_claim_input_air::VmPublicIoWordRelation,
    pub state: VmPublicIoHashStateRelation,
    pub digest: VmPublicIoDigestRelation,
}

impl VmPublicIoHashComponentRelations {
    /// Combine the VM-wide and recursion-local relations touched by both lanes.
    pub fn new(
        vm_relations: &Relations,
        claim_relations: &VmPublicClaimInputRelations,
        io_hash_relations: &VmPublicIoHashRelations,
    ) -> Self {
        Self {
            poseidon2_io: vm_relations.poseidon2_io.clone(),
            io_word: claim_relations.io_word.clone(),
            state: io_hash_relations.state.clone(),
            digest: io_hash_relations.digest.clone(),
        }
    }
}

stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [],
    embedded_component: true,
    embedded_enabler_boolean: false,
    embedded_relations:
        crate::vm_public_io_hash_air::VmPublicIoHashComponentRelations,
    logup_batch: 2,
    embedded_preprocessed: {
        row_mask: "recursion_vm_io_hash_row_mask",
        io_kind: "recursion_vm_io_hash_kind",
        step: "recursion_vm_io_hash_step",
        first: "recursion_vm_io_hash_first_mask",
        last: "recursion_vm_io_hash_last_mask",
        hash_domain: "recursion_vm_io_hash_domain",
        chunk_0_source_mask: "recursion_vm_io_hash_chunk_0_source_mask",
        chunk_0_word_index: "recursion_vm_io_hash_chunk_0_word_index",
        chunk_0_constant: "recursion_vm_io_hash_chunk_0_constant",
        chunk_1_source_mask: "recursion_vm_io_hash_chunk_1_source_mask",
        chunk_1_word_index: "recursion_vm_io_hash_chunk_1_word_index",
        chunk_1_constant: "recursion_vm_io_hash_chunk_1_constant",
        chunk_2_source_mask: "recursion_vm_io_hash_chunk_2_source_mask",
        chunk_2_word_index: "recursion_vm_io_hash_chunk_2_word_index",
        chunk_2_constant: "recursion_vm_io_hash_chunk_2_constant",
        chunk_3_source_mask: "recursion_vm_io_hash_chunk_3_source_mask",
        chunk_3_word_index: "recursion_vm_io_hash_chunk_3_word_index",
        chunk_3_constant: "recursion_vm_io_hash_chunk_3_constant",
        chunk_4_source_mask: "recursion_vm_io_hash_chunk_4_source_mask",
        chunk_4_word_index: "recursion_vm_io_hash_chunk_4_word_index",
        chunk_4_constant: "recursion_vm_io_hash_chunk_4_constant",
        chunk_5_source_mask: "recursion_vm_io_hash_chunk_5_source_mask",
        chunk_5_word_index: "recursion_vm_io_hash_chunk_5_word_index",
        chunk_5_constant: "recursion_vm_io_hash_chunk_5_constant",
        chunk_6_source_mask: "recursion_vm_io_hash_chunk_6_source_mask",
        chunk_6_word_index: "recursion_vm_io_hash_chunk_6_word_index",
        chunk_6_constant: "recursion_vm_io_hash_chunk_6_constant",
        chunk_7_source_mask: "recursion_vm_io_hash_chunk_7_source_mask",
        chunk_7_word_index: "recursion_vm_io_hash_chunk_7_word_index",
        chunk_7_constant: "recursion_vm_io_hash_chunk_7_constant",
    },
    embedded_params: [segment_active],

    relation poseidon2_io(32);
    relation io_word(3);
    relation state(18);
    relation digest(3);

    fn vm_public_io_hash(
        previous_0, previous_1, previous_2, previous_3,
        previous_4, previous_5, previous_6, previous_7,
        previous_8, previous_9, previous_10, previous_11,
        previous_12, previous_13, previous_14, previous_15,
        chunk_0, chunk_1, chunk_2, chunk_3,
        chunk_4, chunk_5, chunk_6, chunk_7,
        output_0, output_1, output_2, output_3,
        output_4, output_5, output_6, output_7,
        output_8, output_9, output_10, output_11,
        output_12, output_13, output_14, output_15,
        row_mask, io_kind, step, first, last, hash_domain,
        chunk_0_source_mask, chunk_0_word_index, chunk_0_constant,
        chunk_1_source_mask, chunk_1_word_index, chunk_1_constant,
        chunk_2_source_mask, chunk_2_word_index, chunk_2_constant,
        chunk_3_source_mask, chunk_3_word_index, chunk_3_constant,
        chunk_4_source_mask, chunk_4_word_index, chunk_4_constant,
        chunk_5_source_mask, chunk_5_word_index, chunk_5_constant,
        chunk_6_source_mask, chunk_6_word_index, chunk_6_constant,
        chunk_7_source_mask, chunk_7_word_index, chunk_7_constant,
        segment_active,
    ) {
        let active = row_mask * segment_active;

        constrain enabler - active;
        constrain (1 - active) * previous_0;
        constrain (1 - active) * previous_1;
        constrain (1 - active) * previous_2;
        constrain (1 - active) * previous_3;
        constrain (1 - active) * previous_4;
        constrain (1 - active) * previous_5;
        constrain (1 - active) * previous_6;
        constrain (1 - active) * previous_7;
        constrain (1 - active) * previous_8;
        constrain (1 - active) * previous_9;
        constrain (1 - active) * previous_10;
        constrain (1 - active) * previous_11;
        constrain (1 - active) * previous_12;
        constrain (1 - active) * previous_13;
        constrain (1 - active) * previous_14;
        constrain (1 - active) * previous_15;
        constrain (1 - active) * chunk_0;
        constrain (1 - active) * chunk_1;
        constrain (1 - active) * chunk_2;
        constrain (1 - active) * chunk_3;
        constrain (1 - active) * chunk_4;
        constrain (1 - active) * chunk_5;
        constrain (1 - active) * chunk_6;
        constrain (1 - active) * chunk_7;
        constrain (1 - active) * output_0;
        constrain (1 - active) * output_1;
        constrain (1 - active) * output_2;
        constrain (1 - active) * output_3;
        constrain (1 - active) * output_4;
        constrain (1 - active) * output_5;
        constrain (1 - active) * output_6;
        constrain (1 - active) * output_7;
        constrain (1 - active) * output_8;
        constrain (1 - active) * output_9;
        constrain (1 - active) * output_10;
        constrain (1 - active) * output_11;
        constrain (1 - active) * output_12;
        constrain (1 - active) * output_13;
        constrain (1 - active) * output_14;
        constrain (1 - active) * output_15;

        constrain segment_active * first * previous_0;
        constrain segment_active * first * previous_1;
        constrain segment_active * first * previous_2;
        constrain segment_active * first * previous_3;
        constrain segment_active * first * previous_4;
        constrain segment_active * first * previous_5;
        constrain segment_active * first * previous_6;
        constrain segment_active * first * previous_7;
        constrain segment_active * first * previous_8;
        constrain segment_active * first * previous_9;
        constrain segment_active * first * previous_10;
        constrain segment_active * first * previous_11;
        constrain segment_active * first * previous_12;
        constrain segment_active * first * previous_13;
        constrain segment_active * first * previous_14;
        constrain segment_active * first * (previous_15 - hash_domain);

        // Trusted source masks are subsets of the row mask, so their
        // difference selects exactly the fixed prefix and padding constants.
        constrain segment_active * (row_mask - chunk_0_source_mask) * (chunk_0 - chunk_0_constant);
        constrain segment_active * (row_mask - chunk_1_source_mask) * (chunk_1 - chunk_1_constant);
        constrain segment_active * (row_mask - chunk_2_source_mask) * (chunk_2 - chunk_2_constant);
        constrain segment_active * (row_mask - chunk_3_source_mask) * (chunk_3 - chunk_3_constant);
        constrain segment_active * (row_mask - chunk_4_source_mask) * (chunk_4 - chunk_4_constant);
        constrain segment_active * (row_mask - chunk_5_source_mask) * (chunk_5 - chunk_5_constant);
        constrain segment_active * (row_mask - chunk_6_source_mask) * (chunk_6 - chunk_6_constant);
        constrain segment_active * (row_mask - chunk_7_source_mask) * (chunk_7 - chunk_7_constant);

        consume(active) poseidon2_io(
            previous_0 + chunk_0,
            previous_1 + chunk_1,
            previous_2 + chunk_2,
            previous_3 + chunk_3,
            previous_4 + chunk_4,
            previous_5 + chunk_5,
            previous_6 + chunk_6,
            previous_7 + chunk_7,
            previous_8, previous_9, previous_10, previous_11,
            previous_12, previous_13, previous_14, previous_15,
            output_0, output_1, output_2, output_3,
            output_4, output_5, output_6, output_7,
            output_8, output_9, output_10, output_11,
            output_12, output_13, output_14, output_15,
        );
        consume(segment_active * chunk_0_source_mask) io_word(
            io_kind, chunk_0_word_index, chunk_0,
        );
        consume(segment_active * chunk_1_source_mask) io_word(
            io_kind, chunk_1_word_index, chunk_1,
        );
        consume(segment_active * chunk_2_source_mask) io_word(
            io_kind, chunk_2_word_index, chunk_2,
        );
        consume(segment_active * chunk_3_source_mask) io_word(
            io_kind, chunk_3_word_index, chunk_3,
        );
        consume(segment_active * chunk_4_source_mask) io_word(
            io_kind, chunk_4_word_index, chunk_4,
        );
        consume(segment_active * chunk_5_source_mask) io_word(
            io_kind, chunk_5_word_index, chunk_5,
        );
        consume(segment_active * chunk_6_source_mask) io_word(
            io_kind, chunk_6_word_index, chunk_6,
        );
        consume(segment_active * chunk_7_source_mask) io_word(
            io_kind, chunk_7_word_index, chunk_7,
        );
        consume(segment_active * (row_mask - first)) state(
            io_kind, step,
            previous_0, previous_1, previous_2, previous_3,
            previous_4, previous_5, previous_6, previous_7,
            previous_8, previous_9, previous_10, previous_11,
            previous_12, previous_13, previous_14, previous_15,
        );
        emit(segment_active * (row_mask - last)) state(
            io_kind, step + 1,
            output_0, output_1, output_2, output_3,
            output_4, output_5, output_6, output_7,
            output_8, output_9, output_10, output_11,
            output_12, output_13, output_14, output_15,
        );
        emit(segment_active * last) digest(io_kind, 0, output_0);
        emit(segment_active * last) digest(io_kind, 1, output_1);
        emit(segment_active * last) digest(io_kind, 2, output_2);
        emit(segment_active * last) digest(io_kind, 3, output_3);
        emit(segment_active * last) digest(io_kind, 4, output_4);
        emit(segment_active * last) digest(io_kind, 5, output_5);
        emit(segment_active * last) digest(io_kind, 6, output_6);
        emit(segment_active * last) digest(io_kind, 7, output_7);

        return (
            output_0, output_1, output_2, output_3,
            output_4, output_5, output_6, output_7,
        );
    }
}

pub use component::air::{Component, Eval};

/// Construct the generated evaluator for the selected universal proof kind.
pub fn eval_for_proof_kind(
    log_size: u32,
    proof_kind: ProofKind,
    vm_relations: &Relations,
    claim_relations: &VmPublicClaimInputRelations,
    io_hash_relations: &VmPublicIoHashRelations,
) -> Eval {
    Eval {
        log_size,
        segment_active: BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        relations: VmPublicIoHashComponentRelations::new(
            vm_relations,
            claim_relations,
            io_hash_relations,
        ),
    }
}

/// Generate Poseidon, IO-word, state, and final-digest interaction fractions.
pub fn gen_interaction_trace(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    preprocessed: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    proof_kind: ProofKind,
    vm_relations: &Relations,
    claim_relations: &VmPublicClaimInputRelations,
    io_hash_relations: &VmPublicIoHashRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    component::witness::gen_interaction_trace(
        trace,
        preprocessed,
        BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        &VmPublicIoHashComponentRelations::new(vm_relations, claim_relations, io_hash_relations),
    )
}

/// Records both semantic IO hashes and their reused Poseidon2 rows.
pub fn push_vm_public_io_hashes(
    table: &mut VmPublicIoHashTable,
    poseidon2: &mut Poseidon2Table,
    preprocessed: &VmPublicIoHashPreprocessed,
    proof_kind: ProofKind,
    public_data: Option<&PublicData>,
) -> Result<(), VmPublicIoHashError> {
    let active = proof_kind == ProofKind::SegmentLeaf;
    match (active, public_data) {
        (true, Some(_)) => {}
        (true, None) => return Err(VmPublicIoHashError::SegmentClaimMissing),
        (false, Some(_)) => return Err(VmPublicIoHashError::InactiveClaimProvided),
        (false, None) => {}
    }
    let claim_words = public_data
        .map(|public_data| canonical_vm_public_claim_words(public_data, preprocessed.shape))
        .transpose()
        .map_err(VmPublicIoHashError::Claim)?;
    push_vm_public_io_word_hashes(
        table,
        poseidon2,
        preprocessed,
        proof_kind,
        claim_words.as_deref().unwrap_or(&[]),
    )
}

/// Records both IO hash lanes directly from the fixed VM claim encoding.
pub fn push_vm_public_io_word_hashes(
    table: &mut VmPublicIoHashTable,
    poseidon2: &mut Poseidon2Table,
    preprocessed: &VmPublicIoHashPreprocessed,
    proof_kind: ProofKind,
    claim_words: &[M31Word],
) -> Result<(), VmPublicIoHashError> {
    let active = proof_kind == ProofKind::SegmentLeaf;
    let streams = if active {
        [
            canonical_public_input_words_from_claim(claim_words, preprocessed.shape)
                .map_err(VmPublicIoHashError::Claim)?,
            canonical_public_output_words_from_claim(claim_words, preprocessed.shape)
                .map_err(VmPublicIoHashError::Claim)?,
        ]
    } else {
        [Vec::new(), Vec::new()]
    };
    if !active {
        for _ in &preprocessed.rows {
            table.push_row_values(&[0; 41]);
        }
        return Ok(());
    }

    let mut row_offset = 0;
    for (lane, words) in streams.iter().enumerate() {
        let io_kind = u32::try_from(lane).expect("two IO lanes fit u32");
        let lane_rows = preprocessed.rows[row_offset..]
            .iter()
            .take_while(|row| row.io_kind == io_kind)
            .count();
        let domain = if io_kind == VM_PUBLIC_INPUT_KIND {
            PUBLIC_INPUT_HASH_DOMAIN
        } else {
            PUBLIC_OUTPUT_HASH_DOMAIN
        };
        let mut stream = words.iter().map(|word| word.as_u32()).collect::<Vec<_>>();
        stream.push(1);
        stream.resize(lane_rows * RATE, 0);
        let mut state = [0_u32; T];
        state[T - 1] = domain;
        for lane_row in 0..lane_rows {
            let chunk: [u32; RATE] = stream[lane_row * RATE..(lane_row + 1) * RATE]
                .try_into()
                .expect("trusted IO chunk width is fixed");
            let mut permutation_input = state;
            for (value, absorbed) in permutation_input.iter_mut().zip(chunk) {
                *value = (u64::from(*value) + u64::from(absorbed))
                    .rem_euclid(u64::from(stwo::core::fields::m31::P))
                    as u32;
            }
            let output = poseidon2_traced_state(poseidon2, permutation_input, false, true);
            let mut values = Vec::with_capacity(41);
            values.push(1);
            values.extend(state);
            values.extend(chunk);
            values.extend(output);
            table.push_row_values(&values);
            state = output;
        }
        let expected = if io_kind == VM_PUBLIC_INPUT_KIND {
            public_input_digest_from_claim(claim_words, preprocessed.shape)
        } else {
            public_output_digest_from_claim(claim_words, preprocessed.shape)
        }
        .map_err(VmPublicIoHashError::Claim)?;
        if state[..RATE] != expected.digest().words().map(M31Word::as_u32) {
            return Err(VmPublicIoHashError::DigestMismatch { io_kind });
        }
        row_offset += lane_rows;
    }
    Ok(())
}

impl VmPublicIoHashTable {
    fn push_row_values(&mut self, values: &[u32]) {
        self.push_row(values);
    }
}

/// Invalid trusted IO schedule or claim witness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VmPublicIoHashError {
    Claim(VmPublicClaimError),
    RowCountOverflow,
    WordIndexOutOfRange { index: usize },
    StepOutOfRange { step: usize },
    LogSizeOutOfRange { log_size: u32 },
    UnknownIoKind { io_kind: u32 },
    CapacityOutOfRange { capacity: usize },
    PrefixIndexOutOfRange { index: usize },
    SegmentClaimMissing,
    InactiveClaimProvided,
    DigestMismatch { io_kind: u32 },
}

impl fmt::Display for VmPublicIoHashError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for VmPublicIoHashError {}

#[cfg(test)]
mod tests {
    use num_traits::Zero;
    use prover::poseidon2_channel::Poseidon2M31Channel;
    use rstest::rstest;
    use stwo::core::fields::FieldExpOps;
    use stwo::core::fields::m31::M31;
    use stwo::core::pcs::TreeVec;
    use stwo_constraint_framework::{FrameworkEval, Relation, assert_constraints_on_polys};

    use super::*;
    use crate::vm_public_claim::tests::{public_data, shape};

    #[derive(Clone, Copy)]
    enum HashTamper {
        InitialCapacity,
        EndMarker,
        InactiveState,
    }

    fn assert_constraints(kind: ProofKind, tamper: Option<HashTamper>) {
        let preprocessing =
            VmPublicIoHashPreprocessed::new(shape()).expect("fixture shape is supported");
        let claim = public_data();
        let witness = (kind == ProofKind::SegmentLeaf).then_some(&claim);
        let mut table = VmPublicIoHashTable::new();
        push_vm_public_io_hashes(
            &mut table,
            &mut Poseidon2Table::new(),
            &preprocessing,
            kind,
            witness,
        )
        .expect("fixture IO hashes materialize");
        match tamper {
            Some(HashTamper::InitialCapacity) => table.previous_15[0] = 0,
            Some(HashTamper::EndMarker) => {
                let marker_index = 9 + shape().max_input_words() as usize * 3;
                let row = marker_index / RATE;
                match marker_index % RATE {
                    0 => table.chunk_0[row] = 0,
                    1 => table.chunk_1[row] = 0,
                    2 => table.chunk_2[row] = 0,
                    3 => table.chunk_3[row] = 0,
                    4 => table.chunk_4[row] = 0,
                    5 => table.chunk_5[row] = 0,
                    6 => table.chunk_6[row] = 0,
                    7 => table.chunk_7[row] = 0,
                    _ => unreachable!("slot is reduced modulo the rate"),
                }
            }
            Some(HashTamper::InactiveState) => table.previous_0[0] = 1,
            None => {}
        }
        let vm_relations = Relations::dummy();
        let claim_relations = VmPublicClaimInputRelations::dummy();
        let io_hash_relations = VmPublicIoHashRelations::dummy();
        let preprocessed = preprocessing.gen_columns();
        let trace = table.into_witness();
        let (interaction, claimed_sum) = gen_interaction_trace(
            &trace,
            &preprocessed,
            kind,
            &vm_relations,
            &claim_relations,
            &io_hash_relations,
        );
        let traces = TreeVec::new(vec![preprocessed, trace, interaction]);
        let trace_polys = traces.map_cols(|column| column.interpolate());
        let eval = eval_for_proof_kind(
            preprocessing.log_size(),
            kind,
            &vm_relations,
            &claim_relations,
            &io_hash_relations,
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

    fn complete_relation_sum(tamper_previous: bool, swap_digest_kinds: bool) -> QM31 {
        let shape = shape();
        let preprocessing =
            VmPublicIoHashPreprocessed::new(shape).expect("fixture shape is supported");
        let claim = public_data();
        let mut table = VmPublicIoHashTable::new();
        let mut poseidon2 = Poseidon2Table::new();
        push_vm_public_io_hashes(
            &mut table,
            &mut poseidon2,
            &preprocessing,
            ProofKind::SegmentLeaf,
            Some(&claim),
        )
        .expect("fixture IO hashes materialize");
        if tamper_previous {
            table.previous_0[1] += 1;
        }

        let mut channel = Poseidon2M31Channel::default();
        let vm_relations = Relations::draw(&mut channel);
        let claim_relations = VmPublicClaimInputRelations::draw(&mut channel);
        let io_hash_relations = VmPublicIoHashRelations::draw(&mut channel);
        let trace = table.into_witness();
        let (_, hash_sum) = gen_interaction_trace(
            &trace,
            &preprocessing.gen_columns(),
            ProofKind::SegmentLeaf,
            &vm_relations,
            &claim_relations,
            &io_hash_relations,
        );
        let poseidon_trace = poseidon2.into_witness();
        let (_, poseidon_sum) = air::poseidon2::component::witness::gen_interaction_trace(
            &poseidon_trace,
            &vm_relations,
        );
        hash_sum
            + poseidon_sum
            + io_word_source_terms(&claim, shape, &claim_relations)
            + digest_consumer_terms(&claim, shape, &io_hash_relations, swap_digest_kinds)
    }

    fn io_word_source_terms(
        claim: &PublicData,
        shape: VmPublicClaimShape,
        relations: &VmPublicClaimInputRelations,
    ) -> QM31 {
        [
            canonical_public_input_words(&claim.io_entries, shape)
                .expect("fixture input words are canonical"),
            canonical_public_output_words(&claim.io_entries, shape)
                .expect("fixture output words are canonical"),
        ]
        .into_iter()
        .enumerate()
        .flat_map(|(io_kind, words)| {
            words
                .into_iter()
                .enumerate()
                .skip(3)
                .map(move |(index, word)| {
                    let denominator: QM31 = relations.io_word.combine(&[
                        M31::from(u32::try_from(io_kind).expect("IO kind fits u32")),
                        M31::from(u32::try_from(index).expect("IO word index fits u32")),
                        M31::from(word.as_u32()),
                    ]);
                    denominator.inverse()
                })
        })
        .fold(QM31::zero(), |sum, term| sum + term)
    }

    fn digest_consumer_terms(
        claim: &PublicData,
        shape: VmPublicClaimShape,
        relations: &VmPublicIoHashRelations,
        swap_kinds: bool,
    ) -> QM31 {
        let digests = [
            public_input_digest(&claim.io_entries, shape)
                .expect("fixture input digest is canonical")
                .into_digest()
                .into_words(),
            public_output_digest(&claim.io_entries, shape)
                .expect("fixture output digest is canonical")
                .into_digest()
                .into_words(),
        ];
        digests
            .into_iter()
            .enumerate()
            .flat_map(|(io_kind, digest)| {
                digest.into_iter().enumerate().map(move |(limb, word)| {
                    let io_kind = if swap_kinds { 1 - io_kind } else { io_kind };
                    let denominator: QM31 = relations.digest.combine(&[
                        M31::from(u32::try_from(io_kind).expect("IO kind fits u32")),
                        M31::from(u32::try_from(limb).expect("digest limb fits u32")),
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
    fn every_universal_mode_satisfies_io_hash_constraints(#[case] kind: ProofKind) {
        assert_constraints(kind, None);
    }

    #[rstest]
    #[should_panic]
    fn the_initial_capacity_domain_cannot_change() {
        assert_constraints(ProofKind::SegmentLeaf, Some(HashTamper::InitialCapacity));
    }

    #[rstest]
    #[should_panic]
    fn canonical_end_marker_cannot_change() {
        assert_constraints(ProofKind::SegmentLeaf, Some(HashTamper::EndMarker));
    }

    #[rstest]
    #[should_panic]
    fn inactive_io_hash_state_must_be_zero() {
        assert_constraints(ProofKind::EmptyLeaf, Some(HashTamper::InactiveState));
    }

    #[rstest]
    fn complete_io_hash_relations_cancel() {
        assert!(complete_relation_sum(false, false).is_zero());
    }

    #[rstest]
    fn a_disconnected_internal_state_does_not_cancel() {
        assert!(!complete_relation_sum(true, false).is_zero());
    }

    #[rstest]
    fn input_and_output_digest_lanes_cannot_be_swapped() {
        assert!(!complete_relation_sum(false, true).is_zero());
    }
}
