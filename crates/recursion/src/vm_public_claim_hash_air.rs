//! Poseidon2 proof of the fixed words behind the VM public-claim digest.
//!
//! Each trusted row consumes eight indexed claim words or canonical padding,
//! chains the full permutation state, and binds the atomic permutation tuple
//! to the standard Poseidon2 component. The first capacity state contains the
//! claim domain, and the last rate state consumes the exact digest absorbed by
//! the segment verifier transcript.

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

use super::control_air::SEGMENT_VERIFIER_ID;
use super::transcript_payload_air::{VerifierInputKind, VerifierInputRelations};
use super::vm_public_claim::{
    VmPublicClaimError, VmPublicClaimShape, canonical_vm_public_claim_words, vm_public_claim_digest,
};
use super::vm_public_claim_input_air::{VM_CLAIM_HASH_SCOPE, VmPublicClaimInputRelations};
use super::wire::ProofKind;

const RATE: usize = T / 2;
const VM_PUBLIC_CLAIM_HASH_DOMAIN: u32 = 0x5643;
const MIN_LOG_SIZE: u32 = 4;
const MAX_LOG_SIZE: u32 = 30;

const ROW_MASK_COLUMN: usize = 0;
const STEP_COLUMN: usize = 1;
const FIRST_MASK_COLUMN: usize = 2;
const LAST_MASK_COLUMN: usize = 3;
const CHUNK_COLUMNS_START: usize = 4;
const CHUNK_COLUMNS_PER_WORD: usize = 3;
const PREPROCESSED_COLUMN_COUNT: usize = CHUNK_COLUMNS_START + RATE * CHUNK_COLUMNS_PER_WORD;

// Internal state tuple: fixed step and the complete 16-word state.
relation!(VmPublicClaimHashStateRelation, 17);

/// Relation used only to close consecutive fixed hash rows.
#[derive(Clone)]
pub struct VmPublicClaimHashRelations {
    pub state: VmPublicClaimHashStateRelation,
}

impl VmPublicClaimHashRelations {
    pub fn dummy() -> Self {
        Self {
            state: VmPublicClaimHashStateRelation::dummy(),
        }
    }

    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            state: VmPublicClaimHashStateRelation::draw(channel),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ChunkSource {
    ClaimWord(u32),
    Constant(u32),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PreprocessedRow {
    step: u32,
    first: bool,
    last: bool,
    chunks: [ChunkSource; RATE],
}

/// Fixed sponge schedule derived from the trusted claim shape.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VmPublicClaimHashPreprocessed {
    shape: VmPublicClaimShape,
    log_size: u32,
    rows: Vec<PreprocessedRow>,
}

impl VmPublicClaimHashPreprocessed {
    pub fn new(shape: VmPublicClaimShape) -> Result<Self, VmPublicClaimHashError> {
        let word_count = shape.claim_word_count();
        let padded_word_count = word_count
            .checked_add(1)
            .ok_or(VmPublicClaimHashError::RowCountOverflow)?;
        let row_count = padded_word_count.div_ceil(RATE);
        let mut rows = Vec::with_capacity(row_count);
        for step in 0..row_count {
            let mut chunks = [ChunkSource::Constant(0); RATE];
            for (slot, source) in chunks.iter_mut().enumerate() {
                let index = step
                    .checked_mul(RATE)
                    .and_then(|start| start.checked_add(slot))
                    .ok_or(VmPublicClaimHashError::RowCountOverflow)?;
                *source = if index < word_count {
                    ChunkSource::ClaimWord(
                        u32::try_from(index)
                            .map_err(|_| VmPublicClaimHashError::WordIndexOutOfRange { index })?,
                    )
                } else if index == word_count {
                    ChunkSource::Constant(1)
                } else {
                    ChunkSource::Constant(0)
                };
            }
            rows.push(PreprocessedRow {
                step: u32::try_from(step)
                    .map_err(|_| VmPublicClaimHashError::StepOutOfRange { step })?,
                first: step == 0,
                last: step + 1 == row_count,
                chunks,
            });
        }
        let padded_rows = row_count
            .checked_next_power_of_two()
            .ok_or(VmPublicClaimHashError::RowCountOverflow)?
            .max(1 << MIN_LOG_SIZE);
        let log_size = padded_rows.ilog2();
        if log_size > MAX_LOG_SIZE {
            return Err(VmPublicClaimHashError::LogSizeOutOfRange { log_size });
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

    pub fn step_count(&self) -> usize {
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
            columns[STEP_COLUMN][row_index] = row.step;
            columns[FIRST_MASK_COLUMN][row_index] = u32::from(row.first);
            columns[LAST_MASK_COLUMN][row_index] = u32::from(row.last);
            for (slot, source) in row.chunks.into_iter().enumerate() {
                let start = chunk_column(slot);
                match source {
                    ChunkSource::ClaimWord(index) => {
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

const fn chunk_column(slot: usize) -> usize {
    CHUNK_COLUMNS_START + slot * CHUNK_COLUMNS_PER_WORD
}

/// Relation instances used by the macro-generated public-claim hash component.
#[derive(Clone)]
pub struct VmPublicClaimHashComponentRelations {
    pub poseidon2_io: air::relations::relation_types::poseidon2_io,
    pub claim_word: super::vm_public_claim_input_air::VmPublicClaimWordRelation,
    pub state: VmPublicClaimHashStateRelation,
    pub input_word: super::transcript_payload_air::VerifierInputWordRelation,
}

impl VmPublicClaimHashComponentRelations {
    /// Combine the VM-wide and recursion-local relations touched by the hash.
    pub fn new(
        vm_relations: &Relations,
        claim_input_relations: &VmPublicClaimInputRelations,
        hash_relations: &VmPublicClaimHashRelations,
        verifier_input_relations: &VerifierInputRelations,
    ) -> Self {
        Self {
            poseidon2_io: vm_relations.poseidon2_io.clone(),
            claim_word: claim_input_relations.claim_word.clone(),
            state: hash_relations.state.clone(),
            input_word: verifier_input_relations.input_word.clone(),
        }
    }
}

stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [],
    embedded_component: true,
    embedded_enabler_boolean: false,
    embedded_relations:
        crate::vm_public_claim_hash_air::VmPublicClaimHashComponentRelations,
    logup_batch: 2,
    embedded_preprocessed: {
        row_mask: "recursion_vm_claim_hash_row_mask",
        step: "recursion_vm_claim_hash_step",
        first: "recursion_vm_claim_hash_first_mask",
        last: "recursion_vm_claim_hash_last_mask",
        chunk_0_source_mask: "recursion_vm_claim_hash_chunk_0_source_mask",
        chunk_0_word_index: "recursion_vm_claim_hash_chunk_0_word_index",
        chunk_0_constant: "recursion_vm_claim_hash_chunk_0_constant",
        chunk_1_source_mask: "recursion_vm_claim_hash_chunk_1_source_mask",
        chunk_1_word_index: "recursion_vm_claim_hash_chunk_1_word_index",
        chunk_1_constant: "recursion_vm_claim_hash_chunk_1_constant",
        chunk_2_source_mask: "recursion_vm_claim_hash_chunk_2_source_mask",
        chunk_2_word_index: "recursion_vm_claim_hash_chunk_2_word_index",
        chunk_2_constant: "recursion_vm_claim_hash_chunk_2_constant",
        chunk_3_source_mask: "recursion_vm_claim_hash_chunk_3_source_mask",
        chunk_3_word_index: "recursion_vm_claim_hash_chunk_3_word_index",
        chunk_3_constant: "recursion_vm_claim_hash_chunk_3_constant",
        chunk_4_source_mask: "recursion_vm_claim_hash_chunk_4_source_mask",
        chunk_4_word_index: "recursion_vm_claim_hash_chunk_4_word_index",
        chunk_4_constant: "recursion_vm_claim_hash_chunk_4_constant",
        chunk_5_source_mask: "recursion_vm_claim_hash_chunk_5_source_mask",
        chunk_5_word_index: "recursion_vm_claim_hash_chunk_5_word_index",
        chunk_5_constant: "recursion_vm_claim_hash_chunk_5_constant",
        chunk_6_source_mask: "recursion_vm_claim_hash_chunk_6_source_mask",
        chunk_6_word_index: "recursion_vm_claim_hash_chunk_6_word_index",
        chunk_6_constant: "recursion_vm_claim_hash_chunk_6_constant",
        chunk_7_source_mask: "recursion_vm_claim_hash_chunk_7_source_mask",
        chunk_7_word_index: "recursion_vm_claim_hash_chunk_7_word_index",
        chunk_7_constant: "recursion_vm_claim_hash_chunk_7_constant",
    },
    embedded_params: [
        segment_active, hash_domain, hash_scope, verifier_id, verifier_input_kind,
    ],

    relation poseidon2_io(32);
    relation claim_word(3);
    relation state(17);
    relation input_word(5);

    fn vm_public_claim_hash(
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
        row_mask, step, first, last,
        chunk_0_source_mask, chunk_0_word_index, chunk_0_constant,
        chunk_1_source_mask, chunk_1_word_index, chunk_1_constant,
        chunk_2_source_mask, chunk_2_word_index, chunk_2_constant,
        chunk_3_source_mask, chunk_3_word_index, chunk_3_constant,
        chunk_4_source_mask, chunk_4_word_index, chunk_4_constant,
        chunk_5_source_mask, chunk_5_word_index, chunk_5_constant,
        chunk_6_source_mask, chunk_6_word_index, chunk_6_constant,
        chunk_7_source_mask, chunk_7_word_index, chunk_7_constant,
        segment_active, hash_domain, hash_scope, verifier_id, verifier_input_kind,
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
        // difference selects exactly the fixed padding constants.
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
        consume(segment_active * chunk_0_source_mask) claim_word(
            hash_scope, chunk_0_word_index, chunk_0,
        );
        consume(segment_active * chunk_1_source_mask) claim_word(
            hash_scope, chunk_1_word_index, chunk_1,
        );
        consume(segment_active * chunk_2_source_mask) claim_word(
            hash_scope, chunk_2_word_index, chunk_2,
        );
        consume(segment_active * chunk_3_source_mask) claim_word(
            hash_scope, chunk_3_word_index, chunk_3,
        );
        consume(segment_active * chunk_4_source_mask) claim_word(
            hash_scope, chunk_4_word_index, chunk_4,
        );
        consume(segment_active * chunk_5_source_mask) claim_word(
            hash_scope, chunk_5_word_index, chunk_5,
        );
        consume(segment_active * chunk_6_source_mask) claim_word(
            hash_scope, chunk_6_word_index, chunk_6,
        );
        consume(segment_active * chunk_7_source_mask) claim_word(
            hash_scope, chunk_7_word_index, chunk_7,
        );
        consume(segment_active * (row_mask - first)) state(
            step,
            previous_0, previous_1, previous_2, previous_3,
            previous_4, previous_5, previous_6, previous_7,
            previous_8, previous_9, previous_10, previous_11,
            previous_12, previous_13, previous_14, previous_15,
        );
        emit(segment_active * (row_mask - last)) state(
            step + 1,
            output_0, output_1, output_2, output_3,
            output_4, output_5, output_6, output_7,
            output_8, output_9, output_10, output_11,
            output_12, output_13, output_14, output_15,
        );
        consume(segment_active * last) input_word(
            verifier_id, verifier_input_kind, 0, 0, output_0,
        );
        consume(segment_active * last) input_word(
            verifier_id, verifier_input_kind, 0, 1, output_1,
        );
        consume(segment_active * last) input_word(
            verifier_id, verifier_input_kind, 0, 2, output_2,
        );
        consume(segment_active * last) input_word(
            verifier_id, verifier_input_kind, 0, 3, output_3,
        );
        consume(segment_active * last) input_word(
            verifier_id, verifier_input_kind, 0, 4, output_4,
        );
        consume(segment_active * last) input_word(
            verifier_id, verifier_input_kind, 0, 5, output_5,
        );
        consume(segment_active * last) input_word(
            verifier_id, verifier_input_kind, 0, 6, output_6,
        );
        consume(segment_active * last) input_word(
            verifier_id, verifier_input_kind, 0, 7, output_7,
        );

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
    claim_input_relations: &VmPublicClaimInputRelations,
    hash_relations: &VmPublicClaimHashRelations,
    verifier_input_relations: &VerifierInputRelations,
) -> Eval {
    Eval {
        log_size,
        segment_active: BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        hash_domain: BaseField::from(VM_PUBLIC_CLAIM_HASH_DOMAIN),
        hash_scope: BaseField::from(VM_CLAIM_HASH_SCOPE),
        verifier_id: BaseField::from(SEGMENT_VERIFIER_ID),
        verifier_input_kind: BaseField::from(VerifierInputKind::VmPublicClaimDigest.as_u32()),
        relations: VmPublicClaimHashComponentRelations::new(
            vm_relations,
            claim_input_relations,
            hash_relations,
            verifier_input_relations,
        ),
    }
}

/// Generate hash, claim-word, state-chain, and transcript-digest fractions.
#[allow(clippy::too_many_arguments)]
pub fn gen_interaction_trace(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    preprocessed: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    proof_kind: ProofKind,
    vm_relations: &Relations,
    claim_input_relations: &VmPublicClaimInputRelations,
    hash_relations: &VmPublicClaimHashRelations,
    verifier_input_relations: &VerifierInputRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    component::witness::gen_interaction_trace(
        trace,
        preprocessed,
        BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        BaseField::from(VM_PUBLIC_CLAIM_HASH_DOMAIN),
        BaseField::from(VM_CLAIM_HASH_SCOPE),
        BaseField::from(SEGMENT_VERIFIER_ID),
        BaseField::from(VerifierInputKind::VmPublicClaimDigest.as_u32()),
        &VmPublicClaimHashComponentRelations::new(
            vm_relations,
            claim_input_relations,
            hash_relations,
            verifier_input_relations,
        ),
    )
}

/// Records the fixed claim sponge and every reused Poseidon2 permutation.
pub fn push_vm_public_claim_hash(
    table: &mut VmPublicClaimHashTable,
    poseidon2: &mut Poseidon2Table,
    preprocessed: &VmPublicClaimHashPreprocessed,
    proof_kind: ProofKind,
    public_data: Option<&PublicData>,
) -> Result<(), VmPublicClaimHashError> {
    let active = proof_kind == ProofKind::SegmentLeaf;
    let words = match (active, public_data) {
        (true, Some(public_data)) => {
            canonical_vm_public_claim_words(public_data, preprocessed.shape)
                .map_err(VmPublicClaimHashError::Claim)?
        }
        (true, None) => return Err(VmPublicClaimHashError::SegmentClaimMissing),
        (false, Some(_)) => return Err(VmPublicClaimHashError::InactiveClaimProvided),
        (false, None) => Vec::new(),
    };
    if !active {
        for _ in &preprocessed.rows {
            table.push_row_values(&[0; 41]);
        }
        return Ok(());
    }

    let mut stream = words.iter().map(|word| word.as_u32()).collect::<Vec<_>>();
    stream.push(1);
    stream.resize(preprocessed.step_count() * RATE, 0);
    let mut state = [0_u32; T];
    state[T - 1] = VM_PUBLIC_CLAIM_HASH_DOMAIN;
    for (row_index, row) in preprocessed.rows.iter().enumerate() {
        let chunk: [u32; RATE] = stream[row_index * RATE..(row_index + 1) * RATE]
            .try_into()
            .expect("trusted chunk width is fixed");
        let mut permutation_input = state;
        for (value, absorbed) in permutation_input.iter_mut().zip(chunk) {
            *value = (u64::from(*value) + u64::from(absorbed))
                .rem_euclid(u64::from(stwo::core::fields::m31::P)) as u32;
        }
        let output = poseidon2_traced_state(poseidon2, permutation_input, false, true);
        let mut values = Vec::with_capacity(41);
        values.push(1);
        values.extend(state);
        values.extend(chunk);
        values.extend(output);
        table.push_row_values(&values);
        state = output;
        debug_assert_eq!(row.step as usize, row_index);
    }
    let expected = vm_public_claim_digest(
        public_data.expect("active claim was checked above"),
        preprocessed.shape,
    )
    .map_err(VmPublicClaimHashError::Claim)?;
    let actual = &state[..RATE];
    if actual != expected.digest().words().map(M31Word::as_u32) {
        return Err(VmPublicClaimHashError::DigestMismatch);
    }
    Ok(())
}

impl VmPublicClaimHashTable {
    fn push_row_values(&mut self, values: &[u32]) {
        self.push_row(values);
    }
}

/// Invalid trusted hash schedule or claim witness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VmPublicClaimHashError {
    Claim(VmPublicClaimError),
    RowCountOverflow,
    WordIndexOutOfRange { index: usize },
    StepOutOfRange { step: usize },
    LogSizeOutOfRange { log_size: u32 },
    SegmentClaimMissing,
    InactiveClaimProvided,
    DigestMismatch,
}

impl fmt::Display for VmPublicClaimHashError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Claim(error) => write!(formatter, "invalid VM public claim: {error}"),
            Self::RowCountOverflow => write!(formatter, "VM claim hash row count overflowed"),
            Self::WordIndexOutOfRange { index } => {
                write!(formatter, "VM claim hash word index {index} exceeds u32")
            }
            Self::StepOutOfRange { step } => {
                write!(formatter, "VM claim hash step {step} exceeds u32")
            }
            Self::LogSizeOutOfRange { log_size } => write!(
                formatter,
                "VM claim hash log size {log_size} exceeds {MAX_LOG_SIZE}"
            ),
            Self::SegmentClaimMissing => write!(formatter, "segment leaf has no VM public claim"),
            Self::InactiveClaimProvided => {
                write!(formatter, "non-segment proof carries a VM public claim")
            }
            Self::DigestMismatch => write!(formatter, "VM claim hash output disagrees with digest"),
        }
    }
}

impl std::error::Error for VmPublicClaimHashError {}

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
            VmPublicClaimHashPreprocessed::new(shape()).expect("fixture shape is supported");
        let claim = public_data();
        let witness = (kind == ProofKind::SegmentLeaf).then_some(&claim);
        let mut table = VmPublicClaimHashTable::new();
        push_vm_public_claim_hash(
            &mut table,
            &mut Poseidon2Table::new(),
            &preprocessing,
            kind,
            witness,
        )
        .expect("fixture claim hash materializes");
        match tamper {
            Some(HashTamper::InitialCapacity) => table.previous_15[0] = 0,
            Some(HashTamper::EndMarker) => {
                let marker_index = preprocessing.shape.claim_word_count();
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
        let claim_input_relations = VmPublicClaimInputRelations::dummy();
        let hash_relations = VmPublicClaimHashRelations::dummy();
        let verifier_input_relations = VerifierInputRelations::dummy();
        let preprocessed = preprocessing.gen_columns();
        let trace = table.into_witness();
        let (interaction, claimed_sum) = gen_interaction_trace(
            &trace,
            &preprocessed,
            kind,
            &vm_relations,
            &claim_input_relations,
            &hash_relations,
            &verifier_input_relations,
        );
        let traces = TreeVec::new(vec![preprocessed, trace, interaction]);
        let trace_polys = traces.map_cols(|column| column.interpolate());
        let eval = eval_for_proof_kind(
            preprocessing.log_size(),
            kind,
            &vm_relations,
            &claim_input_relations,
            &hash_relations,
            &verifier_input_relations,
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

    fn complete_relation_sum(tamper_previous: bool) -> QM31 {
        let shape = shape();
        let preprocessing =
            VmPublicClaimHashPreprocessed::new(shape).expect("fixture shape is supported");
        let claim = public_data();
        let mut table = VmPublicClaimHashTable::new();
        let mut poseidon2 = Poseidon2Table::new();
        push_vm_public_claim_hash(
            &mut table,
            &mut poseidon2,
            &preprocessing,
            ProofKind::SegmentLeaf,
            Some(&claim),
        )
        .expect("fixture claim hash materializes");
        if tamper_previous {
            table.previous_0[1] += 1;
        }

        let mut channel = Poseidon2M31Channel::default();
        let vm_relations = Relations::draw(&mut channel);
        let claim_input_relations = VmPublicClaimInputRelations::draw(&mut channel);
        let hash_relations = VmPublicClaimHashRelations::draw(&mut channel);
        let verifier_input_relations = VerifierInputRelations::draw(&mut channel);
        let trace = table.into_witness();
        let (_, hash_sum) = gen_interaction_trace(
            &trace,
            &preprocessing.gen_columns(),
            ProofKind::SegmentLeaf,
            &vm_relations,
            &claim_input_relations,
            &hash_relations,
            &verifier_input_relations,
        );
        let poseidon_trace = poseidon2.into_witness();
        let (_, poseidon_sum) = air::poseidon2::component::witness::gen_interaction_trace(
            &poseidon_trace,
            &vm_relations,
        );
        hash_sum
            + poseidon_sum
            + claim_hash_source_terms(&claim, shape, &claim_input_relations)
            + digest_source_terms(&claim, shape, &verifier_input_relations)
    }

    fn claim_hash_source_terms(
        claim: &PublicData,
        shape: VmPublicClaimShape,
        relations: &VmPublicClaimInputRelations,
    ) -> QM31 {
        canonical_vm_public_claim_words(claim, shape)
            .expect("fixture claim is canonical")
            .into_iter()
            .enumerate()
            .fold(QM31::zero(), |sum, (index, word)| {
                let denominator: QM31 = relations.claim_word.combine(&[
                    M31::from(VM_CLAIM_HASH_SCOPE),
                    M31::from(u32::try_from(index).expect("fixture word index fits u32")),
                    M31::from(word.as_u32()),
                ]);
                sum + denominator.inverse()
            })
    }

    fn digest_source_terms(
        claim: &PublicData,
        shape: VmPublicClaimShape,
        relations: &VerifierInputRelations,
    ) -> QM31 {
        vm_public_claim_digest(claim, shape)
            .expect("fixture claim is canonical")
            .digest()
            .words()
            .iter()
            .copied()
            .enumerate()
            .fold(QM31::zero(), |sum, (limb, word)| {
                let denominator: QM31 = relations.input_word.combine(&[
                    M31::from(SEGMENT_VERIFIER_ID),
                    M31::from(VerifierInputKind::VmPublicClaimDigest.as_u32()),
                    M31::from(0),
                    M31::from(u32::try_from(limb).expect("digest limb fits u32")),
                    M31::from(word.as_u32()),
                ]);
                sum + denominator.inverse()
            })
    }

    #[rstest]
    #[case::segment(ProofKind::SegmentLeaf)]
    #[case::binary(ProofKind::BinaryNode)]
    #[case::empty(ProofKind::EmptyLeaf)]
    fn every_universal_mode_satisfies_claim_hash_constraints(#[case] kind: ProofKind) {
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
    fn inactive_hash_state_must_be_zero() {
        assert_constraints(ProofKind::EmptyLeaf, Some(HashTamper::InactiveState));
    }

    #[rstest]
    fn complete_claim_hash_relations_cancel() {
        assert!(complete_relation_sum(false).is_zero());
    }

    #[rstest]
    fn a_disconnected_internal_state_does_not_cancel() {
        assert!(!complete_relation_sum(true).is_zero());
    }
}
