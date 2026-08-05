//! Canonical commitments for the VM claim hidden inside a segment leaf.
//!
//! The existing VM claim contains variable-length input and output vectors,
//! register access clocks, and optional roots. A recursion leaf commits that
//! complete value before drawing relation challenges, while the fixed root
//! statement exposes only semantic execution boundaries and IO digests. Raw
//! machine words are split into 16-bit limbs so the encoding remains injective
//! over all `u32` values.

use core::fmt;

use air::digest::{IoDigest, M31Word, VmPublicClaimDigest};
use prover::poseidon2_channel::poseidon2_hash_m31_words;
use prover::public_data::{IoEntries, PublicData};

const VM_PUBLIC_CLAIM_HASH_DOMAIN: u16 = 0x5643;
const PUBLIC_INPUT_HASH_DOMAIN: u16 = 0x5649;
const PUBLIC_OUTPUT_HASH_DOMAIN: u16 = 0x564f;

const FIXED_CLAIM_WORDS: usize = 259;
const INPUT_SLOT_WORDS: usize = 3;
const OUTPUT_SLOT_WORDS: usize = 7;

#[derive(Clone, Copy)]
#[repr(u16)]
enum ClaimTag {
    Claim = 1,
    InitialPc = 2,
    FinalPc = 3,
    Clock = 4,
    InitialRegisters = 5,
    FinalRegisters = 6,
    RegisterLastClocks = 7,
    ProgramRoot = 8,
    InitialRwRoot = 9,
    FinalRwRoot = 10,
    IoHeader = 11,
    InputWords = 12,
    OutputWords = 13,
    Shape = 14,
    PublicInput = 20,
    PublicOutput = 21,
}

impl ClaimTag {
    fn word(self) -> M31Word {
        M31Word::from(self as u16)
    }
}

/// Verifier-owned capacity of the fixed VM public-claim encoding.
///
/// The recursion preprocessing fixes this shape. Each claim carries the same
/// number of input and output slots, with absent suffix slots constrained to
/// zero, so neither vector length can alter the verifier circuit or hash
/// schedule.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct VmPublicClaimShape {
    max_input_words: u32,
    max_output_words: u32,
}

impl VmPublicClaimShape {
    pub fn new(max_input_words: u32, max_output_words: u32) -> Result<Self, VmPublicClaimError> {
        M31Word::try_from(max_input_words).map_err(|_| {
            VmPublicClaimError::ShapeCapacityOutOfRange {
                field: "input words",
                capacity: max_input_words,
            }
        })?;
        M31Word::try_from(max_output_words).map_err(|_| {
            VmPublicClaimError::ShapeCapacityOutOfRange {
                field: "output words",
                capacity: max_output_words,
            }
        })?;
        let word_count = checked_claim_word_count(max_input_words, max_output_words)?;
        let last_word = word_count
            .checked_sub(1)
            .and_then(|index| u32::try_from(index).ok())
            .and_then(|index| M31Word::try_from(index).ok());
        if last_word.is_none() {
            return Err(VmPublicClaimError::ShapeWordCountOutOfRange { word_count });
        }
        Ok(Self {
            max_input_words,
            max_output_words,
        })
    }

    pub const fn max_input_words(self) -> u32 {
        self.max_input_words
    }

    pub const fn max_output_words(self) -> u32 {
        self.max_output_words
    }

    pub fn claim_word_count(self) -> usize {
        checked_claim_word_count(self.max_input_words, self.max_output_words)
            .expect("validated VM public-claim shape has a representable word count")
    }
}

/// Constraint class of one word in the canonical fixed claim.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VmPublicClaimWordKind {
    Constant(M31Word),
    Boolean,
    U16,
    Field,
}

/// Word offsets shared by claim encoding and its fixed verifier circuit.
pub mod canonical_layout {
    use super::{INPUT_SLOT_WORDS, OUTPUT_SLOT_WORDS, VmPublicClaimShape};

    pub const CLAIM_TAG: usize = 0;
    pub const SHAPE_TAG: usize = 1;
    pub const MAX_INPUT_WORDS_START: usize = 2;
    pub const MAX_OUTPUT_WORDS_START: usize = 4;
    pub const INITIAL_PC_TAG: usize = 6;
    pub const INITIAL_PC_START: usize = 7;
    pub const FINAL_PC_TAG: usize = 9;
    pub const FINAL_PC_START: usize = 10;
    pub const CLOCK_TAG: usize = 12;
    pub const CLOCK_START: usize = 13;
    pub const INITIAL_REGISTERS_TAG: usize = 15;
    pub const INITIAL_REGISTERS_START: usize = 16;
    pub const FINAL_REGISTERS_TAG: usize = 80;
    pub const FINAL_REGISTERS_START: usize = 81;
    pub const REGISTER_LAST_CLOCKS_TAG: usize = 145;
    pub const REGISTER_LAST_CLOCKS_START: usize = 146;
    pub const PROGRAM_ROOT_TAG: usize = 210;
    pub const PROGRAM_ROOT_PRESENT: usize = 211;
    pub const PROGRAM_ROOT_START: usize = 212;
    pub const INITIAL_RW_ROOT_TAG: usize = 220;
    pub const INITIAL_RW_ROOT_PRESENT: usize = 221;
    pub const INITIAL_RW_ROOT_START: usize = 222;
    pub const FINAL_RW_ROOT_TAG: usize = 230;
    pub const FINAL_RW_ROOT_PRESENT: usize = 231;
    pub const FINAL_RW_ROOT_START: usize = 232;
    pub const IO_HEADER_TAG: usize = 240;
    pub const INPUT_START_START: usize = 241;
    pub const INPUT_LENGTH_START: usize = 243;
    pub const OUTPUT_LENGTH_ADDRESS_START: usize = 245;
    pub const OUTPUT_DATA_ADDRESS_START: usize = 247;
    pub const OUTPUT_LENGTH_START: usize = 249;
    pub const HEADER_OUTPUT_WORD_COUNT_START: usize = 251;
    pub const INPUT_WORDS_TAG: usize = 253;
    pub const INPUT_WORD_COUNT_START: usize = 254;
    pub const INPUT_SLOTS_START: usize = 256;

    pub const fn input_slot_present(index: usize) -> usize {
        INPUT_SLOTS_START + index * INPUT_SLOT_WORDS
    }

    pub const fn input_slot_value_start(index: usize) -> usize {
        input_slot_present(index) + 1
    }

    pub const fn output_words_tag(shape: VmPublicClaimShape) -> usize {
        INPUT_SLOTS_START + shape.max_input_words() as usize * INPUT_SLOT_WORDS
    }

    pub const fn output_word_count_start(shape: VmPublicClaimShape) -> usize {
        output_words_tag(shape) + 1
    }

    pub const fn output_slots_start(shape: VmPublicClaimShape) -> usize {
        output_words_tag(shape) + 3
    }

    pub const fn output_slot_present(shape: VmPublicClaimShape, index: usize) -> usize {
        output_slots_start(shape) + index * OUTPUT_SLOT_WORDS
    }

    pub const fn output_slot_address_start(shape: VmPublicClaimShape, index: usize) -> usize {
        output_slot_present(shape, index) + 1
    }

    pub const fn output_slot_value_start(shape: VmPublicClaimShape, index: usize) -> usize {
        output_slot_present(shape, index) + 3
    }

    pub const fn output_slot_clock_start(shape: VmPublicClaimShape, index: usize) -> usize {
        output_slot_present(shape, index) + 5
    }
}

/// Returns the complete verifier-owned word classification for one shape.
pub fn canonical_vm_public_claim_word_kinds(
    shape: VmPublicClaimShape,
) -> Vec<VmPublicClaimWordKind> {
    let mut kinds = Vec::with_capacity(shape.claim_word_count());
    push_constant(&mut kinds, ClaimTag::Claim.word());
    push_constant(&mut kinds, ClaimTag::Shape.word());
    push_constant_u32(&mut kinds, shape.max_input_words);
    push_constant_u32(&mut kinds, shape.max_output_words);
    push_tagged_u32_kind(&mut kinds, ClaimTag::InitialPc);
    push_tagged_u32_kind(&mut kinds, ClaimTag::FinalPc);
    push_tagged_u32_kind(&mut kinds, ClaimTag::Clock);
    push_tagged_u32s_kind(&mut kinds, ClaimTag::InitialRegisters, 32);
    push_tagged_u32s_kind(&mut kinds, ClaimTag::FinalRegisters, 32);
    push_tagged_u32s_kind(&mut kinds, ClaimTag::RegisterLastClocks, 32);
    push_optional_root_kind(&mut kinds, ClaimTag::ProgramRoot);
    push_optional_root_kind(&mut kinds, ClaimTag::InitialRwRoot);
    push_optional_root_kind(&mut kinds, ClaimTag::FinalRwRoot);
    push_constant(&mut kinds, ClaimTag::IoHeader.word());
    push_u32_kinds(&mut kinds, 6);
    push_constant(&mut kinds, ClaimTag::InputWords.word());
    push_u32_kinds(&mut kinds, 1);
    for _ in 0..shape.max_input_words {
        kinds.push(VmPublicClaimWordKind::Boolean);
        push_u32_kinds(&mut kinds, 1);
    }
    push_constant(&mut kinds, ClaimTag::OutputWords.word());
    push_u32_kinds(&mut kinds, 1);
    for _ in 0..shape.max_output_words {
        kinds.push(VmPublicClaimWordKind::Boolean);
        push_u32_kinds(&mut kinds, 3);
    }
    debug_assert_eq!(kinds.len(), shape.claim_word_count());
    kinds
}

fn push_constant(kinds: &mut Vec<VmPublicClaimWordKind>, value: M31Word) {
    kinds.push(VmPublicClaimWordKind::Constant(value));
}

fn push_constant_u32(kinds: &mut Vec<VmPublicClaimWordKind>, value: u32) {
    push_constant(kinds, M31Word::from((value & 0xffff) as u16));
    push_constant(kinds, M31Word::from((value >> 16) as u16));
}

fn push_u32_kinds(kinds: &mut Vec<VmPublicClaimWordKind>, count: usize) {
    kinds.extend(core::iter::repeat_n(VmPublicClaimWordKind::U16, count * 2));
}

fn push_tagged_u32_kind(kinds: &mut Vec<VmPublicClaimWordKind>, tag: ClaimTag) {
    push_constant(kinds, tag.word());
    push_u32_kinds(kinds, 1);
}

fn push_tagged_u32s_kind(kinds: &mut Vec<VmPublicClaimWordKind>, tag: ClaimTag, count: usize) {
    push_constant(kinds, tag.word());
    push_u32_kinds(kinds, count);
}

fn push_optional_root_kind(kinds: &mut Vec<VmPublicClaimWordKind>, tag: ClaimTag) {
    push_constant(kinds, tag.word());
    kinds.push(VmPublicClaimWordKind::Boolean);
    kinds.extend([VmPublicClaimWordKind::Field; 8]);
}

/// Encodes every field that contributes VM public LogUp terms or transcript state.
pub fn canonical_vm_public_claim_words(
    public_data: &PublicData,
    shape: VmPublicClaimShape,
) -> Result<Vec<M31Word>, VmPublicClaimError> {
    validate_vector_capacity(
        "input words",
        public_data.io_entries.input_words.len(),
        shape.max_input_words,
    )?;
    validate_vector_capacity(
        "output words",
        public_data.io_entries.output_words.len(),
        shape.max_output_words,
    )?;
    let mut words = Vec::with_capacity(shape.claim_word_count());
    words.push(ClaimTag::Claim.word());
    append_shape(&mut words, shape);
    append_tagged_u32(&mut words, ClaimTag::InitialPc, public_data.initial_pc);
    append_tagged_u32(&mut words, ClaimTag::FinalPc, public_data.final_pc);
    append_tagged_u32(&mut words, ClaimTag::Clock, public_data.clock);
    append_tagged_u32s(
        &mut words,
        ClaimTag::InitialRegisters,
        &public_data.initial_regs,
    );
    append_tagged_u32s(
        &mut words,
        ClaimTag::FinalRegisters,
        &public_data.final_regs,
    );
    append_tagged_u32s(
        &mut words,
        ClaimTag::RegisterLastClocks,
        &public_data.reg_last_clock,
    );
    append_optional_root(
        &mut words,
        ClaimTag::ProgramRoot,
        "program root",
        public_data.program_root,
    )?;
    append_optional_root(
        &mut words,
        ClaimTag::InitialRwRoot,
        "initial read-write root",
        public_data.initial_rw_root,
    )?;
    append_optional_root(
        &mut words,
        ClaimTag::FinalRwRoot,
        "final read-write root",
        public_data.final_rw_root,
    )?;
    append_io_header(&mut words, &public_data.io_entries)?;
    append_input_words(&mut words, &public_data.io_entries, shape)?;
    append_output_words(&mut words, &public_data.io_entries, shape)?;
    debug_assert_eq!(words.len(), shape.claim_word_count());
    Ok(words)
}

/// Commits the exact VM claim that the leaf's public-LogUp circuit consumes.
pub fn vm_public_claim_digest(
    public_data: &PublicData,
    shape: VmPublicClaimShape,
) -> Result<VmPublicClaimDigest, VmPublicClaimError> {
    let words = canonical_vm_public_claim_words(public_data, shape)?;
    vm_public_claim_digest_from_words(&words, shape)
}

/// Commits an already encoded fixed VM claim without reconstructing host data.
pub fn vm_public_claim_digest_from_words(
    words: &[M31Word],
    shape: VmPublicClaimShape,
) -> Result<VmPublicClaimDigest, VmPublicClaimError> {
    validate_claim_word_count(words, shape)?;
    Ok(VmPublicClaimDigest::from(poseidon2_hash_m31_words(
        words,
        M31Word::from(VM_PUBLIC_CLAIM_HASH_DOMAIN),
    )))
}

/// Commits the application-visible input independently of proof access clocks.
pub fn public_input_digest(
    io: &IoEntries,
    shape: VmPublicClaimShape,
) -> Result<IoDigest, VmPublicClaimError> {
    let words = canonical_public_input_words(io, shape)?;
    Ok(IoDigest::from(poseidon2_hash_m31_words(
        &words,
        M31Word::from(PUBLIC_INPUT_HASH_DOMAIN),
    )))
}

/// Fixed application-input words consumed by the input-digest hash AIR.
pub fn canonical_public_input_words(
    io: &IoEntries,
    shape: VmPublicClaimShape,
) -> Result<Vec<M31Word>, VmPublicClaimError> {
    validate_vector_capacity("input words", io.input_words.len(), shape.max_input_words)?;
    let mut words = Vec::with_capacity(6 + INPUT_SLOT_WORDS * shape.max_input_words as usize);
    words.push(ClaimTag::PublicInput.word());
    append_u32(&mut words, shape.max_input_words);
    append_u32(&mut words, io.input_start);
    append_u32(&mut words, io.input_len);
    append_length(&mut words, "input words", io.input_words.len())?;
    for index in 0..shape.max_input_words as usize {
        let value = io.input_words.get(index).copied();
        words.push(M31Word::from(u16::from(value.is_some())));
        append_u32(&mut words, value.unwrap_or(0));
    }
    Ok(words)
}

/// Derives the public-input hash stream from the fixed VM claim encoding.
pub fn canonical_public_input_words_from_claim(
    claim: &[M31Word],
    shape: VmPublicClaimShape,
) -> Result<Vec<M31Word>, VmPublicClaimError> {
    validate_claim_word_count(claim, shape)?;
    let mut words = Vec::with_capacity(6 + INPUT_SLOT_WORDS * shape.max_input_words as usize);
    words.push(ClaimTag::PublicInput.word());
    words.extend_from_slice(&claim[canonical_layout::MAX_INPUT_WORDS_START..][..2]);
    words.extend_from_slice(&claim[canonical_layout::INPUT_START_START..][..2]);
    words.extend_from_slice(&claim[canonical_layout::INPUT_LENGTH_START..][..2]);
    words.extend_from_slice(&claim[canonical_layout::INPUT_WORD_COUNT_START..][..2]);
    words.extend_from_slice(
        &claim[canonical_layout::INPUT_SLOTS_START..canonical_layout::output_words_tag(shape)],
    );
    Ok(words)
}

/// Commits the application-visible output while leaving proof-only clocks in the VM claim.
pub fn public_output_digest(
    io: &IoEntries,
    shape: VmPublicClaimShape,
) -> Result<IoDigest, VmPublicClaimError> {
    let words = canonical_public_output_words(io, shape)?;
    Ok(IoDigest::from(poseidon2_hash_m31_words(
        &words,
        M31Word::from(PUBLIC_OUTPUT_HASH_DOMAIN),
    )))
}

/// Fixed application-output words consumed by the output-digest hash AIR.
pub fn canonical_public_output_words(
    io: &IoEntries,
    shape: VmPublicClaimShape,
) -> Result<Vec<M31Word>, VmPublicClaimError> {
    validate_vector_capacity(
        "output words",
        io.output_words.len(),
        shape.max_output_words,
    )?;
    let mut words = Vec::with_capacity(10 + 5 * shape.max_output_words as usize);
    words.push(ClaimTag::PublicOutput.word());
    append_u32(&mut words, shape.max_output_words);
    append_u32(&mut words, io.output_len_addr);
    append_u32(&mut words, io.output_data_addr);
    append_u32(&mut words, io.output_len);
    append_length(&mut words, "output words", io.output_words.len())?;
    for index in 0..shape.max_output_words as usize {
        let word = io.output_words.get(index);
        words.push(M31Word::from(u16::from(word.is_some())));
        append_u32(&mut words, word.map_or(0, |word| word.addr));
        append_u32(&mut words, word.map_or(0, |word| word.value));
    }
    Ok(words)
}

/// Derives the public-output hash stream from the fixed VM claim encoding.
pub fn canonical_public_output_words_from_claim(
    claim: &[M31Word],
    shape: VmPublicClaimShape,
) -> Result<Vec<M31Word>, VmPublicClaimError> {
    validate_claim_word_count(claim, shape)?;
    let mut words = Vec::with_capacity(10 + 5 * shape.max_output_words as usize);
    words.push(ClaimTag::PublicOutput.word());
    words.extend_from_slice(&claim[canonical_layout::MAX_OUTPUT_WORDS_START..][..2]);
    words.extend_from_slice(&claim[canonical_layout::OUTPUT_LENGTH_ADDRESS_START..][..2]);
    words.extend_from_slice(&claim[canonical_layout::OUTPUT_DATA_ADDRESS_START..][..2]);
    words.extend_from_slice(&claim[canonical_layout::OUTPUT_LENGTH_START..][..2]);
    words.extend_from_slice(&claim[canonical_layout::output_word_count_start(shape)..][..2]);
    for index in 0..shape.max_output_words as usize {
        let start = canonical_layout::output_slot_present(shape, index);
        words.extend_from_slice(&claim[start..][..5]);
    }
    Ok(words)
}

/// Commits the public input directly from the fixed VM claim encoding.
pub fn public_input_digest_from_claim(
    claim: &[M31Word],
    shape: VmPublicClaimShape,
) -> Result<IoDigest, VmPublicClaimError> {
    let words = canonical_public_input_words_from_claim(claim, shape)?;
    Ok(IoDigest::from(poseidon2_hash_m31_words(
        &words,
        M31Word::from(PUBLIC_INPUT_HASH_DOMAIN),
    )))
}

/// Commits the public output directly from the fixed VM claim encoding.
pub fn public_output_digest_from_claim(
    claim: &[M31Word],
    shape: VmPublicClaimShape,
) -> Result<IoDigest, VmPublicClaimError> {
    let words = canonical_public_output_words_from_claim(claim, shape)?;
    Ok(IoDigest::from(poseidon2_hash_m31_words(
        &words,
        M31Word::from(PUBLIC_OUTPUT_HASH_DOMAIN),
    )))
}

fn validate_claim_word_count(
    claim: &[M31Word],
    shape: VmPublicClaimShape,
) -> Result<(), VmPublicClaimError> {
    let expected = shape.claim_word_count();
    if claim.len() == expected {
        Ok(())
    } else {
        Err(VmPublicClaimError::ClaimWordCountMismatch {
            expected,
            actual: claim.len(),
        })
    }
}

fn append_shape(words: &mut Vec<M31Word>, shape: VmPublicClaimShape) {
    words.push(ClaimTag::Shape.word());
    append_u32(words, shape.max_input_words);
    append_u32(words, shape.max_output_words);
}

fn append_tagged_u32(words: &mut Vec<M31Word>, tag: ClaimTag, value: u32) {
    words.push(tag.word());
    append_u32(words, value);
}

fn append_tagged_u32s(words: &mut Vec<M31Word>, tag: ClaimTag, values: &[u32]) {
    words.push(tag.word());
    for value in values {
        append_u32(words, *value);
    }
}

fn append_u32(words: &mut Vec<M31Word>, value: u32) {
    words.extend([
        M31Word::from((value & 0xffff) as u16),
        M31Word::from((value >> 16) as u16),
    ]);
}

fn append_length(
    words: &mut Vec<M31Word>,
    field: &'static str,
    length: usize,
) -> Result<(), VmPublicClaimError> {
    let length = u32::try_from(length)
        .map_err(|_| VmPublicClaimError::LengthOutOfRange { field, length })?;
    append_u32(words, length);
    Ok(())
}

fn append_optional_root(
    words: &mut Vec<M31Word>,
    tag: ClaimTag,
    field: &'static str,
    root: Option<[u32; 8]>,
) -> Result<(), VmPublicClaimError> {
    words.push(tag.word());
    words.push(M31Word::from(u16::from(root.is_some())));
    let root = root.unwrap_or([0; 8]);
    for (index, value) in root.into_iter().enumerate() {
        let word = M31Word::try_from(value).map_err(|_| VmPublicClaimError::NonCanonicalRoot {
            field,
            index,
            value,
        })?;
        words.push(word);
    }
    Ok(())
}

fn append_io_header(words: &mut Vec<M31Word>, io: &IoEntries) -> Result<(), VmPublicClaimError> {
    words.push(ClaimTag::IoHeader.word());
    append_u32(words, io.input_start);
    append_u32(words, io.input_len);
    append_u32(words, io.output_len_addr);
    append_u32(words, io.output_data_addr);
    append_u32(words, io.output_len);
    append_length(words, "output words", io.output_words.len())
}

fn append_input_words(
    words: &mut Vec<M31Word>,
    io: &IoEntries,
    shape: VmPublicClaimShape,
) -> Result<(), VmPublicClaimError> {
    words.push(ClaimTag::InputWords.word());
    append_length(words, "input words", io.input_words.len())?;
    for index in 0..shape.max_input_words as usize {
        let value = io.input_words.get(index).copied();
        words.push(M31Word::from(u16::from(value.is_some())));
        append_u32(words, value.unwrap_or(0));
    }
    Ok(())
}

fn append_output_words(
    words: &mut Vec<M31Word>,
    io: &IoEntries,
    shape: VmPublicClaimShape,
) -> Result<(), VmPublicClaimError> {
    words.push(ClaimTag::OutputWords.word());
    append_length(words, "output words", io.output_words.len())?;
    for index in 0..shape.max_output_words as usize {
        let word = io.output_words.get(index);
        words.push(M31Word::from(u16::from(word.is_some())));
        append_u32(words, word.map_or(0, |word| word.addr));
        append_u32(words, word.map_or(0, |word| word.value));
        append_u32(words, word.map_or(0, |word| word.clock));
    }
    Ok(())
}

fn checked_claim_word_count(
    max_input_words: u32,
    max_output_words: u32,
) -> Result<usize, VmPublicClaimError> {
    let input_words = usize::try_from(max_input_words)
        .ok()
        .and_then(|count| count.checked_mul(INPUT_SLOT_WORDS));
    let output_words = usize::try_from(max_output_words)
        .ok()
        .and_then(|count| count.checked_mul(OUTPUT_SLOT_WORDS));
    input_words
        .zip(output_words)
        .and_then(|(input, output)| FIXED_CLAIM_WORDS.checked_add(input)?.checked_add(output))
        .ok_or(VmPublicClaimError::ShapeWordCountOverflow)
}

fn validate_vector_capacity(
    field: &'static str,
    length: usize,
    capacity: u32,
) -> Result<(), VmPublicClaimError> {
    let capacity = usize::try_from(capacity)
        .map_err(|_| VmPublicClaimError::ShapeCapacityOutOfRange { field, capacity })?;
    if length > capacity {
        return Err(VmPublicClaimError::VectorExceedsShape {
            field,
            length,
            capacity,
        });
    }
    Ok(())
}

/// A VM claim that cannot enter the canonical digest input.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VmPublicClaimError {
    ClaimWordCountMismatch {
        expected: usize,
        actual: usize,
    },
    LengthOutOfRange {
        field: &'static str,
        length: usize,
    },
    NonCanonicalRoot {
        field: &'static str,
        index: usize,
        value: u32,
    },
    ShapeCapacityOutOfRange {
        field: &'static str,
        capacity: u32,
    },
    ShapeWordCountOverflow,
    ShapeWordCountOutOfRange {
        word_count: usize,
    },
    VectorExceedsShape {
        field: &'static str,
        length: usize,
        capacity: usize,
    },
}

impl fmt::Display for VmPublicClaimError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ClaimWordCountMismatch { expected, actual } => write!(
                formatter,
                "VM public claim has {actual} words, expected {expected}"
            ),
            Self::LengthOutOfRange { field, length } => {
                write!(
                    formatter,
                    "VM public claim has {length} {field}, exceeding u32"
                )
            }
            Self::NonCanonicalRoot {
                field,
                index,
                value,
            } => write!(
                formatter,
                "VM public claim {field} limb {index} is 0x{value:08x}, not canonical M31"
            ),
            Self::ShapeCapacityOutOfRange { field, capacity } => write!(
                formatter,
                "VM public-claim shape has {capacity} {field}, which is not a canonical M31 count"
            ),
            Self::ShapeWordCountOverflow => {
                write!(
                    formatter,
                    "VM public-claim shape word count overflows usize"
                )
            }
            Self::ShapeWordCountOutOfRange { word_count } => write!(
                formatter,
                "VM public-claim shape has {word_count} words, exceeding canonical M31 indices"
            ),
            Self::VectorExceedsShape {
                field,
                length,
                capacity,
            } => write!(
                formatter,
                "VM public claim has {length} {field}, exceeding its fixed capacity {capacity}"
            ),
        }
    }
}

impl std::error::Error for VmPublicClaimError {}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use air::digest::Digest8;
    use prover::public_data::OutputWord;
    use stwo::core::fields::m31::P as M31_MODULUS;

    pub(crate) fn shape() -> VmPublicClaimShape {
        VmPublicClaimShape::new(3, 3).expect("fixture claim shape is canonical")
    }

    pub(crate) fn public_data() -> PublicData {
        let mut initial_regs = [0_u32; 32];
        initial_regs[1] = 0x8000_0001;
        let mut final_regs = initial_regs;
        final_regs[2] = 9;
        let mut reg_last_clock = [0_u32; 32];
        reg_last_clock[2] = 7;
        PublicData {
            initial_pc: 0x1000,
            final_pc: 0x1004,
            clock: 8,
            initial_regs,
            final_regs,
            reg_last_clock,
            program_root: Some([1, 2, 3, 4, 5, 6, 7, 8]),
            initial_rw_root: Some([11, 12, 13, 14, 15, 16, 17, 18]),
            final_rw_root: Some([21, 22, 23, 24, 25, 26, 27, 28]),
            io_entries: IoEntries {
                input_start: 0x20_0000,
                input_len: 5,
                input_words: vec![0x4433_2211, 0x55],
                output_len: 4,
                output_len_addr: 0x10_0004,
                output_data_addr: 0x10_0008,
                output_words: vec![
                    OutputWord {
                        addr: 0x10_0004,
                        value: 4,
                        clock: 6,
                    },
                    OutputWord {
                        addr: 0x10_0008,
                        value: 0x8877_6655,
                        clock: 7,
                    },
                ],
            },
        }
    }

    #[test]
    fn vm_public_claim_digest_matches_its_conformance_value() {
        assert_eq!(
            vm_public_claim_digest(&public_data(), shape()),
            Ok(VmPublicClaimDigest::from(Digest8::new(
                [
                    430_820_593_u32,
                    1_891_182_383,
                    113_085_284,
                    1_635_530_231,
                    1_350_730_882,
                    432_104_742,
                    980_554_028,
                    240_635_051,
                ]
                .map(|value| { M31Word::try_from(value).expect("conformance word is canonical") }),
            )))
        );
    }

    #[test]
    fn vm_public_claim_digest_binds_register_last_clocks() {
        let first = public_data();
        let mut second = public_data();
        second.reg_last_clock[2] += 1;
        assert_ne!(
            vm_public_claim_digest(&first, shape()),
            vm_public_claim_digest(&second, shape())
        );
    }

    #[test]
    fn vm_public_claim_digest_binds_input_vector_boundaries() {
        let first = public_data();
        let mut second = public_data();
        second.io_entries.input_words.push(0);
        assert_ne!(
            vm_public_claim_digest(&first, shape()),
            vm_public_claim_digest(&second, shape())
        );
    }

    #[test]
    fn vm_public_claim_digest_binds_the_last_output_clock() {
        let first = public_data();
        let mut second = public_data();
        second
            .io_entries
            .output_words
            .last_mut()
            .expect("fixture output is nonempty")
            .clock += 1;
        assert_ne!(
            vm_public_claim_digest(&first, shape()),
            vm_public_claim_digest(&second, shape())
        );
    }

    #[test]
    fn vm_public_claim_digest_distinguishes_absent_and_zero_roots() {
        let mut absent = public_data();
        absent.program_root = None;
        let mut zero = public_data();
        zero.program_root = Some([0; 8]);
        assert_ne!(
            vm_public_claim_digest(&absent, shape()),
            vm_public_claim_digest(&zero, shape())
        );
    }

    #[test]
    fn public_input_digest_does_not_alias_a_high_machine_word_with_zero() {
        let first = public_data().io_entries;
        let mut second = public_data().io_entries;
        second.input_words[0] = 0;
        assert_ne!(
            public_input_digest(&first, shape()),
            public_input_digest(&second, shape())
        );
    }

    #[test]
    fn public_output_digest_excludes_proof_only_access_clocks() {
        let first = public_data().io_entries;
        let mut second = public_data().io_entries;
        second.output_words[1].clock += 1;
        assert_eq!(
            public_output_digest(&first, shape()),
            public_output_digest(&second, shape())
        );
    }

    #[test]
    fn non_canonical_root_limb_is_rejected() {
        let mut value = public_data();
        value
            .program_root
            .as_mut()
            .expect("fixture root is present")[7] = M31_MODULUS;
        assert_eq!(
            vm_public_claim_digest(&value, shape()),
            Err(VmPublicClaimError::NonCanonicalRoot {
                field: "program root",
                index: 7,
                value: M31_MODULUS,
            })
        );
    }

    #[test]
    fn public_input_digest_binds_the_exact_byte_length() {
        let first = public_data().io_entries;
        let mut second = public_data().io_entries;
        second.input_len -= 1;
        assert_ne!(
            public_input_digest(&first, shape()),
            public_input_digest(&second, shape())
        );
    }

    #[test]
    fn public_output_digest_binds_the_last_output_value() {
        let first = public_data().io_entries;
        let mut second = public_data().io_entries;
        second
            .output_words
            .last_mut()
            .expect("fixture output is nonempty")
            .value ^= 1;
        assert_ne!(
            public_output_digest(&first, shape()),
            public_output_digest(&second, shape())
        );
    }
}
