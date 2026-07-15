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
use prover::public_data::{IoEntries, OutputWord, PublicData};

const VM_PUBLIC_CLAIM_HASH_DOMAIN: u16 = 0x5643;
const PUBLIC_INPUT_HASH_DOMAIN: u16 = 0x5649;
const PUBLIC_OUTPUT_HASH_DOMAIN: u16 = 0x564f;

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
    PublicInput = 20,
    PublicOutput = 21,
}

impl ClaimTag {
    fn word(self) -> M31Word {
        M31Word::from(self as u16)
    }
}

/// Encodes every field that contributes VM public LogUp terms or transcript state.
pub fn canonical_vm_public_claim_words(
    public_data: &PublicData,
) -> Result<Vec<M31Word>, VmPublicClaimError> {
    let mut words = Vec::new();
    words.push(ClaimTag::Claim.word());
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
    append_input_words(&mut words, &public_data.io_entries)?;
    append_output_words(&mut words, &public_data.io_entries)?;
    Ok(words)
}

/// Commits the exact VM claim that the leaf's public-LogUp circuit consumes.
pub fn vm_public_claim_digest(
    public_data: &PublicData,
) -> Result<VmPublicClaimDigest, VmPublicClaimError> {
    let words = canonical_vm_public_claim_words(public_data)?;
    Ok(VmPublicClaimDigest::from(poseidon2_hash_m31_words(
        &words,
        M31Word::from(VM_PUBLIC_CLAIM_HASH_DOMAIN),
    )))
}

/// Commits the application-visible input independently of proof access clocks.
pub fn public_input_digest(io: &IoEntries) -> Result<IoDigest, VmPublicClaimError> {
    let mut words = vec![ClaimTag::PublicInput.word()];
    append_u32(&mut words, io.input_start);
    append_u32(&mut words, io.input_len);
    append_length(&mut words, "input words", io.input_words.len())?;
    for word in &io.input_words {
        append_u32(&mut words, *word);
    }
    Ok(IoDigest::from(poseidon2_hash_m31_words(
        &words,
        M31Word::from(PUBLIC_INPUT_HASH_DOMAIN),
    )))
}

/// Commits the application-visible output while leaving proof-only clocks in the VM claim.
pub fn public_output_digest(io: &IoEntries) -> Result<IoDigest, VmPublicClaimError> {
    let mut words = vec![ClaimTag::PublicOutput.word()];
    append_u32(&mut words, io.output_len_addr);
    append_u32(&mut words, io.output_data_addr);
    append_u32(&mut words, io.output_len);
    append_length(&mut words, "output words", io.output_words.len())?;
    for word in &io.output_words {
        append_u32(&mut words, word.addr);
        append_u32(&mut words, word.value);
    }
    Ok(IoDigest::from(poseidon2_hash_m31_words(
        &words,
        M31Word::from(PUBLIC_OUTPUT_HASH_DOMAIN),
    )))
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

fn append_input_words(words: &mut Vec<M31Word>, io: &IoEntries) -> Result<(), VmPublicClaimError> {
    words.push(ClaimTag::InputWords.word());
    append_length(words, "input words", io.input_words.len())?;
    for word in &io.input_words {
        append_u32(words, *word);
    }
    Ok(())
}

fn append_output_words(words: &mut Vec<M31Word>, io: &IoEntries) -> Result<(), VmPublicClaimError> {
    words.push(ClaimTag::OutputWords.word());
    append_length(words, "output words", io.output_words.len())?;
    for OutputWord { addr, value, clock } in &io.output_words {
        append_u32(words, *addr);
        append_u32(words, *value);
        append_u32(words, *clock);
    }
    Ok(())
}

/// A VM claim that cannot enter the canonical digest input.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VmPublicClaimError {
    LengthOutOfRange {
        field: &'static str,
        length: usize,
    },
    NonCanonicalRoot {
        field: &'static str,
        index: usize,
        value: u32,
    },
}

impl fmt::Display for VmPublicClaimError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
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
        }
    }
}

impl std::error::Error for VmPublicClaimError {}

#[cfg(test)]
mod tests {
    use super::*;
    use air::digest::Digest8;
    use stwo::core::fields::m31::P as M31_MODULUS;

    fn public_data() -> PublicData {
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
            vm_public_claim_digest(&public_data()),
            Ok(VmPublicClaimDigest::from(Digest8::new(
                [
                    227_188_391_u32,
                    1_795_321_842,
                    1_140_296_826,
                    1_245_089_431,
                    1_986_171_563,
                    1_312_865_325,
                    798_237_105,
                    855_814_532,
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
            vm_public_claim_digest(&first),
            vm_public_claim_digest(&second)
        );
    }

    #[test]
    fn vm_public_claim_digest_binds_input_vector_boundaries() {
        let first = public_data();
        let mut second = public_data();
        second.io_entries.input_words.push(0);
        assert_ne!(
            vm_public_claim_digest(&first),
            vm_public_claim_digest(&second)
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
            vm_public_claim_digest(&first),
            vm_public_claim_digest(&second)
        );
    }

    #[test]
    fn vm_public_claim_digest_distinguishes_absent_and_zero_roots() {
        let mut absent = public_data();
        absent.program_root = None;
        let mut zero = public_data();
        zero.program_root = Some([0; 8]);
        assert_ne!(
            vm_public_claim_digest(&absent),
            vm_public_claim_digest(&zero)
        );
    }

    #[test]
    fn public_input_digest_does_not_alias_a_high_machine_word_with_zero() {
        let first = public_data().io_entries;
        let mut second = public_data().io_entries;
        second.input_words[0] = 0;
        assert_ne!(public_input_digest(&first), public_input_digest(&second));
    }

    #[test]
    fn public_output_digest_excludes_proof_only_access_clocks() {
        let first = public_data().io_entries;
        let mut second = public_data().io_entries;
        second.output_words[1].clock += 1;
        assert_eq!(public_output_digest(&first), public_output_digest(&second));
    }

    #[test]
    fn non_canonical_root_limb_is_rejected() {
        let mut value = public_data();
        value
            .program_root
            .as_mut()
            .expect("fixture root is present")[7] = M31_MODULUS;
        assert_eq!(
            vm_public_claim_digest(&value),
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
        assert_ne!(public_input_digest(&first), public_input_digest(&second));
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
        assert_ne!(public_output_digest(&first), public_output_digest(&second));
    }
}
