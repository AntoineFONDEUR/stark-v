//! Poseidon2-M31 Fiat-Shamir channel and Merkle hasher (docs/recursion.md, M4).
//!
//! Inner stark-v proofs committed with this channel hash with the same
//! Poseidon2 permutation the `poseidon2`/`merkle` AIR components already
//! prove, so the recursion verifier checks channel and Merkle work by
//! component reuse — no new hash constraints anywhere.
//!
//! Construction (mirrors the Blake2s channel structure: digest + counter):
//! - The digest is 8 M31 words (~124-bit collision resistance from the
//!   permutation's 248-bit capacity-equivalent).
//! - Mixing rehashes `digest || data` through a Poseidon2 sponge (rate 8,
//!   additive absorption, 1-word end marker as padding).
//! - Drawing hashes `digest || n_draws || DRAW_TAG`, incrementing the
//!   counter, so draws never feed back into the digest.
//! - `u32` inputs are split into 16-bit halves before absorption: a u32 can
//!   exceed the field modulus, and the split keeps encoding injective.
//! - Merkle node hashing overwrites the full 16-word state with the two
//!   child digests; leaf hashing runs the sponge with a tagged capacity word
//!   for domain separation from node hashing.

use air::digest::{Digest8, M31Word};
use runner::poseidon2::{T, poseidon2_permutation};
use serde::{Deserialize, Serialize};
use stwo::core::channel::{Channel, MerkleChannel};
use stwo::core::fields::m31::{BaseField, P};
use stwo::core::fields::qm31::{SECURE_EXTENSION_DEGREE, SecureField};
use stwo::core::proof_of_work::GrindOps;
use stwo::core::vcs::hash::Hash;
use stwo::core::vcs_lifted::merkle_hasher::MerkleHasherLifted;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::{Col, Column, ColumnOps, CpuBackend};
use stwo::prover::vcs_lifted::ops::MerkleOpsLifted;

/// Sponge rate in M31 words; the remaining 8 words are capacity.
const RATE: usize = 8;
/// Tag absorbed when drawing randomness (domain separation from mixing).
const DRAW_TAG: u32 = 0x44524157; // "DRAW"
/// Capacity tag for leaf hashing (domain separation from node hashing).
const LEAF_TAG: u32 = 1;

/// An 8-word M31 digest.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Poseidon2M31Hash(pub [u32; RATE]);

impl core::fmt::Display for Poseidon2M31Hash {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:08x?}", self.0)
    }
}

impl Hash for Poseidon2M31Hash {}

/// Add a word into the state modulo P.
fn absorb_word(slot: &mut u32, word: u32) {
    debug_assert!(word < P);
    let sum = *slot as u64 + word as u64;
    *slot = (sum % P as u64) as u32;
}

/// Sponge-hash a stream of M31 words (each must be `< P`).
///
/// Additive absorption in chunks of [`RATE`], a single `1` end-marker word as
/// padding, `capacity_tag` in the last capacity word.
fn hash_words(words: &[u32], capacity_tag: u32) -> Poseidon2M31Hash {
    let mut state = [0u32; T];
    state[T - 1] = capacity_tag;
    let mut filled = 0usize;
    for &word in words.iter().chain(core::iter::once(&1u32)) {
        absorb_word(&mut state[filled], word);
        filled += 1;
        if filled == RATE {
            poseidon2_permutation(&mut state);
            filled = 0;
        }
    }
    if filled != 0 {
        poseidon2_permutation(&mut state);
    }
    Poseidon2M31Hash(state[..RATE].try_into().expect("rate slice"))
}

/// Hashes canonical M31 words with a capacity-domain tag into a full digest.
///
/// Protocol identities use this entry point so their encoding cannot pass
/// through `mix_u32s`, whose 16-bit split intentionally has different
/// semantics for unrestricted machine words.
pub fn poseidon2_hash_m31_words(words: &[M31Word], domain: M31Word) -> Digest8 {
    let words: Vec<u32> = words.iter().map(|word| word.as_u32()).collect();
    let digest = hash_words(&words, domain.as_u32());
    Digest8::try_from(digest.0).expect("Poseidon2 outputs canonical M31 words")
}

/// Split u32s into 16-bit halves so every absorbed word is a canonical M31.
pub fn encode_u32s(data: &[u32]) -> impl Iterator<Item = u32> + '_ {
    data.iter()
        .flat_map(|&word| [word & 0xFFFF, word >> 16].into_iter())
}

/// Poseidon2-M31 Fiat-Shamir channel.
#[derive(Clone, Debug, Default)]
pub struct Poseidon2M31Channel {
    digest: Poseidon2M31Hash,
    n_draws: u32,
}

impl Poseidon2M31Channel {
    pub fn digest(&self) -> Poseidon2M31Hash {
        self.digest
    }

    fn mix_words(&mut self, words: impl Iterator<Item = u32>) {
        let input: Vec<u32> = self.digest.0.iter().copied().chain(words).collect();
        self.digest = hash_words(&input, 0);
        self.n_draws = 0;
    }

    fn draw_words(&mut self) -> [u32; RATE] {
        let input: Vec<u32> = self
            .digest
            .0
            .iter()
            .copied()
            .chain([self.n_draws, DRAW_TAG])
            .collect();
        self.n_draws += 1;
        hash_words(&input, 0).0
    }

    fn draw_base_felts(&mut self) -> [BaseField; RATE] {
        self.draw_words().map(BaseField::from_u32_unchecked)
    }
}

impl Channel for Poseidon2M31Channel {
    const BYTES_PER_HASH: usize = RATE * 4;

    fn verify_pow_nonce(&self, n_bits: u32, nonce: u64) -> bool {
        let mut channel = self.clone();
        channel.mix_u64(nonce);
        channel.draw_words()[0].trailing_zeros() >= n_bits
    }

    fn mix_u32s(&mut self, data: &[u32]) {
        let words: Vec<u32> = encode_u32s(data).collect();
        self.mix_words(words.into_iter());
    }

    fn mix_felts(&mut self, felts: &[SecureField]) {
        let words: Vec<u32> = felts
            .iter()
            .flat_map(|felt| felt.to_m31_array())
            .map(|m31| m31.0)
            .collect();
        self.mix_words(words.into_iter());
    }

    fn mix_u64(&mut self, value: u64) {
        self.mix_u32s(&[value as u32, (value >> 32) as u32]);
    }

    fn draw_secure_felt(&mut self) -> SecureField {
        let felts = self.draw_base_felts();
        SecureField::from_m31_array(
            felts[..SECURE_EXTENSION_DEGREE]
                .try_into()
                .expect("4 felts"),
        )
    }

    fn draw_secure_felts(&mut self, n_felts: usize) -> Vec<SecureField> {
        let mut out = Vec::with_capacity(n_felts);
        while out.len() < n_felts {
            let felts = self.draw_base_felts();
            for chunk in felts.chunks_exact(SECURE_EXTENSION_DEGREE) {
                if out.len() == n_felts {
                    break;
                }
                out.push(SecureField::from_m31_array(
                    chunk.try_into().expect("4 felts"),
                ));
            }
        }
        out
    }

    fn draw_u32s(&mut self) -> Vec<u32> {
        self.draw_words().to_vec()
    }
}

/// Incremental leaf hasher: the sponge state plus the fill position.
#[derive(Clone, Debug)]
pub struct Poseidon2M31MerkleHasher {
    state: [u32; T],
    filled: usize,
}

impl Default for Poseidon2M31MerkleHasher {
    fn default() -> Self {
        let mut state = [0u32; T];
        state[T - 1] = LEAF_TAG;
        Self { state, filled: 0 }
    }
}

impl MerkleHasherLifted for Poseidon2M31MerkleHasher {
    type Hash = Poseidon2M31Hash;

    fn hash_children(children_hashes: (Self::Hash, Self::Hash)) -> Self::Hash {
        let mut state = [0u32; T];
        state[..RATE].copy_from_slice(&children_hashes.0.0);
        state[RATE..].copy_from_slice(&children_hashes.1.0);
        poseidon2_permutation(&mut state);
        Poseidon2M31Hash(state[..RATE].try_into().expect("rate slice"))
    }

    fn update_leaf(&mut self, column_values: &[BaseField]) {
        for value in column_values {
            absorb_word(&mut self.state[self.filled], value.0);
            self.filled += 1;
            if self.filled == RATE {
                poseidon2_permutation(&mut self.state);
                self.filled = 0;
            }
        }
    }

    fn finalize(mut self) -> Self::Hash {
        // 1-word end marker, then squeeze (same padding as `hash_words`).
        absorb_word(&mut self.state[self.filled], 1);
        poseidon2_permutation(&mut self.state);
        Poseidon2M31Hash(self.state[..RATE].try_into().expect("rate slice"))
    }
}

/// The Merkle channel tying the channel and the hasher together.
#[derive(Default)]
pub struct Poseidon2M31MerkleChannel;

impl MerkleChannel for Poseidon2M31MerkleChannel {
    type C = Poseidon2M31Channel;
    type H = Poseidon2M31MerkleHasher;

    fn mix_root(channel: &mut Self::C, root: Poseidon2M31Hash) {
        channel.mix_words(root.0.into_iter());
    }
}

// -----------------------------------------------------------------------------
// SimdBackend support: hash columns are plain vectors, tree building delegates
// to the generic CpuBackend implementation. Correct first, fast later.
// -----------------------------------------------------------------------------

impl ColumnOps<Poseidon2M31Hash> for SimdBackend {
    type Column = Vec<Poseidon2M31Hash>;

    fn bit_reverse_column(column: &mut Self::Column) {
        <CpuBackend as ColumnOps<Poseidon2M31Hash>>::bit_reverse_column(column)
    }
}

impl MerkleOpsLifted<Poseidon2M31MerkleHasher> for SimdBackend {
    fn build_leaves(
        columns: &[&Col<Self, BaseField>],
        lifting_log_size: u32,
    ) -> Col<Self, Poseidon2M31Hash> {
        let cpu_columns: Vec<Vec<BaseField>> = columns.iter().map(|col| col.to_cpu()).collect();
        let cpu_refs: Vec<&Vec<BaseField>> = cpu_columns.iter().collect();
        <CpuBackend as MerkleOpsLifted<Poseidon2M31MerkleHasher>>::build_leaves(
            &cpu_refs,
            lifting_log_size,
        )
    }

    fn build_next_layer(prev_layer: &Col<Self, Poseidon2M31Hash>) -> Col<Self, Poseidon2M31Hash> {
        <CpuBackend as MerkleOpsLifted<Poseidon2M31MerkleHasher>>::build_next_layer(prev_layer)
    }
}

impl GrindOps<Poseidon2M31Channel> for SimdBackend {
    fn grind(channel: &Poseidon2M31Channel, pow_bits: u32) -> u64 {
        <CpuBackend as GrindOps<Poseidon2M31Channel>>::grind(channel, pow_bits)
    }
}

impl stwo::prover::backend::BackendForChannel<Poseidon2M31MerkleChannel> for SimdBackend {}

#[cfg(test)]
mod tests {
    use air::digest::M31Word;

    use super::*;

    #[test]
    fn test_channel_mixing_changes_draws() {
        let mut a = Poseidon2M31Channel::default();
        let mut b = Poseidon2M31Channel::default();
        b.mix_u32s(&[42]);
        assert_ne!(a.draw_secure_felt(), b.draw_secure_felt());
    }

    #[test]
    fn test_channel_draws_are_deterministic() {
        let mut a = Poseidon2M31Channel::default();
        let mut b = Poseidon2M31Channel::default();
        a.mix_u64(7);
        b.mix_u64(7);
        assert_eq!(a.draw_secure_felts(3), b.draw_secure_felts(3));
    }

    #[test]
    fn test_channel_successive_draws_differ() {
        let mut channel = Poseidon2M31Channel::default();
        assert_ne!(channel.draw_secure_felt(), channel.draw_secure_felt());
    }

    #[test]
    fn test_u32_encoding_is_injective_beyond_modulus() {
        // P and 0 reduce to the same M31 word; the 16-bit split keeps the
        // channel states distinct.
        let mut a = Poseidon2M31Channel::default();
        let mut b = Poseidon2M31Channel::default();
        a.mix_u32s(&[P]);
        b.mix_u32s(&[0]);
        assert_ne!(a.draw_secure_felt(), b.draw_secure_felt());
    }

    #[test]
    fn test_grind_satisfies_pow() {
        let mut channel = Poseidon2M31Channel::default();
        channel.mix_u32s(&[1, 2, 3]);
        let nonce = <SimdBackend as GrindOps<Poseidon2M31Channel>>::grind(&channel, 8);
        assert!(channel.verify_pow_nonce(8, nonce));
    }

    #[test]
    fn test_leaf_and_node_hashing_are_domain_separated() {
        // A leaf whose content equals two concatenated digests must not
        // collide with the corresponding inner node.
        let child = Poseidon2M31Hash([1, 2, 3, 4, 5, 6, 7, 8]);
        let node = Poseidon2M31MerkleHasher::hash_children((child, child));
        let mut leaf_hasher = Poseidon2M31MerkleHasher::default();
        let words: Vec<BaseField> = child
            .0
            .iter()
            .chain(child.0.iter())
            .map(|&w| BaseField::from_u32_unchecked(w))
            .collect();
        leaf_hasher.update_leaf(&words);
        assert_ne!(leaf_hasher.finalize(), node);
    }

    #[test]
    fn test_canonical_word_hash_is_domain_separated() {
        let words = [M31Word::from(1), M31Word::from(2)];
        assert_ne!(
            poseidon2_hash_m31_words(&words, M31Word::from(10)),
            poseidon2_hash_m31_words(&words, M31Word::from(11))
        );
    }

    #[test]
    fn test_canonical_word_hash_matches_conformance_vector() {
        let words = [M31Word::from(1), M31Word::from(2)];
        assert_eq!(
            poseidon2_hash_m31_words(&words, M31Word::from(10)),
            Digest8::try_from([
                1_683_618_890,
                22_281_548,
                1_108_016_194,
                1_368_459_274,
                926_884_817,
                1_781_577_565,
                1_099_953_524,
                427_524_185,
            ])
            .expect("the conformance digest words are canonical")
        );
    }

    #[test]
    fn test_simd_tree_layers_match_cpu() {
        let layer: Vec<Poseidon2M31Hash> = (0..8u32).map(|i| Poseidon2M31Hash([i; 8])).collect();
        assert_eq!(
            <SimdBackend as MerkleOpsLifted<Poseidon2M31MerkleHasher>>::build_next_layer(&layer),
            <CpuBackend as MerkleOpsLifted<Poseidon2M31MerkleHasher>>::build_next_layer(&layer),
        );
    }
}
