//! Backend-neutral Poseidon2 transcript engine for recursion V2.
//!
//! Transcript state transitions are implemented once. The native backend is
//! the outer-verifier oracle; the recording backend materializes the same
//! permutation inputs, outputs, and PoW checks as witness data for the
//! universal AIR. Raw machine words are split into 16-bit limbs, while
//! digests and field values remain canonical M31 words. This distinction is
//! required for an injective transcript encoding.

use core::fmt;

use air::digest::{Digest8, M31Word};
use air::poseidon2::{T, poseidon2_permutation};
use stwo::core::fields::m31::P as M31_MODULUS;
use stwo::core::fields::qm31::SecureField;

use crate::prover::{ChannelClaim, RecursionTraces};

const RATE: usize = 8;
const DRAW_TAG: u32 = 0x4452_4157;

/// Coordinates one permutation within both the global and per-hash schedules.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PermutationId {
    pub call_id: u32,
    pub hash_id: u32,
    pub step: u32,
}

/// One atomic permutation call shared with the Poseidon2 AIR relation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoseidonCall {
    pub id: PermutationId,
    pub input: [M31Word; T],
    pub output: [M31Word; T],
}

/// One nonce check against a transcript-derived M31 word.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PowCheck {
    pub call_id: u32,
    pub nonce: u64,
    pub bits: u32,
    pub word: M31Word,
}

/// The cryptographic operations emitted by the shared transcript algorithm.
pub trait TranscriptBackend {
    type Error;

    fn permute(
        &mut self,
        id: PermutationId,
        input: [M31Word; T],
    ) -> Result<[M31Word; T], Self::Error>;

    fn verify_pow(&mut self, check: PowCheck) -> Result<(), Self::Error>;
}

/// Native Poseidon2 execution and PoW checking for the outer verifier.
#[derive(Clone, Copy, Debug, Default)]
pub struct NativeTranscriptBackend;

impl TranscriptBackend for NativeTranscriptBackend {
    type Error = TranscriptError;

    fn permute(
        &mut self,
        _id: PermutationId,
        input: [M31Word; T],
    ) -> Result<[M31Word; T], Self::Error> {
        Ok(permute_words(input))
    }

    fn verify_pow(&mut self, check: PowCheck) -> Result<(), Self::Error> {
        if check.word.as_u32().trailing_zeros() >= check.bits {
            Ok(())
        } else {
            Err(TranscriptError::InvalidProofOfWork {
                nonce: check.nonce,
                bits: check.bits,
                word: check.word,
            })
        }
    }
}

/// Witness events produced by the AIR-facing transcript backend.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TranscriptTrace {
    pub poseidon_calls: Vec<PoseidonCall>,
    pub pow_checks: Vec<PowCheck>,
}

/// One sponge row with reset/chaining data made explicit for AIR columns.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SpongeRow {
    pub id: PermutationId,
    pub previous: [M31Word; T],
    pub chunk: [M31Word; RATE],
    pub output: [M31Word; T],
}

impl TranscriptTrace {
    /// Reconstructs rate chunks and rejects malformed session coordinates.
    pub fn sponge_rows(&self) -> Result<Vec<SpongeRow>, TranscriptError> {
        let mut rows = Vec::with_capacity(self.poseidon_calls.len());
        let mut current_hash = None;
        let mut next_hash_id = 0_u32;
        let mut expected_step = 0_u32;
        let mut previous = [M31Word::ZERO; T];

        for (call_index, call) in self.poseidon_calls.iter().copied().enumerate() {
            let expected_call_id = u32::try_from(call_index)
                .map_err(|_| TranscriptError::TraceIndexOutOfRange { index: call_index })?;
            if call.id.call_id != expected_call_id {
                return Err(TranscriptError::TraceCallIdMismatch {
                    index: call_index,
                    expected: expected_call_id,
                    actual: call.id.call_id,
                });
            }
            if current_hash != Some(call.id.hash_id) {
                if call.id.hash_id != next_hash_id {
                    return Err(TranscriptError::TraceHashIdMismatch {
                        call_id: call.id.call_id,
                        expected: next_hash_id,
                        actual: call.id.hash_id,
                    });
                }
                current_hash = Some(call.id.hash_id);
                next_hash_id = next_hash_id
                    .checked_add(1)
                    .ok_or(TranscriptError::HashIdOverflow)?;
                expected_step = 0;
                previous = [M31Word::ZERO; T];
            }
            if call.id.step != expected_step {
                return Err(TranscriptError::TraceStepMismatch {
                    call_id: call.id.call_id,
                    expected: expected_step,
                    actual: call.id.step,
                });
            }
            for (word, (&actual, &expected)) in
                call.input.iter().zip(&previous).enumerate().skip(RATE)
            {
                if actual != expected {
                    return Err(TranscriptError::TraceCapacityMismatch {
                        call_id: call.id.call_id,
                        word,
                        expected,
                        actual,
                    });
                }
            }
            let chunk =
                core::array::from_fn(|word| subtract_m31_words(call.input[word], previous[word]));
            rows.push(SpongeRow {
                id: call.id,
                previous,
                chunk,
                output: call.output,
            });
            previous = call.output;
            expected_step = expected_step
                .checked_add(1)
                .ok_or(TranscriptError::HashStepOverflow)?;
        }

        for check in &self.pow_checks {
            let call = self.poseidon_calls.get(check.call_id as usize).ok_or(
                TranscriptError::PowDrawCallMissing {
                    call_id: check.call_id,
                },
            )?;
            if call.output[0] != check.word {
                return Err(TranscriptError::PowDrawWordMismatch {
                    call_id: check.call_id,
                    expected: call.output[0],
                    actual: check.word,
                });
            }
        }
        Ok(rows)
    }

    /// Materializes the checked sessions through the atomic sponge/Poseidon AIR tables.
    pub fn materialize_air_witness(
        &self,
        traces: &mut RecursionTraces,
    ) -> Result<Vec<ChannelClaim>, TranscriptError> {
        let rows = self.sponge_rows()?;
        let mut claims = Vec::new();
        let mut current_hash = None;
        let mut chunks = Vec::new();
        for row in rows {
            if current_hash != Some(row.id.hash_id) {
                if let Some(channel_id) = current_hash {
                    claims.push(ChannelClaim { channel_id, chunks });
                    chunks = Vec::new();
                }
                current_hash = Some(row.id.hash_id);
            }
            let previous = row.previous.map(M31Word::as_u32);
            let chunk = row.chunk.map(M31Word::as_u32);
            let output = crate::channel_replay::push_sponge_step(
                &mut traces.channel_replay,
                &mut traces.poseidon2,
                row.id.hash_id,
                row.id.step,
                previous,
                chunk,
            );
            if output != row.output.map(M31Word::as_u32) {
                return Err(TranscriptError::RecordedPoseidonOutputMismatch {
                    call_id: row.id.call_id,
                });
            }
            chunks.push(chunk);
        }
        if let Some(channel_id) = current_hash {
            claims.push(ChannelClaim { channel_id, chunks });
        }
        Ok(claims)
    }
}

/// Records values for constraints without defining a second transcript order.
#[derive(Clone, Debug, Default)]
pub struct RecordingTranscriptBackend {
    trace: TranscriptTrace,
}

impl RecordingTranscriptBackend {
    pub fn trace(&self) -> &TranscriptTrace {
        &self.trace
    }

    pub fn into_trace(self) -> TranscriptTrace {
        self.trace
    }
}

impl TranscriptBackend for RecordingTranscriptBackend {
    type Error = TranscriptError;

    fn permute(
        &mut self,
        id: PermutationId,
        input: [M31Word; T],
    ) -> Result<[M31Word; T], Self::Error> {
        let output = permute_words(input);
        self.trace
            .poseidon_calls
            .push(PoseidonCall { id, input, output });
        Ok(output)
    }

    fn verify_pow(&mut self, check: PowCheck) -> Result<(), Self::Error> {
        self.trace.pow_checks.push(check);
        if check.word.as_u32().trailing_zeros() >= check.bits {
            Ok(())
        } else {
            Err(TranscriptError::InvalidProofOfWork {
                nonce: check.nonce,
                bits: check.bits,
                word: check.word,
            })
        }
    }
}

/// One transcript state parameterized only by how operations are enforced.
#[derive(Clone, Debug)]
pub struct TranscriptKernel<B> {
    digest: Digest8,
    n_draws: u32,
    next_call_id: u32,
    next_hash_id: u32,
    backend: B,
}

impl<B: Default> Default for TranscriptKernel<B> {
    fn default() -> Self {
        Self {
            digest: Digest8::ZERO,
            n_draws: 0,
            next_call_id: 0,
            next_hash_id: 0,
            backend: B::default(),
        }
    }
}

impl<B: TranscriptBackend> TranscriptKernel<B>
where
    B::Error: From<TranscriptError>,
{
    pub fn new(backend: B) -> Self {
        Self {
            digest: Digest8::ZERO,
            n_draws: 0,
            next_call_id: 0,
            next_hash_id: 0,
            backend,
        }
    }

    pub const fn digest(&self) -> Digest8 {
        self.digest
    }

    pub const fn draw_count(&self) -> u32 {
        self.n_draws
    }

    pub const fn backend(&self) -> &B {
        &self.backend
    }

    pub fn into_backend(self) -> B {
        self.backend
    }

    /// Absorbs canonical field words without applying the RV32 limb split.
    pub fn absorb_m31_words(&mut self, words: &[M31Word]) -> Result<(), B::Error> {
        let mut stream = Vec::with_capacity(RATE + words.len());
        stream.extend_from_slice(self.digest.words());
        stream.extend_from_slice(words);
        let output = self.hash_stream(&stream)?;
        self.digest = Digest8::new(output[..RATE].try_into().expect("rate-sized digest"));
        self.n_draws = 0;
        Ok(())
    }

    /// Absorbs unrestricted machine words through an injective 16-bit split.
    pub fn absorb_u32s(&mut self, words: &[u32]) -> Result<(), B::Error> {
        let encoded: Vec<M31Word> = words
            .iter()
            .flat_map(|word| [word & 0xffff, word >> 16])
            .map(|limb| M31Word::try_from(limb).expect("a 16-bit limb is canonical M31"))
            .collect();
        self.absorb_m31_words(&encoded)
    }

    pub fn absorb_u64(&mut self, value: u64) -> Result<(), B::Error> {
        self.absorb_u32s(&[value as u32, (value >> 32) as u32])
    }

    pub fn absorb_digest(&mut self, digest: Digest8) -> Result<(), B::Error> {
        self.absorb_m31_words(digest.words())
    }

    pub fn absorb_secure_fields(&mut self, values: &[SecureField]) -> Result<(), B::Error> {
        let words: Vec<M31Word> = values
            .iter()
            .flat_map(|value| value.to_m31_array())
            .map(M31Word::from)
            .collect();
        self.absorb_m31_words(&words)
    }

    /// Draws one rate block without feeding it back into the transcript digest.
    pub fn draw_block(&mut self) -> Result<[M31Word; RATE], B::Error> {
        let draw_count =
            M31Word::try_from(self.n_draws).map_err(|_| TranscriptError::DrawCountOutOfRange {
                draw_count: self.n_draws,
            })?;
        let draw_tag = M31Word::try_from(DRAW_TAG).expect("the draw tag is canonical M31");
        let mut stream = Vec::with_capacity(RATE + 2);
        stream.extend_from_slice(self.digest.words());
        stream.extend([draw_count, draw_tag]);
        let output = self.hash_stream(&stream)?;
        self.n_draws = self
            .n_draws
            .checked_add(1)
            .ok_or(TranscriptError::DrawCountOverflow)?;
        Ok(output[..RATE].try_into().expect("rate-sized draw"))
    }

    pub fn draw_secure_field(&mut self) -> Result<SecureField, B::Error> {
        let words = self.draw_block()?;
        let limbs: [M31Word; 4] = words[..4].try_into().expect("QM31 has four limbs");
        Ok(SecureField::from_m31_array(
            limbs.map(stwo::core::fields::m31::M31::from),
        ))
    }

    /// Derives fixed raw query slots directly from constrained draw words.
    pub fn draw_queries<const N: usize>(
        &mut self,
        log_domain_size: u32,
    ) -> Result<[u32; N], B::Error> {
        if !(1..=30).contains(&log_domain_size) {
            return Err(TranscriptError::QueryLogSizeOutOfRange { log_domain_size }.into());
        }
        let query_mask = (1_u32 << log_domain_size) - 1;
        let mut queries = Vec::with_capacity(N);
        while queries.len() < N {
            let words = self.draw_block()?;
            for word in words {
                if queries.len() == N {
                    break;
                }
                queries.push(word.as_u32() & query_mask);
            }
        }
        match queries.try_into() {
            Ok(queries) => Ok(queries),
            Err(_) => unreachable!("query derivation fills the fixed array exactly"),
        }
    }

    /// Verifies the nonce challenge and performs its transcript absorption once.
    pub fn verify_and_absorb_pow(&mut self, nonce: u64, bits: u32) -> Result<(), B::Error> {
        if bits > 31 {
            return Err(TranscriptError::PowBitsOutOfRange { bits }.into());
        }

        self.absorb_u64(nonce)?;
        let nonce_digest = self.digest;
        let word = self.draw_block()?[0];
        let call_id = self
            .next_call_id
            .checked_sub(1)
            .ok_or(TranscriptError::MissingPowDraw)?;
        self.backend.verify_pow(PowCheck {
            call_id,
            nonce,
            bits,
            word,
        })?;

        // Verification draws from a temporary channel. Acceptance absorbs the
        // nonce but leaves the real channel with a reset draw counter.
        self.digest = nonce_digest;
        self.n_draws = 0;
        Ok(())
    }

    fn hash_stream(&mut self, words: &[M31Word]) -> Result<[M31Word; T], B::Error> {
        let hash_id = self.next_hash_id;
        self.next_hash_id = self
            .next_hash_id
            .checked_add(1)
            .ok_or(TranscriptError::HashIdOverflow)?;
        let mut state = [M31Word::ZERO; T];
        let mut filled = 0;
        let mut step = 0_u32;
        for word in words
            .iter()
            .copied()
            .chain(core::iter::once(M31Word::from(1)))
        {
            state[filled] = add_m31_words(state[filled], word);
            filled += 1;
            if filled == RATE {
                state = self.permute(hash_id, step, state)?;
                step = step
                    .checked_add(1)
                    .ok_or(TranscriptError::HashStepOverflow)?;
                filled = 0;
            }
        }
        if filled != 0 {
            state = self.permute(hash_id, step, state)?;
        }
        Ok(state)
    }

    fn permute(
        &mut self,
        hash_id: u32,
        step: u32,
        input: [M31Word; T],
    ) -> Result<[M31Word; T], B::Error> {
        let call_id = self.next_call_id;
        self.next_call_id = self
            .next_call_id
            .checked_add(1)
            .ok_or(TranscriptError::CallIdOverflow)?;
        self.backend.permute(
            PermutationId {
                call_id,
                hash_id,
                step,
            },
            input,
        )
    }
}

fn add_m31_words(left: M31Word, right: M31Word) -> M31Word {
    let sum = u64::from(left.as_u32()) + u64::from(right.as_u32());
    M31Word::try_from((sum % u64::from(M31_MODULUS)) as u32)
        .expect("modular addition returns a canonical M31 word")
}

fn subtract_m31_words(left: M31Word, right: M31Word) -> M31Word {
    let value = (u64::from(left.as_u32()) + u64::from(M31_MODULUS) - u64::from(right.as_u32()))
        % u64::from(M31_MODULUS);
    M31Word::try_from(value as u32).expect("modular subtraction returns a canonical M31 word")
}

fn permute_words(input: [M31Word; T]) -> [M31Word; T] {
    let mut state = input.map(M31Word::as_u32);
    poseidon2_permutation(&mut state);
    state.map(|word| M31Word::try_from(word).expect("Poseidon2 output is canonical M31"))
}

/// Failure at a checked transcript boundary.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TranscriptError {
    DrawCountOutOfRange {
        draw_count: u32,
    },
    DrawCountOverflow,
    CallIdOverflow,
    HashIdOverflow,
    HashStepOverflow,
    PowBitsOutOfRange {
        bits: u32,
    },
    QueryLogSizeOutOfRange {
        log_domain_size: u32,
    },
    TraceIndexOutOfRange {
        index: usize,
    },
    TraceCallIdMismatch {
        index: usize,
        expected: u32,
        actual: u32,
    },
    TraceHashIdMismatch {
        call_id: u32,
        expected: u32,
        actual: u32,
    },
    TraceStepMismatch {
        call_id: u32,
        expected: u32,
        actual: u32,
    },
    TraceCapacityMismatch {
        call_id: u32,
        word: usize,
        expected: M31Word,
        actual: M31Word,
    },
    PowDrawCallMissing {
        call_id: u32,
    },
    PowDrawWordMismatch {
        call_id: u32,
        expected: M31Word,
        actual: M31Word,
    },
    RecordedPoseidonOutputMismatch {
        call_id: u32,
    },
    MissingPowDraw,
    InvalidProofOfWork {
        nonce: u64,
        bits: u32,
        word: M31Word,
    },
}

impl fmt::Display for TranscriptError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DrawCountOutOfRange { draw_count } => {
                write!(formatter, "draw count {draw_count} is not canonical M31")
            }
            Self::DrawCountOverflow => write!(formatter, "transcript draw count overflowed"),
            Self::CallIdOverflow => write!(formatter, "transcript Poseidon call id overflowed"),
            Self::HashIdOverflow => write!(formatter, "transcript hash session id overflowed"),
            Self::HashStepOverflow => write!(formatter, "transcript hash step overflowed"),
            Self::PowBitsOutOfRange { bits } => {
                write!(formatter, "PoW bits {bits} exceed the M31 maximum 31")
            }
            Self::QueryLogSizeOutOfRange { log_domain_size } => write!(
                formatter,
                "query log domain size {log_domain_size} is outside 1..=30"
            ),
            Self::TraceIndexOutOfRange { index } => {
                write!(formatter, "transcript trace index {index} does not fit u32")
            }
            Self::TraceCallIdMismatch {
                index,
                expected,
                actual,
            } => write!(
                formatter,
                "transcript call at index {index} has id {actual}, expected {expected}"
            ),
            Self::TraceHashIdMismatch {
                call_id,
                expected,
                actual,
            } => write!(
                formatter,
                "transcript call {call_id} has hash id {actual}, expected {expected}"
            ),
            Self::TraceStepMismatch {
                call_id,
                expected,
                actual,
            } => write!(
                formatter,
                "transcript call {call_id} has hash step {actual}, expected {expected}"
            ),
            Self::TraceCapacityMismatch {
                call_id,
                word,
                expected,
                actual,
            } => write!(
                formatter,
                "transcript call {call_id} capacity word {word} is {}, expected {}",
                actual.as_u32(),
                expected.as_u32()
            ),
            Self::PowDrawCallMissing { call_id } => {
                write!(formatter, "PoW check references missing call {call_id}")
            }
            Self::PowDrawWordMismatch {
                call_id,
                expected,
                actual,
            } => write!(
                formatter,
                "PoW call {call_id} checks word {}, expected {}",
                actual.as_u32(),
                expected.as_u32()
            ),
            Self::RecordedPoseidonOutputMismatch { call_id } => write!(
                formatter,
                "recorded Poseidon output for call {call_id} does not match its AIR witness"
            ),
            Self::MissingPowDraw => write!(formatter, "PoW check has no transcript draw call"),
            Self::InvalidProofOfWork { nonce, bits, word } => write!(
                formatter,
                "nonce {nonce} does not satisfy {bits} PoW bits in word {}",
                word.as_u32()
            ),
        }
    }
}

impl std::error::Error for TranscriptError {}

#[cfg(test)]
mod tests {
    use rstest::rstest;
    use stwo::core::channel::{Channel, MerkleChannel};
    use stwo::core::pcs::PcsConfig;
    use stwo::core::proof_of_work::GrindOps;
    use stwo::core::queries::draw_queries;
    use stwo::prover::backend::simd::SimdBackend;

    use prover::poseidon2_channel::{
        Poseidon2M31Channel, Poseidon2M31Hash, Poseidon2M31MerkleChannel,
    };

    use super::*;

    #[rstest]
    fn raw_u32_absorption_matches_the_existing_channel() {
        let words = [M31_MODULUS, u32::MAX, 7];
        let mut reference = Poseidon2M31Channel::default();
        reference.mix_u32s(&words);
        let mut kernel = TranscriptKernel::<NativeTranscriptBackend>::default();
        kernel
            .absorb_u32s(&words)
            .expect("the native transcript accepts unrestricted u32 words");
        assert_eq!(kernel.draw_secure_field(), Ok(reference.draw_secure_felt()));
    }

    #[rstest]
    fn digest_absorption_matches_merkle_channel_root_mixing() {
        let raw = [1, 2, 3, 4, 5, 6, 7, 8];
        let digest = Digest8::try_from(raw).expect("the fixture root is canonical");
        let mut reference = Poseidon2M31Channel::default();
        Poseidon2M31MerkleChannel::mix_root(&mut reference, Poseidon2M31Hash(raw));
        let mut kernel = TranscriptKernel::<NativeTranscriptBackend>::default();
        kernel
            .absorb_digest(digest)
            .expect("the native transcript accepts a canonical digest");
        assert_eq!(
            kernel.draw_block().map(|words| words.map(M31Word::as_u32)),
            Ok(reference
                .draw_u32s()
                .try_into()
                .expect("the reference channel draws one rate block"))
        );
    }

    #[rstest]
    fn successive_draws_match_the_existing_channel() {
        let mut reference = Poseidon2M31Channel::default();
        reference.mix_u64(0x1122_3344_5566_7788);
        let mut kernel = TranscriptKernel::<NativeTranscriptBackend>::default();
        kernel
            .absorb_u64(0x1122_3344_5566_7788)
            .expect("the nonce limbs are canonical");
        let first = kernel.draw_block();
        let second = kernel.draw_block();
        assert_eq!(
            (first, second),
            (
                Ok(reference
                    .draw_u32s()
                    .into_iter()
                    .map(|word| M31Word::try_from(word).expect("draws are canonical"))
                    .collect::<Vec<_>>()
                    .try_into()
                    .expect("one rate block")),
                Ok(reference
                    .draw_u32s()
                    .into_iter()
                    .map(|word| M31Word::try_from(word).expect("draws are canonical"))
                    .collect::<Vec<_>>()
                    .try_into()
                    .expect("one rate block")),
            )
        );
    }

    #[rstest]
    fn valid_pow_transition_matches_the_existing_channel() {
        let mut reference = Poseidon2M31Channel::default();
        reference.mix_u32s(&[1, 2, 3]);
        let nonce = <SimdBackend as GrindOps<Poseidon2M31Channel>>::grind(&reference, 8);
        let mut kernel = TranscriptKernel::<NativeTranscriptBackend>::default();
        kernel
            .absorb_u32s(&[1, 2, 3])
            .expect("the fixture words are accepted");
        let result = kernel
            .verify_and_absorb_pow(nonce, 8)
            .and_then(|()| kernel.draw_secure_field());
        reference.mix_u64(nonce);
        assert_eq!(result, Ok(reference.draw_secure_felt()));
    }

    #[rstest]
    fn invalid_pow_transition_is_rejected() {
        let mut reference = Poseidon2M31Channel::default();
        reference.mix_u32s(&[1, 2, 3]);
        let mut nonce = 0;
        while reference.verify_pow_nonce(8, nonce) {
            nonce += 1;
        }
        let mut kernel = TranscriptKernel::<NativeTranscriptBackend>::default();
        kernel
            .absorb_u32s(&[1, 2, 3])
            .expect("the fixture words are accepted");
        assert!(matches!(
            kernel.verify_and_absorb_pow(nonce, 8),
            Err(TranscriptError::InvalidProofOfWork {
                nonce: rejected,
                bits: 8,
                ..
            }) if rejected == nonce
        ));
    }

    #[rstest]
    fn recording_and_native_backends_execute_identical_transitions() {
        let mut native = TranscriptKernel::<NativeTranscriptBackend>::default();
        let mut recording = TranscriptKernel::<RecordingTranscriptBackend>::default();
        native
            .absorb_u32s(&[M31_MODULUS, 9])
            .expect("the native transcript accepts the fixture");
        recording
            .absorb_u32s(&[M31_MODULUS, 9])
            .expect("the recording transcript accepts the fixture");
        let native_draw = native.draw_block();
        let recording_draw = recording.draw_block();
        assert_eq!(
            (native.digest(), native_draw),
            (recording.digest(), recording_draw)
        );
    }

    #[rstest]
    fn secure_field_absorption_matches_the_existing_channel() {
        let values = [
            SecureField::from_u32_unchecked(1, 2, 3, 4),
            SecureField::from_u32_unchecked(5, 6, 7, 8),
        ];
        let mut reference = Poseidon2M31Channel::default();
        reference.mix_felts(&values);
        let mut kernel = TranscriptKernel::<NativeTranscriptBackend>::default();
        kernel
            .absorb_secure_fields(&values)
            .expect("the secure-field limbs are canonical");
        assert_eq!(kernel.draw_secure_field(), Ok(reference.draw_secure_felt()));
    }

    #[rstest]
    fn absorption_resets_the_draw_counter_like_the_existing_channel() {
        let mut reference = Poseidon2M31Channel::default();
        let mut kernel = TranscriptKernel::<NativeTranscriptBackend>::default();
        reference.draw_u32s();
        reference.draw_u32s();
        kernel.draw_block().expect("the first draw succeeds");
        kernel.draw_block().expect("the second draw succeeds");
        reference.mix_u32s(&[9]);
        kernel.absorb_u32s(&[9]).expect("the absorption succeeds");
        assert_eq!(
            (kernel.draw_secure_field(), kernel.draw_count()),
            (Ok(reference.draw_secure_felt()), 1)
        );
    }

    #[rstest]
    fn raw_query_slots_match_stwo_draw_queries_without_deduplication() {
        let mut reference = Poseidon2M31Channel::default();
        reference.mix_u32s(&[11, 12]);
        let expected: [u32; 9] = draw_queries(&mut reference, 7, 9)
            .into_iter()
            .map(|query| u32::try_from(query).expect("the seven-bit query fits u32"))
            .collect::<Vec<_>>()
            .try_into()
            .expect("the reference returns the requested raw query count");
        let mut kernel = TranscriptKernel::<NativeTranscriptBackend>::default();
        kernel
            .absorb_u32s(&[11, 12])
            .expect("the fixture words are accepted");
        assert_eq!(kernel.draw_queries::<9>(7), Ok(expected));
    }

    #[rstest]
    #[case::zero(0)]
    #[case::above_circle_maximum(31)]
    fn invalid_query_domain_size_is_rejected(#[case] log_domain_size: u32) {
        let mut kernel = TranscriptKernel::<NativeTranscriptBackend>::default();
        assert_eq!(
            kernel.draw_queries::<1>(log_domain_size),
            Err(TranscriptError::QueryLogSizeOutOfRange { log_domain_size })
        );
    }

    #[rstest]
    fn recorded_pow_check_is_anchored_to_its_draw_permutation() {
        let mut reference = Poseidon2M31Channel::default();
        reference.mix_u32s(&[1, 2, 3]);
        let nonce = <SimdBackend as GrindOps<Poseidon2M31Channel>>::grind(&reference, 8);
        let mut kernel = TranscriptKernel::<RecordingTranscriptBackend>::default();
        kernel
            .absorb_u32s(&[1, 2, 3])
            .expect("the fixture words are accepted");
        kernel
            .verify_and_absorb_pow(nonce, 8)
            .expect("the generated nonce satisfies the fixture challenge");
        let trace = kernel.backend().trace();
        let check = trace.pow_checks[0];
        assert_eq!(
            trace
                .poseidon_calls
                .iter()
                .find(|call| call.id.call_id == check.call_id)
                .map(|call| call.output[0]),
            Some(check.word)
        );
    }

    #[rstest]
    fn recorded_calls_preserve_hash_session_and_step_coordinates() {
        let mut kernel = TranscriptKernel::<RecordingTranscriptBackend>::default();
        kernel
            .absorb_u32s(&[1, 2, 3, 4, 5])
            .expect("the fixture words are accepted");
        kernel.draw_block().expect("the draw succeeds");
        let trace = kernel.into_backend().into_trace();
        assert_eq!(
            trace.sponge_rows().map(|rows| rows
                .into_iter()
                .map(|row| (row.id.hash_id, row.id.step))
                .collect::<Vec<_>>()),
            Ok(vec![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1)])
        );
    }

    #[rstest]
    fn reordered_hash_steps_are_rejected_before_air_materialization() {
        let mut kernel = TranscriptKernel::<RecordingTranscriptBackend>::default();
        kernel
            .absorb_u32s(&[1])
            .expect("the fixture word is accepted");
        let mut trace = kernel.into_backend().into_trace();
        trace.poseidon_calls[1].id.step = 0;
        assert!(matches!(
            trace.sponge_rows(),
            Err(TranscriptError::TraceStepMismatch {
                call_id: 1,
                expected: 1,
                actual: 0,
            })
        ));
    }

    #[rstest]
    fn broken_hash_capacity_chaining_is_rejected_before_air_materialization() {
        let mut kernel = TranscriptKernel::<RecordingTranscriptBackend>::default();
        kernel
            .absorb_u32s(&[1])
            .expect("the fixture word is accepted");
        let mut trace = kernel.into_backend().into_trace();
        let expected = trace.poseidon_calls[0].output[RATE];
        trace.poseidon_calls[1].input[RATE] = add_m31_words(expected, M31Word::from(1));
        assert!(matches!(
            trace.sponge_rows(),
            Err(TranscriptError::TraceCapacityMismatch {
                call_id: 1,
                word: RATE,
                expected: actual_expected,
                ..
            }) if actual_expected == expected
        ));
    }

    #[rstest]
    fn recorded_transcript_proves_in_the_atomic_sponge_air() {
        let mut kernel = TranscriptKernel::<RecordingTranscriptBackend>::default();
        kernel
            .absorb_u32s(&[M31_MODULUS, u32::MAX, 7])
            .expect("the fixture words are accepted");
        kernel.draw_block().expect("the draw succeeds");
        let trace = kernel.into_backend().into_trace();
        let mut traces = RecursionTraces::default();
        let claims = trace
            .materialize_air_witness(&mut traces)
            .expect("the recorded sessions are structurally canonical");
        let proof = crate::prover::prove_recursion(
            traces,
            vec![],
            vec![],
            claims,
            vec![],
            PcsConfig::default(),
        );
        assert!(crate::prover::verify_recursion(proof, &[], PcsConfig::default()).is_ok());
    }
}
