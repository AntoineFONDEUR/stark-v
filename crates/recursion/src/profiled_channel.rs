//! STWO channel adapter for the manifest-bound recursive verifier transcript.
//!
//! A recursion-targeted child proof must be produced under the same typed
//! operation headers that the universal transcript AIR authenticates. This
//! channel consumes the trusted verifier plan as STWO requests commitments,
//! randomness, proof-of-work checks, and query blocks, while retaining the
//! Poseidon2-M31 Merkle hash used by ordinary VM proofs.

use core::fmt;

use air::digest::{Digest8, M31Word, ProtocolId, VmPublicClaimDigest};
use prover::poseidon2_channel::{Poseidon2M31Hash, Poseidon2M31MerkleHasher};
use stwo::core::channel::{Channel, MerkleChannel};
use stwo::core::fields::qm31::{SECURE_EXTENSION_DEGREE, SecureField};
use stwo::core::proof_of_work::GrindOps;
use stwo::prover::backend::simd::SimdBackend;

use crate::kernel::{VerifierControlPlan, VerifierSchema, VerifierStep};
use crate::protocol::CanonicalWords;
use crate::statement::SpanStatement;
use crate::transcript::{NativeTranscriptBackend, TranscriptError, TranscriptKernel};
use crate::transcript_program::operation_header;

const DRAW_WORD_COUNT: usize = 8;

/// Poseidon2-M31 Fiat-Shamir state driven by one trusted verifier plan.
#[derive(Clone, Debug, Default)]
pub struct ProfiledPoseidon2M31Channel {
    kernel: TranscriptKernel<NativeTranscriptBackend>,
    plan: Option<VerifierControlPlan>,
    next_sequence: usize,
    draws: Vec<(VerifierStep, [M31Word; DRAW_WORD_COUNT])>,
}

impl ProfiledPoseidon2M31Channel {
    /// Initializes the fixed prefix known before the first trace commitment.
    pub fn for_vm_proof(
        plan: &VerifierControlPlan,
        protocol_id: ProtocolId,
        statement: &SpanStatement,
    ) -> Result<Self, ProfiledChannelError> {
        if plan.schema() != VerifierSchema::Vm {
            return Err(ProfiledChannelError::SchemaMismatch {
                expected: VerifierSchema::Vm,
                actual: plan.schema(),
            });
        }
        let mut channel = Self {
            kernel: TranscriptKernel::default(),
            plan: Some(plan.clone()),
            next_sequence: 0,
            draws: Vec::new(),
        };
        channel.consume_exact_mix(VerifierStep::BindProtocol, protocol_id.digest().words())?;
        channel.consume_exact_mix(VerifierStep::BindStatement, &statement.canonical_words())?;
        channel.consume_exact_mix(
            VerifierStep::BindPcsParameters,
            &plan.pcs_parameters().canonical_words(),
        )?;
        Ok(channel)
    }

    /// Initializes the fixed prefix of one universal recursion proof.
    pub fn for_recursion_proof(
        plan: &VerifierControlPlan,
        protocol_id: ProtocolId,
        statement: &SpanStatement,
    ) -> Result<Self, ProfiledChannelError> {
        if plan.schema() != VerifierSchema::Recursion {
            return Err(ProfiledChannelError::SchemaMismatch {
                expected: VerifierSchema::Recursion,
                actual: plan.schema(),
            });
        }
        let mut channel = Self {
            kernel: TranscriptKernel::default(),
            plan: Some(plan.clone()),
            next_sequence: 0,
            draws: Vec::new(),
        };
        channel.consume_exact_mix(VerifierStep::BindProtocol, protocol_id.digest().words())?;
        channel.consume_exact_mix(VerifierStep::BindStatement, &statement.canonical_words())?;
        channel.consume_exact_mix(
            VerifierStep::BindPcsParameters,
            &plan.pcs_parameters().canonical_words(),
        )?;
        Ok(channel)
    }

    /// Binds the fixed canonical VM claim after the main trace commitment.
    pub fn absorb_vm_public_claim(
        &mut self,
        digest: VmPublicClaimDigest,
    ) -> Result<(), ProfiledChannelError> {
        self.consume_exact_mix(VerifierStep::AbsorbPublicClaim, digest.digest().words())
    }

    /// Consumes the recursion schema's empty public-claim frame.
    ///
    /// The complete recursion claim is the statement bound in the fixed prefix,
    /// but the shared verifier schedule retains this domain-separation step.
    pub fn absorb_recursion_public_claim(&mut self) -> Result<(), ProfiledChannelError> {
        self.consume_exact_mix(VerifierStep::AbsorbPublicClaim, &[])
    }

    /// Binds all component LogUp claims in canonical roster order.
    pub fn absorb_claimed_sums(
        &mut self,
        claimed_sums: &[SecureField],
    ) -> Result<(), ProfiledChannelError> {
        let (_, step) = self.next_transcript_step()?;
        let VerifierStep::AbsorbClaimedSums { count } = step else {
            return Err(self.unexpected("claimed sums", step));
        };
        require_count("claimed sums", count, claimed_sums.len())?;
        self.consume_secure_field_mix(step, claimed_sums)
    }

    /// Requires the STWO prover to have consumed every transcript operation.
    pub fn finish(&self) -> Result<(), ProfiledChannelError> {
        if let Some((sequence, step)) = self.peek_transcript_step() {
            Err(ProfiledChannelError::UnconsumedStep { sequence, step })
        } else {
            Ok(())
        }
    }

    /// Returns every STWO randomness block in trusted verifier-step order.
    pub fn draws(&self) -> &[(VerifierStep, [M31Word; DRAW_WORD_COUNT])] {
        &self.draws
    }

    fn consume_root(&mut self, root: Poseidon2M31Hash) -> Result<(), ProfiledChannelError> {
        let (_, step) = self.next_transcript_step()?;
        if !matches!(
            step,
            VerifierStep::AbsorbTraceCommitment { .. } | VerifierStep::AbsorbFriCommitment { .. }
        ) {
            return Err(self.unexpected("Merkle commitment", step));
        }
        let digest = Digest8::try_from(root.0).expect("Poseidon2 roots are canonical M31 words");
        self.consume_mix(step, digest.words())
    }

    fn consume_secure_field_mix(
        &mut self,
        step: VerifierStep,
        values: &[SecureField],
    ) -> Result<(), ProfiledChannelError> {
        let words = values
            .iter()
            .flat_map(|value| value.to_m31_array())
            .map(M31Word::from)
            .collect::<Vec<_>>();
        self.consume_mix(step, &words)
    }

    fn consume_exact_mix(
        &mut self,
        expected: VerifierStep,
        payload: &[M31Word],
    ) -> Result<(), ProfiledChannelError> {
        let (_, actual) = self.next_transcript_step()?;
        if actual != expected {
            return Err(self.unexpected("fixed transcript mix", actual));
        }
        self.consume_mix(actual, payload)
    }

    fn consume_mix(
        &mut self,
        step: VerifierStep,
        payload: &[M31Word],
    ) -> Result<(), ProfiledChannelError> {
        let (sequence, actual) = self.next_transcript_step()?;
        if actual != step {
            return Err(self.unexpected("transcript mix", actual));
        }
        let mut words = operation_header(sequence, step)
            .map_err(ProfiledChannelError::Program)?
            .to_vec();
        words.extend_from_slice(payload);
        self.kernel
            .absorb_m31_words(&words)
            .map_err(ProfiledChannelError::Transcript)?;
        self.next_sequence = sequence as usize + 1;
        Ok(())
    }

    fn consume_draw(&mut self) -> Result<[M31Word; DRAW_WORD_COUNT], ProfiledChannelError> {
        let (sequence, step) = self.next_transcript_step()?;
        if !matches!(
            step,
            VerifierStep::DrawRelationChallenge { .. }
                | VerifierStep::DrawCompositionRandomness
                | VerifierStep::DrawOodsPoint
                | VerifierStep::DrawDeepRandomness
                | VerifierStep::DrawFriAlpha { .. }
                | VerifierStep::DrawQueryBlock { .. }
        ) {
            return Err(self.unexpected("randomness draw", step));
        }
        let header = operation_header(sequence, step).map_err(ProfiledChannelError::Program)?;
        self.kernel
            .absorb_m31_words(&header)
            .map_err(ProfiledChannelError::Transcript)?;
        let words = self
            .kernel
            .draw_block()
            .map_err(ProfiledChannelError::Transcript)?;
        self.draws.push((step, words));
        self.next_sequence = sequence as usize + 1;
        Ok(words)
    }

    fn consume_pow(&mut self, nonce: u64, bits: u32) -> Result<(), ProfiledChannelError> {
        let (sequence, step) = self.next_transcript_step()?;
        let expected_bits = match step {
            VerifierStep::VerifyAndAbsorbInteractionPow { bits }
            | VerifierStep::VerifyAndAbsorbPcsPow { bits } => bits,
            _ => return Err(self.unexpected("proof of work", step)),
        };
        if bits != expected_bits {
            return Err(ProfiledChannelError::PowBitsMismatch {
                expected: expected_bits,
                actual: bits,
            });
        }
        let mut words = operation_header(sequence, step)
            .map_err(ProfiledChannelError::Program)?
            .to_vec();
        words.extend(crate::transcript::encode_u64_words(nonce));
        self.kernel
            .absorb_m31_words(&words)
            .map_err(ProfiledChannelError::Transcript)?;
        self.kernel
            .verify_pow_from_current_digest(nonce, bits)
            .map_err(ProfiledChannelError::Transcript)?;
        self.next_sequence = sequence as usize + 1;
        Ok(())
    }

    fn next_transcript_step(&self) -> Result<(u32, VerifierStep), ProfiledChannelError> {
        self.peek_transcript_step()
            .ok_or(ProfiledChannelError::PlanExhausted)
    }

    fn peek_transcript_step(&self) -> Option<(u32, VerifierStep)> {
        let plan = self.plan.as_ref()?;
        plan.steps()
            .iter()
            .copied()
            .enumerate()
            .skip(self.next_sequence)
            .find(|(_, step)| step.transcript_effect().is_some())
            .map(|(sequence, step)| {
                (
                    u32::try_from(sequence).expect("verifier plans fit u32"),
                    step,
                )
            })
    }

    fn unexpected(&self, operation: &'static str, actual: VerifierStep) -> ProfiledChannelError {
        ProfiledChannelError::UnexpectedStep {
            operation,
            sequence: self
                .peek_transcript_step()
                .map_or(self.next_sequence as u32, |(sequence, _)| sequence),
            actual,
        }
    }
}

impl Channel for ProfiledPoseidon2M31Channel {
    const BYTES_PER_HASH: usize = DRAW_WORD_COUNT * 4;

    fn verify_pow_nonce(&self, n_bits: u32, nonce: u64) -> bool {
        let mut candidate = self.clone();
        candidate.consume_pow(nonce, n_bits).is_ok()
    }

    fn mix_u32s(&mut self, _data: &[u32]) {
        panic!("the profiled transcript accepts typed canonical payloads only")
    }

    fn mix_felts(&mut self, felts: &[SecureField]) {
        let (_, step) = self
            .next_transcript_step()
            .expect("STWO requested field absorption after the verifier plan ended");
        let expected = match step {
            VerifierStep::AbsorbSampledValues { count }
            | VerifierStep::AbsorbLastLayerCoefficients { count } => count,
            _ => panic!("STWO field absorption disagrees with verifier step {step:?}"),
        };
        require_count("secure fields", expected, felts.len())
            .and_then(|()| self.consume_secure_field_mix(step, felts))
            .expect("STWO field absorption matches the trusted verifier plan");
    }

    fn mix_u64(&mut self, value: u64) {
        let (_, step) = self
            .next_transcript_step()
            .expect("STWO requested nonce absorption after the verifier plan ended");
        let bits = match step {
            VerifierStep::VerifyAndAbsorbInteractionPow { bits }
            | VerifierStep::VerifyAndAbsorbPcsPow { bits } => bits,
            _ => panic!("STWO nonce absorption disagrees with verifier step {step:?}"),
        };
        self.consume_pow(value, bits)
            .expect("STWO absorbs only a nonce accepted under the trusted verifier plan");
    }

    fn draw_secure_felt(&mut self) -> SecureField {
        self.draw_secure_felts(1)
            .into_iter()
            .next()
            .expect("one secure field was requested")
    }

    fn draw_secure_felts(&mut self, n_felts: usize) -> Vec<SecureField> {
        if n_felts == 0 {
            return Vec::new();
        }
        assert!(
            n_felts <= DRAW_WORD_COUNT / SECURE_EXTENSION_DEGREE,
            "one verifier draw returns at most two secure fields"
        );
        let words = self
            .consume_draw()
            .expect("STWO randomness draw matches the trusted verifier plan");
        words
            .chunks_exact(SECURE_EXTENSION_DEGREE)
            .take(n_felts)
            .map(|limbs| {
                let limbs: [M31Word; SECURE_EXTENSION_DEGREE] =
                    limbs.try_into().expect("one secure-field chunk");
                SecureField::from_m31_array(limbs.map(stwo::core::fields::m31::M31::from))
            })
            .collect()
    }

    fn draw_u32s(&mut self) -> Vec<u32> {
        self.consume_draw()
            .expect("STWO query draw matches the trusted verifier plan")
            .map(M31Word::as_u32)
            .to_vec()
    }
}

/// Merkle channel pairing the profiled transcript with the existing hash AIR.
#[derive(Default)]
pub struct ProfiledPoseidon2M31MerkleChannel;

impl MerkleChannel for ProfiledPoseidon2M31MerkleChannel {
    type C = ProfiledPoseidon2M31Channel;
    type H = Poseidon2M31MerkleHasher;

    fn mix_root(channel: &mut Self::C, root: Poseidon2M31Hash) {
        channel
            .consume_root(root)
            .expect("STWO commitment order matches the trusted verifier plan");
    }
}

impl GrindOps<ProfiledPoseidon2M31Channel> for SimdBackend {
    fn grind(channel: &ProfiledPoseidon2M31Channel, pow_bits: u32) -> u64 {
        (0_u64..)
            .find(|nonce| channel.verify_pow_nonce(pow_bits, *nonce))
            .expect("the u64 nonce space contains a proof-of-work solution")
    }
}

impl stwo::prover::backend::BackendForChannel<ProfiledPoseidon2M31MerkleChannel> for SimdBackend {}

fn require_count(
    field: &'static str,
    expected: u32,
    actual: usize,
) -> Result<(), ProfiledChannelError> {
    let actual = u32::try_from(actual)
        .map_err(|_| ProfiledChannelError::CountOutOfRange { field, actual })?;
    if actual == expected {
        Ok(())
    } else {
        Err(ProfiledChannelError::CountMismatch {
            field,
            expected,
            actual,
        })
    }
}

/// Invalid use of the manifest-bound STWO transcript adapter.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProfiledChannelError {
    SchemaMismatch {
        expected: VerifierSchema,
        actual: VerifierSchema,
    },
    PlanExhausted,
    UnexpectedStep {
        operation: &'static str,
        sequence: u32,
        actual: VerifierStep,
    },
    UnconsumedStep {
        sequence: u32,
        step: VerifierStep,
    },
    PowBitsMismatch {
        expected: u32,
        actual: u32,
    },
    CountOutOfRange {
        field: &'static str,
        actual: usize,
    },
    CountMismatch {
        field: &'static str,
        expected: u32,
        actual: u32,
    },
    Program(crate::transcript_program::TranscriptProgramError),
    Transcript(TranscriptError),
}

impl fmt::Display for ProfiledChannelError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SchemaMismatch { expected, actual } => {
                write!(
                    formatter,
                    "expected {expected:?} verifier plan, got {actual:?}"
                )
            }
            Self::PlanExhausted => write!(formatter, "verifier transcript plan is exhausted"),
            Self::UnexpectedStep {
                operation,
                sequence,
                actual,
            } => write!(
                formatter,
                "{operation} reached verifier step {sequence} ({actual:?})"
            ),
            Self::UnconsumedStep { sequence, step } => {
                write!(
                    formatter,
                    "verifier step {sequence} ({step:?}) was not consumed"
                )
            }
            Self::PowBitsMismatch { expected, actual } => {
                write!(
                    formatter,
                    "PoW uses {actual} bits, verifier plan requires {expected}"
                )
            }
            Self::CountOutOfRange { field, actual } => {
                write!(formatter, "{field} count {actual} does not fit u32")
            }
            Self::CountMismatch {
                field,
                expected,
                actual,
            } => write!(formatter, "{field} count is {actual}, expected {expected}"),
            Self::Program(error) => write!(formatter, "invalid verifier operation: {error}"),
            Self::Transcript(error) => write!(formatter, "invalid transcript transition: {error}"),
        }
    }
}

impl std::error::Error for ProfiledChannelError {}

/// Claim-phase policy for recursion-targeted VM proofs.
#[derive(Clone, Copy, Debug)]
pub struct RecursionVmClaimTranscript {
    public_claim: VmPublicClaimDigest,
}

impl RecursionVmClaimTranscript {
    pub const fn new(public_claim: VmPublicClaimDigest) -> Self {
        Self { public_claim }
    }
}

impl prover::VmClaimTranscript<ProfiledPoseidon2M31Channel> for RecursionVmClaimTranscript {
    type Error = ProfiledChannelError;

    fn bind_before_commitments(
        &self,
        _channel: &mut ProfiledPoseidon2M31Channel,
        _public_data: &prover::public_data::PublicData,
    ) -> Result<(), Self::Error> {
        // The constructor binds the trusted protocol prefix before any root exists.
        Ok(())
    }

    fn bind_after_main_commitment(
        &self,
        channel: &mut ProfiledPoseidon2M31Channel,
        _public_data: &prover::public_data::PublicData,
        _claim: &prover::components::Claim,
    ) -> Result<(), Self::Error> {
        channel.absorb_vm_public_claim(self.public_claim)
    }

    fn bind_interaction_claim(
        &self,
        channel: &mut ProfiledPoseidon2M31Channel,
        interaction_claim: &prover::InteractionClaim,
    ) -> Result<(), Self::Error> {
        channel.absorb_claimed_sums(&interaction_claim.claimed_sum.component_values())
    }
}
