//! Verifier for RV32IM proofs.

use num_traits::Zero;
use stwo::core::channel::{Channel, MerkleChannel};
use stwo::core::pcs::{CommitmentSchemeVerifier, PcsConfig};
use stwo::core::vcs_lifted::blake2_merkle::{Blake2sMerkleChannel, Blake2sMerkleHasher};
use stwo::core::verifier::verify;
use stwo_constraint_framework::TraceLocationAllocator;

use crate::Preprocessing;
use crate::Proof;
use crate::components::Components;
use crate::errors::VerificationError;
use crate::relations::{INTERACTION_POW_BITS, Relations};

/// Replay the claim phase of the Fiat-Shamir transcript: mix public data,
/// commit the preprocessed/main/interaction trees, check the interaction
/// proof of work, and draw the LogUp relations.
///
/// Returns the channel and commitment scheme advanced to the state right
/// before `stwo::core::verifier::verify` takes over (composition commitment
/// and OODS draws). Keeping this phase explicit lets other verifiers replay
/// the exact VM transcript prefix without duplicating its order.
pub fn replay_claim_phase<MC: MerkleChannel>(
    proof: &Proof<MC::H>,
    config: PcsConfig,
    preprocessing: &Preprocessing<MC::H>,
) -> Result<(MC::C, CommitmentSchemeVerifier<MC>, Relations), VerificationError> {
    // Preprocessing defines trusted lookup columns, so its commitment must not come from the proof.
    let proof_preprocessing_root = proof
        .stark_proof
        .commitments
        .first()
        .ok_or(VerificationError::MissingProofPreprocessingCommitment)?;
    let verifier_preprocessing_root = preprocessing
        .commitment_root()
        .ok_or(VerificationError::MissingVerifierPreprocessingCommitment)?;
    if *proof_preprocessing_root != verifier_preprocessing_root {
        return Err(VerificationError::PreprocessingCommitmentMismatch);
    }

    let mut channel = MC::C::default();
    let mut commitment_scheme = CommitmentSchemeVerifier::<MC>::new(config);

    // Public data.
    proof.public_data.mix_into(&mut channel);

    // Preprocessed trace — use pre-computed log sizes from preprocessing.
    let mut commitment_index = 0usize;
    {
        let commitments = &proof.stark_proof.commitments;
        commitment_scheme.commit(
            commitments[commitment_index],
            &preprocessing.log_sizes,
            &mut channel,
        );
        commitment_index += 1;

        // Main execution trace.
        let main_log_sizes = proof.claim.main_trace_log_sizes();
        commitment_scheme.commit(commitments[commitment_index], &main_log_sizes, &mut channel);
        commitment_index += 1;
    }
    proof.claim.mix_into(&mut channel);

    // Interaction proof of work.
    if !channel.verify_pow_nonce(INTERACTION_POW_BITS, proof.interaction_pow) {
        return Err(VerificationError::InteractionProofOfWork);
    }
    channel.mix_u64(proof.interaction_pow);

    // Draw lookup elements.
    let relations = Relations::draw(&mut channel);

    // Mix interaction claim and commit interaction trace.
    proof.interaction_claim.mix_into(&mut channel);
    if !proof.interaction_claim.log_sizes.is_empty() {
        let commitments = &proof.stark_proof.commitments;
        commitment_scheme.commit(
            commitments[commitment_index],
            &proof.interaction_claim.log_sizes,
            &mut channel,
        );
    }

    Ok((channel, commitment_scheme, relations))
}

pub fn verify_rv32im(
    proof: Proof<Blake2sMerkleHasher>,
    config: PcsConfig,
    preprocessing: &Preprocessing,
) -> Result<(), VerificationError> {
    verify_rv32im_with_channel::<Blake2sMerkleChannel>(proof, config, preprocessing)
}

/// Verify an RV32IM proof with any Merkle channel.
pub fn verify_rv32im_with_channel<MC: MerkleChannel>(
    proof: Proof<MC::H>,
    config: PcsConfig,
    preprocessing: &Preprocessing<MC::H>,
) -> Result<(), VerificationError> {
    let (mut channel, mut commitment_scheme, relations) =
        replay_claim_phase::<MC>(&proof, config, preprocessing)?;

    // Verify LogUp sum (components + public data).
    let total_sum =
        proof.interaction_claim.claimed_sum.total() + proof.public_data.logup_sum(&relations);
    if !total_sum.is_zero() {
        return Err(VerificationError::InvalidLogupSum);
    }

    // Verify STARK proof.
    let preprocessed_ids = preprocessing.column_ids();
    let mut location_allocator =
        TraceLocationAllocator::new_with_preprocessed_columns(&preprocessed_ids);
    let components = Components::new(
        &proof.claim,
        &mut location_allocator,
        relations,
        &proof.interaction_claim.claimed_sum,
    );

    verify(
        &components.verifiers(),
        &mut channel,
        &mut commitment_scheme,
        proof.stark_proof,
    )
    .map_err(VerificationError::from)
}
