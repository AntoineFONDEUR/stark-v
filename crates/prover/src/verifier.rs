//! Verifier for RV32IM proofs.

use num_traits::Zero;
use stwo::core::channel::{Channel, MerkleChannel};
use stwo::core::pcs::{CommitmentSchemeVerifier, PcsConfig};
use stwo::core::vcs_lifted::blake2_merkle::{Blake2sMerkleChannel, Blake2sMerkleHasher};
use stwo::core::verifier::verify;
use stwo_constraint_framework::TraceLocationAllocator;

use crate::Preprocessing;
use crate::Proof;
use crate::SegmentProof;
use crate::components::Components;
use crate::errors::VerificationError;
use crate::poseidon2_precompile::replay_poseidon2_precompile;
use crate::precompile::{bind_joint_interaction, verify_joint_interaction_in_channel};
use crate::relations::Relations;

/// Replays the VM transcript through its main commitment.
fn replay_vm_main<MC: MerkleChannel>(
    proof: &Proof<MC::H>,
    config: PcsConfig,
    preprocessing: &Preprocessing<MC::H>,
) -> Result<(MC::C, CommitmentSchemeVerifier<MC>), VerificationError> {
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
    let commitments = &proof.stark_proof.commitments;
    let preprocessing_root = commitments
        .first()
        .ok_or(VerificationError::MissingProofPreprocessingCommitment)?;
    let main_root = commitments.get(1).ok_or_else(|| {
        stwo::core::verifier::VerificationError::InvalidStructure(
            "VM proof has no main commitment".to_string(),
        )
    })?;
    commitment_scheme.commit(*preprocessing_root, &preprocessing.log_sizes, &mut channel);
    commitment_scheme.commit(
        *main_root,
        &proof.claim.main_trace_log_sizes(),
        &mut channel,
    );
    proof.claim.mix_into(&mut channel);
    Ok((channel, commitment_scheme))
}

pub fn verify_rv32im(
    proof: SegmentProof<Blake2sMerkleHasher>,
    config: PcsConfig,
    preprocessing: &Preprocessing,
) -> Result<(), VerificationError> {
    verify_rv32im_with_channel::<Blake2sMerkleChannel>(proof, config, preprocessing)
}

/// Verify an RV32IM proof with any Merkle channel.
pub fn verify_rv32im_with_channel<MC: MerkleChannel>(
    proof: SegmentProof<MC::H>,
    config: PcsConfig,
    preprocessing: &Preprocessing<MC::H>,
) -> Result<(), VerificationError> {
    let SegmentProof {
        vm,
        poseidon2,
        joint_interaction,
    } = proof;
    let (mut vm_channel, mut vm_commitment_scheme) =
        replay_vm_main::<MC>(&vm, config, preprocessing)?;
    let vm_seed = vm_channel.draw_secure_felt();
    let (poseidon2_seed, mut poseidon2_verifier) =
        replay_poseidon2_precompile::<MC>(poseidon2, config)?;
    let seeds = [vm_seed, poseidon2_seed];
    verify_joint_interaction_in_channel(&mut vm_channel, seeds, joint_interaction, true)?;
    let relations = Relations::draw(&mut vm_channel);
    bind_joint_interaction(&mut poseidon2_verifier.channel, seeds, joint_interaction);

    let shared_relation_sum =
        vm.interaction_claim.claimed_sum.total() + vm.public_data.logup_sum(&relations);
    if shared_relation_sum != vm.interaction_claim.shared_relation_sum {
        return Err(VerificationError::InvalidSharedRelationClaim);
    }
    if !(shared_relation_sum + poseidon2_verifier.claimed_sum()).is_zero() {
        return Err(VerificationError::SharedRelationMismatch);
    }

    vm.interaction_claim.mix_into(&mut vm_channel);
    if !vm.interaction_claim.log_sizes.is_empty() {
        let interaction_root = vm.stark_proof.commitments.get(2).ok_or_else(|| {
            stwo::core::verifier::VerificationError::InvalidStructure(
                "VM proof has no interaction commitment".to_string(),
            )
        })?;
        vm_commitment_scheme.commit(
            *interaction_root,
            &vm.interaction_claim.log_sizes,
            &mut vm_channel,
        );
    }

    // Verify STARK proof.
    let preprocessed_ids = preprocessing.column_ids();
    let mut location_allocator =
        TraceLocationAllocator::new_with_preprocessed_columns(&preprocessed_ids);
    let components = Components::new(
        &vm.claim,
        &mut location_allocator,
        relations.clone(),
        &vm.interaction_claim.claimed_sum,
    );

    verify(
        &components.verifiers(),
        &mut vm_channel,
        &mut vm_commitment_scheme,
        vm.stark_proof,
    )
    .map_err(VerificationError::from)?;
    poseidon2_verifier
        .verify_bound(seeds, relations)
        .map_err(VerificationError::from)
}
