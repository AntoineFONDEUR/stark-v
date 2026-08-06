//! Standalone Poseidon2 STARK instance for a split VM segment proof.
//!
//! The prover commits the DSL-generated Poseidon2 trace before exposing its
//! interaction seed. A caller combines that seed with the VM seed, performs
//! the joint interaction grind, and supplies the resulting shared relations
//! before this instance can finish.

use core::fmt;

use serde::{Deserialize, Serialize};
use stwo::core::air::Component as AirComponent;
use stwo::core::channel::{Channel, MerkleChannel};
use stwo::core::fields::qm31::SecureField;
use stwo::core::pcs::quotients::CommitmentSchemeProofAux;
use stwo::core::pcs::{CommitmentSchemeVerifier, PcsConfig};
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::proof::StarkProof;
use stwo::core::vcs_lifted::merkle_hasher::MerkleHasherLifted;
use stwo::core::verifier::{VerificationError, verify};
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::pcs::CommitmentSchemeProver;
use stwo::prover::poly::circle::PolyOps;
use stwo::prover::poly::twiddles::TwiddleTree;
use stwo::prover::{ProvingError, prove_ex};
use stwo_constraint_framework::TraceLocationAllocator;

use air::trace::Poseidon2Table;
use air::trace::prover_columns::Poseidon2Columns;

use crate::precompile::{JointInteractionProof, bind_joint_interaction};
use crate::relations::Relations;

type B = SimdBackend;

/// Public main-trace shape of one standalone Poseidon2 instance.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Poseidon2PrecompileClaim {
    pub log_size: u32,
}

impl Poseidon2PrecompileClaim {
    fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u32s(&[self.log_size]);
    }

    fn main_trace_log_sizes(&self) -> Vec<u32> {
        vec![self.log_size; Poseidon2Columns::<()>::SIZE]
    }
}

/// Public shared-relation sum and interaction-tree shape.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Poseidon2PrecompileInteractionClaim {
    pub claimed_sum: SecureField,
    pub log_sizes: Vec<u32>,
}

impl Poseidon2PrecompileInteractionClaim {
    fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
        channel.mix_u64(self.log_sizes.len() as u64);
        for log_size in &self.log_sizes {
            channel.mix_u64(*log_size as u64);
        }
    }
}

/// One standalone Poseidon2 proof and the public claim needed by its binder.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Poseidon2PrecompileProof<H: MerkleHasherLifted> {
    pub claim: Poseidon2PrecompileClaim,
    pub interaction_claim: Poseidon2PrecompileInteractionClaim,
    pub stark_proof: StarkProof<H>,
    /// Raw opening expansion retained until recursion adapts the proof.
    #[serde(skip, default)]
    pub stark_aux: Option<CommitmentSchemeProofAux<H>>,
}

/// Failure while building the fixed standalone Poseidon2 proof.
#[derive(Clone, Debug)]
pub enum Poseidon2PrecompileProvingError {
    TraceCapacityExceeded { rows: usize, log_size: u32 },
    JointSeedMismatch,
    InteractionShapeMismatch,
    Stark(ProvingError),
}

impl fmt::Display for Poseidon2PrecompileProvingError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TraceCapacityExceeded { rows, log_size } => write!(
                formatter,
                "Poseidon2 precompile has {rows} rows, exceeding fixed log size {log_size}",
            ),
            Self::JointSeedMismatch => {
                formatter.write_str("joint transcript does not contain the Poseidon2 seed")
            }
            Self::InteractionShapeMismatch => {
                formatter.write_str("Poseidon2 interaction trace does not match its DSL AIR")
            }
            Self::Stark(error) => write!(formatter, "Poseidon2 proof generation failed: {error}"),
        }
    }
}

impl std::error::Error for Poseidon2PrecompileProvingError {}

impl From<ProvingError> for Poseidon2PrecompileProvingError {
    fn from(error: ProvingError) -> Self {
        Self::Stark(error)
    }
}

/// Poseidon2 main commitment before the shared relation draw.
pub struct CommittedPoseidon2Precompile<'a, MC>
where
    MC: MerkleChannel,
    B: stwo::prover::backend::BackendForChannel<MC>
        + stwo::prover::backend::ColumnOps<
            <MC::H as MerkleHasherLifted>::Hash,
            Column = Vec<<MC::H as MerkleHasherLifted>::Hash>,
        >,
{
    trace: stwo::core::ColumnVec<
        stwo::prover::poly::circle::CircleEvaluation<
            B,
            stwo::core::fields::m31::BaseField,
            stwo::prover::poly::BitReversedOrder,
        >,
    >,
    claim: Poseidon2PrecompileClaim,
    commitment_scheme: CommitmentSchemeProver<'a, B, MC>,
    channel: MC::C,
}

/// Poseidon2 commitment after its unique post-commitment seed was drawn.
pub struct SeededPoseidon2Precompile<'a, MC>
where
    MC: MerkleChannel,
    B: stwo::prover::backend::BackendForChannel<MC>
        + stwo::prover::backend::ColumnOps<
            <MC::H as MerkleHasherLifted>::Hash,
            Column = Vec<<MC::H as MerkleHasherLifted>::Hash>,
        >,
{
    committed: CommittedPoseidon2Precompile<'a, MC>,
    interaction_seed: SecureField,
}

/// Builds the evaluation-domain twiddles for a fixed Poseidon2 shape.
pub fn precompute_poseidon2_precompile_twiddles(
    config: PcsConfig,
    log_size: u32,
) -> TwiddleTree<B> {
    B::precompute_twiddles(
        CanonicCoset::new(log_size + 2 + config.fri_config.log_blowup_factor)
            .circle_domain()
            .half_coset,
    )
}

/// Commits a fixed-size Poseidon2 trace without drawing interaction relations.
pub fn commit_poseidon2_precompile<'a, MC>(
    table: Poseidon2Table,
    log_size: u32,
    config: PcsConfig,
    twiddles: &'a TwiddleTree<B>,
    mut channel: MC::C,
) -> Result<CommittedPoseidon2Precompile<'a, MC>, Poseidon2PrecompileProvingError>
where
    MC: MerkleChannel,
    B: stwo::prover::backend::BackendForChannel<MC>
        + stwo::prover::backend::ColumnOps<
            <MC::H as MerkleHasherLifted>::Hash,
            Column = Vec<<MC::H as MerkleHasherLifted>::Hash>,
        >,
{
    let rows = table.len();
    let trace = table
        .into_witness_with_log_size(log_size)
        .ok_or(Poseidon2PrecompileProvingError::TraceCapacityExceeded { rows, log_size })?;
    let claim = Poseidon2PrecompileClaim { log_size };
    let mut commitment_scheme = CommitmentSchemeProver::<B, MC>::new(config, twiddles);

    // The instance has no execution-independent columns, but STWO keeps the
    // preprocessing tree position in every proof transcript.
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(vec![]);
    tree_builder.commit(&mut channel);

    claim.mix_into(&mut channel);
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(trace.clone());
    tree_builder.commit(&mut channel);

    Ok(CommittedPoseidon2Precompile {
        trace,
        claim,
        commitment_scheme,
        channel,
    })
}

impl<'a, MC> CommittedPoseidon2Precompile<'a, MC>
where
    MC: MerkleChannel,
    B: stwo::prover::backend::BackendForChannel<MC>
        + stwo::prover::backend::ColumnOps<
            <MC::H as MerkleHasherLifted>::Hash,
            Column = Vec<<MC::H as MerkleHasherLifted>::Hash>,
        >,
{
    /// Draws the seed that the joint VM/hash transcript must absorb second.
    pub fn into_seeded(mut self) -> (SecureField, SeededPoseidon2Precompile<'a, MC>) {
        let interaction_seed = self.channel.draw_secure_felt();
        (
            interaction_seed,
            SeededPoseidon2Precompile {
                committed: self,
                interaction_seed,
            },
        )
    }
}

impl<'a, MC> SeededPoseidon2Precompile<'a, MC>
where
    MC: MerkleChannel,
    B: stwo::prover::backend::BackendForChannel<MC>
        + stwo::prover::backend::ColumnOps<
            <MC::H as MerkleHasherLifted>::Hash,
            Column = Vec<<MC::H as MerkleHasherLifted>::Hash>,
        >,
{
    /// Finishes the interaction trace and STARK under the joint relation draw.
    pub fn prove(
        mut self,
        seeds: [SecureField; 2],
        joint_interaction: JointInteractionProof,
        relations: Relations,
    ) -> Result<Poseidon2PrecompileProof<MC::H>, Poseidon2PrecompileProvingError> {
        if seeds[1] != self.interaction_seed {
            return Err(Poseidon2PrecompileProvingError::JointSeedMismatch);
        }
        bind_joint_interaction(&mut self.committed.channel, seeds, joint_interaction);

        let (interaction_trace, claimed_sum) =
            air::poseidon2::component::witness::gen_interaction_trace(
                &self.committed.trace,
                &relations,
            );
        let interaction_claim = Poseidon2PrecompileInteractionClaim {
            claimed_sum,
            log_sizes: interaction_trace
                .iter()
                .map(|column| column.domain.log_size())
                .collect(),
        };

        let mut location_allocator = TraceLocationAllocator::default();
        let component = air::poseidon2::component::air::Component::new(
            &mut location_allocator,
            air::poseidon2::component::air::Eval {
                log_size: self.committed.claim.log_size,
                relations,
            },
            claimed_sum,
        );
        if component.trace_log_degree_bounds()[2] != interaction_claim.log_sizes {
            return Err(Poseidon2PrecompileProvingError::InteractionShapeMismatch);
        }

        interaction_claim.mix_into(&mut self.committed.channel);
        let mut tree_builder = self.committed.commitment_scheme.tree_builder();
        tree_builder.extend_evals(interaction_trace);
        tree_builder.commit(&mut self.committed.channel);

        let extended = prove_ex(
            &[&component],
            &mut self.committed.channel,
            self.committed.commitment_scheme,
            false,
        )?;
        Ok(Poseidon2PrecompileProof {
            claim: self.committed.claim,
            interaction_claim,
            stark_proof: extended.proof,
            stark_aux: Some(extended.aux),
        })
    }
}

/// Verifies the hash instance under the VM seed and the shared joint grind.
///
/// This verifies the carried sum but does not require it to be zero; the
/// segment binder must cancel it against the VM proof's shared deficit.
pub fn verify_poseidon2_precompile<MC>(
    proof: Poseidon2PrecompileProof<MC::H>,
    config: PcsConfig,
    vm_seed: SecureField,
    joint_interaction: JointInteractionProof,
) -> Result<(), VerificationError>
where
    MC: MerkleChannel,
{
    let commitments = &proof.stark_proof.commitments;
    let preprocessing_root = commitments.first().ok_or_else(|| {
        VerificationError::InvalidStructure(
            "Poseidon2 proof has no preprocessing commitment".to_string(),
        )
    })?;
    let main_root = commitments.get(1).ok_or_else(|| {
        VerificationError::InvalidStructure("Poseidon2 proof has no main commitment".to_string())
    })?;
    let interaction_root = commitments.get(2).ok_or_else(|| {
        VerificationError::InvalidStructure(
            "Poseidon2 proof has no interaction commitment".to_string(),
        )
    })?;

    let mut channel = MC::C::default();
    let mut commitment_scheme = CommitmentSchemeVerifier::<MC>::new(config);
    commitment_scheme.commit(*preprocessing_root, &[], &mut channel);
    proof.claim.mix_into(&mut channel);
    commitment_scheme.commit(
        *main_root,
        &proof.claim.main_trace_log_sizes(),
        &mut channel,
    );

    let precompile_seed = channel.draw_secure_felt();
    let seeds = [vm_seed, precompile_seed];
    let mut joint_channel =
        crate::precompile::verify_joint_interaction::<MC::C>(seeds, joint_interaction)?;
    let relations = Relations::draw(&mut joint_channel);
    bind_joint_interaction(&mut channel, seeds, joint_interaction);

    let mut location_allocator = TraceLocationAllocator::default();
    let component = air::poseidon2::component::air::Component::new(
        &mut location_allocator,
        air::poseidon2::component::air::Eval {
            log_size: proof.claim.log_size,
            relations,
        },
        proof.interaction_claim.claimed_sum,
    );
    if component.trace_log_degree_bounds()[2] != proof.interaction_claim.log_sizes {
        return Err(VerificationError::InvalidStructure(
            "Poseidon2 interaction shape does not match its DSL AIR".to_string(),
        ));
    }

    proof.interaction_claim.mix_into(&mut channel);
    commitment_scheme.commit(
        *interaction_root,
        &proof.interaction_claim.log_sizes,
        &mut channel,
    );
    verify(
        &[&component],
        &mut channel,
        &mut commitment_scheme,
        proof.stark_proof,
    )
}

#[cfg(test)]
mod tests {
    use num_traits::Zero;
    use stwo::core::fields::m31::BaseField;
    use stwo::core::vcs_lifted::blake2_merkle::{Blake2sMerkleChannel, Blake2sMerkleHasher};

    use super::*;
    use crate::poseidon2_channel::{Poseidon2M31Channel, Poseidon2M31MerkleChannel};
    use crate::precompile::prove_joint_interaction;

    type TestProof = Poseidon2PrecompileProof<Blake2sMerkleHasher>;

    fn proof_fixture() -> (TestProof, SecureField, JointInteractionProof) {
        let config = PcsConfig::default();
        let log_size = 4;
        let mut table = Poseidon2Table::new();
        air::poseidon2::poseidon2_traced_state(
            &mut table,
            core::array::from_fn(|index| index as u32 + 1),
            false,
            true,
        );
        let twiddles = precompute_poseidon2_precompile_twiddles(config, log_size);
        let committed = commit_poseidon2_precompile::<Blake2sMerkleChannel>(
            table,
            log_size,
            config,
            &twiddles,
            Default::default(),
        )
        .expect("the fixture fits its fixed trace");
        let (precompile_seed, seeded) = committed.into_seeded();
        let vm_seed = SecureField::from(BaseField::from(7));
        let seeds = [vm_seed, precompile_seed];
        let (joint_interaction, mut joint_channel) =
            prove_joint_interaction::<stwo::core::channel::Blake2sChannel>(seeds);
        let relations = Relations::draw(&mut joint_channel);
        let proof = seeded
            .prove(seeds, joint_interaction, relations)
            .expect("the joint transcript contains the fixture seed");
        (proof, vm_seed, joint_interaction)
    }

    #[test]
    fn standalone_poseidon2_proof_verifies() {
        let (proof, vm_seed, joint_interaction) = proof_fixture();
        assert!(
            verify_poseidon2_precompile::<Blake2sMerkleChannel>(
                proof,
                PcsConfig::default(),
                vm_seed,
                joint_interaction,
            )
            .is_ok()
        );
    }

    #[test]
    fn standalone_poseidon2_proof_verifies_with_the_recursion_channel() {
        let config = PcsConfig::default();
        let log_size = 4;
        let mut table = Poseidon2Table::new();
        air::poseidon2::poseidon2_traced_state(&mut table, [3; 16], false, true);
        let twiddles = precompute_poseidon2_precompile_twiddles(config, log_size);
        let committed = commit_poseidon2_precompile::<Poseidon2M31MerkleChannel>(
            table,
            log_size,
            config,
            &twiddles,
            Default::default(),
        )
        .expect("the recursion-channel fixture fits its fixed trace");
        let (precompile_seed, seeded) = committed.into_seeded();
        let vm_seed = SecureField::from(BaseField::from(9));
        let seeds = [vm_seed, precompile_seed];
        let (joint_interaction, mut joint_channel) =
            prove_joint_interaction::<Poseidon2M31Channel>(seeds);
        let relations = Relations::draw(&mut joint_channel);
        let proof = seeded
            .prove(seeds, joint_interaction, relations)
            .expect("the joint transcript contains the recursion-channel seed");
        assert!(
            verify_poseidon2_precompile::<Poseidon2M31MerkleChannel>(
                proof,
                config,
                vm_seed,
                joint_interaction,
            )
            .is_ok()
        );
    }

    #[test]
    fn standalone_poseidon2_proof_carries_a_nonzero_shared_sum() {
        let (proof, _, _) = proof_fixture();
        assert!(!proof.interaction_claim.claimed_sum.is_zero());
    }

    #[test]
    fn forged_poseidon2_shared_sum_is_rejected() {
        let (mut proof, vm_seed, joint_interaction) = proof_fixture();
        proof.interaction_claim.claimed_sum += SecureField::from(BaseField::from(1));
        assert!(
            verify_poseidon2_precompile::<Blake2sMerkleChannel>(
                proof,
                PcsConfig::default(),
                vm_seed,
                joint_interaction,
            )
            .is_err()
        );
    }

    #[test]
    fn fixed_poseidon2_capacity_rejects_too_many_rows() {
        let config = PcsConfig::default();
        let log_size = 4;
        let mut table = Poseidon2Table::new();
        for index in 0..17 {
            air::poseidon2::poseidon2_traced_state(
                &mut table,
                core::array::from_fn(|lane| index + lane as u32),
                false,
                true,
            );
        }
        let twiddles = precompute_poseidon2_precompile_twiddles(config, log_size);
        let result = commit_poseidon2_precompile::<Blake2sMerkleChannel>(
            table,
            log_size,
            config,
            &twiddles,
            Default::default(),
        );
        assert!(matches!(
            result,
            Err(Poseidon2PrecompileProvingError::TraceCapacityExceeded {
                rows: 17,
                log_size: 4,
            })
        ));
    }
}
