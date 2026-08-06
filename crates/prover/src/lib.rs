#![allow(non_camel_case_types)]
#![feature(
    allocator_api,
    portable_simd,
    iter_array_chunks,
    macro_metavar_expr_concat
)]

/// Print all enabled features for debugging/benchmarking.
pub fn print_enabled_features() {
    use tracing::info;

    let features: Vec<&str> = vec![
        #[cfg(feature = "parallel")]
        "parallel",
        #[cfg(not(feature = "parallel"))]
        "non-parallel",
    ];

    info!("Features: {}", features.join(", "));
}

pub mod components;
pub mod errors;
pub mod poseidon2_channel;
pub mod poseidon2_precompile;
pub mod precompile;
pub mod preprocessed;
pub mod prover;
pub mod public_data;
pub mod relations;
pub mod verifier;

pub use errors::VerificationError;
pub use preprocessed::{Preprocessing, preprocess, preprocess_with_channel};
pub use prover::{
    NativeVmClaimTranscript, SegmentProofChannels, VmClaimTranscript, VmTranscriptProofResult,
    VmTranscriptProvingError, prove_rv32im, prove_rv32im_with_channel,
    prove_rv32im_with_channel_at_log_sizes, prove_rv32im_with_channel_at_log_sizes_and_transcript,
};
pub use public_data::PublicData;
pub use verifier::{verify_rv32im, verify_rv32im_with_channel};

// Re-export stwo types needed by external consumers
pub use stwo::core::fri::FriConfig;
pub use stwo::core::pcs::PcsConfig;

/// E2E test infrastructure (building and running guest binaries).
#[doc(hidden)]
pub mod e2e;

use serde::{Deserialize, Serialize};
use stwo::core::channel::Channel;
use stwo::core::pcs::quotients::CommitmentSchemeProofAux;
use stwo::core::proof::StarkProof;
use stwo::core::vcs_lifted::MerkleHasherLifted;

use crate::components::ClaimedSum;

/// Interaction claim for LogUp (claimed sums + interaction trace log sizes).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct InteractionClaim {
    pub claimed_sum: ClaimedSum,
    /// Aggregate VM deficit discharged by the standalone Poseidon2 proof.
    pub shared_relation_sum: stwo::core::fields::qm31::SecureField,
    pub log_sizes: Vec<u32>,
}

impl InteractionClaim {
    pub fn mix_into(&self, channel: &mut impl Channel) {
        self.claimed_sum.mix_into(channel);
        channel.mix_felts(&[self.shared_relation_sum]);
        channel.mix_u64(self.log_sizes.len() as u64);
        for log_size in &self.log_sizes {
            channel.mix_u64(*log_size as u64);
        }
    }
}

/// RV32IM constituent proof whose shared deficit requires a hash proof.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Proof<H: MerkleHasherLifted> {
    pub claim: components::Claim,
    pub interaction_claim: InteractionClaim,
    pub public_data: PublicData,
    pub stark_proof: StarkProof<H>,
    /// Expansion data used to materialize independent raw-query openings.
    ///
    /// The fixed-layout prover retains this material until recursion adapts the
    /// proof. Ordinary proving and every serialized VM proof omit it.
    #[serde(skip, default)]
    pub stark_aux: Option<CommitmentSchemeProofAux<H>>,
}

/// Complete proof artifact for one VM segment and its Poseidon2 work.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SegmentProof<H: MerkleHasherLifted> {
    pub vm: Proof<H>,
    pub poseidon2: poseidon2_precompile::Poseidon2PrecompileProof<H>,
    pub joint_interaction: precompile::JointInteractionProof,
}
