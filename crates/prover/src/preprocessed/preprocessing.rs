//! Cached preprocessed commitment data for RV32IM proofs.

use serde::{Deserialize, Serialize};
use stwo::core::pcs::PcsConfig;
use stwo::core::vcs_lifted::blake2_merkle::{Blake2sMerkleChannel, Blake2sMerkleHasher};
use stwo::core::vcs_lifted::merkle_hasher::MerkleHasherLifted;

use crate::preprocessed::PreProcessedTrace;

/// Serializable preprocessed data for RV32IM proving.
///
/// Caches the expensive preprocessing computation including:
/// - Extended polynomial evaluations after interpolation and blowup
/// - Merkle tree layers for the commitment structure
/// - Column IDs for trace allocation
///
/// The data can be serialized to disk and reused across multiple proofs,
/// avoiding the need to rebuild the Merkle tree each time.
#[derive(Clone, Serialize, Deserialize)]
#[serde(bound(
    serialize = "H::Hash: Serialize",
    deserialize = "H::Hash: serde::de::DeserializeOwned"
))]
pub struct Preprocessing<H: MerkleHasherLifted = Blake2sMerkleHasher> {
    /// Column IDs for trace allocation.
    pub ids: Vec<String>,
    /// Original column log sizes before extension for verifier commitments.
    pub log_sizes: Vec<u32>,
    /// Domain log sizes for each extended evaluation column after blowup.
    pub domain_log_sizes: Vec<u32>,
    /// Extended polynomial evaluations after blowup as raw u32 data per column.
    ///
    /// Each inner Vec contains the flattened PackedBaseField data as u32 values.
    pub extended_evals: Vec<Vec<u32>>,
    /// Merkle tree layers ordered from the root layer to the largest layer.
    pub merkle_layers: Vec<Vec<H::Hash>>,
}

impl<H: MerkleHasherLifted> Preprocessing<H> {
    /// Get the preprocessed column IDs as PreProcessedColumnId objects.
    pub fn column_ids(
        &self,
    ) -> Vec<stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId> {
        self.ids
            .iter()
            .map(
                |id| stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId {
                    id: id.clone(),
                },
            )
            .collect()
    }

    /// Reconstruct the CommitmentTreeProver from the cached data.
    ///
    /// Converts the serialized data back into the stwo types needed for proving.
    /// Uses 64-byte aligned allocation for SIMD compatibility.
    pub fn to_commitment_tree(
        &self,
    ) -> (
        Vec<stwo::prover::Poly<stwo::prover::backend::simd::SimdBackend>>,
        stwo::prover::vcs_lifted::prover::MerkleProverLifted<
            stwo::prover::backend::simd::SimdBackend,
            H,
        >,
    )
    where
        stwo::prover::backend::simd::SimdBackend: stwo::prover::vcs_lifted::ops::MerkleOpsLifted<H>
            + stwo::prover::backend::ColumnOps<H::Hash, Column = Vec<H::Hash>>,
    {
        use stwo::core::poly::circle::CanonicCoset;
        use stwo::prover::Poly;
        use stwo::prover::backend::simd::column::BaseColumn;
        use stwo::prover::poly::circle::CircleEvaluation;
        use stwo::prover::vcs_lifted::prover::MerkleProverLifted;

        let polynomials: Vec<Poly<stwo::prover::backend::simd::SimdBackend>> = self
            .extended_evals
            .iter()
            .zip(self.domain_log_sizes.iter())
            .map(|(data, &domain_log_size)| {
                // SIMD columns require the cached words to live in aligned memory.
                let mut aligned = simd::AlignedVec::with_capacity(data.len());
                aligned.extend_from_slice(data);
                let values: BaseColumn = aligned.into();

                let domain = CanonicCoset::new(domain_log_size).circle_domain();
                let evals = CircleEvaluation::new(domain, values);

                Poly::new(None, evals)
            })
            .collect();

        let merkle_prover = MerkleProverLifted {
            layers: self.merkle_layers.clone(),
        };

        (polynomials, merkle_prover)
    }

    /// Reconstruct the cached commitment tree for the scalar CPU backend.
    ///
    /// Raw M31 words are copied without field reduction because `0` and `P`
    /// are distinct commitment inputs even though they denote the same field
    /// element.
    pub(crate) fn to_cpu_commitment_tree(
        &self,
    ) -> (
        Vec<stwo::prover::Poly<stwo::prover::backend::CpuBackend>>,
        stwo::prover::vcs_lifted::prover::MerkleProverLifted<stwo::prover::backend::CpuBackend, H>,
    ) {
        use stwo::core::poly::circle::CanonicCoset;
        use stwo::prover::Poly;
        use stwo::prover::backend::CpuBackend;
        use stwo::prover::poly::circle::CircleEvaluation;
        use stwo::prover::vcs_lifted::prover::MerkleProverLifted;

        let polynomials: Vec<Poly<CpuBackend>> = self
            .extended_evals
            .iter()
            .zip(self.domain_log_sizes.iter())
            .map(|(data, &domain_log_size)| {
                let values = data
                    .iter()
                    .copied()
                    .map(crate::backend_bridge::checked_m31_from_raw)
                    .collect();
                let domain = CanonicCoset::new(domain_log_size).circle_domain();
                let evals = CircleEvaluation::new(domain, values);

                Poly::new(None, evals)
            })
            .collect();

        let merkle_prover = MerkleProverLifted {
            layers: self.merkle_layers.clone(),
        };

        (polynomials, merkle_prover)
    }
}

/// Generate preprocessed data for RV32IM proving.
///
/// Performs the full preprocessing pipeline once:
/// 1. Generates constant lookup table columns
/// 2. Computes twiddles for polynomial extension
/// 3. Builds the Merkle tree commitment
/// 4. Extracts committed data including extended evaluations and Merkle layers
///
/// The result can be serialized and reused across multiple prove/verify calls.
pub fn preprocess(config: PcsConfig) -> Preprocessing {
    preprocess_with_channel::<Blake2sMerkleChannel>(config)
}

/// Generate preprocessed data committed with any Merkle channel.
pub fn preprocess_with_channel<MC: stwo::core::channel::MerkleChannel>(
    config: PcsConfig,
) -> Preprocessing<MC::H>
where
    stwo::prover::backend::simd::SimdBackend: stwo::prover::backend::BackendForChannel<MC>
        + stwo::prover::backend::ColumnOps<
            <MC::H as MerkleHasherLifted>::Hash,
            Column = Vec<<MC::H as MerkleHasherLifted>::Hash>,
        >,
{
    use stwo::core::poly::circle::CanonicCoset;
    use stwo::prover::CommitmentSchemeProver;
    use stwo::prover::backend::simd::SimdBackend;
    use stwo::prover::poly::circle::PolyOps;
    use tracing::{Level, span};

    let span = span!(Level::INFO, "Preprocess").entered();

    let span_1 = span!(Level::INFO, "Generate trace").entered();
    let preprocessed_trace = PreProcessedTrace::new();
    span_1.exit();

    let span_2 = span!(Level::INFO, "Precompute twiddles").entered();
    let max_log_size = preprocessed_trace
        .trace
        .iter()
        .map(|c| c.domain.log_size())
        .max()
        .unwrap_or(0);
    let twiddles = SimdBackend::precompute_twiddles(
        // The extension domain includes interpolation, the FRI blowup, and the circle coset shift.
        CanonicCoset::new(max_log_size + 2 + config.fri_config.log_blowup_factor)
            .circle_domain()
            .half_coset,
    );
    span_2.exit();

    let log_sizes: Vec<u32> = preprocessed_trace
        .trace
        .iter()
        .map(|c| c.domain.log_size())
        .collect();

    let span_3 = span!(Level::INFO, "Commit").entered();
    let channel = &mut <MC::C as Default>::default();
    let mut commitment_scheme = CommitmentSchemeProver::<_, MC>::new(config, &twiddles);

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(preprocessed_trace.trace);
    tree_builder.commit(channel);
    span_3.exit();

    let span_4 = span!(Level::INFO, "Extract data").entered();
    let tree = &commitment_scheme.trees[0];

    let ids: Vec<String> = preprocessed_trace
        .ids
        .iter()
        .map(|id| id.id.clone())
        .collect();

    let domain_log_sizes: Vec<u32> = tree
        .polynomials
        .iter()
        .map(|poly| poly.evals.domain.log_size())
        .collect();

    let extended_evals: Vec<Vec<u32>> = tree
        .polynomials
        .iter()
        .map(|poly| {
            let packed_slice: &[u32] = bytemuck::cast_slice(&poly.evals.values.data);
            packed_slice.to_vec()
        })
        .collect();

    let merkle_layers = tree.commitment.layers.clone();

    span_4.exit();
    span.exit();

    Preprocessing {
        ids,
        log_sizes,
        domain_log_sizes,
        extended_evals,
        merkle_layers,
    }
}
