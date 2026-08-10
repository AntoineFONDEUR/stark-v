//! Main proving function for RV32IM execution traces.

#[cfg(feature = "track-relations")]
use crate::relations::PreProcessedTrace;
#[cfg(feature = "track-relations")]
use num_traits::Zero;
use stwo::core::channel::{Channel, MerkleChannel};
use stwo::core::fields::m31::BaseField;
use stwo::core::pcs::PcsConfig;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::proof_of_work::GrindOps;
use stwo::core::vcs_lifted::blake2_merkle::{Blake2sMerkleChannel, Blake2sMerkleHasher};
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::{BackendForChannel, CpuBackend};
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo::prover::vcs_lifted::prover::MerkleProverLifted;
use stwo::prover::{CommitmentSchemeProver, CommitmentTreeProver, ComponentProver, Poly, prove};
use stwo_constraint_framework::TraceLocationAllocator;
use tracing::{Level, info, span};

use crate::components::{Components, gen_interaction_trace, gen_trace};
use crate::public_data::PublicData;
use crate::relations::{INTERACTION_POW_BITS, Relations};
use crate::{InteractionClaim, Preprocessing, Proof};

type BaseEvaluation<B> = CircleEvaluation<B, BaseField, BitReversedOrder>;
type EvaluationConverter<B> = fn(Vec<BaseEvaluation<SimdBackend>>) -> Vec<BaseEvaluation<B>>;
type CachedCommitment<B, H> = (Vec<Poly<B>>, MerkleProverLifted<B, H>);
type PreprocessingReconstructor<B, MC> =
    fn(&Preprocessing<<MC as MerkleChannel>::H>) -> CachedCommitment<B, <MC as MerkleChannel>::H>;

/// Prove execution of an RV32IM program.
///
/// Takes a `RunResult` from the runner and generates a STARK proof.
/// The `preprocessing` parameter contains cached commitment tree data
/// that is injected directly, skipping the expensive tree rebuild.
///
/// # Panics
///
/// Panics if proof generation fails or if the logup sum is non-zero
/// (indicating unbalanced lookups).
pub fn prove_rv32im(
    run_result: runner::RunResult,
    config: PcsConfig,
    preprocessing: &Preprocessing,
) -> Proof<Blake2sMerkleHasher> {
    prove_rv32im_with_channel::<Blake2sMerkleChannel>(run_result, config, preprocessing)
}

/// Prove an RV32IM execution with the scalar CPU backend.
///
/// This entry point is explicit so the backend is fixed before the Fiat-Shamir
/// transcript is initialized. [`prove_rv32im`] remains the default SIMD path.
pub fn prove_rv32im_cpu(
    run_result: runner::RunResult,
    config: PcsConfig,
    preprocessing: &Preprocessing,
) -> Proof<Blake2sMerkleHasher> {
    prove_rv32im_backend::<CpuBackend, Blake2sMerkleChannel>(
        run_result,
        config,
        preprocessing,
        crate::backend_bridge::simd_circle_evaluations_to_cpu,
        Preprocessing::to_cpu_commitment_tree,
        Components::cpu_provers,
    )
}

/// Prove an RV32IM execution with any Merkle channel — in particular the
/// Poseidon2-M31 channel whose hash the recursion verifier AIR proves.
pub fn prove_rv32im_with_channel<MC: MerkleChannel>(
    run_result: runner::RunResult,
    config: PcsConfig,
    preprocessing: &Preprocessing<MC::H>,
) -> Proof<MC::H>
where
    SimdBackend: stwo::prover::backend::BackendForChannel<MC>
        + stwo::prover::backend::ColumnOps<
            <MC::H as stwo::core::vcs_lifted::merkle_hasher::MerkleHasherLifted>::Hash,
            Column = Vec<
                <MC::H as stwo::core::vcs_lifted::merkle_hasher::MerkleHasherLifted>::Hash,
            >,
        >,
{
    prove_rv32im_backend::<SimdBackend, MC>(
        run_result,
        config,
        preprocessing,
        |evaluations| evaluations,
        Preprocessing::to_commitment_tree,
        Components::provers,
    )
}

fn prove_rv32im_backend<B, MC>(
    run_result: runner::RunResult,
    config: PcsConfig,
    preprocessing: &Preprocessing<MC::H>,
    convert_evaluations: EvaluationConverter<B>,
    reconstruct_preprocessing: PreprocessingReconstructor<B, MC>,
    component_provers: for<'a> fn(&'a Components) -> Vec<&'a dyn ComponentProver<B>>,
) -> Proof<MC::H>
where
    B: BackendForChannel<MC>,
    MC: MerkleChannel,
    SimdBackend: GrindOps<MC::C>,
{
    let public_data = PublicData::new(&run_result);

    // 1. Generate traces from execution
    let span = span!(Level::INFO, "Generate traces").entered();
    let tracer = run_result.tracer;
    info!("Tracer total_traces: {}", tracer.total_traces());
    let traces = gen_trace(tracer);
    let log_size = traces.max_log_size();
    info!("Max trace log_size: {log_size}");
    span.exit();

    // 2. Precompute twiddles (need enough for largest domain + blowup)
    let span = span!(Level::INFO, "Precompute twiddles").entered();
    let max_preprocessed_log_size = preprocessing
        .domain_log_sizes
        .iter()
        .copied()
        .max()
        .unwrap_or(0);
    let twiddles_log_size = log_size.max(max_preprocessed_log_size);
    let twiddles = B::precompute_twiddles(
        // See https://github.com/starkware-libs/stwo-cairo/blob/main/stwo_cairo_prover/crates/prover/src/prover.rs#L46-L47
        CanonicCoset::new(twiddles_log_size + 2 + config.fri_config.log_blowup_factor)
            .circle_domain()
            .half_coset,
    );
    span.exit();

    // 3. Setup protocol
    let channel = &mut <MC::C as Default>::default();
    let mut commitment_scheme = CommitmentSchemeProver::<_, MC>::new(config, &twiddles);

    // 4. Public data
    public_data.mix_into(channel);

    // 5. Load preprocessed trace — reconstruct from cached data and inject directly
    //    (skips interpolation, extension, and Merkle tree building)
    let span = span!(Level::INFO, "Load preprocessed trace").entered();
    let preprocessed_ids = preprocessing.column_ids();
    info!("Preprocessed trace ids len: {}", preprocessed_ids.len());

    let (polynomials, merkle_prover) = reconstruct_preprocessing(preprocessing);
    let root = stwo::prover::backend::Column::at(&merkle_prover.layers[0], 0);
    commitment_scheme
        .trees
        .push(stwo::core::utils::MaybeOwned::Owned(CommitmentTreeProver {
            polynomials,
            commitment: merkle_prover,
        }));
    MC::mix_root(channel, root);
    span.exit();

    // 6. Main execution trace (opcode + multiplicity columns)
    let span = span!(Level::INFO, "Main trace").entered();
    let claim: crate::components::Claim = (&traces).into();
    let columns = convert_evaluations(traces.columns_cloned());
    info!("Main trace columns committed: {}", columns.len());

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(columns);
    tree_builder.commit(channel);
    span.exit();

    // 7. Mix claim into channel
    claim.mix_into(channel);

    // 8. Proof of work before drawing lookup elements
    info!("proof of work with {} bits", INTERACTION_POW_BITS);
    let interaction_pow = SimdBackend::grind(channel, INTERACTION_POW_BITS);
    channel.mix_u64(interaction_pow);

    // 9. Draw lookup elements
    let relations = Relations::draw(channel);
    #[cfg(feature = "track-relations")]
    let public_logup_sum = public_data.logup_sum(&relations);

    // 10. Interaction trace (LogUp fractions) - only commit if non-empty
    let span = span!(Level::INFO, "Interaction trace").entered();
    let (interaction_trace, claimed_sum) = gen_interaction_trace(&traces, &relations);
    let interaction_log_sizes = interaction_trace
        .iter()
        .map(|col| col.domain.log_size())
        .collect::<Vec<_>>();
    let interaction_claim = InteractionClaim {
        claimed_sum,
        log_sizes: interaction_log_sizes,
    };
    interaction_claim.mix_into(channel);
    if !interaction_trace.is_empty() {
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(convert_evaluations(interaction_trace));
        tree_builder.commit(channel);
    }
    span.exit();

    // 11. Create components
    let span = span!(Level::INFO, "Create components").entered();
    let mut location_allocator =
        TraceLocationAllocator::new_with_preprocessed_columns(&preprocessed_ids);
    let components = Components::new(
        &claim,
        &mut location_allocator,
        relations,
        &interaction_claim.claimed_sum,
    );
    span.exit();

    #[cfg(feature = "track-relations")]
    info!(
        "Trace log degree bounds: {:?}",
        components.trace_log_degree_bounds()
    );

    // 12. Verify claimed sum is zero (all lookups balanced)
    // Only enabled with track-relations feature until all components are implemented
    #[cfg(feature = "track-relations")]
    {
        let total_sum = interaction_claim.claimed_sum.total() + public_logup_sum;
        info!("Claimed sum: {total_sum:?}");
        if !total_sum.is_zero() {
            let preprocessed_trace = PreProcessedTrace::new();
            info!(
                "Relation summary: {:?}",
                components.track_relations(&preprocessed_trace.trace, &traces)
            );
            panic!("Relation sum must be zero, got {total_sum:?}");
        }
    }

    // 13. Generate proof
    let span = span!(Level::INFO, "Prove").entered();
    let proof = prove(&component_provers(&components), channel, commitment_scheme)
        .expect("Proof generation failed");
    span.exit();

    Proof {
        claim,
        interaction_claim,
        public_data,
        stark_proof: proof,
        interaction_pow,
    }
}
