//! Main proving function for RV32IM execution traces.

use core::convert::Infallible;
use core::fmt;

#[cfg(feature = "track-relations")]
use crate::relations::PreProcessedTrace;
#[cfg(feature = "track-relations")]
use num_traits::Zero;
use stwo::core::channel::{Channel, MerkleChannel};
use stwo::core::pcs::PcsConfig;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::proof_of_work::GrindOps;
use stwo::core::vcs_lifted::blake2_merkle::{Blake2sMerkleChannel, Blake2sMerkleHasher};
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::PolyOps;
use stwo::prover::{CommitmentSchemeProver, CommitmentTreeProver, prove, prove_ex};
use stwo_constraint_framework::TraceLocationAllocator;
use tracing::{Level, info, span};

use crate::components::{
    COMPONENT_COUNT, Components, FixedTraceError, gen_interaction_trace, gen_trace,
    gen_trace_at_log_sizes,
};
use crate::public_data::PublicData;
use crate::relations::{INTERACTION_POW_BITS, Relations};
use crate::{InteractionClaim, Preprocessing, Proof};

/// Claim-phase transcript policy used before STWO proves the committed traces.
///
/// STWO owns the composition, OODS, PCS, and FRI suffix. The VM prover owns the
/// preceding public-data and LogUp claim phase, so recursion profiles can bind
/// that phase without duplicating trace generation or the STWO prover.
pub trait VmClaimTranscript<C: Channel> {
    type Error;

    fn bind_before_commitments(
        &self,
        channel: &mut C,
        public_data: &PublicData,
    ) -> Result<(), Self::Error>;

    fn bind_after_main_commitment(
        &self,
        channel: &mut C,
        public_data: &PublicData,
        claim: &crate::components::Claim,
    ) -> Result<(), Self::Error>;

    fn bind_interaction_claim(
        &self,
        channel: &mut C,
        interaction_claim: &InteractionClaim,
    ) -> Result<(), Self::Error>;
}

/// Ordinary stark-v transcript policy used by the public VM prover API.
#[derive(Clone, Copy, Debug, Default)]
pub struct NativeVmClaimTranscript;

impl<C: Channel> VmClaimTranscript<C> for NativeVmClaimTranscript {
    type Error = Infallible;

    fn bind_before_commitments(
        &self,
        channel: &mut C,
        public_data: &PublicData,
    ) -> Result<(), Self::Error> {
        public_data.mix_into(channel);
        Ok(())
    }

    fn bind_after_main_commitment(
        &self,
        channel: &mut C,
        _public_data: &PublicData,
        claim: &crate::components::Claim,
    ) -> Result<(), Self::Error> {
        claim.mix_into(channel);
        Ok(())
    }

    fn bind_interaction_claim(
        &self,
        channel: &mut C,
        interaction_claim: &InteractionClaim,
    ) -> Result<(), Self::Error> {
        interaction_claim.mix_into(channel);
        Ok(())
    }
}

/// Failure while preparing a fixed VM proof under a caller-owned transcript.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VmTranscriptProvingError<E> {
    FixedTrace(FixedTraceError),
    Transcript(E),
}

impl<E: fmt::Display> fmt::Display for VmTranscriptProvingError<E> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::FixedTrace(error) => write!(formatter, "fixed trace generation failed: {error}"),
            Self::Transcript(error) => write!(formatter, "VM transcript binding failed: {error}"),
        }
    }
}

impl<E: fmt::Debug + fmt::Display> std::error::Error for VmTranscriptProvingError<E> {}

/// Proof and fully advanced channel returned by a caller-owned VM transcript.
pub type VmTranscriptProofResult<H, C, E> = Result<(Proof<H>, C), VmTranscriptProvingError<E>>;

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
    let (proof, _) = prove_rv32im_with_channel_inner::<MC, _>(
        run_result,
        config,
        preprocessing,
        None,
        MC::C::default(),
        &NativeVmClaimTranscript,
    )
    .expect("dynamic trace generation has no fixed capacity or transcript failure");
    proof
}

/// Proves one execution against verifier-owned component log sizes.
///
/// The fixed layout is part of a recursive protocol identity. A segment that
/// exceeds one component capacity is rejected instead of selecting a larger
/// proof shape.
pub fn prove_rv32im_with_channel_at_log_sizes<MC: MerkleChannel>(
    run_result: runner::RunResult,
    config: PcsConfig,
    preprocessing: &Preprocessing<MC::H>,
    component_log_sizes: [u32; COMPONENT_COUNT],
) -> Result<Proof<MC::H>, FixedTraceError>
where
    SimdBackend: stwo::prover::backend::BackendForChannel<MC>
        + stwo::prover::backend::ColumnOps<
            <MC::H as stwo::core::vcs_lifted::merkle_hasher::MerkleHasherLifted>::Hash,
            Column = Vec<
                <MC::H as stwo::core::vcs_lifted::merkle_hasher::MerkleHasherLifted>::Hash,
            >,
        >,
{
    prove_rv32im_with_channel_inner::<MC, _>(
        run_result,
        config,
        preprocessing,
        Some(component_log_sizes),
        MC::C::default(),
        &NativeVmClaimTranscript,
    )
    .map(|(proof, _)| proof)
    .map_err(|error| match error {
        VmTranscriptProvingError::FixedTrace(error) => error,
        VmTranscriptProvingError::Transcript(never) => match never {},
    })
}

/// Proves a fixed-layout VM trace with a caller-owned claim transcript.
///
/// The returned channel is advanced past the complete STWO proof so the
/// caller can require that its trusted transcript plan was consumed exactly.
pub fn prove_rv32im_with_channel_at_log_sizes_and_transcript<MC, T>(
    run_result: runner::RunResult,
    config: PcsConfig,
    preprocessing: &Preprocessing<MC::H>,
    component_log_sizes: [u32; COMPONENT_COUNT],
    channel: MC::C,
    transcript: &T,
) -> VmTranscriptProofResult<MC::H, MC::C, T::Error>
where
    MC: MerkleChannel,
    T: VmClaimTranscript<MC::C>,
    SimdBackend: stwo::prover::backend::BackendForChannel<MC>
        + stwo::prover::backend::ColumnOps<
            <MC::H as stwo::core::vcs_lifted::merkle_hasher::MerkleHasherLifted>::Hash,
            Column = Vec<
                <MC::H as stwo::core::vcs_lifted::merkle_hasher::MerkleHasherLifted>::Hash,
            >,
        >,
{
    prove_rv32im_with_channel_inner::<MC, T>(
        run_result,
        config,
        preprocessing,
        Some(component_log_sizes),
        channel,
        transcript,
    )
}

fn prove_rv32im_with_channel_inner<MC, T>(
    run_result: runner::RunResult,
    config: PcsConfig,
    preprocessing: &Preprocessing<MC::H>,
    component_log_sizes: Option<[u32; COMPONENT_COUNT]>,
    mut channel: MC::C,
    transcript: &T,
) -> VmTranscriptProofResult<MC::H, MC::C, T::Error>
where
    MC: MerkleChannel,
    T: VmClaimTranscript<MC::C>,
    SimdBackend: stwo::prover::backend::BackendForChannel<MC>
        + stwo::prover::backend::ColumnOps<
            <MC::H as stwo::core::vcs_lifted::merkle_hasher::MerkleHasherLifted>::Hash,
            Column = Vec<
                <MC::H as stwo::core::vcs_lifted::merkle_hasher::MerkleHasherLifted>::Hash,
            >,
        >,
{
    let public_data = PublicData::new(&run_result);
    let retain_query_expansion = component_log_sizes.is_some();

    // 1. Generate traces from execution
    let span = span!(Level::INFO, "Generate traces").entered();
    let tracer = run_result.tracer;
    info!("Tracer total_traces: {}", tracer.total_traces());
    let traces = match component_log_sizes {
        Some(log_sizes) => gen_trace_at_log_sizes(tracer, log_sizes)
            .map_err(VmTranscriptProvingError::FixedTrace)?,
        None => gen_trace(tracer),
    };
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
    let twiddles = SimdBackend::precompute_twiddles(
        // See https://github.com/starkware-libs/stwo-cairo/blob/main/stwo_cairo_prover/crates/prover/src/prover.rs#L46-L47
        CanonicCoset::new(twiddles_log_size + 2 + config.fri_config.log_blowup_factor)
            .circle_domain()
            .half_coset,
    );
    span.exit();

    // 3. Setup protocol
    let channel = &mut channel;
    let mut commitment_scheme = CommitmentSchemeProver::<_, MC>::new(config, &twiddles);

    // 4. Public data
    transcript
        .bind_before_commitments(channel, &public_data)
        .map_err(VmTranscriptProvingError::Transcript)?;

    // 5. Load preprocessed trace — reconstruct from cached data and inject directly
    //    (skips interpolation, extension, and Merkle tree building)
    let span = span!(Level::INFO, "Load preprocessed trace").entered();
    let preprocessed_ids = preprocessing.column_ids();
    info!("Preprocessed trace ids len: {}", preprocessed_ids.len());

    let (polynomials, merkle_prover) = preprocessing.to_commitment_tree();
    let root = merkle_prover.layers[0][0];
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
    let columns = traces.columns_cloned();
    info!("Main trace columns committed: {}", columns.len());

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(columns);
    tree_builder.commit(channel);
    span.exit();

    // 7. Mix claim into channel
    transcript
        .bind_after_main_commitment(channel, &public_data, &claim)
        .map_err(VmTranscriptProvingError::Transcript)?;

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
    transcript
        .bind_interaction_claim(channel, &interaction_claim)
        .map_err(VmTranscriptProvingError::Transcript)?;
    if !interaction_trace.is_empty() {
        let mut tree_builder = commitment_scheme.tree_builder();
        tree_builder.extend_evals(interaction_trace);
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
    let (stark_proof, stark_aux) = if retain_query_expansion {
        // Recursion needs every raw opening independently, while ordinary VM
        // proofs keep STWO's smaller deduplicated representation.
        let extended = prove_ex(&components.provers(), channel, commitment_scheme, false)
            .expect("Proof generation failed");
        (extended.proof, Some(extended.aux))
    } else {
        let proof = prove(&components.provers(), channel, commitment_scheme)
            .expect("Proof generation failed");
        (proof, None)
    };
    span.exit();

    let final_channel = (*channel).clone();
    Ok((
        Proof {
            claim,
            interaction_claim,
            public_data,
            stark_proof,
            stark_aux,
            interaction_pow,
        },
        final_channel,
    ))
}
