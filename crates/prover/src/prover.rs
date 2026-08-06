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
use crate::poseidon2_precompile::{
    Poseidon2PrecompileProvingError, commit_poseidon2_precompile, poseidon2_precompile_log_size,
    precompute_poseidon2_precompile_twiddles,
};
use crate::precompile::prove_joint_interaction_in_channel;
use crate::public_data::PublicData;
use crate::relations::Relations;
use crate::{InteractionClaim, Preprocessing, Proof, SegmentProof};

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
#[derive(Clone, Debug)]
pub enum VmTranscriptProvingError<E> {
    FixedTrace(FixedTraceError),
    Poseidon2(Poseidon2PrecompileProvingError),
    Transcript(E),
}

impl<E: fmt::Display> fmt::Display for VmTranscriptProvingError<E> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::FixedTrace(error) => write!(formatter, "fixed trace generation failed: {error}"),
            Self::Poseidon2(error) => write!(formatter, "Poseidon2 proof failed: {error}"),
            Self::Transcript(error) => write!(formatter, "VM transcript binding failed: {error}"),
        }
    }
}

impl<E: fmt::Debug + fmt::Display> std::error::Error for VmTranscriptProvingError<E> {}

/// Fully advanced constituent channels returned by a caller-owned transcript.
pub struct SegmentProofChannels<C> {
    pub vm: C,
    pub poseidon2: C,
}

/// Segment proof and channels returned by a caller-owned VM transcript.
pub type VmTranscriptProofResult<H, C, E> =
    Result<(SegmentProof<H>, SegmentProofChannels<C>), VmTranscriptProvingError<E>>;

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
) -> SegmentProof<Blake2sMerkleHasher> {
    prove_rv32im_with_channel::<Blake2sMerkleChannel>(run_result, config, preprocessing)
}

/// Prove an RV32IM execution with any Merkle channel — in particular the
/// Poseidon2-M31 channel whose hash the recursion verifier AIR proves.
pub fn prove_rv32im_with_channel<MC: MerkleChannel>(
    run_result: runner::RunResult,
    config: PcsConfig,
    preprocessing: &Preprocessing<MC::H>,
) -> SegmentProof<MC::H>
where
    SimdBackend: stwo::prover::backend::BackendForChannel<MC>
        + GrindOps<MC::C>
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
        None,
        SegmentProofChannels {
            vm: MC::C::default(),
            poseidon2: MC::C::default(),
        },
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
    poseidon2_log_size: u32,
) -> Result<SegmentProof<MC::H>, VmTranscriptProvingError<Infallible>>
where
    SimdBackend: stwo::prover::backend::BackendForChannel<MC>
        + GrindOps<MC::C>
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
        Some(poseidon2_log_size),
        SegmentProofChannels {
            vm: MC::C::default(),
            poseidon2: MC::C::default(),
        },
        &NativeVmClaimTranscript,
    )
    .map(|(proof, _)| proof)
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
    poseidon2_log_size: u32,
    channels: SegmentProofChannels<MC::C>,
    transcript: &T,
) -> VmTranscriptProofResult<MC::H, MC::C, T::Error>
where
    MC: MerkleChannel,
    T: VmClaimTranscript<MC::C>,
    SimdBackend: stwo::prover::backend::BackendForChannel<MC>
        + GrindOps<MC::C>
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
        Some(poseidon2_log_size),
        channels,
        transcript,
    )
}

fn prove_rv32im_with_channel_inner<MC, T>(
    run_result: runner::RunResult,
    config: PcsConfig,
    preprocessing: &Preprocessing<MC::H>,
    component_log_sizes: Option<[u32; COMPONENT_COUNT]>,
    poseidon2_log_size: Option<u32>,
    channels: SegmentProofChannels<MC::C>,
    transcript: &T,
) -> VmTranscriptProofResult<MC::H, MC::C, T::Error>
where
    MC: MerkleChannel,
    T: VmClaimTranscript<MC::C>,
    SimdBackend: stwo::prover::backend::BackendForChannel<MC>
        + GrindOps<MC::C>
        + stwo::prover::backend::ColumnOps<
            <MC::H as stwo::core::vcs_lifted::merkle_hasher::MerkleHasherLifted>::Hash,
            Column = Vec<
                <MC::H as stwo::core::vcs_lifted::merkle_hasher::MerkleHasherLifted>::Hash,
            >,
        >,
{
    let SegmentProofChannels {
        vm: mut channel,
        poseidon2: poseidon2_channel,
    } = channels;
    let public_data = PublicData::new(&run_result);
    let retain_query_expansion = component_log_sizes.is_some();

    // 1. Generate traces from execution
    let span = span!(Level::INFO, "Generate traces").entered();
    let mut tracer = run_result.tracer;
    info!("Tracer total_traces: {}", tracer.total_traces());
    let poseidon2_table = core::mem::take(&mut tracer.poseidon2);
    let poseidon2_log_size =
        poseidon2_log_size.unwrap_or_else(|| poseidon2_precompile_log_size(poseidon2_table.len()));
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
    let poseidon2_twiddles = precompute_poseidon2_precompile_twiddles(config, poseidon2_log_size);
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

    // 8. Commit the detached Poseidon2 trace before either interaction seed is drawn.
    let poseidon2_committed = commit_poseidon2_precompile::<MC>(
        poseidon2_table,
        poseidon2_log_size,
        config,
        &poseidon2_twiddles,
        poseidon2_channel,
        retain_query_expansion,
    )
    .map_err(VmTranscriptProvingError::Poseidon2)?;

    // 9. Grind once over both ordered post-commitment seeds, then draw every relation.
    let vm_seed = channel.draw_secure_felt();
    let (poseidon2_seed, poseidon2_seeded) = poseidon2_committed.into_seeded();
    let seeds = [vm_seed, poseidon2_seed];
    let joint_interaction = prove_joint_interaction_in_channel(channel, seeds, true);
    let relations = Relations::draw(channel);

    // 10. Interaction trace (LogUp fractions) - only commit if non-empty
    let span = span!(Level::INFO, "Interaction trace").entered();
    let (interaction_trace, claimed_sum) = gen_interaction_trace(&traces, &relations);
    let interaction_log_sizes = interaction_trace
        .iter()
        .map(|col| col.domain.log_size())
        .collect::<Vec<_>>();
    let interaction_claim = InteractionClaim {
        shared_relation_sum: claimed_sum.total() + public_data.logup_sum(&relations),
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
        relations.clone(),
        &interaction_claim.claimed_sum,
    );
    span.exit();

    #[cfg(feature = "track-relations")]
    info!(
        "Trace log degree bounds: {:?}",
        components.trace_log_degree_bounds()
    );

    // 12. Report the detached deficit without requiring the VM constituent to close alone.
    #[cfg(feature = "track-relations")]
    {
        let preprocessed_trace = PreProcessedTrace::new();
        info!(
            "Shared relation deficit: {:?}",
            interaction_claim.shared_relation_sum
        );
        info!(
            "Relation summary: {:?}",
            components.track_relations(&preprocessed_trace.trace, &traces)
        );
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

    let final_vm_channel = (*channel).clone();
    let (poseidon2, final_poseidon2_channel) = poseidon2_seeded
        .prove(seeds, joint_interaction, relations)
        .map_err(VmTranscriptProvingError::Poseidon2)?;
    Ok((
        SegmentProof {
            vm: Proof {
                claim,
                interaction_claim,
                public_data,
                stark_proof,
                stark_aux,
            },
            poseidon2,
            joint_interaction,
        },
        SegmentProofChannels {
            vm: final_vm_channel,
            poseidon2: final_poseidon2_channel,
        },
    ))
}
