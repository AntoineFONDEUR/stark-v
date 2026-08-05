//! Native prover and verifier for the universal recursion AIR.
//!
//! The trusted preprocessing owns the generated 36-component roster and its
//! fixed geometry. Proving commits the relation-independent main trace first,
//! derives every LogUp challenge from the manifest-bound transcript, then
//! materializes the interaction trace under those challenges.

use core::fmt;

use air::digest::ProtocolId;
use num_traits::Zero;
use prover::poseidon2_channel::{Poseidon2M31MerkleChannel, Poseidon2M31MerkleHasher};
use stwo::core::air::Components as CoreComponents;
use stwo::core::channel::Channel;
use stwo::core::fields::qm31::SecureField;
use stwo::core::pcs::{CommitmentSchemeVerifier, TreeVec};
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::proof::StarkProof;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::PolyOps;
use stwo::prover::{CommitmentSchemeProver, CommitmentTreeProver};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;

use crate::profile::{FrozenProtocolProfile, recursion_preprocessed_column_ids};
use crate::profiled_channel::{ProfiledPoseidon2M31Channel, ProfiledPoseidon2M31MerkleChannel};
use crate::recursion_air_program::{
    UNIVERSAL_COMPONENT_COUNT, UniversalComponentLogSizes, universal_components,
};
use crate::segment_leaf::VmSegmentLeafWire;
use crate::statement::SpanStatement;
use crate::universal_relations::UniversalRelations;
use crate::universal_witness::{
    UniversalMainWitness, UniversalPreprocessing, UniversalTrace, UniversalWitnessError,
    finish_prepared_witness, prepare_empty_leaf, prepare_segment_leaf,
    universal_public_relation_sum,
};
use crate::wire::ProofKind;

/// Verifier-owned universal preprocessing and its cached Poseidon commitment.
pub struct RecursionPreprocessing {
    protocol: ProtocolId,
    component_log_sizes: UniversalComponentLogSizes,
    column_log_sizes: TreeVec<Vec<u32>>,
    ids: Vec<PreProcessedColumnId>,
    cached: prover::Preprocessing<Poseidon2M31MerkleHasher>,
    universal: UniversalPreprocessing,
}

/// Public component geometry selecting one universal predicate branch.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecursionComponentClaim {
    pub proof_kind: ProofKind,
    pub log_sizes: UniversalComponentLogSizes,
}

/// Public LogUp claims and interaction-tree geometry.
#[derive(Clone, Debug)]
pub struct RecursionInteractionClaim {
    pub claimed_sums: [SecureField; UNIVERSAL_COMPONENT_COUNT],
    pub public_relation_sum: SecureField,
    pub log_sizes: Vec<u32>,
}

/// One manifest-shaped native proof of a universal recursion statement.
#[derive(Clone, Debug)]
pub struct RecursionProof {
    pub protocol: ProtocolId,
    pub statement: SpanStatement,
    pub component_claim: RecursionComponentClaim,
    pub interaction_claim: RecursionInteractionClaim,
    pub stark_proof: StarkProof<Poseidon2M31MerkleHasher>,
    pub interaction_pow: u64,
}

/// Preprocesses the fixed universal AIR under the frozen protocol profile.
pub fn preprocess_recursion(
    profile: &FrozenProtocolProfile,
) -> Result<RecursionPreprocessing, RecursionProofError> {
    let universal = UniversalPreprocessing::new(profile).map_err(RecursionProofError::Witness)?;
    let column_log_sizes = profile.recursion_program().column_log_sizes().clone();
    let component_log_sizes = *profile.recursion_program().component_log_sizes();
    let ids = recursion_preprocessed_column_ids();
    let components = universal
        .preprocessed_components(&column_log_sizes[0])
        .map_err(RecursionProofError::Witness)?;
    let trace = components.into_iter().flatten().collect::<UniversalTrace>();
    if trace.len() != ids.len() {
        return Err(RecursionProofError::Geometry(
            "preprocessing column count differs from the frozen registry",
        ));
    }
    let cached = prover::preprocessed::preprocess_trace_with_channel::<Poseidon2M31MerkleChannel>(
        profile.manifest().recursion_pcs().config(),
        ids.clone(),
        trace,
    );
    Ok(RecursionPreprocessing {
        protocol: profile.manifest().protocol_id(),
        component_log_sizes,
        column_log_sizes,
        ids,
        cached,
        universal,
    })
}

/// Proves one authenticated VM segment through the universal recursion AIR.
pub fn prove_segment_leaf(
    profile: &FrozenProtocolProfile,
    preprocessing: &RecursionPreprocessing,
    leaf: &VmSegmentLeafWire,
) -> Result<RecursionProof, RecursionProofError> {
    validate_preprocessing(profile, preprocessing)?;
    let main = prepare_segment_leaf(profile, leaf, &preprocessing.universal)
        .map_err(RecursionProofError::Witness)?;
    prove_prepared(profile, preprocessing, *leaf.statement(), main)
}

/// Proves one canonical padding statement through the universal recursion AIR.
pub fn prove_empty_leaf(
    profile: &FrozenProtocolProfile,
    preprocessing: &RecursionPreprocessing,
    statement: &SpanStatement,
) -> Result<RecursionProof, RecursionProofError> {
    validate_preprocessing(profile, preprocessing)?;
    let main = prepare_empty_leaf(profile, statement, &preprocessing.universal)
        .map_err(RecursionProofError::Witness)?;
    prove_prepared(profile, preprocessing, *statement, main)
}

fn prove_prepared(
    profile: &FrozenProtocolProfile,
    preprocessing: &RecursionPreprocessing,
    statement: SpanStatement,
    main: UniversalMainWitness,
) -> Result<RecursionProof, RecursionProofError> {
    let config = profile.manifest().recursion_pcs().config();
    let interaction_pow_bits = profile.manifest().recursion_pcs().interaction_pow_bits();
    let twiddles = universal_twiddles(&preprocessing.column_log_sizes, config);
    let mut channel = ProfiledPoseidon2M31Channel::for_recursion_proof(
        profile.recursion_plan(),
        preprocessing.protocol,
        &statement,
    )
    .map_err(|error| RecursionProofError::Transcript(error.to_string()))?;
    let mut commitment_scheme =
        CommitmentSchemeProver::<_, ProfiledPoseidon2M31MerkleChannel>::new(config, &twiddles);
    commit_preprocessing(&mut commitment_scheme, &preprocessing.cached, &mut channel);
    // The committed copy keeps the main polynomials alive while interaction
    // generation still reads the original evaluations under the drawn relations.
    commit_trace(
        &mut commitment_scheme,
        main.original_trace_cloned(),
        &mut channel,
    );
    channel
        .absorb_recursion_public_claim()
        .map_err(|error| RecursionProofError::Transcript(error.to_string()))?;
    let interaction_pow = <SimdBackend as stwo::core::proof_of_work::GrindOps<_>>::grind(
        &channel,
        interaction_pow_bits,
    );
    channel.mix_u64(interaction_pow);
    let relations = UniversalRelations::draw(&mut channel);
    let witness = finish_prepared_witness(&preprocessing.universal, main, &relations)
        .map_err(RecursionProofError::Witness)?;
    if !witness.global_relation_sum().is_zero() {
        return Err(RecursionProofError::GlobalRelationSum);
    }
    let proof_kind = witness.proof_kind();
    let claimed_sums = *witness.claimed_sums();
    let public_relation_sum = witness.public_relation_sum();
    let mut trees = witness.into_traces().0.into_iter();
    let preprocessed_trace = trees
        .next()
        .ok_or(RecursionProofError::Geometry("missing preprocessing tree"))?;
    let original_trace = trees
        .next()
        .ok_or(RecursionProofError::Geometry("missing main tree"))?;
    let interaction_trace = trees
        .next()
        .ok_or(RecursionProofError::Geometry("missing interaction tree"))?;
    if trees.next().is_some() {
        return Err(RecursionProofError::Geometry(
            "universal witness has more than three trace trees",
        ));
    }
    drop(preprocessed_trace);
    drop(original_trace);
    let interaction_log_sizes = interaction_trace
        .iter()
        .map(|column| column.domain.log_size())
        .collect::<Vec<_>>();

    channel
        .absorb_claimed_sums(&claimed_sums)
        .map_err(|error| RecursionProofError::Transcript(error.to_string()))?;
    commit_trace(&mut commitment_scheme, interaction_trace, &mut channel);

    let components = universal_components(
        &preprocessing.ids,
        &relations,
        proof_kind,
        &preprocessing.component_log_sizes,
        &claimed_sums,
    );
    let stark_proof = stwo::prover::prove(&components.provers(), &mut channel, commitment_scheme)
        .map_err(|error| RecursionProofError::Stwo(error.to_string()))?;
    channel
        .finish()
        .map_err(|error| RecursionProofError::Transcript(error.to_string()))?;

    Ok(RecursionProof {
        protocol: preprocessing.protocol,
        statement,
        component_claim: RecursionComponentClaim {
            proof_kind,
            log_sizes: preprocessing.component_log_sizes,
        },
        interaction_claim: RecursionInteractionClaim {
            claimed_sums,
            public_relation_sum,
            log_sizes: interaction_log_sizes,
        },
        stark_proof,
        interaction_pow,
    })
}

/// Verifies one recursion proof against caller-owned protocol and statement claims.
pub fn verify_recursion_proof(
    profile: &FrozenProtocolProfile,
    preprocessing: &RecursionPreprocessing,
    expected_protocol: ProtocolId,
    expected_statement: &SpanStatement,
    proof: RecursionProof,
) -> Result<(), RecursionProofError> {
    validate_preprocessing(profile, preprocessing)?;
    if expected_protocol != preprocessing.protocol || proof.protocol != expected_protocol {
        return Err(RecursionProofError::ProtocolMismatch);
    }
    if expected_statement != &proof.statement {
        return Err(RecursionProofError::StatementMismatch);
    }
    if expected_statement.job().complete().protocol() != expected_protocol {
        return Err(RecursionProofError::StatementProtocolMismatch);
    }
    let expected_kind = proof_kind_for_statement(expected_statement);
    if expected_kind == ProofKind::BinaryNode {
        return Err(RecursionProofError::UnsupportedProofKind);
    }
    if proof.component_claim.proof_kind != expected_kind {
        return Err(RecursionProofError::ProofKindMismatch);
    }
    if proof.component_claim.log_sizes != preprocessing.component_log_sizes {
        return Err(RecursionProofError::ComponentLogSizesMismatch);
    }
    if proof.interaction_claim.log_sizes != preprocessing.column_log_sizes[2] {
        return Err(RecursionProofError::InteractionLogSizesMismatch);
    }
    let config = profile.manifest().recursion_pcs().config();
    if proof.stark_proof.config != config {
        return Err(RecursionProofError::PcsConfigMismatch);
    }
    if proof.stark_proof.commitments.len() != 4 {
        return Err(RecursionProofError::CommitmentCountMismatch);
    }
    if proof.stark_proof.commitments[0]
        != preprocessing
            .cached
            .commitment_root()
            .ok_or(RecursionProofError::MissingPreprocessingCommitment)?
    {
        return Err(RecursionProofError::PreprocessingCommitmentMismatch);
    }

    let mut channel = ProfiledPoseidon2M31Channel::for_recursion_proof(
        profile.recursion_plan(),
        expected_protocol,
        expected_statement,
    )
    .map_err(|error| RecursionProofError::Transcript(error.to_string()))?;
    let mut commitment_scheme =
        CommitmentSchemeVerifier::<ProfiledPoseidon2M31MerkleChannel>::new(config);
    commitment_scheme.commit(
        proof.stark_proof.commitments[0],
        &preprocessing.column_log_sizes[0],
        &mut channel,
    );
    commitment_scheme.commit(
        proof.stark_proof.commitments[1],
        &preprocessing.column_log_sizes[1],
        &mut channel,
    );
    channel
        .absorb_recursion_public_claim()
        .map_err(|error| RecursionProofError::Transcript(error.to_string()))?;
    let interaction_pow_bits = profile.manifest().recursion_pcs().interaction_pow_bits();
    if !channel.verify_pow_nonce(interaction_pow_bits, proof.interaction_pow) {
        return Err(RecursionProofError::InteractionPow);
    }
    channel.mix_u64(proof.interaction_pow);
    let relations = UniversalRelations::draw(&mut channel);
    let public_relation_sum = universal_public_relation_sum(
        &preprocessing.universal,
        expected_statement,
        expected_kind,
        &relations,
    )
    .map_err(RecursionProofError::Witness)?;
    if public_relation_sum != proof.interaction_claim.public_relation_sum {
        return Err(RecursionProofError::PublicRelationSumMismatch);
    }
    if !(proof
        .interaction_claim
        .claimed_sums
        .iter()
        .copied()
        .sum::<SecureField>()
        + public_relation_sum)
        .is_zero()
    {
        return Err(RecursionProofError::GlobalRelationSum);
    }
    channel
        .absorb_claimed_sums(&proof.interaction_claim.claimed_sums)
        .map_err(|error| RecursionProofError::Transcript(error.to_string()))?;
    commitment_scheme.commit(
        proof.stark_proof.commitments[2],
        &proof.interaction_claim.log_sizes,
        &mut channel,
    );

    let components = universal_components(
        &preprocessing.ids,
        &relations,
        expected_kind,
        &proof.component_claim.log_sizes,
        &proof.interaction_claim.claimed_sums,
    );
    let core_components = CoreComponents {
        components: components.verifiers(),
        n_preprocessed_columns: preprocessing.ids.len(),
    };
    let expected_degree = core_components.composition_log_degree_bound() - 1;
    if preprocessing.column_log_sizes[3]
        != vec![expected_degree; preprocessing.column_log_sizes[3].len()]
    {
        return Err(RecursionProofError::Geometry(
            "composition geometry differs from the generated roster",
        ));
    }
    stwo::core::verifier::verify(
        &components.verifiers(),
        &mut channel,
        &mut commitment_scheme,
        proof.stark_proof,
    )
    .map_err(|error| RecursionProofError::Stwo(error.to_string()))?;
    channel
        .finish()
        .map_err(|error| RecursionProofError::Transcript(error.to_string()))
}

fn validate_preprocessing(
    profile: &FrozenProtocolProfile,
    preprocessing: &RecursionPreprocessing,
) -> Result<(), RecursionProofError> {
    if preprocessing.protocol != profile.manifest().protocol_id() {
        return Err(RecursionProofError::ProtocolMismatch);
    }
    if preprocessing.component_log_sizes != *profile.recursion_program().component_log_sizes()
        || preprocessing.column_log_sizes.0 != profile.recursion_program().column_log_sizes().0
        || preprocessing.ids != recursion_preprocessed_column_ids()
    {
        return Err(RecursionProofError::Geometry(
            "preprocessing differs from the frozen recursion AIR",
        ));
    }
    Ok(())
}

fn proof_kind_for_statement(statement: &SpanStatement) -> ProofKind {
    if statement.slots().height() == 0 {
        if statement.body().is_empty() {
            ProofKind::EmptyLeaf
        } else {
            ProofKind::SegmentLeaf
        }
    } else {
        ProofKind::BinaryNode
    }
}

fn universal_twiddles(
    column_log_sizes: &TreeVec<Vec<u32>>,
    config: stwo::core::pcs::PcsConfig,
) -> stwo::prover::poly::twiddles::TwiddleTree<SimdBackend> {
    let max_log_size = column_log_sizes
        .iter()
        .flatten()
        .copied()
        .max()
        .unwrap_or(0);
    SimdBackend::precompute_twiddles(
        CanonicCoset::new(max_log_size + 2 + config.fri_config.log_blowup_factor)
            .circle_domain()
            .half_coset,
    )
}

fn commit_preprocessing<'a>(
    commitment_scheme: &mut CommitmentSchemeProver<
        'a,
        SimdBackend,
        ProfiledPoseidon2M31MerkleChannel,
    >,
    preprocessing: &prover::Preprocessing<Poseidon2M31MerkleHasher>,
    channel: &mut ProfiledPoseidon2M31Channel,
) {
    let (polynomials, commitment) = preprocessing.to_commitment_tree();
    commitment_scheme.commit_tree(
        stwo::core::utils::MaybeOwned::Owned(CommitmentTreeProver {
            polynomials,
            commitment,
        }),
        channel,
    );
}

fn commit_trace(
    commitment_scheme: &mut CommitmentSchemeProver<
        '_,
        SimdBackend,
        ProfiledPoseidon2M31MerkleChannel,
    >,
    trace: UniversalTrace,
    channel: &mut ProfiledPoseidon2M31Channel,
) {
    let mut builder = commitment_scheme.tree_builder();
    builder.extend_evals(trace);
    builder.commit(channel);
}

/// A malformed public claim, preprocessing key, or STWO proof.
#[derive(Debug)]
pub enum RecursionProofError {
    Witness(UniversalWitnessError),
    ProtocolMismatch,
    StatementMismatch,
    StatementProtocolMismatch,
    UnsupportedProofKind,
    ProofKindMismatch,
    ComponentLogSizesMismatch,
    InteractionLogSizesMismatch,
    PcsConfigMismatch,
    CommitmentCountMismatch,
    MissingPreprocessingCommitment,
    PreprocessingCommitmentMismatch,
    InteractionPow,
    PublicRelationSumMismatch,
    GlobalRelationSum,
    Geometry(&'static str),
    Transcript(String),
    Stwo(String),
}

impl fmt::Display for RecursionProofError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Witness(error) => write!(formatter, "universal witness: {error}"),
            Self::ProtocolMismatch => write!(formatter, "recursion protocol does not match"),
            Self::StatementMismatch => write!(formatter, "recursion statement does not match"),
            Self::StatementProtocolMismatch => {
                write!(
                    formatter,
                    "statement protocol does not match the expected protocol"
                )
            }
            Self::UnsupportedProofKind => {
                write!(formatter, "binary recursion proofs are not supported yet")
            }
            Self::ProofKindMismatch => write!(formatter, "proof kind does not match the statement"),
            Self::ComponentLogSizesMismatch => {
                write!(formatter, "component geometry does not match preprocessing")
            }
            Self::InteractionLogSizesMismatch => {
                write!(
                    formatter,
                    "interaction geometry does not match preprocessing"
                )
            }
            Self::PcsConfigMismatch => write!(formatter, "PCS configuration does not match"),
            Self::CommitmentCountMismatch => write!(formatter, "commitment count does not match"),
            Self::MissingPreprocessingCommitment => {
                write!(formatter, "preprocessing commitment is missing")
            }
            Self::PreprocessingCommitmentMismatch => {
                write!(formatter, "preprocessing commitment does not match")
            }
            Self::InteractionPow => write!(formatter, "interaction proof of work is invalid"),
            Self::PublicRelationSumMismatch => {
                write!(formatter, "public relation sum does not match")
            }
            Self::GlobalRelationSum => write!(formatter, "global relation sum is nonzero"),
            Self::Geometry(detail) => write!(formatter, "invalid recursion geometry: {detail}"),
            Self::Transcript(detail) => write!(formatter, "invalid recursion transcript: {detail}"),
            Self::Stwo(detail) => write!(formatter, "STWO proof error: {detail}"),
        }
    }
}

impl std::error::Error for RecursionProofError {}

#[cfg(test)]
mod tests {
    use air::digest::{IoDigest, ProgramDigest};
    use num_traits::One;

    use super::*;
    use crate::statement::{CompleteExecutionStatement, EdgeClaim, ExecutedSpan, JobContext};
    use crate::test_fixtures::{digest, state};

    fn empty_statement(profile: &FrozenProtocolProfile, program_seed: u16) -> SpanStatement {
        let complete = CompleteExecutionStatement::new(
            profile.manifest().protocol_id(),
            ProgramDigest::from(digest(program_seed)),
            state(0),
            state(3),
            IoDigest::from(digest(3)),
            IoDigest::from(digest(4)),
            12,
        )
        .expect("fixture execution is nonempty");
        let job = JobContext::new(complete, 3).expect("fixture job has three segments");
        SpanStatement::empty_leaf(job, 3).expect("slot three is canonical padding")
    }

    fn binary_statement(profile: &FrozenProtocolProfile) -> SpanStatement {
        let complete = CompleteExecutionStatement::new(
            profile.manifest().protocol_id(),
            ProgramDigest::from(digest(2)),
            state(0),
            state(2),
            IoDigest::from(digest(3)),
            IoDigest::from(digest(4)),
            2,
        )
        .expect("fixture execution is nonempty");
        let job = JobContext::new(complete, 2).expect("fixture job has two segments");
        let left_span = ExecutedSpan::new(
            0,
            1,
            0,
            1,
            state(0),
            state(1),
            EdgeClaim::present(complete.public_input()),
            EdgeClaim::absent(),
        )
        .expect("left fixture span is nonempty");
        let right_span = ExecutedSpan::new(
            1,
            1,
            1,
            1,
            state(1),
            state(2),
            EdgeClaim::absent(),
            EdgeClaim::present(complete.public_output()),
        )
        .expect("right fixture span is nonempty");
        let left =
            SpanStatement::segment_leaf(job, 0, left_span).expect("left statement matches the job");
        let right = SpanStatement::segment_leaf(job, 1, right_span)
            .expect("right statement matches the job");
        SpanStatement::fold(&left, &right).expect("fixture leaves form one binary span")
    }

    #[test]
    fn empty_proof_binds_every_public_claim_and_stark_region() {
        let _assembly_guard = crate::segment_leaf::tests::universal_assembly_guard();
        let profile = crate::profile::frozen_protocol_profile().expect("frozen profile is valid");
        let preprocessing =
            preprocess_recursion(&profile).expect("universal preprocessing is valid");
        let statement = empty_statement(&profile, 2);
        let proof = prove_empty_leaf(&profile, &preprocessing, &statement)
            .expect("canonical padding proves");
        let protocol = profile.manifest().protocol_id();
        let valid = verify_recursion_proof(
            &profile,
            &preprocessing,
            protocol,
            &statement,
            proof.clone(),
        )
        .is_ok();

        let wrong_protocol = ProtocolId::from(digest(90));
        let expected_protocol_rejected = verify_recursion_proof(
            &profile,
            &preprocessing,
            wrong_protocol,
            &statement,
            proof.clone(),
        )
        .is_err();
        let mut protocol_claim = proof.clone();
        protocol_claim.protocol = wrong_protocol;
        let protocol_claim_rejected = verify_recursion_proof(
            &profile,
            &preprocessing,
            protocol,
            &statement,
            protocol_claim,
        )
        .is_err();

        let other_statement = empty_statement(&profile, 20);
        let expected_statement_rejected = verify_recursion_proof(
            &profile,
            &preprocessing,
            protocol,
            &other_statement,
            proof.clone(),
        )
        .is_err();
        let mut statement_claim = proof.clone();
        statement_claim.statement = other_statement;
        let statement_claim_rejected = verify_recursion_proof(
            &profile,
            &preprocessing,
            protocol,
            &statement,
            statement_claim,
        )
        .is_err();

        let mut proof_kind = proof.clone();
        proof_kind.component_claim.proof_kind = ProofKind::BinaryNode;
        let proof_kind_rejected =
            verify_recursion_proof(&profile, &preprocessing, protocol, &statement, proof_kind)
                .is_err();
        let binary_statement = binary_statement(&profile);
        let mut unsupported_binary = proof.clone();
        unsupported_binary.statement = binary_statement;
        unsupported_binary.component_claim.proof_kind = ProofKind::BinaryNode;
        let unsupported_binary_rejected = verify_recursion_proof(
            &profile,
            &preprocessing,
            protocol,
            &binary_statement,
            unsupported_binary,
        )
        .is_err();
        let mut component_geometry = proof.clone();
        component_geometry.component_claim.log_sizes[0] += 1;
        let component_geometry_rejected = verify_recursion_proof(
            &profile,
            &preprocessing,
            protocol,
            &statement,
            component_geometry,
        )
        .is_err();
        let mut interaction_geometry = proof.clone();
        interaction_geometry.interaction_claim.log_sizes[0] += 1;
        let interaction_geometry_rejected = verify_recursion_proof(
            &profile,
            &preprocessing,
            protocol,
            &statement,
            interaction_geometry,
        )
        .is_err();

        let mut claimed_sum = proof.clone();
        claimed_sum.interaction_claim.claimed_sums[0] += SecureField::one();
        let claimed_sum_rejected =
            verify_recursion_proof(&profile, &preprocessing, protocol, &statement, claimed_sum)
                .is_err();
        let mut public_sum = proof.clone();
        public_sum.interaction_claim.public_relation_sum += SecureField::one();
        let public_sum_rejected =
            verify_recursion_proof(&profile, &preprocessing, protocol, &statement, public_sum)
                .is_err();

        let mut pcs_config = proof.clone();
        pcs_config.stark_proof.0.config.pow_bits += 1;
        let pcs_config_rejected =
            verify_recursion_proof(&profile, &preprocessing, protocol, &statement, pcs_config)
                .is_err();
        let mut interaction_pow = proof.clone();
        interaction_pow.interaction_pow = interaction_pow.interaction_pow.wrapping_add(1);
        let interaction_pow_rejected = verify_recursion_proof(
            &profile,
            &preprocessing,
            protocol,
            &statement,
            interaction_pow,
        )
        .is_err();
        let mut commitment_count = proof.clone();
        commitment_count.stark_proof.0.commitments.pop();
        let commitment_count_rejected = verify_recursion_proof(
            &profile,
            &preprocessing,
            protocol,
            &statement,
            commitment_count,
        )
        .is_err();
        let mut preprocessing_commitment = proof.clone();
        preprocessing_commitment.stark_proof.0.commitments[0].0[0] ^= 1;
        let preprocessing_commitment_rejected = verify_recursion_proof(
            &profile,
            &preprocessing,
            protocol,
            &statement,
            preprocessing_commitment,
        )
        .is_err();
        let mut main_commitment = proof.clone();
        main_commitment.stark_proof.0.commitments[1].0[0] ^= 1;
        let main_commitment_rejected = verify_recursion_proof(
            &profile,
            &preprocessing,
            protocol,
            &statement,
            main_commitment,
        )
        .is_err();
        let mut interaction_commitment = proof.clone();
        interaction_commitment.stark_proof.0.commitments[2].0[0] ^= 1;
        let interaction_commitment_rejected = verify_recursion_proof(
            &profile,
            &preprocessing,
            protocol,
            &statement,
            interaction_commitment,
        )
        .is_err();
        let mut composition_commitment = proof.clone();
        composition_commitment.stark_proof.0.commitments[3].0[0] ^= 1;
        let composition_commitment_rejected = verify_recursion_proof(
            &profile,
            &preprocessing,
            protocol,
            &statement,
            composition_commitment,
        )
        .is_err();
        let mut sampled_value = proof;
        sampled_value.stark_proof.0.sampled_values[0][0][0] += SecureField::one();
        let sampled_value_rejected = verify_recursion_proof(
            &profile,
            &preprocessing,
            protocol,
            &statement,
            sampled_value,
        )
        .is_err();

        assert_eq!(
            [
                valid,
                expected_protocol_rejected,
                protocol_claim_rejected,
                expected_statement_rejected,
                statement_claim_rejected,
                proof_kind_rejected,
                unsupported_binary_rejected,
                component_geometry_rejected,
                interaction_geometry_rejected,
                claimed_sum_rejected,
                public_sum_rejected,
                pcs_config_rejected,
                interaction_pow_rejected,
                commitment_count_rejected,
                preprocessing_commitment_rejected,
                main_commitment_rejected,
                interaction_commitment_rejected,
                composition_commitment_rejected,
                sampled_value_rejected,
            ],
            [true; 19]
        );
    }

    #[test]
    fn real_segment_leaf_produces_a_valid_recursion_proof() {
        let _assembly_guard = crate::segment_leaf::tests::universal_assembly_guard();
        let fixture = crate::segment_leaf::tests::real_fixture();
        let preprocessing =
            preprocess_recursion(&fixture.profile).expect("universal preprocessing is valid");
        let proof = prove_segment_leaf(&fixture.profile, &preprocessing, &fixture.wire)
            .expect("the authenticated VM segment proves through the universal AIR");
        assert!(
            verify_recursion_proof(
                &fixture.profile,
                &preprocessing,
                fixture.profile.manifest().protocol_id(),
                fixture.wire.statement(),
                proof,
            )
            .is_ok()
        );
    }
}
