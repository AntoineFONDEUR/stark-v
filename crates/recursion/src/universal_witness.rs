//! Canonical assembly of the universal recursion witness.
//!
//! The trusted protocol profile owns every preprocessing layout and component
//! capacity. Assembly executes that schedule once, fills the 36 generated AIR
//! components in roster order, pads committed tables with their constrained
//! inactive rows, and derives all interaction claims from one relation draw.

use core::fmt;

use air::digest::{Digest8, M31Word};
use air::preprocessed::PreprocessedTable;
use air::trace::Poseidon2Table;
use num_traits::{One, Zero};
use prover::components::COMPONENT_COUNT;
use prover::relations::{Counters, Relations};
use stwo::core::ColumnVec;
use stwo::core::circle::CirclePoint;
use stwo::core::fields::FieldExpOps;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::SecureField;
use stwo::core::pcs::TreeVec;
use stwo::core::pcs::quotients::{PointSample, fri_answers};
use stwo::core::poly::circle::CanonicCoset;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;

use crate::circuit::CircuitTraces;
use crate::control_air::{
    ControlPreprocessed, LEFT_RECURSION_VERIFIER_ID, POSEIDON2_VERIFIER_ID,
    RIGHT_RECURSION_VERIFIER_ID, SEGMENT_VERIFIER_ID,
};
use crate::fri_merkle_air::{
    FriMerkleOpeningSet, FriMerklePreprocessed, UniversalFriMerkleWitness,
};
use crate::fri_verifier_circuit::{
    FriVerifierCircuit, FriVerifierProfile, FriVerifierWitness, build_fri_verifier_circuit,
    build_fri_verifier_reference, verify_derived_query_values,
};
use crate::fri_verifier_control_air::{
    FriVerifierControlLane, FriVerifierControlPreprocessed, FriVerifierQueryLane,
};
use crate::fri_verifier_input_air::{FriVerifierCircuitLane, FriVerifierInputPreprocessed};
use crate::kernel::{VerifierControlPlan, VerifierStep};
use crate::merkle_root_air::MerkleRootPreprocessed;
use crate::pcs_deep_circuit::{
    PcsDeepCircuit, PcsDeepProfile, PcsDeepWitness, build_pcs_deep_circuit,
    build_pcs_deep_reference,
};
use crate::pcs_deep_input_air::{PcsDeepCircuitLane, PcsDeepInputPreprocessed};
use crate::pow::PowKind;
use crate::profile::{
    FrozenProtocolProfile, POSEIDON2_COMPONENT_LOG_SIZE, RECURSION_MAX_MERKLE_DEPTH, RootProofWire,
    recursion_component_log_sizes, recursion_preprocessed_column_ids,
};
use crate::protocol::CanonicalWords;
use crate::query_position_air::{
    QueryPositionKind, QueryPositionPreprocessed, UniversalRawQueryWitness,
};
use crate::recursion_air_composition_circuit::{
    RecursionAirCompositionCircuit, RecursionAirCompositionWitness,
    build_recursion_air_composition_circuit, build_recursion_air_composition_reference,
};
use crate::recursion_air_program::{
    UNIVERSAL_COMPONENT_COUNT, UniversalComponentLogSizes, universal_preprocessed_column_ids,
};
use crate::relation_challenge_air::RelationChallengePreprocessed;
use crate::segment_leaf::VmSegmentLeafWire;
use crate::statement::{SPAN_STATEMENT_CANONICAL_WORDS, SpanStatement};
use crate::statement_input_air::{
    LEFT_STATEMENT_SCOPE, RIGHT_STATEMENT_SCOPE, StatementInputPreprocessed, StatementInputWitness,
};
use crate::statement_semantics_circuit::{
    StatementSemanticsCircuit, StatementSemanticsCircuitWitness, StatementWords,
    build_statement_semantics_circuit,
};
use crate::statement_semantics_input_air::StatementSemanticsInputPreprocessed;
use crate::trace_merkle_air::{
    TraceMerklePreprocessed, TraceOpeningSet, TracePathSet, UniversalTraceOpeningWitness,
    UniversalTracePathWitness,
};
use crate::transcript::{RecordingTranscriptBackend, TranscriptTrace};
use crate::transcript_binding_air::{TranscriptCallPreprocessed, UniversalTranscriptWitness};
use crate::transcript_payload_air::TranscriptPayloadPreprocessed;
use crate::transcript_program::{
    JointInteractionContext, VerifierPublicClaim, VerifierTranscriptExecution,
    derive_interaction_seed, execute_fixed_transcript, execute_fixed_transcript_with_joint,
};
use crate::transcript_state_air::TranscriptStatePreprocessed;
use crate::transcript_word_air::TranscriptWordPreprocessed;
use crate::universal_relations::{UNIVERSAL_RELATION_COUNT, UniversalRelations};
use crate::verifier_randomness_air::VerifierRandomnessPreprocessed;
use crate::vm_air_composition_circuit::{
    VmAirCompositionCircuit, VmAirCompositionWitness, build_poseidon2_air_composition_circuit,
    build_poseidon2_air_composition_reference, build_vm_air_composition_circuit,
    build_vm_air_composition_reference,
};
use crate::vm_air_composition_control_air::VmAirCompositionControlPreprocessed;
use crate::vm_air_composition_input_air::{
    CircuitAnchorLane, CircuitAnchorMode, RecursionCompositionInputLane,
    SegmentCompositionInputLane, VmAirCompositionInputPreprocessed,
};
use crate::vm_public_claim::{
    public_input_digest_from_claim, public_output_digest_from_claim,
    vm_public_claim_digest_from_words,
};
use crate::vm_public_claim_hash_air::VmPublicClaimHashPreprocessed;
use crate::vm_public_claim_input_air::VmPublicClaimInputPreprocessed;
use crate::vm_public_claim_semantics_circuit::{
    VmPublicClaimSemanticsCircuit, VmPublicClaimSemanticsWitness,
    build_vm_public_claim_semantics_circuit,
};
use crate::vm_public_claim_semantics_input_air::VmPublicClaimSemanticsInputPreprocessed;
use crate::vm_public_io_hash_air::VmPublicIoHashPreprocessed;
use crate::vm_public_logup_circuit::{
    VmPublicLogupChallengeWords, VmPublicLogupCircuit, VmPublicLogupWitness,
    build_vm_public_logup_circuit, build_vm_public_logup_reference,
};
use crate::vm_public_logup_control_air::VmPublicLogupControlPreprocessed;
use crate::vm_public_logup_input_air::VmPublicLogupInputPreprocessed;
use crate::wire::{MerklePathWire, ProofKind};
use crate::{linear_ops, merkle_path, qm31_inv, qm31_mul};

/// One SIMD base-field trace tree used by the universal prover.
pub type UniversalTrace = ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>;

/// Fully assembled columns and public terms for one universal proof.
#[derive(Clone, Debug)]
pub struct UniversalWitness {
    proof_kind: ProofKind,
    traces: TreeVec<UniversalTrace>,
    claimed_sums: [SecureField; UNIVERSAL_COMPONENT_COUNT],
    public_relation_sum: SecureField,
    component_log_sizes: UniversalComponentLogSizes,
    preprocessing_ids: Vec<PreProcessedColumnId>,
}

/// Relation-independent preprocessing and main trace for one universal proof.
pub(crate) struct UniversalMainWitness {
    proof_kind: ProofKind,
    statement: SpanStatement,
    preprocessed_components: [UniversalTrace; UNIVERSAL_COMPONENT_COUNT],
    original_components: [UniversalTrace; UNIVERSAL_COMPONENT_COUNT],
    component_log_sizes: UniversalComponentLogSizes,
    expected_column_log_sizes: TreeVec<Vec<u32>>,
}

impl UniversalMainWitness {
    /// Clones the main columns only for the transcript precommit that derives LogUp challenges.
    pub(crate) fn original_trace_cloned(&self) -> UniversalTrace {
        self.original_components.iter().flatten().cloned().collect()
    }
}

impl UniversalWitness {
    pub const fn proof_kind(&self) -> ProofKind {
        self.proof_kind
    }

    pub const fn traces(&self) -> &TreeVec<UniversalTrace> {
        &self.traces
    }

    pub const fn claimed_sums(&self) -> &[SecureField; UNIVERSAL_COMPONENT_COUNT] {
        &self.claimed_sums
    }

    pub const fn public_relation_sum(&self) -> SecureField {
        self.public_relation_sum
    }

    /// Sum checked by the outer verifier after adding every component claim.
    pub fn global_relation_sum(&self) -> SecureField {
        self.claimed_sums.iter().copied().sum::<SecureField>() + self.public_relation_sum
    }

    pub const fn component_log_sizes(&self) -> &UniversalComponentLogSizes {
        &self.component_log_sizes
    }

    pub fn preprocessing_ids(&self) -> &[PreProcessedColumnId] {
        &self.preprocessing_ids
    }

    pub(crate) fn into_traces(self) -> TreeVec<UniversalTrace> {
        self.traces
    }
}

/// Assembles every universal component for one authenticated VM segment.
pub fn assemble_segment_leaf(
    profile: &FrozenProtocolProfile,
    leaf: &VmSegmentLeafWire,
    relations: &UniversalRelations,
) -> Result<UniversalWitness, UniversalWitnessError> {
    let preprocessing = UniversalPreprocessing::new(profile)?;
    let main = prepare_segment_leaf(profile, leaf, &preprocessing)?;
    finish_prepared_witness(&preprocessing, main, relations)
}

/// Builds the segment branch before the outer Fiat-Shamir relation draw.
pub(crate) fn prepare_segment_leaf(
    profile: &FrozenProtocolProfile,
    leaf: &VmSegmentLeafWire,
    preprocessing: &UniversalPreprocessing,
) -> Result<UniversalMainWitness, UniversalWitnessError> {
    let component_log_sizes = recursion_component_log_sizes();
    if profile.recursion_program().component_log_sizes() != &component_log_sizes {
        return Err(stage(
            "universal component capacities",
            "profile and assembler log sizes differ",
        ));
    }
    preprocessing.validate_capacities(&component_log_sizes)?;

    let claim_digest =
        vm_public_claim_digest_from_words(leaf.public_claim_words(), profile.public_claim_shape())
            .map_err(|error| stage("VM public-claim digest", error))?;
    let vm_public_claim = VerifierPublicClaim::Vm(claim_digest);
    let poseidon2_public_claim = VerifierPublicClaim::Poseidon2([M31Word::from(
        u16::try_from(POSEIDON2_COMPONENT_LOG_SIZE)
            .expect("the fixed Poseidon2 log size fits one canonical word"),
    )]);
    let seeds = [
        derive_interaction_seed(
            RecordingTranscriptBackend::default(),
            profile.vm_plan(),
            profile.manifest().protocol_id(),
            leaf.statement(),
            vm_public_claim,
            leaf.proof(),
        )
        .map_err(|error| stage("VM interaction seed", error))?,
        derive_interaction_seed(
            RecordingTranscriptBackend::default(),
            profile.poseidon2_plan(),
            profile.manifest().protocol_id(),
            leaf.statement(),
            poseidon2_public_claim,
            leaf.poseidon2_proof(),
        )
        .map_err(|error| stage("Poseidon2 interaction seed", error))?,
    ];
    let joint = JointInteractionContext {
        seeds,
        shared_relation_sum: Some(SecureField::from(leaf.shared_relation_sum())),
    };
    let vm_transcript = execute_fixed_transcript_with_joint(
        RecordingTranscriptBackend::default(),
        profile.vm_plan(),
        profile.manifest().protocol_id(),
        leaf.statement(),
        vm_public_claim,
        leaf.proof(),
        joint,
    )
    .map_err(|error| stage("VM verifier transcript", error))?;
    let poseidon2_transcript = execute_fixed_transcript_with_joint(
        RecordingTranscriptBackend::default(),
        profile.poseidon2_plan(),
        profile.manifest().protocol_id(),
        leaf.statement(),
        poseidon2_public_claim,
        leaf.poseidon2_proof(),
        joint,
    )
    .map_err(|error| stage("Poseidon2 verifier transcript", error))?;
    let relation_challenges =
        relation_challenge_words(&vm_transcript, Relations::DESCRIPTORS.len())?;
    let composition_randomness = secure_draw_words(
        &vm_transcript,
        VerifierStep::DrawCompositionRandomness,
        "composition randomness",
    )?;
    let oods_seed = secure_draw_words(&vm_transcript, VerifierStep::DrawOodsPoint, "OODS point")?;
    let deep_randomness = secure_draw_words(
        &vm_transcript,
        VerifierStep::DrawDeepRandomness,
        "DEEP randomness",
    )?;
    let fri_alphas = fri_alpha_values(&vm_transcript, preprocessing.fri_profiles[0].layer_count())?;
    let raw_queries = raw_query_words(
        &vm_transcript,
        preprocessing.query_position.vm_query_count(),
    )?;
    let poseidon2_raw_queries = raw_query_words(
        &poseidon2_transcript,
        preprocessing.query_position.poseidon2_query_count(),
    )?;
    let poseidon2_composition_randomness = secure_draw_words(
        &poseidon2_transcript,
        VerifierStep::DrawCompositionRandomness,
        "Poseidon2 composition randomness",
    )?;
    let poseidon2_oods_seed = secure_draw_words(
        &poseidon2_transcript,
        VerifierStep::DrawOodsPoint,
        "Poseidon2 OODS point",
    )?;
    let poseidon2_deep_randomness = secure_draw_words(
        &poseidon2_transcript,
        VerifierStep::DrawDeepRandomness,
        "Poseidon2 DEEP randomness",
    )?;
    let poseidon2_fri_alphas = fri_alpha_values(
        &poseidon2_transcript,
        preprocessing.fri_profiles[1].layer_count(),
    )?;

    let statement_words: StatementWords =
        leaf.statement()
            .canonical_words()
            .try_into()
            .map_err(|words: Vec<M31Word>| {
                stage(
                    "segment statement words",
                    format_args!(
                        "got {} words, expected {SPAN_STATEMENT_CANONICAL_WORDS}",
                        words.len()
                    ),
                )
            })?;
    let zero_statement = [M31Word::ZERO; SPAN_STATEMENT_CANONICAL_WORDS];
    let statement_circuit = build_statement_semantics_circuit(StatementSemanticsCircuitWitness {
        segment_selector: true,
        binary_selector: false,
        empty_selector: false,
        segment: &statement_words,
        left: &zero_statement,
        right: &zero_statement,
        parent: &statement_words,
    });
    ensure_zero_outputs(
        "segment statement circuit",
        statement_circuit.nonzero_output_count(),
    )?;
    let input_digest =
        *public_input_digest_from_claim(leaf.public_claim_words(), profile.public_claim_shape())
            .map_err(|error| stage("public-input digest", error))?
            .digest()
            .words();
    let output_digest =
        *public_output_digest_from_claim(leaf.public_claim_words(), profile.public_claim_shape())
            .map_err(|error| stage("public-output digest", error))?
            .digest()
            .words();
    let vm_claim_circuit = build_vm_public_claim_semantics_circuit(
        profile.public_claim_shape(),
        VmPublicClaimSemanticsWitness {
            segment_selector: true,
            claim_words: leaf.public_claim_words(),
            statement_words: &statement_words,
            input_digest: &input_digest,
            output_digest: &output_digest,
        },
    )
    .map_err(|error| stage("VM public-claim semantic circuit", error))?;
    ensure_zero_outputs(
        "VM public-claim semantic circuit",
        vm_claim_circuit.nonzero_output_count(),
    )?;
    let proof_claimed_sums = leaf
        .proof()
        .claimed_sums
        .iter()
        .copied()
        .map(SecureField::from)
        .collect::<Vec<_>>();
    let vm_public_logup_circuit = build_vm_public_logup_circuit(
        profile.public_claim_shape(),
        u32::try_from(proof_claimed_sums.len())
            .map_err(|error| stage("VM claimed-sum count", error))?,
        VmPublicLogupWitness {
            segment_selector: true,
            claim_words: leaf.public_claim_words(),
            relation_challenges: VmPublicLogupChallengeWords::new(
                relation_challenges[0],
                relation_challenges[1],
                relation_challenges[3],
                relation_challenges[6],
            ),
            claimed_sums: &proof_claimed_sums,
            shared_relation_sum: SecureField::from(leaf.shared_relation_sum()),
        },
    )
    .map_err(|error| stage("VM public-LogUp circuit", error))?;
    ensure_zero_outputs(
        "VM public-LogUp circuit",
        vm_public_logup_circuit.nonzero_output_count(),
    )?;
    let sampled_values = leaf
        .proof()
        .sampled_values
        .iter()
        .copied()
        .map(SecureField::from)
        .collect::<Vec<_>>();
    let vm_composition_circuit = build_vm_air_composition_circuit(
        crate::profile::vm_component_log_sizes(),
        VmAirCompositionWitness {
            segment_selector: true,
            sampled_values: &sampled_values,
            claimed_sums: &proof_claimed_sums,
            relation_challenges: &relation_challenges,
            composition_randomness,
            oods_point: oods_seed,
        },
    )
    .map_err(|error| stage("VM AIR-composition circuit", error))?;
    ensure_zero_outputs(
        "VM AIR-composition circuit",
        vm_composition_circuit.nonzero_output_count(),
    )?;

    let queried_values = leaf
        .proof()
        .queried_values
        .iter()
        .copied()
        .map(|word| BaseField::from(word.as_u32()))
        .collect::<Vec<_>>();
    let fri_opening = FriMerkleOpeningSet::from_wire(&raw_queries, &leaf.proof().fri_layers[..]);
    let poseidon2_fri_opening = FriMerkleOpeningSet::from_wire(
        &poseidon2_raw_queries,
        &leaf.poseidon2_proof().fri_layers[..],
    );
    let vm_fri_routes = fri_routes(
        &preprocessing.query_position,
        SEGMENT_VERIFIER_ID,
        &raw_queries,
        preprocessing.fri_profiles[0].layer_count(),
    )?;
    let deep_answers = native_deep_answers(
        &preprocessing.pcs_profiles[0],
        &sampled_values,
        &queried_values,
        oods_seed,
        deep_randomness,
        &raw_queries,
    )?;
    let authenticated_values = fri_opening
        .layers
        .iter()
        .map(|layer| {
            layer
                .queries
                .iter()
                .flat_map(|query| query.values.iter().copied())
                .map(SecureField::from)
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    verify_derived_query_values(
        &preprocessing.fri_profiles[0],
        &deep_answers,
        &authenticated_values,
        &fri_alphas,
        &raw_queries,
    )
    .map_err(|error| stage("VM FRI query canonicity", error))?;
    let pcs_circuit = build_pcs_deep_circuit(
        &preprocessing.pcs_profiles[0],
        PcsDeepWitness {
            active: true,
            sampled_values: &sampled_values,
            queried_values: &queried_values,
            oods_seed,
            deep_randomness,
            raw_queries: &raw_queries,
            answers: &deep_answers,
        },
    )
    .map_err(|error| stage("VM PCS DEEP circuit", error))?;
    ensure_zero_outputs("VM PCS DEEP circuit", pcs_circuit.nonzero_output_count())?;
    let vm_last_layer_positions = last_layer_positions(
        &preprocessing.query_position,
        SEGMENT_VERIFIER_ID,
        &raw_queries,
    )?;
    let last_layer_coefficients = leaf
        .proof()
        .last_layer_coefficients
        .iter()
        .copied()
        .map(SecureField::from)
        .collect::<Vec<_>>();
    let fri_circuit = build_fri_verifier_circuit(
        &preprocessing.fri_profiles[0],
        FriVerifierWitness {
            active: true,
            deep_answers: &deep_answers,
            authenticated_values: &authenticated_values,
            fri_alphas: &fri_alphas,
            raw_queries: &raw_queries,
            fri_positions: &vm_fri_routes.positions,
            fri_offsets: &vm_fri_routes.offsets,
            last_layer_positions: &vm_last_layer_positions,
            last_layer_coefficients: &last_layer_coefficients,
        },
    )
    .map_err(|error| stage("VM FRI verifier circuit", error))?;
    ensure_zero_outputs(
        "VM FRI verifier circuit",
        fri_circuit.nonzero_output_count(),
    )?;

    let poseidon2_sampled_values = leaf
        .poseidon2_proof()
        .sampled_values
        .iter()
        .copied()
        .map(SecureField::from)
        .collect::<Vec<_>>();
    let poseidon2_claimed_sums = leaf
        .poseidon2_proof()
        .claimed_sums
        .iter()
        .copied()
        .map(SecureField::from)
        .collect::<Vec<_>>();
    let poseidon2_composition_circuit = build_poseidon2_air_composition_circuit(
        POSEIDON2_COMPONENT_LOG_SIZE,
        VmAirCompositionWitness {
            segment_selector: true,
            sampled_values: &poseidon2_sampled_values,
            claimed_sums: &poseidon2_claimed_sums,
            relation_challenges: &relation_challenges,
            composition_randomness: poseidon2_composition_randomness,
            oods_point: poseidon2_oods_seed,
        },
    )
    .map_err(|error| stage("Poseidon2 AIR-composition circuit", error))?;
    ensure_zero_outputs(
        "Poseidon2 AIR-composition circuit",
        poseidon2_composition_circuit.nonzero_output_count(),
    )?;
    let poseidon2_queried_values = leaf
        .poseidon2_proof()
        .queried_values
        .iter()
        .copied()
        .map(|word| BaseField::from(word.as_u32()))
        .collect::<Vec<_>>();
    let poseidon2_fri_routes = fri_routes(
        &preprocessing.query_position,
        POSEIDON2_VERIFIER_ID,
        &poseidon2_raw_queries,
        preprocessing.fri_profiles[1].layer_count(),
    )?;
    let poseidon2_deep_answers = native_deep_answers(
        &preprocessing.pcs_profiles[1],
        &poseidon2_sampled_values,
        &poseidon2_queried_values,
        poseidon2_oods_seed,
        poseidon2_deep_randomness,
        &poseidon2_raw_queries,
    )?;
    let poseidon2_authenticated_values = poseidon2_fri_opening
        .layers
        .iter()
        .map(|layer| {
            layer
                .queries
                .iter()
                .flat_map(|query| query.values.iter().copied())
                .map(SecureField::from)
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    verify_derived_query_values(
        &preprocessing.fri_profiles[1],
        &poseidon2_deep_answers,
        &poseidon2_authenticated_values,
        &poseidon2_fri_alphas,
        &poseidon2_raw_queries,
    )
    .map_err(|error| stage("Poseidon2 FRI query canonicity", error))?;
    let poseidon2_pcs_circuit = build_pcs_deep_circuit(
        &preprocessing.pcs_profiles[1],
        PcsDeepWitness {
            active: true,
            sampled_values: &poseidon2_sampled_values,
            queried_values: &poseidon2_queried_values,
            oods_seed: poseidon2_oods_seed,
            deep_randomness: poseidon2_deep_randomness,
            raw_queries: &poseidon2_raw_queries,
            answers: &poseidon2_deep_answers,
        },
    )
    .map_err(|error| stage("Poseidon2 PCS DEEP circuit", error))?;
    ensure_zero_outputs(
        "Poseidon2 PCS DEEP circuit",
        poseidon2_pcs_circuit.nonzero_output_count(),
    )?;
    let poseidon2_last_layer_positions = last_layer_positions(
        &preprocessing.query_position,
        POSEIDON2_VERIFIER_ID,
        &poseidon2_raw_queries,
    )?;
    let poseidon2_last_layer_coefficients = leaf
        .poseidon2_proof()
        .last_layer_coefficients
        .iter()
        .copied()
        .map(SecureField::from)
        .collect::<Vec<_>>();
    let poseidon2_fri_circuit = build_fri_verifier_circuit(
        &preprocessing.fri_profiles[1],
        FriVerifierWitness {
            active: true,
            deep_answers: &poseidon2_deep_answers,
            authenticated_values: &poseidon2_authenticated_values,
            fri_alphas: &poseidon2_fri_alphas,
            raw_queries: &poseidon2_raw_queries,
            fri_positions: &poseidon2_fri_routes.positions,
            fri_offsets: &poseidon2_fri_routes.offsets,
            last_layer_positions: &poseidon2_last_layer_positions,
            last_layer_coefficients: &poseidon2_last_layer_coefficients,
        },
    )
    .map_err(|error| stage("Poseidon2 FRI verifier circuit", error))?;
    ensure_zero_outputs(
        "Poseidon2 FRI verifier circuit",
        poseidon2_fri_circuit.nonzero_output_count(),
    )?;

    assemble_universal_components(
        profile,
        preprocessing,
        component_log_sizes,
        UniversalAssemblyBranch::Segment {
            leaf,
            vm_transcript: Box::new(vm_transcript),
            poseidon2_transcript: Box::new(poseidon2_transcript),
            interaction_seeds: seeds,
            raw_queries,
            poseidon2_raw_queries,
            fri_opening,
            poseidon2_fri_opening: Box::new(poseidon2_fri_opening),
            statement_circuit: Box::new(statement_circuit),
            vm_claim_circuit: Box::new(vm_claim_circuit),
            vm_public_logup_circuit: Box::new(vm_public_logup_circuit),
            vm_composition_circuit: Box::new(vm_composition_circuit),
            poseidon2_composition_circuit: Box::new(poseidon2_composition_circuit),
            pcs_circuit: Box::new(pcs_circuit),
            poseidon2_pcs_circuit: Box::new(poseidon2_pcs_circuit),
            fri_circuit: Box::new(fri_circuit),
            poseidon2_fri_circuit: Box::new(poseidon2_fri_circuit),
        },
    )
}

/// Assembles one binary parent from two fixed-size universal child proofs.
pub fn assemble_binary_node(
    profile: &FrozenProtocolProfile,
    left: &RootProofWire,
    right: &RootProofWire,
    relations: &UniversalRelations,
) -> Result<UniversalWitness, UniversalWitnessError> {
    let preprocessing = UniversalPreprocessing::new(profile)?;
    let main = prepare_binary_node(profile, left, right, &preprocessing)?;
    finish_prepared_witness(&preprocessing, main, relations)
}

/// Builds the binary branch before the outer Fiat-Shamir relation draw.
pub(crate) fn prepare_binary_node(
    profile: &FrozenProtocolProfile,
    left: &RootProofWire,
    right: &RootProofWire,
    preprocessing: &UniversalPreprocessing,
) -> Result<UniversalMainWitness, UniversalWitnessError> {
    let component_log_sizes = recursion_component_log_sizes();
    if profile.recursion_program().component_log_sizes() != &component_log_sizes {
        return Err(stage(
            "universal component capacities",
            "profile and assembler log sizes differ",
        ));
    }
    preprocessing.validate_capacities(&component_log_sizes)?;
    let version = profile.manifest().manifest().version;
    if left.version() != version || right.version() != version {
        return Err(stage(
            "binary child version",
            "both children must use the active protocol version",
        ));
    }
    let statement = SpanStatement::fold(left.statement(), right.statement())
        .map_err(|error| stage("binary statement fold", error))?;
    let left_words = canonical_statement_words(left.statement(), "left child statement")?;
    let right_words = canonical_statement_words(right.statement(), "right child statement")?;
    let parent_words = canonical_statement_words(&statement, "binary parent statement")?;
    let zero_statement = [M31Word::ZERO; SPAN_STATEMENT_CANONICAL_WORDS];
    let statement_circuit = build_statement_semantics_circuit(StatementSemanticsCircuitWitness {
        segment_selector: false,
        binary_selector: true,
        empty_selector: false,
        segment: &zero_statement,
        left: &left_words,
        right: &right_words,
        parent: &parent_words,
    });
    ensure_zero_outputs(
        "binary statement circuit",
        statement_circuit.nonzero_output_count(),
    )?;
    let zero_claim = vec![M31Word::ZERO; profile.public_claim_shape().claim_word_count()];
    let zero_claimed_sums = vec![SecureField::zero(); COMPONENT_COUNT];
    let vm_public_logup_circuit = build_vm_public_logup_circuit(
        profile.public_claim_shape(),
        u32::try_from(COMPONENT_COUNT).map_err(|error| stage("VM component count", error))?,
        VmPublicLogupWitness {
            segment_selector: false,
            claim_words: &zero_claim,
            relation_challenges: VmPublicLogupChallengeWords::new(
                [M31Word::ZERO; 8],
                [M31Word::ZERO; 8],
                [M31Word::ZERO; 8],
                [M31Word::ZERO; 8],
            ),
            claimed_sums: &zero_claimed_sums,
            shared_relation_sum: SecureField::zero(),
        },
    )
    .map_err(|error| stage("inactive VM public-LogUp circuit", error))?;
    let left_child = prepare_recursion_child(
        profile,
        preprocessing,
        left,
        LEFT_RECURSION_VERIFIER_ID,
        LEFT_RECURSION_COMPOSITION_CIRCUIT_ID,
        LEFT_STATEMENT_SCOPE,
        "left recursion child",
    )?;
    let right_child = prepare_recursion_child(
        profile,
        preprocessing,
        right,
        RIGHT_RECURSION_VERIFIER_ID,
        RIGHT_RECURSION_COMPOSITION_CIRCUIT_ID,
        RIGHT_STATEMENT_SCOPE,
        "right recursion child",
    )?;
    assemble_universal_components(
        profile,
        preprocessing,
        component_log_sizes,
        UniversalAssemblyBranch::Binary {
            statement: Box::new(statement),
            left,
            right,
            statement_circuit: Box::new(statement_circuit),
            vm_public_logup_circuit: Box::new(vm_public_logup_circuit),
            left_child: Box::new(left_child),
            right_child: Box::new(right_child),
        },
    )
}

struct PreparedRecursionChild {
    verifier_id: u32,
    circuit_id: u32,
    statement_scope: u32,
    transcript: VerifierTranscriptExecution<RecordingTranscriptBackend>,
    raw_queries: Vec<M31Word>,
    fri_opening: FriMerkleOpeningSet,
    composition_circuit: RecursionAirCompositionCircuit,
    pcs_circuit: PcsDeepCircuit,
    fri_circuit: FriVerifierCircuit,
}

impl PreparedRecursionChild {
    fn composition_lane(&self) -> RecursionCompositionInputLane<'_> {
        RecursionCompositionInputLane {
            verifier_id: self.verifier_id,
            circuit_id: self.circuit_id,
            statement_scope: self.statement_scope,
            circuit: &self.composition_circuit,
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn prepare_recursion_child(
    profile: &FrozenProtocolProfile,
    preprocessing: &UniversalPreprocessing,
    child: &RootProofWire,
    verifier_id: u32,
    circuit_id: u32,
    statement_scope: u32,
    stage_name: &'static str,
) -> Result<PreparedRecursionChild, UniversalWitnessError> {
    if child.statement().job().complete().protocol() != profile.manifest().protocol_id() {
        return Err(stage(stage_name, "child statement protocol mismatch"));
    }
    child
        .stark()
        .validate_against_shape(&profile.manifest().manifest().recursion_proof_shape)
        .map_err(|error| stage(stage_name, error))?;
    let transcript = execute_fixed_transcript(
        RecordingTranscriptBackend::default(),
        profile.recursion_plan(),
        profile.manifest().protocol_id(),
        child.statement(),
        VerifierPublicClaim::Recursion,
        child.stark(),
    )
    .map_err(|error| stage(stage_name, error))?;
    let relation_challenges = relation_challenge_words(&transcript, UNIVERSAL_RELATION_COUNT)?;
    let composition_randomness = secure_draw_words(
        &transcript,
        VerifierStep::DrawCompositionRandomness,
        "recursion composition randomness",
    )?;
    let oods_seed = secure_draw_words(
        &transcript,
        VerifierStep::DrawOodsPoint,
        "recursion OODS point",
    )?;
    let deep_randomness = secure_draw_words(
        &transcript,
        VerifierStep::DrawDeepRandomness,
        "recursion DEEP randomness",
    )?;
    let fri_alphas = fri_alpha_values(&transcript, preprocessing.fri_profiles[2].layer_count())?;
    let raw_queries = raw_query_words(
        &transcript,
        preprocessing.query_position.recursion_query_count(),
    )?;
    let statement_words = canonical_statement_words(child.statement(), stage_name)?;
    let sampled_values = child
        .stark()
        .sampled_values
        .iter()
        .copied()
        .map(SecureField::from)
        .collect::<Vec<_>>();
    let claimed_sums = child
        .stark()
        .claimed_sums
        .iter()
        .copied()
        .map(SecureField::from)
        .collect::<Vec<_>>();
    let composition_circuit = build_recursion_air_composition_circuit(
        recursion_component_log_sizes(),
        &recursion_preprocessed_column_ids(),
        RecursionAirCompositionWitness {
            parent_binary_selector: true,
            child_kind: child.kind(),
            statement_words: &statement_words,
            sampled_values: &sampled_values,
            claimed_sums: &claimed_sums,
            relation_challenges: &relation_challenges,
            composition_randomness,
            oods_point: oods_seed,
        },
    )
    .map_err(|error| stage(stage_name, error))?;
    ensure_zero_outputs(
        "recursion AIR-composition circuit",
        composition_circuit.nonzero_output_count(),
    )?;

    let queried_values = child
        .stark()
        .queried_values
        .iter()
        .copied()
        .map(|word| BaseField::from(word.as_u32()))
        .collect::<Vec<_>>();
    let fri_opening = FriMerkleOpeningSet::from_wire(&raw_queries, &child.stark().fri_layers[..]);
    let fri_routes = fri_routes(
        &preprocessing.query_position,
        verifier_id,
        &raw_queries,
        preprocessing.fri_profiles[2].layer_count(),
    )?;
    let deep_answers = native_deep_answers(
        &preprocessing.pcs_profiles[2],
        &sampled_values,
        &queried_values,
        oods_seed,
        deep_randomness,
        &raw_queries,
    )?;
    let authenticated_values = fri_opening
        .layers
        .iter()
        .map(|layer| {
            layer
                .queries
                .iter()
                .flat_map(|query| query.values.iter().copied())
                .map(SecureField::from)
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    verify_derived_query_values(
        &preprocessing.fri_profiles[2],
        &deep_answers,
        &authenticated_values,
        &fri_alphas,
        &raw_queries,
    )
    .map_err(|error| stage(stage_name, error))?;
    let pcs_circuit = build_pcs_deep_circuit(
        &preprocessing.pcs_profiles[2],
        PcsDeepWitness {
            active: true,
            sampled_values: &sampled_values,
            queried_values: &queried_values,
            oods_seed,
            deep_randomness,
            raw_queries: &raw_queries,
            answers: &deep_answers,
        },
    )
    .map_err(|error| stage(stage_name, error))?;
    ensure_zero_outputs(
        "recursion PCS DEEP circuit",
        pcs_circuit.nonzero_output_count(),
    )?;
    let last_layer_positions =
        last_layer_positions(&preprocessing.query_position, verifier_id, &raw_queries)?;
    let last_layer_coefficients = child
        .stark()
        .last_layer_coefficients
        .iter()
        .copied()
        .map(SecureField::from)
        .collect::<Vec<_>>();
    let fri_circuit = build_fri_verifier_circuit(
        &preprocessing.fri_profiles[2],
        FriVerifierWitness {
            active: true,
            deep_answers: &deep_answers,
            authenticated_values: &authenticated_values,
            fri_alphas: &fri_alphas,
            raw_queries: &raw_queries,
            fri_positions: &fri_routes.positions,
            fri_offsets: &fri_routes.offsets,
            last_layer_positions: &last_layer_positions,
            last_layer_coefficients: &last_layer_coefficients,
        },
    )
    .map_err(|error| stage(stage_name, error))?;
    ensure_zero_outputs(
        "recursion FRI verifier circuit",
        fri_circuit.nonzero_output_count(),
    )?;
    Ok(PreparedRecursionChild {
        verifier_id,
        circuit_id,
        statement_scope,
        transcript,
        raw_queries,
        fri_opening,
        composition_circuit,
        pcs_circuit,
        fri_circuit,
    })
}

#[cfg(test)]
pub(crate) fn validate_recursion_child_for_test(
    profile: &FrozenProtocolProfile,
    preprocessing: &UniversalPreprocessing,
    child: &RootProofWire,
) -> Result<(), UniversalWitnessError> {
    // Mutation tests exercise the complete child-verifier circuit stack without
    // materializing an unrelated parent trace after a child has already failed.
    prepare_recursion_child(
        profile,
        preprocessing,
        child,
        LEFT_RECURSION_VERIFIER_ID,
        LEFT_RECURSION_COMPOSITION_CIRCUIT_ID,
        LEFT_STATEMENT_SCOPE,
        "recursion child mutation",
    )
    .map(drop)
}

fn canonical_statement_words(
    statement: &SpanStatement,
    stage_name: &'static str,
) -> Result<StatementWords, UniversalWitnessError> {
    statement
        .canonical_words()
        .try_into()
        .map_err(|words: Vec<M31Word>| {
            stage(
                stage_name,
                format_args!(
                    "got {} words, expected {SPAN_STATEMENT_CANONICAL_WORDS}",
                    words.len()
                ),
            )
        })
}

fn widen_merkle_path<const SOURCE_DEPTH: usize>(
    path: &MerklePathWire<SOURCE_DEPTH>,
) -> Result<MerklePathWire<RECURSION_MAX_MERKLE_DEPTH>, UniversalWitnessError> {
    let mut siblings = [Digest8::ZERO; RECURSION_MAX_MERKLE_DEPTH];
    siblings[..SOURCE_DEPTH].copy_from_slice(path.siblings());
    MerklePathWire::new(path.active_depth(), siblings)
        .map_err(|error| stage("trace-path width normalization", error))
}

/// Assembles the unique proof-free witness for one canonical padding slot.
pub fn assemble_empty_leaf(
    profile: &FrozenProtocolProfile,
    statement: &SpanStatement,
    relations: &UniversalRelations,
) -> Result<UniversalWitness, UniversalWitnessError> {
    let preprocessing = UniversalPreprocessing::new(profile)?;
    let main = prepare_empty_leaf(profile, statement, &preprocessing)?;
    finish_prepared_witness(&preprocessing, main, relations)
}

/// Builds the empty branch before the outer Fiat-Shamir relation draw.
pub(crate) fn prepare_empty_leaf(
    profile: &FrozenProtocolProfile,
    statement: &SpanStatement,
    preprocessing: &UniversalPreprocessing,
) -> Result<UniversalMainWitness, UniversalWitnessError> {
    if statement.slots().height() != 0 || !statement.body().is_empty() {
        return Err(stage(
            "empty-leaf statement",
            "the empty branch requires one canonical height-zero padding slot",
        ));
    }
    let component_log_sizes = recursion_component_log_sizes();
    if profile.recursion_program().component_log_sizes() != &component_log_sizes {
        return Err(stage(
            "universal component capacities",
            "profile and assembler log sizes differ",
        ));
    }
    preprocessing.validate_capacities(&component_log_sizes)?;

    let parent: StatementWords =
        statement
            .canonical_words()
            .try_into()
            .map_err(|words: Vec<M31Word>| {
                stage(
                    "empty statement words",
                    format_args!(
                        "got {} words, expected {SPAN_STATEMENT_CANONICAL_WORDS}",
                        words.len()
                    ),
                )
            })?;
    let zero_statement = [M31Word::ZERO; SPAN_STATEMENT_CANONICAL_WORDS];
    let statement_circuit = build_statement_semantics_circuit(StatementSemanticsCircuitWitness {
        segment_selector: false,
        binary_selector: false,
        empty_selector: true,
        segment: &zero_statement,
        left: &zero_statement,
        right: &zero_statement,
        parent: &parent,
    });
    ensure_zero_outputs(
        "empty statement circuit",
        statement_circuit.nonzero_output_count(),
    )?;
    let zero_claim = vec![M31Word::ZERO; profile.public_claim_shape().claim_word_count()];
    let claimed_sum_count =
        u32::try_from(COMPONENT_COUNT).map_err(|error| stage("VM component count", error))?;
    let zero_claimed_sums = vec![SecureField::zero(); COMPONENT_COUNT];
    let vm_public_logup_circuit = build_vm_public_logup_circuit(
        profile.public_claim_shape(),
        claimed_sum_count,
        VmPublicLogupWitness {
            segment_selector: false,
            claim_words: &zero_claim,
            relation_challenges: VmPublicLogupChallengeWords::new(
                [M31Word::ZERO; 8],
                [M31Word::ZERO; 8],
                [M31Word::ZERO; 8],
                [M31Word::ZERO; 8],
            ),
            claimed_sums: &zero_claimed_sums,
            shared_relation_sum: SecureField::zero(),
        },
    )
    .map_err(|error| stage("inactive VM public-LogUp circuit", error))?;

    assemble_universal_components(
        profile,
        preprocessing,
        component_log_sizes,
        UniversalAssemblyBranch::Empty {
            statement,
            statement_circuit: Box::new(statement_circuit),
            vm_public_logup_circuit: Box::new(vm_public_logup_circuit),
        },
    )
}

enum UniversalAssemblyBranch<'a> {
    Segment {
        leaf: &'a VmSegmentLeafWire,
        vm_transcript: Box<VerifierTranscriptExecution<RecordingTranscriptBackend>>,
        poseidon2_transcript: Box<VerifierTranscriptExecution<RecordingTranscriptBackend>>,
        interaction_seeds: [SecureField; 2],
        raw_queries: Vec<M31Word>,
        poseidon2_raw_queries: Vec<M31Word>,
        fri_opening: FriMerkleOpeningSet,
        poseidon2_fri_opening: Box<FriMerkleOpeningSet>,
        statement_circuit: Box<StatementSemanticsCircuit>,
        vm_claim_circuit: Box<VmPublicClaimSemanticsCircuit>,
        vm_public_logup_circuit: Box<VmPublicLogupCircuit>,
        vm_composition_circuit: Box<VmAirCompositionCircuit>,
        poseidon2_composition_circuit: Box<VmAirCompositionCircuit>,
        pcs_circuit: Box<PcsDeepCircuit>,
        poseidon2_pcs_circuit: Box<PcsDeepCircuit>,
        fri_circuit: Box<FriVerifierCircuit>,
        poseidon2_fri_circuit: Box<FriVerifierCircuit>,
    },
    Binary {
        statement: Box<SpanStatement>,
        left: &'a RootProofWire,
        right: &'a RootProofWire,
        statement_circuit: Box<StatementSemanticsCircuit>,
        vm_public_logup_circuit: Box<VmPublicLogupCircuit>,
        left_child: Box<PreparedRecursionChild>,
        right_child: Box<PreparedRecursionChild>,
    },
    Empty {
        statement: &'a SpanStatement,
        statement_circuit: Box<StatementSemanticsCircuit>,
        vm_public_logup_circuit: Box<VmPublicLogupCircuit>,
    },
}

impl UniversalAssemblyBranch<'_> {
    const fn proof_kind(&self) -> ProofKind {
        match self {
            Self::Segment { .. } => ProofKind::SegmentLeaf,
            Self::Binary { .. } => ProofKind::BinaryNode,
            Self::Empty { .. } => ProofKind::EmptyLeaf,
        }
    }

    const fn statement(&self) -> &SpanStatement {
        match self {
            Self::Segment { leaf, .. } => leaf.statement(),
            Self::Binary { statement, .. } => statement,
            Self::Empty { statement, .. } => statement,
        }
    }

    fn statement_circuit(&self) -> &StatementSemanticsCircuit {
        match self {
            Self::Segment {
                statement_circuit, ..
            }
            | Self::Binary {
                statement_circuit, ..
            }
            | Self::Empty {
                statement_circuit, ..
            } => statement_circuit.as_ref(),
        }
    }
}

struct FriRoutes {
    positions: Vec<Vec<M31Word>>,
    offsets: Vec<Vec<M31Word>>,
}

fn relation_challenge_words(
    execution: &VerifierTranscriptExecution<RecordingTranscriptBackend>,
    count: usize,
) -> Result<Vec<[M31Word; 8]>, UniversalWitnessError> {
    let mut challenges = vec![None; count];
    for operation in execution.operations() {
        let VerifierStep::DrawRelationChallenge { challenge } = operation.step() else {
            continue;
        };
        let index =
            usize::try_from(challenge).map_err(|error| stage("relation-challenge index", error))?;
        let slot = challenges
            .get_mut(index)
            .ok_or_else(|| stage("relation challenges", "challenge index is out of range"))?;
        if slot.is_some() {
            return Err(stage("relation challenges", "challenge draw is duplicated"));
        }
        *slot = operation.draw();
    }
    challenges
        .into_iter()
        .enumerate()
        .map(|(challenge, words)| {
            words.ok_or_else(|| {
                stage(
                    "relation challenges",
                    format_args!("challenge {challenge} is missing"),
                )
            })
        })
        .collect()
}

fn secure_draw_words(
    execution: &VerifierTranscriptExecution<RecordingTranscriptBackend>,
    step: VerifierStep,
    name: &'static str,
) -> Result<[M31Word; 4], UniversalWitnessError> {
    let draw = execution
        .operations()
        .iter()
        .find(|operation| operation.step() == step)
        .and_then(|operation| operation.draw())
        .ok_or_else(|| stage(name, "draw is missing"))?;
    Ok(draw[..4]
        .try_into()
        .expect("one transcript draw contains four secure-field limbs"))
}

fn fri_alpha_values(
    execution: &VerifierTranscriptExecution<RecordingTranscriptBackend>,
    layer_count: usize,
) -> Result<Vec<SecureField>, UniversalWitnessError> {
    (0..layer_count)
        .map(|layer| {
            let layer_u32 = u32::try_from(layer).map_err(|error| stage("FRI layer", error))?;
            secure_draw_words(
                execution,
                VerifierStep::DrawFriAlpha { layer: layer_u32 },
                "FRI alpha",
            )
            .map(secure_field_from_words)
        })
        .collect()
}

fn secure_field_from_words(words: [M31Word; 4]) -> SecureField {
    SecureField::from_m31_array(words.map(Into::into))
}

fn raw_query_words(
    execution: &VerifierTranscriptExecution<RecordingTranscriptBackend>,
    query_count: usize,
) -> Result<Vec<M31Word>, UniversalWitnessError> {
    let mut queries = vec![None; query_count];
    for operation in execution.operations() {
        let VerifierStep::DrawQueryBlock {
            first_query,
            query_count,
            ..
        } = operation.step()
        else {
            continue;
        };
        let draw = operation
            .draw()
            .ok_or_else(|| stage("raw queries", "query draw is missing"))?;
        for offset in 0..query_count {
            let query = first_query
                .checked_add(offset)
                .ok_or_else(|| stage("raw queries", "query index overflowed"))?;
            let query = usize::try_from(query).map_err(|error| stage("raw query index", error))?;
            let offset = usize::try_from(offset).map_err(|error| stage("query offset", error))?;
            let slot = queries
                .get_mut(query)
                .ok_or_else(|| stage("raw queries", "query index is out of range"))?;
            if slot.replace(draw[offset]).is_some() {
                return Err(stage("raw queries", "query slot is duplicated"));
            }
        }
    }
    queries
        .into_iter()
        .enumerate()
        .map(|(query, word)| {
            word.ok_or_else(|| stage("raw queries", format_args!("query {query} is missing")))
        })
        .collect()
}

fn fri_routes(
    preprocessed: &QueryPositionPreprocessed,
    verifier_id: u32,
    raw_queries: &[M31Word],
    layer_count: usize,
) -> Result<FriRoutes, UniversalWitnessError> {
    let mut positions = Vec::with_capacity(layer_count);
    let mut offsets = Vec::with_capacity(layer_count);
    for layer in 0..layer_count {
        let layer = u32::try_from(layer).map_err(|error| stage("FRI layer", error))?;
        let routes = raw_queries
            .iter()
            .copied()
            .enumerate()
            .map(|(query, raw)| {
                preprocessed
                    .evaluate_route(
                        verifier_id,
                        QueryPositionKind::FriFold,
                        layer,
                        u32::try_from(query).map_err(|error| stage("FRI query", error))?,
                        raw,
                    )
                    .map_err(|error| stage("FRI fold route", error))
            })
            .collect::<Result<Vec<_>, _>>()?;
        positions.push(
            routes
                .iter()
                .map(|(position, _)| M31Word::try_from(*position))
                .collect::<Result<Vec<_>, _>>()
                .map_err(|error| stage("FRI position", error))?,
        );
        offsets.push(
            routes
                .iter()
                .map(|(_, offset)| M31Word::try_from(*offset))
                .collect::<Result<Vec<_>, _>>()
                .map_err(|error| stage("FRI offset", error))?,
        );
    }
    Ok(FriRoutes { positions, offsets })
}

fn native_deep_answers(
    profile: &PcsDeepProfile,
    sampled_values: &[SecureField],
    queried_values: &[BaseField],
    oods_seed: [M31Word; 4],
    deep_randomness: [M31Word; 4],
    raw_queries: &[M31Word],
) -> Result<Vec<SecureField>, UniversalWitnessError> {
    let seed = SecureField::from_m31_array(oods_seed.map(stwo::core::fields::m31::M31::from));
    let square = seed.square();
    let inverse = (SecureField::one() + square).inverse();
    let oods = CirclePoint {
        x: (SecureField::one() - square) * inverse,
        y: (seed + seed) * inverse,
    };
    let mut sample = 0_usize;
    let samples = profile
        .sample_point_offsets()
        .iter()
        .map(|tree| {
            tree.iter()
                .map(|points| {
                    points
                        .iter()
                        .map(|offset| {
                            let value = sampled_values[sample];
                            sample += 1;
                            let offset = offset.to_point();
                            PointSample {
                                point: oods
                                    + CirclePoint {
                                        x: SecureField::from(offset.x),
                                        y: SecureField::from(offset.y),
                                    },
                                value,
                            }
                        })
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let mut value = 0_usize;
    let queried = profile
        .column_log_sizes()
        .iter()
        .map(|tree| {
            tree.iter()
                .map(|_| {
                    let end = value + profile.query_count();
                    let column = queried_values[value..end].to_vec();
                    value = end;
                    column
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let mask = (1_usize << profile.lifting_log_size()) - 1;
    let query_positions = raw_queries
        .iter()
        .map(|query| query.as_u32() as usize & mask)
        .collect::<Vec<_>>();
    fri_answers(
        TreeVec::new(profile.column_log_sizes().to_vec()),
        TreeVec::new(samples),
        SecureField::from_m31_array(deep_randomness.map(stwo::core::fields::m31::M31::from)),
        &query_positions,
        TreeVec::new(queried),
        profile.lifting_log_size(),
    )
    .map_err(|error| stage("native DEEP quotient", error))
}

fn last_layer_positions(
    preprocessed: &QueryPositionPreprocessed,
    verifier_id: u32,
    raw_queries: &[M31Word],
) -> Result<Vec<M31Word>, UniversalWitnessError> {
    raw_queries
        .iter()
        .copied()
        .enumerate()
        .map(|(query, raw)| {
            let (position, offset) = preprocessed
                .evaluate_route(
                    verifier_id,
                    QueryPositionKind::LastLayer,
                    0,
                    u32::try_from(query).map_err(|error| stage("last-layer query", error))?,
                    raw,
                )
                .map_err(|error| stage("last-layer route", error))?;
            if offset != 0 {
                return Err(stage("last-layer route", "offset must be zero"));
            }
            M31Word::try_from(position).map_err(|error| stage("last-layer position", error))
        })
        .collect()
}

fn push_pow_checks(
    table: &mut crate::pow::PowCheckTable,
    verifier_id: u32,
    plan: &VerifierControlPlan,
    trace: &TranscriptTrace,
) -> Result<(), UniversalWitnessError> {
    let kinds = plan.steps().iter().filter_map(|step| match step {
        VerifierStep::VerifyAndAbsorbInteractionPow { .. } => Some(PowKind::Interaction),
        VerifierStep::VerifyAndAbsorbPcsPow { .. } => Some(PowKind::Pcs),
        _ => None,
    });
    let kinds = kinds.collect::<Vec<_>>();
    if kinds.len() != trace.pow_checks.len() {
        return Err(stage(
            "PoW checks",
            format_args!(
                "control has {} checks, transcript has {}",
                kinds.len(),
                trace.pow_checks.len()
            ),
        ));
    }
    for (kind, check) in kinds.into_iter().zip(trace.pow_checks.iter().copied()) {
        crate::pow::push_pow_check(table, verifier_id, kind, check)
            .map_err(|error| stage("PoW check", error))?;
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn lower_all_fixed_circuits(
    traces: &mut CircuitTraces,
    proof_kind: ProofKind,
    statement: &StatementSemanticsCircuit,
    vm_claim: &VmPublicClaimSemanticsCircuit,
    vm_public_logup: &VmPublicLogupCircuit,
    segment_composition: [SegmentCompositionInputLane<'_>; 2],
    recursion_composition: [RecursionCompositionInputLane<'_>; 2],
    pcs: [PcsDeepCircuitLane<'_>; 4],
    fri: [FriVerifierCircuitLane<'_>; 4],
    stage_name: &'static str,
) -> Result<(), UniversalWitnessError> {
    crate::statement_semantics_lowering::lower_statement_semantics_circuit(
        traces,
        STATEMENT_CIRCUIT_ID,
        statement,
        statement,
    )
    .map_err(|error| stage(stage_name, error))?;
    if proof_kind == ProofKind::SegmentLeaf {
        crate::vm_public_claim_semantics_lowering::lower_vm_public_claim_semantics_circuit(
            traces,
            VM_CLAIM_CIRCUIT_ID,
            vm_claim,
            vm_claim,
        )
        .map_err(|error| stage(stage_name, error))?;
        crate::vm_public_logup_lowering::lower_vm_public_logup_circuit(
            traces,
            VM_PUBLIC_LOGUP_CIRCUIT_ID,
            vm_public_logup,
            vm_public_logup,
        )
        .map_err(|error| stage(stage_name, error))?;
        for lane in segment_composition {
            crate::vm_air_composition_lowering::lower_vm_air_composition_circuit(
                traces,
                lane.circuit_id,
                lane.circuit,
                lane.circuit,
            )
            .map_err(|error| stage(stage_name, error))?;
        }
    }
    if proof_kind == ProofKind::BinaryNode {
        for lane in recursion_composition {
            crate::recursion_air_composition_lowering::lower_recursion_air_composition_circuit(
                traces,
                lane.circuit_id,
                lane.circuit,
                lane.circuit,
            )
            .map_err(|error| stage(stage_name, error))?;
        }
    }
    let active_pcs = match proof_kind {
        ProofKind::SegmentLeaf => &pcs[..2],
        ProofKind::BinaryNode => &pcs[2..],
        ProofKind::EmptyLeaf => &pcs[..0],
    };
    for lane in active_pcs {
        crate::pcs_deep_lowering::lower_pcs_deep_circuit(
            traces,
            lane.circuit_id,
            lane.circuit,
            lane.circuit,
        )
        .map_err(|error| stage(stage_name, error))?;
    }
    let active_fri = match proof_kind {
        ProofKind::SegmentLeaf => &fri[..2],
        ProofKind::BinaryNode => &fri[2..],
        ProofKind::EmptyLeaf => &fri[..0],
    };
    for lane in active_fri {
        crate::fri_verifier_lowering::lower_fri_verifier_circuit(
            traces,
            lane.circuit_id,
            lane.circuit,
            lane.circuit,
        )
        .map_err(|error| stage(stage_name, error))?;
    }
    Ok(())
}

fn table_trace(
    trace: Option<UniversalTrace>,
    name: &'static str,
) -> Result<UniversalTrace, UniversalWitnessError> {
    trace.ok_or_else(|| stage(name, "table rows exceed the frozen capacity"))
}

fn pad_preprocessed_column(
    column: CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>,
    expected_log_size: u32,
    column_index: usize,
) -> Result<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>, UniversalWitnessError> {
    let actual_log_size = column.domain.log_size();
    if actual_log_size > expected_log_size {
        return Err(stage(
            "universal preprocessing capacity",
            format_args!(
                "column {column_index} needs log size {actual_log_size}, compiled capacity is {expected_log_size}"
            ),
        ));
    }
    if actual_log_size == expected_log_size {
        return Ok(column);
    }
    let mut values = column.values.into_cpu_vec();
    values.resize(1_usize << expected_log_size, BaseField::zero());
    Ok(CircleEvaluation::new(
        CanonicCoset::new(expected_log_size).circle_domain(),
        BaseColumn::from_cpu(&values),
    ))
}

fn ensure_trace_log_size(
    trace: &UniversalTrace,
    expected: u32,
    name: &'static str,
) -> Result<(), UniversalWitnessError> {
    for column in trace {
        let actual = column.domain.log_size();
        if actual != expected {
            return Err(stage(
                name,
                format_args!("trace log size is {actual}, expected {expected}"),
            ));
        }
    }
    Ok(())
}

fn ensure_universal_trace_layout(
    traces: &TreeVec<UniversalTrace>,
    expected: &TreeVec<Vec<u32>>,
) -> Result<(), UniversalWitnessError> {
    // STWO appends the composition tree during proving, so witness assembly
    // owns exactly the preprocessing, original, and interaction trees.
    if expected.len() != traces.len() + 1 {
        return Err(stage(
            "universal trace layout",
            format_args!(
                "program has {} trees while the witness owns {} pre-composition trees",
                expected.len(),
                traces.len(),
            ),
        ));
    }
    for (tree, (columns, expected_log_sizes)) in traces.iter().zip(expected.iter()).enumerate() {
        if columns.len() != expected_log_sizes.len() {
            return Err(stage(
                "universal trace layout",
                format_args!(
                    "tree {tree} has {} columns, expected {}",
                    columns.len(),
                    expected_log_sizes.len(),
                ),
            ));
        }
        for (column, (evaluation, expected_log_size)) in
            columns.iter().zip(expected_log_sizes).enumerate()
        {
            let actual_log_size = evaluation.domain.log_size();
            if actual_log_size != *expected_log_size {
                return Err(stage(
                    "universal trace layout",
                    format_args!(
                        "tree {tree} column {column} has log size {actual_log_size}, expected {expected_log_size}",
                    ),
                ));
            }
        }
    }
    Ok(())
}

pub(crate) fn finish_prepared_witness(
    preprocessing: &UniversalPreprocessing,
    main: UniversalMainWitness,
    relations: &UniversalRelations,
) -> Result<UniversalWitness, UniversalWitnessError> {
    let public_relation_sum =
        universal_public_relation_sum(preprocessing, &main.statement, main.proof_kind, relations)?;
    finalize_universal_witness(main, relations, public_relation_sum)
}

/// Computes every verifier-owned LogUp term for one universal public claim.
pub(crate) fn universal_public_relation_sum(
    preprocessing: &UniversalPreprocessing,
    statement: &SpanStatement,
    proof_kind: ProofKind,
    relations: &UniversalRelations,
) -> Result<SecureField, UniversalWitnessError> {
    let sum =
        crate::statement_input_air::public_statement_terms(statement, &relations.statement_input)
            .map_err(|error| stage("public statement terms", error))?;
    let _ = (preprocessing, proof_kind);
    Ok(sum)
}

fn generate_universal_interactions(
    main: &UniversalMainWitness,
    relations: &UniversalRelations,
) -> (
    [UniversalTrace; UNIVERSAL_COMPONENT_COUNT],
    [SecureField; UNIVERSAL_COMPONENT_COUNT],
) {
    let proof_kind = main.proof_kind;
    let preprocessed_components = &main.preprocessed_components;
    let original_components = &main.original_components;
    let mut interaction_components: [UniversalTrace; UNIVERSAL_COMPONENT_COUNT] =
        core::array::from_fn(|_| Vec::new());
    let mut claimed_sums = [SecureField::zero(); UNIVERSAL_COMPONENT_COUNT];

    (interaction_components[0], claimed_sums[0]) = crate::control_air::gen_interaction_trace(
        &preprocessed_components[0],
        proof_kind,
        &relations.control,
    );
    (interaction_components[1], claimed_sums[1]) = crate::transcript_air::gen_interaction_trace(
        &original_components[1],
        &relations.vm,
        &relations.transcript,
    );
    (interaction_components[2], claimed_sums[2]) =
        crate::transcript_binding_air::gen_interaction_trace(
            &original_components[2],
            &preprocessed_components[2],
            proof_kind,
            &relations.control,
            &relations.transcript,
            &relations.transcript_binding,
        );
    (interaction_components[3], claimed_sums[3]) =
        crate::transcript_state_air::gen_interaction_trace(
            &original_components[3],
            &preprocessed_components[3],
            proof_kind,
            &relations.transcript_binding,
            &relations.transcript_state,
        );
    (interaction_components[4], claimed_sums[4]) =
        crate::transcript_word_air::gen_interaction_trace(
            &original_components[4],
            &preprocessed_components[4],
            proof_kind,
            &relations.transcript_binding,
            &relations.transcript_word,
        );
    (interaction_components[5], claimed_sums[5]) =
        crate::transcript_payload_air::gen_interaction_trace(
            &original_components[5],
            &preprocessed_components[5],
            proof_kind,
            &relations.transcript_word,
            &relations.verifier_input,
        );
    (interaction_components[6], claimed_sums[6]) =
        crate::pow::gen_interaction_trace(&original_components[6], &relations.pow);
    (interaction_components[7], claimed_sums[7]) = crate::pow::gen_frame_interaction_trace(
        &original_components[7],
        &relations.pow,
        &relations.transcript_binding,
    );
    (interaction_components[8], claimed_sums[8]) =
        crate::relation_challenge_air::gen_interaction_trace(
            &original_components[8],
            &preprocessed_components[8],
            proof_kind,
            &relations.transcript_state,
            &relations.relation_challenge,
        );
    (interaction_components[9], claimed_sums[9]) =
        crate::verifier_randomness_air::gen_interaction_trace(
            &original_components[9],
            &preprocessed_components[9],
            proof_kind,
            &relations.transcript_state,
            &relations.verifier_randomness,
        );
    (interaction_components[10], claimed_sums[10]) =
        crate::statement_input_air::gen_interaction_trace(
            &original_components[10],
            &preprocessed_components[10],
            proof_kind,
            &relations.verifier_input,
            &relations.statement_input,
        );
    (interaction_components[11], claimed_sums[11]) =
        crate::statement_semantics_input_air::gen_interaction_trace(
            &original_components[11],
            &preprocessed_components[11],
            proof_kind,
            &relations.statement_input,
            &relations.recursion,
            &relations.vm,
        );
    (interaction_components[12], claimed_sums[12]) =
        crate::vm_public_claim_input_air::gen_interaction_trace(
            &original_components[12],
            &preprocessed_components[12],
            proof_kind,
            &relations.vm_public_claim_input,
            &relations.vm,
        );
    (interaction_components[13], claimed_sums[13]) =
        crate::vm_public_claim_hash_air::gen_interaction_trace(
            &original_components[13],
            &preprocessed_components[13],
            proof_kind,
            &relations.vm,
            &relations.vm_public_claim_input,
            &relations.vm_public_claim_hash,
            &relations.verifier_input,
        );
    (interaction_components[14], claimed_sums[14]) =
        crate::vm_public_io_hash_air::gen_interaction_trace(
            &original_components[14],
            &preprocessed_components[14],
            proof_kind,
            &relations.vm,
            &relations.vm_public_claim_input,
            &relations.vm_public_io_hash,
        );
    (interaction_components[15], claimed_sums[15]) =
        crate::vm_public_claim_semantics_input_air::gen_interaction_trace(
            &original_components[15],
            &preprocessed_components[15],
            proof_kind,
            &relations.vm_public_claim_input,
            &relations.statement_input,
            &relations.recursion,
            &relations.vm_public_io_hash,
        );
    (interaction_components[16], claimed_sums[16]) =
        crate::vm_public_logup_input_air::gen_interaction_trace(
            &original_components[16],
            &preprocessed_components[16],
            proof_kind,
            &relations.vm_public_claim_input,
            &relations.relation_challenge,
            &relations.verifier_input,
            &relations.recursion,
        );
    (interaction_components[17], claimed_sums[17]) =
        crate::vm_public_logup_control_air::gen_interaction_trace(
            &original_components[17],
            &preprocessed_components[17],
            proof_kind,
            &relations.control,
            &relations.verifier_input,
            &relations.verifier_randomness,
        );
    (interaction_components[18], claimed_sums[18]) =
        crate::vm_air_composition_input_air::gen_interaction_trace(
            &original_components[18],
            &preprocessed_components[18],
            proof_kind,
            &relations.relation_challenge,
            &relations.verifier_input,
            &relations.verifier_randomness,
            &relations.statement_input,
            &relations.recursion,
        );
    (interaction_components[19], claimed_sums[19]) =
        crate::vm_air_composition_control_air::gen_interaction_trace(
            &preprocessed_components[19],
            proof_kind,
            &relations.control,
        );
    (interaction_components[20], claimed_sums[20]) =
        crate::query_position_air::gen_bits_interaction_trace(
            &original_components[20],
            &preprocessed_components[20],
            proof_kind,
            &relations.verifier_randomness,
            &relations.query_position,
        );
    (interaction_components[21], claimed_sums[21]) =
        crate::query_position_air::gen_mapping_interaction_trace(
            &original_components[21],
            &preprocessed_components[21],
            proof_kind,
            &relations.query_position,
        );
    (interaction_components[22], claimed_sums[22]) = crate::merkle_root_air::gen_interaction_trace(
        &original_components[22],
        &preprocessed_components[22],
        proof_kind,
        &relations.verifier_input,
        &relations.recursion,
    );
    (interaction_components[23], claimed_sums[23]) = crate::trace_merkle_air::gen_interaction_trace(
        &original_components[23],
        &preprocessed_components[23],
        proof_kind,
        &relations.vm,
        &relations.control,
        &relations.query_position,
        &relations.trace_merkle,
        &relations.recursion,
    );
    (interaction_components[24], claimed_sums[24]) =
        crate::pcs_deep_input_air::gen_interaction_trace(
            &original_components[24],
            &preprocessed_components[24],
            proof_kind,
            &relations.verifier_input,
            &relations.trace_merkle,
            &relations.verifier_randomness,
            &relations.query_position,
            &relations.pcs_deep,
            &relations.recursion,
        );
    (interaction_components[25], claimed_sums[25]) =
        crate::fri_merkle_air::gen_leaf_interaction_trace(
            &original_components[25],
            &preprocessed_components[25],
            proof_kind,
            &relations.vm,
            &relations.fri_merkle,
            &relations.recursion,
        );
    (interaction_components[26], claimed_sums[26]) =
        crate::fri_merkle_air::gen_node_interaction_trace(
            &original_components[26],
            &preprocessed_components[26],
            proof_kind,
            &relations.vm,
            &relations.fri_merkle,
            &relations.recursion,
        );
    (interaction_components[27], claimed_sums[27]) =
        crate::fri_merkle_air::gen_anchor_interaction_trace(
            &original_components[27],
            &preprocessed_components[27],
            proof_kind,
            &relations.control,
            &relations.query_position,
            &relations.fri_merkle,
            &relations.recursion,
        );
    (interaction_components[28], claimed_sums[28]) =
        crate::fri_verifier_control_air::gen_interaction_trace(
            &original_components[28],
            &preprocessed_components[28],
            proof_kind,
            &relations.control,
            &relations.query_position,
            &relations.fri_verifier_route,
        );
    (interaction_components[29], claimed_sums[29]) =
        crate::fri_verifier_input_air::gen_interaction_trace(
            &original_components[29],
            &preprocessed_components[29],
            proof_kind,
            &relations.verifier_input,
            &relations.verifier_randomness,
            &relations.query_position,
            &relations.pcs_deep,
            &relations.fri_merkle,
            &relations.fri_verifier_route,
            &relations.recursion,
        );
    (interaction_components[30], claimed_sums[30]) = qm31_mul::gen_interaction_trace(
        &original_components[30],
        &preprocessed_components[30],
        proof_kind,
        &relations.recursion,
    );
    (interaction_components[31], claimed_sums[31]) = qm31_inv::gen_interaction_trace(
        &original_components[31],
        &preprocessed_components[31],
        proof_kind,
        &relations.recursion,
    );
    (interaction_components[32], claimed_sums[32]) = linear_ops::gen_interaction_trace(
        &original_components[32],
        &preprocessed_components[32],
        proof_kind,
        &relations.recursion,
    );
    (interaction_components[33], claimed_sums[33]) = merkle_path::gen_interaction_trace(
        &original_components[33],
        &relations.vm,
        &relations.recursion,
    );
    (interaction_components[34], claimed_sums[34]) =
        air::poseidon2::component::witness::gen_interaction_trace(
            &original_components[34],
            &relations.vm,
        );
    (interaction_components[35], claimed_sums[35]) =
        prover::components::lookups::range_check_8_8::witness::gen_interaction_trace(
            &original_components[35],
            &relations.vm,
        );

    (interaction_components, claimed_sums)
}

fn finalize_universal_witness(
    main: UniversalMainWitness,
    relations: &UniversalRelations,
    public_relation_sum: SecureField,
) -> Result<UniversalWitness, UniversalWitnessError> {
    let (interaction_components, claimed_sums) = generate_universal_interactions(&main, relations);
    let global_relation_sum =
        claimed_sums.iter().copied().sum::<SecureField>() + public_relation_sum;
    if !global_relation_sum.is_zero() {
        return Err(stage(
            "universal relation closure",
            format_args!(
                "global LogUp sum is nonzero: {global_relation_sum:?}; public={public_relation_sum:?}; components={claimed_sums:?}"
            ),
        ));
    }
    let UniversalMainWitness {
        proof_kind,
        statement: _,
        preprocessed_components,
        original_components,
        component_log_sizes,
        expected_column_log_sizes,
    } = main;

    for (component, trace) in interaction_components.iter().enumerate() {
        ensure_trace_log_size(
            trace,
            component_log_sizes[component],
            "universal interaction trace",
        )?;
    }

    let preprocessing_ids = universal_preprocessed_column_ids(&component_log_sizes);
    let preprocessed_trace = preprocessed_components
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();
    if preprocessing_ids.len() != preprocessed_trace.len() {
        return Err(stage(
            "universal preprocessing",
            format_args!(
                "{} identifiers describe {} columns",
                preprocessing_ids.len(),
                preprocessed_trace.len()
            ),
        ));
    }
    let original_trace = original_components
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();
    let interaction_trace = interaction_components
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();
    let traces = TreeVec::new(vec![preprocessed_trace, original_trace, interaction_trace]);
    ensure_universal_trace_layout(&traces, &expected_column_log_sizes)?;
    let witness = UniversalWitness {
        proof_kind,
        traces,
        claimed_sums,
        public_relation_sum,
        component_log_sizes,
        preprocessing_ids,
    };
    Ok(witness)
}

fn assemble_universal_components(
    profile: &FrozenProtocolProfile,
    preprocessing: &UniversalPreprocessing,
    component_log_sizes: UniversalComponentLogSizes,
    branch: UniversalAssemblyBranch<'_>,
) -> Result<UniversalMainWitness, UniversalWitnessError> {
    let proof_kind = branch.proof_kind();
    let statement = branch.statement();
    let statement_circuit = branch.statement_circuit();
    let transcript_witness = match &branch {
        UniversalAssemblyBranch::Segment {
            vm_transcript,
            poseidon2_transcript,
            ..
        } => UniversalTranscriptWitness::Segment {
            vm: vm_transcript,
            poseidon2: poseidon2_transcript,
        },
        UniversalAssemblyBranch::Binary {
            left_child,
            right_child,
            ..
        } => UniversalTranscriptWitness::Binary {
            left: &left_child.transcript,
            right: &right_child.transcript,
        },
        UniversalAssemblyBranch::Empty { .. } => UniversalTranscriptWitness::Empty,
    };
    let transcript_lanes = match &branch {
        UniversalAssemblyBranch::Segment {
            vm_transcript,
            poseidon2_transcript,
            ..
        } => vec![
            (
                SEGMENT_VERIFIER_ID,
                profile.vm_plan(),
                vm_transcript.backend().trace(),
            ),
            (
                POSEIDON2_VERIFIER_ID,
                profile.poseidon2_plan(),
                poseidon2_transcript.backend().trace(),
            ),
        ],
        UniversalAssemblyBranch::Binary {
            left_child,
            right_child,
            ..
        } => vec![
            (
                LEFT_RECURSION_VERIFIER_ID,
                profile.recursion_plan(),
                left_child.transcript.backend().trace(),
            ),
            (
                RIGHT_RECURSION_VERIFIER_ID,
                profile.recursion_plan(),
                right_child.transcript.backend().trace(),
            ),
        ],
        UniversalAssemblyBranch::Empty { .. } => Vec::new(),
    };
    let mut poseidon2 = Poseidon2Table::new();
    let mut original_components: [UniversalTrace; UNIVERSAL_COMPONENT_COUNT] =
        core::array::from_fn(|_| Vec::new());

    let mut transcript_table = crate::transcript_air::TranscriptHashCallTable::new();
    for (verifier_id, _, transcript_trace) in &transcript_lanes {
        crate::transcript_air::push_transcript_calls(
            &mut transcript_table,
            &mut poseidon2,
            *verifier_id,
            transcript_trace,
        )
        .map_err(|error| stage("transcript hash calls", error))?;
    }

    let mut binding_table = crate::transcript_binding_air::TranscriptCallBindingTable::new();
    crate::transcript_binding_air::push_call_bindings(
        &mut binding_table,
        &preprocessing.transcript_calls,
        transcript_witness,
    )
    .map_err(|error| stage("transcript call bindings", error))?;
    let mut state_table = crate::transcript_state_air::TranscriptFrameStateTable::new();
    crate::transcript_state_air::push_frame_states(
        &mut state_table,
        &preprocessing.transcript_state,
        transcript_witness,
    )
    .map_err(|error| stage("transcript frame states", error))?;
    let mut word_table = crate::transcript_word_air::TranscriptWordTable::new();
    crate::transcript_word_air::push_transcript_words(
        &mut word_table,
        &preprocessing.transcript_word,
        transcript_witness,
    )
    .map_err(|error| stage("transcript words", error))?;
    let mut payload_table = crate::transcript_payload_air::TranscriptPayloadTable::new();
    crate::transcript_payload_air::push_transcript_payloads(
        &mut payload_table,
        &preprocessing.transcript_payload,
        transcript_witness,
    )
    .map_err(|error| stage("transcript payloads", error))?;

    let mut pow_table = crate::pow::PowCheckTable::new();
    let mut pow_frame_table = crate::pow::PowFrameTable::new();
    for (verifier_id, plan, transcript_trace) in &transcript_lanes {
        push_pow_checks(&mut pow_table, *verifier_id, plan, transcript_trace)?;
        crate::pow::push_pow_frames(&mut pow_frame_table, *verifier_id, plan, transcript_trace)
            .map_err(|error| stage("PoW frames", error))?;
    }

    let mut challenge_table = crate::relation_challenge_air::RelationChallengeTable::new();
    crate::relation_challenge_air::push_relation_challenges(
        &mut challenge_table,
        &preprocessing.relation_challenge,
        transcript_witness,
    )
    .map_err(|error| stage("relation challenges", error))?;
    let mut randomness_table = crate::verifier_randomness_air::VerifierRandomnessTable::new();
    crate::verifier_randomness_air::push_verifier_randomness(
        &mut randomness_table,
        &preprocessing.verifier_randomness,
        transcript_witness,
    )
    .map_err(|error| stage("verifier randomness", error))?;

    let mut statement_table = crate::statement_input_air::StatementInputTable::new();
    crate::statement_input_air::push_statement_inputs(
        &mut statement_table,
        &preprocessing.statement_input,
        match &branch {
            UniversalAssemblyBranch::Segment { leaf, .. } => {
                StatementInputWitness::Segment(leaf.statement())
            }
            UniversalAssemblyBranch::Binary { left, right, .. } => StatementInputWitness::Binary {
                left: left.statement(),
                right: right.statement(),
            },
            UniversalAssemblyBranch::Empty { .. } => StatementInputWitness::Empty,
        },
    )
    .map_err(|error| stage("statement inputs", error))?;
    let mut statement_semantics_table =
        crate::statement_semantics_input_air::StatementSemanticsInputTable::new();
    crate::statement_semantics_input_air::push_statement_semantics_inputs(
        &mut statement_semantics_table,
        &preprocessing.statement_semantics,
        statement_circuit,
        proof_kind,
    )
    .map_err(|error| stage("statement-semantic inputs", error))?;

    let zero_claim = vec![M31Word::ZERO; profile.public_claim_shape().claim_word_count()];
    let claim_words: &[M31Word] = match &branch {
        UniversalAssemblyBranch::Segment { leaf, .. } => &leaf.public_claim_words()[..],
        UniversalAssemblyBranch::Binary { .. } | UniversalAssemblyBranch::Empty { .. } => {
            &zero_claim
        }
    };
    let mut claim_table = crate::vm_public_claim_input_air::VmPublicClaimInputTable::new();
    crate::vm_public_claim_input_air::push_vm_public_claim_word_inputs(
        &mut claim_table,
        &preprocessing.vm_claim_input,
        proof_kind,
        claim_words,
    )
    .map_err(|error| stage("VM public-claim inputs", error))?;
    let mut claim_hash_table = crate::vm_public_claim_hash_air::VmPublicClaimHashTable::new();
    crate::vm_public_claim_hash_air::push_vm_public_claim_word_hash(
        &mut claim_hash_table,
        &mut poseidon2,
        &preprocessing.vm_claim_hash,
        proof_kind,
        claim_words,
    )
    .map_err(|error| stage("VM public-claim hash", error))?;
    let mut io_hash_table = crate::vm_public_io_hash_air::VmPublicIoHashTable::new();
    crate::vm_public_io_hash_air::push_vm_public_io_word_hashes(
        &mut io_hash_table,
        &mut poseidon2,
        &preprocessing.vm_io_hash,
        proof_kind,
        claim_words,
    )
    .map_err(|error| stage("VM public-IO hashes", error))?;
    let mut claim_semantics_table =
        crate::vm_public_claim_semantics_input_air::VmPublicClaimSemanticsInputTable::new();
    crate::vm_public_claim_semantics_input_air::push_vm_public_claim_semantics_inputs(
        &mut claim_semantics_table,
        &preprocessing.vm_claim_semantics,
        &preprocessing.vm_claim_reference,
        match &branch {
            UniversalAssemblyBranch::Segment {
                vm_claim_circuit, ..
            } => vm_claim_circuit,
            UniversalAssemblyBranch::Binary { .. } | UniversalAssemblyBranch::Empty { .. } => {
                &preprocessing.vm_claim_reference
            }
        },
        proof_kind,
    )
    .map_err(|error| stage("VM claim-semantic inputs", error))?;
    let mut public_logup_table = crate::vm_public_logup_input_air::VmPublicLogupInputTable::new();
    crate::vm_public_logup_input_air::push_vm_public_logup_inputs(
        &mut public_logup_table,
        &preprocessing.vm_public_logup_input,
        &preprocessing.vm_public_logup_reference,
        match &branch {
            UniversalAssemblyBranch::Segment {
                vm_public_logup_circuit,
                ..
            } => vm_public_logup_circuit,
            UniversalAssemblyBranch::Binary {
                vm_public_logup_circuit,
                ..
            } => vm_public_logup_circuit,
            UniversalAssemblyBranch::Empty {
                vm_public_logup_circuit,
                ..
            } => vm_public_logup_circuit,
        },
        proof_kind,
    )
    .map_err(|error| stage("VM public-LogUp inputs", error))?;
    let mut public_logup_control_table =
        crate::vm_public_logup_control_air::VmPublicLogupControlTable::new();
    let segment_joint_binding = match &branch {
        UniversalAssemblyBranch::Segment {
            leaf,
            interaction_seeds,
            ..
        } => Some(
            crate::vm_public_logup_control_air::SegmentJointBindingWitness {
                interaction_seeds: *interaction_seeds,
                interaction_pow: leaf.proof().interaction_pow,
                shared_relation_sum: SecureField::from(leaf.shared_relation_sum()),
                poseidon2_claimed_sum: SecureField::from(leaf.poseidon2_proof().claimed_sums[0]),
            },
        ),
        UniversalAssemblyBranch::Binary { .. } | UniversalAssemblyBranch::Empty { .. } => None,
    };
    crate::vm_public_logup_control_air::push_vm_public_logup_control(
        &mut public_logup_control_table,
        &preprocessing.vm_public_logup_control,
        proof_kind,
        segment_joint_binding,
    )
    .map_err(|error| stage("public-LogUp control and segment binding", error))?;
    let mut composition_table =
        crate::vm_air_composition_input_air::VmAirCompositionInputTable::new();
    let recursion_references = preprocessing.recursion_composition_references.lanes();
    let recursion_witnesses = match &branch {
        UniversalAssemblyBranch::Binary {
            left_child,
            right_child,
            ..
        } => [
            left_child.composition_lane(),
            right_child.composition_lane(),
        ],
        UniversalAssemblyBranch::Segment { .. } | UniversalAssemblyBranch::Empty { .. } => {
            recursion_references
        }
    };
    let segment_references = [
        SegmentCompositionInputLane {
            verifier_id: SEGMENT_VERIFIER_ID,
            circuit_id: VM_COMPOSITION_CIRCUIT_ID,
            circuit: &preprocessing.vm_composition_reference,
        },
        SegmentCompositionInputLane {
            verifier_id: POSEIDON2_VERIFIER_ID,
            circuit_id: POSEIDON2_COMPOSITION_CIRCUIT_ID,
            circuit: &preprocessing.poseidon2_composition_reference,
        },
    ];
    let segment_witnesses = match &branch {
        UniversalAssemblyBranch::Segment {
            vm_composition_circuit,
            poseidon2_composition_circuit,
            ..
        } => [
            SegmentCompositionInputLane {
                verifier_id: SEGMENT_VERIFIER_ID,
                circuit_id: VM_COMPOSITION_CIRCUIT_ID,
                circuit: vm_composition_circuit,
            },
            SegmentCompositionInputLane {
                verifier_id: POSEIDON2_VERIFIER_ID,
                circuit_id: POSEIDON2_COMPOSITION_CIRCUIT_ID,
                circuit: poseidon2_composition_circuit,
            },
        ],
        UniversalAssemblyBranch::Binary { .. } | UniversalAssemblyBranch::Empty { .. } => {
            segment_references
        }
    };
    crate::vm_air_composition_input_air::push_segment_air_composition_inputs(
        &mut composition_table,
        &preprocessing.vm_composition_input,
        &segment_references,
        &segment_witnesses,
        &recursion_references,
        &recursion_witnesses,
        proof_kind,
    )
    .map_err(|error| stage("segment AIR-composition inputs", error))?;

    let mut query_bits_table = crate::query_position_air::QueryBitsTable::new();
    let mut query_mapping_table = crate::query_position_air::QueryMappingTable::new();
    crate::query_position_air::push_query_positions(
        &mut query_bits_table,
        &mut query_mapping_table,
        &preprocessing.query_position,
        match &branch {
            UniversalAssemblyBranch::Segment {
                raw_queries,
                poseidon2_raw_queries,
                ..
            } => UniversalRawQueryWitness::Segment {
                vm: raw_queries,
                poseidon2: poseidon2_raw_queries,
            },
            UniversalAssemblyBranch::Binary {
                left_child,
                right_child,
                ..
            } => UniversalRawQueryWitness::Binary {
                left: &left_child.raw_queries,
                right: &right_child.raw_queries,
            },
            UniversalAssemblyBranch::Empty { .. } => UniversalRawQueryWitness::Empty,
        },
    )
    .map_err(|error| stage("query positions", error))?;

    let (left_fri_commitments, poseidon2_fri_commitments, right_fri_commitments) = match &branch {
        UniversalAssemblyBranch::Segment {
            leaf, fri_opening, ..
        } => (
            fri_opening
                .layers
                .iter()
                .map(|layer| layer.commitment)
                .collect::<Vec<_>>(),
            leaf.poseidon2_proof()
                .fri_layers
                .iter()
                .map(|layer| layer.commitment())
                .collect::<Vec<_>>(),
            Vec::new(),
        ),
        UniversalAssemblyBranch::Binary {
            left_child,
            right_child,
            ..
        } => (
            left_child
                .fri_opening
                .layers
                .iter()
                .map(|layer| layer.commitment)
                .collect(),
            Vec::new(),
            right_child
                .fri_opening
                .layers
                .iter()
                .map(|layer| layer.commitment)
                .collect(),
        ),
        UniversalAssemblyBranch::Empty { .. } => (Vec::new(), Vec::new(), Vec::new()),
    };
    let mut merkle_root_table = crate::merkle_root_air::MerkleRootTable::new();
    crate::merkle_root_air::push_merkle_roots(
        &mut merkle_root_table,
        &preprocessing.merkle_root,
        match &branch {
            UniversalAssemblyBranch::Segment { leaf, .. } => {
                crate::merkle_root_air::UniversalMerkleRootWitness::Segment {
                    vm: crate::merkle_root_air::MerkleRootSet {
                        trace: &leaf.proof().commitments,
                        fri: &left_fri_commitments,
                    },
                    poseidon2: crate::merkle_root_air::MerkleRootSet {
                        trace: &leaf.poseidon2_proof().commitments,
                        fri: &poseidon2_fri_commitments,
                    },
                }
            }
            UniversalAssemblyBranch::Binary { left, right, .. } => {
                crate::merkle_root_air::UniversalMerkleRootWitness::Binary {
                    left: crate::merkle_root_air::MerkleRootSet {
                        trace: &left.stark().commitments,
                        fri: &left_fri_commitments,
                    },
                    right: crate::merkle_root_air::MerkleRootSet {
                        trace: &right.stark().commitments,
                        fri: &right_fri_commitments,
                    },
                }
            }
            UniversalAssemblyBranch::Empty { .. } => {
                crate::merkle_root_air::UniversalMerkleRootWitness::Empty
            }
        },
    )
    .map_err(|error| stage("Merkle roots", error))?;

    let mut trace_merkle_table = crate::trace_merkle_air::TraceMerkleLeafTable::new();
    let trace_claims = crate::trace_merkle_air::push_trace_merkle_leaves(
        &mut trace_merkle_table,
        &mut poseidon2,
        &preprocessing.trace_merkle,
        &preprocessing.query_position,
        match &branch {
            UniversalAssemblyBranch::Segment {
                leaf,
                raw_queries,
                poseidon2_raw_queries,
                ..
            } => UniversalTraceOpeningWitness::Segment {
                vm: TraceOpeningSet {
                    queried_values: &leaf.proof().queried_values[..],
                    raw_queries,
                },
                poseidon2: TraceOpeningSet {
                    queried_values: &leaf.poseidon2_proof().queried_values[..],
                    raw_queries: poseidon2_raw_queries,
                },
            },
            UniversalAssemblyBranch::Binary {
                left,
                right,
                left_child,
                right_child,
                ..
            } => UniversalTraceOpeningWitness::Binary {
                left: TraceOpeningSet {
                    queried_values: &left.stark().queried_values[..],
                    raw_queries: &left_child.raw_queries,
                },
                right: TraceOpeningSet {
                    queried_values: &right.stark().queried_values[..],
                    raw_queries: &right_child.raw_queries,
                },
            },
            UniversalAssemblyBranch::Empty { .. } => UniversalTraceOpeningWitness::Empty,
        },
    )
    .map_err(|error| stage("trace Merkle leaves", error))?;
    let segment_trace_paths = match &branch {
        UniversalAssemblyBranch::Segment { leaf, .. } => leaf
            .proof()
            .trace_paths
            .iter()
            .map(widen_merkle_path)
            .collect::<Result<Vec<_>, _>>()?,
        UniversalAssemblyBranch::Binary { .. } | UniversalAssemblyBranch::Empty { .. } => {
            Vec::new()
        }
    };
    let poseidon2_trace_paths = match &branch {
        UniversalAssemblyBranch::Segment { leaf, .. } => leaf
            .poseidon2_proof()
            .trace_paths
            .iter()
            .map(widen_merkle_path)
            .collect::<Result<Vec<_>, _>>()?,
        UniversalAssemblyBranch::Binary { .. } | UniversalAssemblyBranch::Empty { .. } => {
            Vec::new()
        }
    };
    let mut merkle_path_table = merkle_path::MerklePathTable::new();
    crate::trace_merkle_air::push_trace_merkle_paths(
        &mut merkle_path_table,
        &mut poseidon2,
        &trace_claims,
        match &branch {
            UniversalAssemblyBranch::Segment { leaf, .. } => UniversalTracePathWitness::Segment {
                vm: TracePathSet {
                    roots: &leaf.proof().commitments,
                    paths: &segment_trace_paths,
                },
                poseidon2: TracePathSet {
                    roots: &leaf.poseidon2_proof().commitments,
                    paths: &poseidon2_trace_paths,
                },
            },
            UniversalAssemblyBranch::Binary { left, right, .. } => {
                UniversalTracePathWitness::Binary {
                    left: TracePathSet {
                        roots: &left.stark().commitments,
                        paths: &left.stark().trace_paths[..],
                    },
                    right: TracePathSet {
                        roots: &right.stark().commitments,
                        paths: &right.stark().trace_paths[..],
                    },
                }
            }
            UniversalAssemblyBranch::Empty { .. } => UniversalTracePathWitness::Empty,
        },
    )
    .map_err(|error| stage("trace Merkle paths", error))?;

    let pcs_references = preprocessing.pcs_references.lanes();
    let pcs_witnesses = match &branch {
        UniversalAssemblyBranch::Segment {
            pcs_circuit,
            poseidon2_pcs_circuit,
            ..
        } => [
            PcsDeepCircuitLane {
                verifier_id: SEGMENT_VERIFIER_ID,
                circuit_id: PCS_CIRCUIT_IDS[0],
                circuit: pcs_circuit,
            },
            PcsDeepCircuitLane {
                verifier_id: POSEIDON2_VERIFIER_ID,
                circuit_id: PCS_CIRCUIT_IDS[1],
                circuit: poseidon2_pcs_circuit,
            },
            pcs_references[2],
            pcs_references[3],
        ],
        UniversalAssemblyBranch::Binary {
            left_child,
            right_child,
            ..
        } => [
            pcs_references[0],
            pcs_references[1],
            PcsDeepCircuitLane {
                verifier_id: LEFT_RECURSION_VERIFIER_ID,
                circuit_id: PCS_CIRCUIT_IDS[2],
                circuit: &left_child.pcs_circuit,
            },
            PcsDeepCircuitLane {
                verifier_id: RIGHT_RECURSION_VERIFIER_ID,
                circuit_id: PCS_CIRCUIT_IDS[3],
                circuit: &right_child.pcs_circuit,
            },
        ],
        UniversalAssemblyBranch::Empty { .. } => pcs_references,
    };
    let mut pcs_input_table = crate::pcs_deep_input_air::PcsDeepInputTable::new();
    crate::pcs_deep_input_air::push_pcs_deep_inputs(
        &mut pcs_input_table,
        &preprocessing.pcs_input,
        pcs_references,
        pcs_witnesses,
        proof_kind,
    )
    .map_err(|error| stage("PCS DEEP inputs", error))?;

    let mut fri_leaf_table = crate::fri_merkle_air::FriMerkleLeafTable::new();
    let mut fri_node_table = crate::fri_merkle_air::FriMerkleNodeTable::new();
    let mut fri_anchor_table = crate::fri_merkle_air::FriMerkleAnchorTable::new();
    crate::fri_merkle_air::push_fri_merkle_authentication(
        &mut fri_leaf_table,
        &mut fri_node_table,
        &mut fri_anchor_table,
        &mut merkle_path_table,
        &mut poseidon2,
        &preprocessing.fri_merkle,
        &preprocessing.query_position,
        match &branch {
            UniversalAssemblyBranch::Segment {
                fri_opening,
                poseidon2_fri_opening,
                ..
            } => UniversalFriMerkleWitness::Segment {
                vm: fri_opening,
                poseidon2: poseidon2_fri_opening,
            },
            UniversalAssemblyBranch::Binary {
                left_child,
                right_child,
                ..
            } => UniversalFriMerkleWitness::Binary {
                left: &left_child.fri_opening,
                right: &right_child.fri_opening,
            },
            UniversalAssemblyBranch::Empty { .. } => UniversalFriMerkleWitness::Empty,
        },
    )
    .map_err(|error| stage("FRI Merkle authentication", error))?;

    let inactive_vm_queries = vec![M31Word::ZERO; preprocessing.query_position.vm_query_count()];
    let inactive_poseidon2_queries =
        vec![M31Word::ZERO; preprocessing.query_position.poseidon2_query_count()];
    let inactive_recursion_queries =
        vec![M31Word::ZERO; preprocessing.query_position.recursion_query_count()];
    let query_lanes =
        [
            FriVerifierQueryLane {
                verifier_id: SEGMENT_VERIFIER_ID,
                raw_queries: match &branch {
                    UniversalAssemblyBranch::Segment { raw_queries, .. } => raw_queries,
                    UniversalAssemblyBranch::Binary { .. }
                    | UniversalAssemblyBranch::Empty { .. } => &inactive_vm_queries,
                },
            },
            FriVerifierQueryLane {
                verifier_id: POSEIDON2_VERIFIER_ID,
                raw_queries: match &branch {
                    UniversalAssemblyBranch::Segment {
                        poseidon2_raw_queries,
                        ..
                    } => poseidon2_raw_queries,
                    UniversalAssemblyBranch::Binary { .. }
                    | UniversalAssemblyBranch::Empty { .. } => &inactive_poseidon2_queries,
                },
            },
            FriVerifierQueryLane {
                verifier_id: LEFT_RECURSION_VERIFIER_ID,
                raw_queries: match &branch {
                    UniversalAssemblyBranch::Binary { left_child, .. } => &left_child.raw_queries,
                    UniversalAssemblyBranch::Segment { .. }
                    | UniversalAssemblyBranch::Empty { .. } => &inactive_recursion_queries,
                },
            },
            FriVerifierQueryLane {
                verifier_id: RIGHT_RECURSION_VERIFIER_ID,
                raw_queries: match &branch {
                    UniversalAssemblyBranch::Binary { right_child, .. } => &right_child.raw_queries,
                    UniversalAssemblyBranch::Segment { .. }
                    | UniversalAssemblyBranch::Empty { .. } => &inactive_recursion_queries,
                },
            },
        ];
    let mut fri_control_table = crate::fri_verifier_control_air::FriVerifierControlTable::new();
    crate::fri_verifier_control_air::push_fri_verifier_control(
        &mut fri_control_table,
        &preprocessing.fri_control,
        &preprocessing.query_position,
        query_lanes,
        proof_kind,
    )
    .map_err(|error| stage("FRI verifier control", error))?;
    let fri_references = preprocessing.fri_references.lanes();
    let fri_witnesses = match &branch {
        UniversalAssemblyBranch::Segment {
            fri_circuit,
            poseidon2_fri_circuit,
            ..
        } => [
            FriVerifierCircuitLane {
                verifier_id: SEGMENT_VERIFIER_ID,
                circuit_id: FRI_CIRCUIT_IDS[0],
                circuit: fri_circuit,
            },
            FriVerifierCircuitLane {
                verifier_id: POSEIDON2_VERIFIER_ID,
                circuit_id: FRI_CIRCUIT_IDS[1],
                circuit: poseidon2_fri_circuit,
            },
            fri_references[2],
            fri_references[3],
        ],
        UniversalAssemblyBranch::Binary {
            left_child,
            right_child,
            ..
        } => [
            fri_references[0],
            fri_references[1],
            FriVerifierCircuitLane {
                verifier_id: LEFT_RECURSION_VERIFIER_ID,
                circuit_id: FRI_CIRCUIT_IDS[2],
                circuit: &left_child.fri_circuit,
            },
            FriVerifierCircuitLane {
                verifier_id: RIGHT_RECURSION_VERIFIER_ID,
                circuit_id: FRI_CIRCUIT_IDS[3],
                circuit: &right_child.fri_circuit,
            },
        ],
        UniversalAssemblyBranch::Empty { .. } => fri_references,
    };
    let mut fri_input_table = crate::fri_verifier_input_air::FriVerifierInputTable::new();
    crate::fri_verifier_input_air::push_fri_verifier_inputs(
        &mut fri_input_table,
        &preprocessing.fri_input,
        fri_references,
        fri_witnesses,
        proof_kind,
    )
    .map_err(|error| stage("FRI verifier inputs", error))?;

    let mut circuit_traces = CircuitTraces::default();
    crate::statement_semantics_lowering::lower_statement_semantics_circuit(
        &mut circuit_traces,
        STATEMENT_CIRCUIT_ID,
        &preprocessing.statement_reference,
        statement_circuit,
    )
    .map_err(|error| stage("statement circuit lowering", error))?;
    if let UniversalAssemblyBranch::Segment {
        vm_claim_circuit,
        vm_public_logup_circuit,
        vm_composition_circuit,
        poseidon2_composition_circuit,
        ..
    } = &branch
    {
        crate::vm_public_claim_semantics_lowering::lower_vm_public_claim_semantics_circuit(
            &mut circuit_traces,
            VM_CLAIM_CIRCUIT_ID,
            &preprocessing.vm_claim_reference,
            vm_claim_circuit,
        )
        .map_err(|error| stage("VM claim circuit lowering", error))?;
        crate::vm_public_logup_lowering::lower_vm_public_logup_circuit(
            &mut circuit_traces,
            VM_PUBLIC_LOGUP_CIRCUIT_ID,
            &preprocessing.vm_public_logup_reference,
            vm_public_logup_circuit,
        )
        .map_err(|error| stage("VM public-LogUp circuit lowering", error))?;
        crate::vm_air_composition_lowering::lower_vm_air_composition_circuit(
            &mut circuit_traces,
            VM_COMPOSITION_CIRCUIT_ID,
            &preprocessing.vm_composition_reference,
            vm_composition_circuit,
        )
        .map_err(|error| stage("VM AIR-composition circuit lowering", error))?;
        crate::vm_air_composition_lowering::lower_vm_air_composition_circuit(
            &mut circuit_traces,
            POSEIDON2_COMPOSITION_CIRCUIT_ID,
            &preprocessing.poseidon2_composition_reference,
            poseidon2_composition_circuit,
        )
        .map_err(|error| stage("Poseidon2 AIR-composition circuit lowering", error))?;
    }
    if let UniversalAssemblyBranch::Binary {
        left_child,
        right_child,
        ..
    } = &branch
    {
        for (reference, witness) in preprocessing
            .recursion_composition_references
            .lanes()
            .into_iter()
            .zip([
                left_child.composition_lane(),
                right_child.composition_lane(),
            ])
        {
            crate::recursion_air_composition_lowering::lower_recursion_air_composition_circuit(
                &mut circuit_traces,
                reference.circuit_id,
                reference.circuit,
                witness.circuit,
            )
            .map_err(|error| stage("recursion AIR-composition circuit lowering", error))?;
        }
    }
    let active_pcs = match proof_kind {
        ProofKind::SegmentLeaf => 0..2,
        ProofKind::BinaryNode => 2..4,
        ProofKind::EmptyLeaf => 0..0,
    };
    for lane in active_pcs {
        let reference = pcs_references[lane];
        let witness = pcs_witnesses[lane];
        crate::pcs_deep_lowering::lower_pcs_deep_circuit(
            &mut circuit_traces,
            reference.circuit_id,
            reference.circuit,
            witness.circuit,
        )
        .map_err(|error| stage("PCS DEEP circuit lowering", error))?;
    }
    let active_fri = match proof_kind {
        ProofKind::SegmentLeaf => 0..2,
        ProofKind::BinaryNode => 2..4,
        ProofKind::EmptyLeaf => 0..0,
    };
    for lane in active_fri {
        let reference = fri_references[lane];
        let witness = fri_witnesses[lane];
        crate::fri_verifier_lowering::lower_fri_verifier_circuit(
            &mut circuit_traces,
            reference.circuit_id,
            reference.circuit,
            witness.circuit,
        )
        .map_err(|error| stage("FRI verifier circuit lowering", error))?;
    }

    original_components[1] = table_trace(
        transcript_table.into_witness_with_log_size(component_log_sizes[1]),
        "transcript trace capacity",
    )?;
    original_components[2] = table_trace(
        binding_table.into_witness_with_log_size(component_log_sizes[2]),
        "transcript-binding capacity",
    )?;
    original_components[3] = table_trace(
        state_table.into_witness_with_log_size(component_log_sizes[3]),
        "transcript-state capacity",
    )?;
    original_components[4] = table_trace(
        word_table.into_witness_with_log_size(component_log_sizes[4]),
        "transcript-word capacity",
    )?;
    original_components[5] = table_trace(
        payload_table.into_witness_with_log_size(component_log_sizes[5]),
        "transcript-payload capacity",
    )?;
    original_components[6] = table_trace(
        pow_table.into_witness_with_log_size(component_log_sizes[6]),
        "PoW capacity",
    )?;
    original_components[7] = table_trace(
        pow_frame_table.into_witness_with_log_size(component_log_sizes[7]),
        "PoW-frame capacity",
    )?;
    original_components[8] = table_trace(
        challenge_table.into_witness_with_log_size(component_log_sizes[8]),
        "relation-challenge capacity",
    )?;
    original_components[9] = table_trace(
        randomness_table.into_witness_with_log_size(component_log_sizes[9]),
        "verifier-randomness capacity",
    )?;
    original_components[10] = table_trace(
        statement_table.into_witness_with_log_size(component_log_sizes[10]),
        "statement-input capacity",
    )?;
    original_components[11] = table_trace(
        statement_semantics_table.into_witness_with_log_size(component_log_sizes[11]),
        "statement-semantic capacity",
    )?;
    original_components[12] = table_trace(
        claim_table.into_witness_with_log_size(component_log_sizes[12]),
        "VM public-claim capacity",
    )?;
    original_components[13] = table_trace(
        claim_hash_table.into_witness_with_log_size(component_log_sizes[13]),
        "VM public-claim hash capacity",
    )?;
    original_components[14] = table_trace(
        io_hash_table.into_witness_with_log_size(component_log_sizes[14]),
        "VM public-IO hash capacity",
    )?;
    original_components[15] = table_trace(
        claim_semantics_table.into_witness_with_log_size(component_log_sizes[15]),
        "VM claim-semantic capacity",
    )?;
    original_components[16] = table_trace(
        public_logup_table.into_witness_with_log_size(component_log_sizes[16]),
        "VM public-LogUp capacity",
    )?;
    original_components[17] = table_trace(
        public_logup_control_table.into_witness_with_log_size(component_log_sizes[17]),
        "public-LogUp control capacity",
    )?;
    original_components[18] = table_trace(
        composition_table.into_witness_with_log_size(component_log_sizes[18]),
        "VM AIR-composition capacity",
    )?;
    original_components[20] = table_trace(
        query_bits_table.into_witness_with_log_size(component_log_sizes[20]),
        "query-bit capacity",
    )?;
    original_components[21] = table_trace(
        query_mapping_table.into_witness_with_log_size(component_log_sizes[21]),
        "query-mapping capacity",
    )?;
    original_components[22] = table_trace(
        merkle_root_table.into_witness_with_log_size(component_log_sizes[22]),
        "Merkle-root capacity",
    )?;
    original_components[23] = table_trace(
        trace_merkle_table.into_witness_with_log_size(component_log_sizes[23]),
        "trace-Merkle capacity",
    )?;
    original_components[24] = table_trace(
        pcs_input_table.into_witness_with_log_size(component_log_sizes[24]),
        "PCS DEEP-input capacity",
    )?;
    original_components[25] = table_trace(
        fri_leaf_table.into_witness_with_log_size(component_log_sizes[25]),
        "FRI leaf capacity",
    )?;
    original_components[26] = table_trace(
        fri_node_table.into_witness_with_log_size(component_log_sizes[26]),
        "FRI node capacity",
    )?;
    original_components[27] = table_trace(
        fri_anchor_table.into_witness_with_log_size(component_log_sizes[27]),
        "FRI anchor capacity",
    )?;
    original_components[28] = table_trace(
        fri_control_table.into_witness_with_log_size(component_log_sizes[28]),
        "FRI control capacity",
    )?;
    original_components[29] = table_trace(
        fri_input_table.into_witness_with_log_size(component_log_sizes[29]),
        "FRI input capacity",
    )?;
    original_components[30] = table_trace(
        circuit_traces
            .qm31_mul
            .into_witness_with_log_size(component_log_sizes[30]),
        "QM31 multiplication capacity",
    )?;
    original_components[31] = table_trace(
        circuit_traces
            .qm31_inv
            .into_witness_with_log_size(component_log_sizes[31]),
        "QM31 inversion capacity",
    )?;
    original_components[32] = table_trace(
        circuit_traces
            .linear_ops
            .into_witness_with_log_size(component_log_sizes[32]),
        "linear-operation capacity",
    )?;
    original_components[33] = table_trace(
        merkle_path_table.into_witness_with_log_size(component_log_sizes[33]),
        "Merkle-path capacity",
    )?;
    original_components[34] = table_trace(
        poseidon2.into_witness_with_log_size(component_log_sizes[34]),
        "Poseidon2 capacity",
    )?;

    let preprocessed_components = preprocessing
        .preprocessed_components(&profile.recursion_program().column_log_sizes()[0])?;
    let mut counters = Counters::new();
    crate::statement_semantics_input_air::register_range_check_multiplicities(
        &original_components[11],
        &preprocessed_components[11],
        proof_kind,
        &mut counters,
    );
    crate::vm_public_claim_input_air::register_range_check_multiplicities(
        &original_components[12],
        &preprocessed_components[12],
        proof_kind,
        &mut counters,
    );
    original_components[35] = counters.range_check_8_8.into_trace();
    ensure_trace_log_size(
        &original_components[35],
        component_log_sizes[35],
        "range-check trace",
    )?;

    Ok(UniversalMainWitness {
        proof_kind,
        statement: *statement,
        preprocessed_components,
        original_components,
        component_log_sizes,
        expected_column_log_sizes: profile.recursion_program().column_log_sizes().clone(),
    })
}

const STATEMENT_CIRCUIT_ID: u32 = 1;
const VM_CLAIM_CIRCUIT_ID: u32 = 2;
const VM_PUBLIC_LOGUP_CIRCUIT_ID: u32 = 3;
const VM_COMPOSITION_CIRCUIT_ID: u32 = 4;
const POSEIDON2_COMPOSITION_CIRCUIT_ID: u32 = 5;
const LEFT_RECURSION_COMPOSITION_CIRCUIT_ID: u32 = 6;
const RIGHT_RECURSION_COMPOSITION_CIRCUIT_ID: u32 = 7;
const PCS_CIRCUIT_IDS: [u32; 4] = [10, 11, 12, 13];
const FRI_CIRCUIT_IDS: [u32; 4] = [20, 21, 22, 23];

struct PcsCircuitSet {
    vm: PcsDeepCircuit,
    poseidon2: PcsDeepCircuit,
    left: PcsDeepCircuit,
    right: PcsDeepCircuit,
}

struct RecursionCompositionCircuitSet {
    left: RecursionAirCompositionCircuit,
    right: RecursionAirCompositionCircuit,
}

impl RecursionCompositionCircuitSet {
    fn lanes(&self) -> [RecursionCompositionInputLane<'_>; 2] {
        [
            RecursionCompositionInputLane {
                verifier_id: LEFT_RECURSION_VERIFIER_ID,
                circuit_id: LEFT_RECURSION_COMPOSITION_CIRCUIT_ID,
                statement_scope: LEFT_STATEMENT_SCOPE,
                circuit: &self.left,
            },
            RecursionCompositionInputLane {
                verifier_id: RIGHT_RECURSION_VERIFIER_ID,
                circuit_id: RIGHT_RECURSION_COMPOSITION_CIRCUIT_ID,
                statement_scope: RIGHT_STATEMENT_SCOPE,
                circuit: &self.right,
            },
        ]
    }
}

impl PcsCircuitSet {
    fn lanes(&self) -> [PcsDeepCircuitLane<'_>; 4] {
        [
            PcsDeepCircuitLane {
                verifier_id: SEGMENT_VERIFIER_ID,
                circuit_id: PCS_CIRCUIT_IDS[0],
                circuit: &self.vm,
            },
            PcsDeepCircuitLane {
                verifier_id: POSEIDON2_VERIFIER_ID,
                circuit_id: PCS_CIRCUIT_IDS[1],
                circuit: &self.poseidon2,
            },
            PcsDeepCircuitLane {
                verifier_id: LEFT_RECURSION_VERIFIER_ID,
                circuit_id: PCS_CIRCUIT_IDS[2],
                circuit: &self.left,
            },
            PcsDeepCircuitLane {
                verifier_id: RIGHT_RECURSION_VERIFIER_ID,
                circuit_id: PCS_CIRCUIT_IDS[3],
                circuit: &self.right,
            },
        ]
    }
}

struct FriCircuitSet {
    vm: FriVerifierCircuit,
    poseidon2: FriVerifierCircuit,
    left: FriVerifierCircuit,
    right: FriVerifierCircuit,
}

impl FriCircuitSet {
    fn lanes(&self) -> [FriVerifierCircuitLane<'_>; 4] {
        [
            FriVerifierCircuitLane {
                verifier_id: SEGMENT_VERIFIER_ID,
                circuit_id: FRI_CIRCUIT_IDS[0],
                circuit: &self.vm,
            },
            FriVerifierCircuitLane {
                verifier_id: POSEIDON2_VERIFIER_ID,
                circuit_id: FRI_CIRCUIT_IDS[1],
                circuit: &self.poseidon2,
            },
            FriVerifierCircuitLane {
                verifier_id: LEFT_RECURSION_VERIFIER_ID,
                circuit_id: FRI_CIRCUIT_IDS[2],
                circuit: &self.left,
            },
            FriVerifierCircuitLane {
                verifier_id: RIGHT_RECURSION_VERIFIER_ID,
                circuit_id: FRI_CIRCUIT_IDS[3],
                circuit: &self.right,
            },
        ]
    }
}

/// Trusted preprocessing and inactive circuit structure for the full roster.
pub(crate) struct UniversalPreprocessing {
    control: ControlPreprocessed,
    transcript_calls: TranscriptCallPreprocessed,
    transcript_state: TranscriptStatePreprocessed,
    transcript_word: TranscriptWordPreprocessed,
    transcript_payload: TranscriptPayloadPreprocessed,
    relation_challenge: RelationChallengePreprocessed,
    verifier_randomness: VerifierRandomnessPreprocessed,
    statement_input: StatementInputPreprocessed,
    statement_reference: StatementSemanticsCircuit,
    statement_semantics: StatementSemanticsInputPreprocessed,
    vm_claim_input: VmPublicClaimInputPreprocessed,
    vm_claim_hash: VmPublicClaimHashPreprocessed,
    vm_io_hash: VmPublicIoHashPreprocessed,
    vm_claim_reference: VmPublicClaimSemanticsCircuit,
    vm_claim_semantics: VmPublicClaimSemanticsInputPreprocessed,
    vm_public_logup_reference: VmPublicLogupCircuit,
    vm_public_logup_input: VmPublicLogupInputPreprocessed,
    vm_public_logup_control: VmPublicLogupControlPreprocessed,
    vm_composition_reference: VmAirCompositionCircuit,
    poseidon2_composition_reference: VmAirCompositionCircuit,
    recursion_composition_references: RecursionCompositionCircuitSet,
    vm_composition_input: VmAirCompositionInputPreprocessed,
    vm_composition_control: VmAirCompositionControlPreprocessed,
    query_position: QueryPositionPreprocessed,
    merkle_root: MerkleRootPreprocessed,
    trace_merkle: TraceMerklePreprocessed,
    pcs_profiles: [PcsDeepProfile; 3],
    pcs_references: PcsCircuitSet,
    pcs_input: PcsDeepInputPreprocessed,
    fri_merkle: FriMerklePreprocessed,
    fri_profiles: [FriVerifierProfile; 3],
    fri_references: FriCircuitSet,
    fri_control: FriVerifierControlPreprocessed,
    fri_input: FriVerifierInputPreprocessed,
    qm31_mul_schedule: crate::qm31_mul::Qm31MulPreprocessed,
    qm31_inv_schedule: crate::qm31_inv::Qm31InvPreprocessed,
    linear_ops_schedule: crate::linear_ops::LinearOpsPreprocessed,
}

impl UniversalPreprocessing {
    pub(crate) fn new(profile: &FrozenProtocolProfile) -> Result<Self, UniversalWitnessError> {
        let vm_plan = profile.vm_plan();
        let poseidon2_plan = profile.poseidon2_plan();
        let recursion_plan = profile.recursion_plan();
        let manifest = profile.manifest();
        let raw_manifest = manifest.manifest();
        let control = ControlPreprocessed::new(vm_plan, poseidon2_plan, recursion_plan)
            .map_err(|error| stage("control preprocessing", error))?;
        let transcript_calls =
            TranscriptCallPreprocessed::new(vm_plan, poseidon2_plan, recursion_plan)
                .map_err(|error| stage("transcript-call preprocessing", error))?;
        let transcript_state = TranscriptStatePreprocessed::new(&transcript_calls)
            .map_err(|error| stage("transcript-state preprocessing", error))?;
        let transcript_word = TranscriptWordPreprocessed::new(&transcript_calls)
            .map_err(|error| stage("transcript-word preprocessing", error))?;
        let poseidon2_log_size = M31Word::from(
            u16::try_from(POSEIDON2_COMPONENT_LOG_SIZE)
                .expect("the fixed Poseidon2 log size fits one canonical word"),
        );
        let transcript_payload = TranscriptPayloadPreprocessed::new(
            &transcript_calls,
            manifest.protocol_id(),
            poseidon2_log_size,
        )
        .map_err(|error| stage("transcript-payload preprocessing", error))?;
        let relation_challenge = RelationChallengePreprocessed::new(vm_plan, recursion_plan)
            .map_err(|error| stage("relation-challenge preprocessing", error))?;
        let verifier_randomness =
            VerifierRandomnessPreprocessed::new(vm_plan, poseidon2_plan, recursion_plan)
                .map_err(|error| stage("verifier-randomness preprocessing", error))?;
        let statement_input = StatementInputPreprocessed::new(&transcript_calls)
            .map_err(|error| stage("statement-input preprocessing", error))?;

        let zero_statement = [M31Word::ZERO; SPAN_STATEMENT_CANONICAL_WORDS];
        let statement_reference =
            build_statement_semantics_circuit(StatementSemanticsCircuitWitness {
                segment_selector: false,
                binary_selector: false,
                empty_selector: false,
                segment: &zero_statement,
                left: &zero_statement,
                right: &zero_statement,
                parent: &zero_statement,
            });
        let statement_semantics =
            StatementSemanticsInputPreprocessed::new(&statement_reference, STATEMENT_CIRCUIT_ID)
                .map_err(|error| stage("statement-semantics preprocessing", error))?;

        let claim_shape = profile.public_claim_shape();
        let vm_claim_input = VmPublicClaimInputPreprocessed::new(claim_shape)
            .map_err(|error| stage("VM-claim preprocessing", error))?;
        let vm_claim_hash = VmPublicClaimHashPreprocessed::new(claim_shape)
            .map_err(|error| stage("VM-claim-hash preprocessing", error))?;
        let vm_io_hash = VmPublicIoHashPreprocessed::new(claim_shape)
            .map_err(|error| stage("VM-IO-hash preprocessing", error))?;
        let zero_claim = vec![M31Word::ZERO; claim_shape.claim_word_count()];
        let zero_digest = [M31Word::ZERO; 8];
        let vm_claim_reference = build_vm_public_claim_semantics_circuit(
            claim_shape,
            VmPublicClaimSemanticsWitness {
                segment_selector: false,
                claim_words: &zero_claim,
                statement_words: &zero_statement,
                input_digest: &zero_digest,
                output_digest: &zero_digest,
            },
        )
        .map_err(|error| stage("VM-claim semantic reference", error))?;
        let vm_claim_semantics =
            VmPublicClaimSemanticsInputPreprocessed::new(&vm_claim_reference, VM_CLAIM_CIRCUIT_ID)
                .map_err(|error| stage("VM-claim semantic preprocessing", error))?;

        let claimed_sum_count =
            u32::try_from(COMPONENT_COUNT).map_err(|error| stage("VM component count", error))?;
        let vm_public_logup_reference =
            build_vm_public_logup_reference(claim_shape, claimed_sum_count)
                .map_err(|error| stage("VM public-LogUp reference", error))?;
        let vm_public_logup_input = VmPublicLogupInputPreprocessed::new(
            &vm_public_logup_reference,
            VM_PUBLIC_LOGUP_CIRCUIT_ID,
        )
        .map_err(|error| stage("VM public-LogUp input preprocessing", error))?;
        let vm_public_logup_control = VmPublicLogupControlPreprocessed::new(
            vm_plan,
            vm_public_logup_reference.public_term_count(),
            recursion_plan,
            0,
        )
        .map_err(|error| stage("universal public-LogUp control preprocessing", error))?;

        let vm_composition_reference =
            build_vm_air_composition_reference(crate::profile::vm_component_log_sizes())
                .map_err(|error| stage("VM composition reference", error))?;
        let poseidon2_composition_reference =
            build_poseidon2_air_composition_reference(POSEIDON2_COMPONENT_LOG_SIZE)
                .map_err(|error| stage("Poseidon2 composition reference", error))?;
        let recursion_composition_references = RecursionCompositionCircuitSet {
            left: build_recursion_air_composition_reference(
                recursion_component_log_sizes(),
                &recursion_preprocessed_column_ids(),
            )
            .map_err(|error| stage("left recursion composition reference", error))?,
            right: build_recursion_air_composition_reference(
                recursion_component_log_sizes(),
                &recursion_preprocessed_column_ids(),
            )
            .map_err(|error| stage("right recursion composition reference", error))?,
        };
        let recursion_air_instruction_count =
            u32::try_from(profile.recursion_program().air_instruction_count())
                .map_err(|error| stage("recursion AIR instruction count", error))?;
        let vm_composition_control = VmAirCompositionControlPreprocessed::new_with_poseidon2(
            vm_plan,
            vm_composition_reference.profile(),
            Some((poseidon2_plan, poseidon2_composition_reference.profile())),
            recursion_plan,
            recursion_air_instruction_count,
            raw_manifest
                .recursion_proof_shape
                .sampled_value_count
                .as_u32(),
        )
        .map_err(|error| stage("universal composition control preprocessing", error))?;

        let query_position = QueryPositionPreprocessed::new(
            manifest.vm_pcs(),
            &raw_manifest.vm_proof_shape,
            manifest.vm_pcs(),
            profile.poseidon2_proof_shape(),
            manifest.recursion_pcs(),
            &raw_manifest.recursion_proof_shape,
        )
        .map_err(|error| stage("query-position preprocessing", error))?;
        let merkle_root = MerkleRootPreprocessed::new(
            manifest.vm_pcs(),
            &raw_manifest.vm_proof_shape,
            manifest.vm_pcs(),
            profile.poseidon2_proof_shape(),
            manifest.recursion_pcs(),
            &raw_manifest.recursion_proof_shape,
        )
        .map_err(|error| stage("Merkle-root preprocessing", error))?;
        let trace_merkle = TraceMerklePreprocessed::new(
            vm_plan,
            &raw_manifest.vm_proof_shape,
            &profile.vm_program().column_log_sizes().0,
            poseidon2_plan,
            profile.poseidon2_proof_shape(),
            &profile.poseidon2_program().column_log_sizes().0,
            recursion_plan,
            &raw_manifest.recursion_proof_shape,
            &profile.recursion_program().column_log_sizes().0,
        )
        .map_err(|error| stage("trace-Merkle preprocessing", error))?;

        let vm_pcs_profile = PcsDeepProfile::from_vm(profile.vm_program(), profile.vm_layout())
            .map_err(|error| stage("VM PCS circuit profile", error))?;
        let poseidon2_pcs_profile = PcsDeepProfile::from_poseidon2(
            profile.poseidon2_program(),
            manifest.vm_pcs(),
            profile.poseidon2_proof_shape(),
        )
        .map_err(|error| stage("Poseidon2 PCS circuit profile", error))?;
        let recursion_pcs_profile = recursion_pcs_profile(profile)?;
        let pcs_references = PcsCircuitSet {
            vm: build_pcs_deep_reference(&vm_pcs_profile)
                .map_err(|error| stage("VM PCS reference", error))?,
            poseidon2: build_pcs_deep_reference(&poseidon2_pcs_profile)
                .map_err(|error| stage("Poseidon2 PCS reference", error))?,
            left: build_pcs_deep_reference(&recursion_pcs_profile)
                .map_err(|error| stage("left PCS reference", error))?,
            right: build_pcs_deep_reference(&recursion_pcs_profile)
                .map_err(|error| stage("right PCS reference", error))?,
        };
        let pcs_input = PcsDeepInputPreprocessed::new(pcs_references.lanes())
            .map_err(|error| stage("PCS input preprocessing", error))?;

        let fri_merkle = FriMerklePreprocessed::new(
            vm_plan,
            &raw_manifest.vm_proof_shape,
            poseidon2_plan,
            profile.poseidon2_proof_shape(),
            recursion_plan,
            &raw_manifest.recursion_proof_shape,
        )
        .map_err(|error| stage("FRI Merkle preprocessing", error))?;
        let vm_fri_profile =
            FriVerifierProfile::from_shape(manifest.vm_pcs(), &raw_manifest.vm_proof_shape)
                .map_err(|error| stage("VM FRI profile", error))?;
        let poseidon2_fri_profile =
            FriVerifierProfile::from_shape(manifest.vm_pcs(), profile.poseidon2_proof_shape())
                .map_err(|error| stage("Poseidon2 FRI profile", error))?;
        let recursion_fri_profile = FriVerifierProfile::from_shape(
            manifest.recursion_pcs(),
            &raw_manifest.recursion_proof_shape,
        )
        .map_err(|error| stage("recursion FRI profile", error))?;
        let fri_references = FriCircuitSet {
            vm: build_fri_verifier_reference(&vm_fri_profile)
                .map_err(|error| stage("VM FRI reference", error))?,
            poseidon2: build_fri_verifier_reference(&poseidon2_fri_profile)
                .map_err(|error| stage("Poseidon2 FRI reference", error))?,
            left: build_fri_verifier_reference(&recursion_fri_profile)
                .map_err(|error| stage("left FRI reference", error))?,
            right: build_fri_verifier_reference(&recursion_fri_profile)
                .map_err(|error| stage("right FRI reference", error))?,
        };
        let fri_control = FriVerifierControlPreprocessed::new([
            FriVerifierControlLane {
                verifier_id: SEGMENT_VERIFIER_ID,
                plan: vm_plan,
                profile: &vm_fri_profile,
            },
            FriVerifierControlLane {
                verifier_id: POSEIDON2_VERIFIER_ID,
                plan: poseidon2_plan,
                profile: &poseidon2_fri_profile,
            },
            FriVerifierControlLane {
                verifier_id: LEFT_RECURSION_VERIFIER_ID,
                plan: recursion_plan,
                profile: &recursion_fri_profile,
            },
            FriVerifierControlLane {
                verifier_id: RIGHT_RECURSION_VERIFIER_ID,
                plan: recursion_plan,
                profile: &recursion_fri_profile,
            },
        ])
        .map_err(|error| stage("FRI control preprocessing", error))?;
        let fri_input = FriVerifierInputPreprocessed::new(fri_references.lanes())
            .map_err(|error| stage("FRI input preprocessing", error))?;

        let vm_composition_input =
            VmAirCompositionInputPreprocessed::new_with_segment_and_recursion_inputs(
                &[
                    SegmentCompositionInputLane {
                        verifier_id: SEGMENT_VERIFIER_ID,
                        circuit_id: VM_COMPOSITION_CIRCUIT_ID,
                        circuit: &vm_composition_reference,
                    },
                    SegmentCompositionInputLane {
                        verifier_id: POSEIDON2_VERIFIER_ID,
                        circuit_id: POSEIDON2_COMPOSITION_CIRCUIT_ID,
                        circuit: &poseidon2_composition_reference,
                    },
                ],
                &recursion_composition_references.lanes(),
                &[
                    CircuitAnchorLane {
                        circuit_id: STATEMENT_CIRCUIT_ID,
                        circuit: statement_reference.circuit(),
                        active_in: CircuitAnchorMode::ALL,
                    },
                    CircuitAnchorLane {
                        circuit_id: VM_CLAIM_CIRCUIT_ID,
                        circuit: vm_claim_reference.circuit(),
                        active_in: CircuitAnchorMode::SEGMENT,
                    },
                    CircuitAnchorLane {
                        circuit_id: VM_PUBLIC_LOGUP_CIRCUIT_ID,
                        circuit: vm_public_logup_reference.circuit(),
                        active_in: CircuitAnchorMode::SEGMENT,
                    },
                    CircuitAnchorLane {
                        circuit_id: LEFT_RECURSION_COMPOSITION_CIRCUIT_ID,
                        circuit: recursion_composition_references.left.circuit(),
                        active_in: CircuitAnchorMode::BINARY,
                    },
                    CircuitAnchorLane {
                        circuit_id: RIGHT_RECURSION_COMPOSITION_CIRCUIT_ID,
                        circuit: recursion_composition_references.right.circuit(),
                        active_in: CircuitAnchorMode::BINARY,
                    },
                    CircuitAnchorLane {
                        circuit_id: PCS_CIRCUIT_IDS[0],
                        circuit: pcs_references.vm.circuit(),
                        active_in: CircuitAnchorMode::SEGMENT,
                    },
                    CircuitAnchorLane {
                        circuit_id: PCS_CIRCUIT_IDS[1],
                        circuit: pcs_references.poseidon2.circuit(),
                        active_in: CircuitAnchorMode::SEGMENT,
                    },
                    CircuitAnchorLane {
                        circuit_id: PCS_CIRCUIT_IDS[2],
                        circuit: pcs_references.left.circuit(),
                        active_in: CircuitAnchorMode::BINARY,
                    },
                    CircuitAnchorLane {
                        circuit_id: PCS_CIRCUIT_IDS[3],
                        circuit: pcs_references.right.circuit(),
                        active_in: CircuitAnchorMode::BINARY,
                    },
                    CircuitAnchorLane {
                        circuit_id: FRI_CIRCUIT_IDS[0],
                        circuit: fri_references.vm.circuit(),
                        active_in: CircuitAnchorMode::SEGMENT,
                    },
                    CircuitAnchorLane {
                        circuit_id: FRI_CIRCUIT_IDS[1],
                        circuit: fri_references.poseidon2.circuit(),
                        active_in: CircuitAnchorMode::SEGMENT,
                    },
                    CircuitAnchorLane {
                        circuit_id: FRI_CIRCUIT_IDS[2],
                        circuit: fri_references.left.circuit(),
                        active_in: CircuitAnchorMode::BINARY,
                    },
                    CircuitAnchorLane {
                        circuit_id: FRI_CIRCUIT_IDS[3],
                        circuit: fri_references.right.circuit(),
                        active_in: CircuitAnchorMode::BINARY,
                    },
                ],
            )
            .map_err(|error| stage("circuit-anchor preprocessing", error))?;

        let mut segment_operations = CircuitTraces::default();
        let mut binary_operations = CircuitTraces::default();
        let mut empty_operations = CircuitTraces::default();
        for (proof_kind, operations) in [
            (ProofKind::SegmentLeaf, &mut segment_operations),
            (ProofKind::BinaryNode, &mut binary_operations),
            (ProofKind::EmptyLeaf, &mut empty_operations),
        ] {
            lower_all_fixed_circuits(
                operations,
                proof_kind,
                &statement_reference,
                &vm_claim_reference,
                &vm_public_logup_reference,
                [
                    SegmentCompositionInputLane {
                        verifier_id: SEGMENT_VERIFIER_ID,
                        circuit_id: VM_COMPOSITION_CIRCUIT_ID,
                        circuit: &vm_composition_reference,
                    },
                    SegmentCompositionInputLane {
                        verifier_id: POSEIDON2_VERIFIER_ID,
                        circuit_id: POSEIDON2_COMPOSITION_CIRCUIT_ID,
                        circuit: &poseidon2_composition_reference,
                    },
                ],
                recursion_composition_references.lanes(),
                pcs_references.lanes(),
                fri_references.lanes(),
                "reference circuit schedule",
            )?;
        }
        let capacities = recursion_component_log_sizes();
        let qm31_mul_schedule = crate::qm31_mul::Qm31MulPreprocessed::new_for_modes(
            capacities[30],
            [
                segment_operations.qm31_mul_schedule,
                binary_operations.qm31_mul_schedule,
                empty_operations.qm31_mul_schedule,
            ],
        )
        .map_err(|error| stage("multiplication schedule preprocessing", error))?;
        let qm31_inv_schedule = crate::qm31_inv::Qm31InvPreprocessed::new_for_modes(
            capacities[31],
            [
                segment_operations.qm31_inv_schedule,
                binary_operations.qm31_inv_schedule,
                empty_operations.qm31_inv_schedule,
            ],
        )
        .map_err(|error| stage("inversion schedule preprocessing", error))?;
        let linear_ops_schedule = crate::linear_ops::LinearOpsPreprocessed::new_for_modes(
            capacities[32],
            [
                segment_operations.linear_ops_schedule,
                binary_operations.linear_ops_schedule,
                empty_operations.linear_ops_schedule,
            ],
        )
        .map_err(|error| stage("linear-operation schedule preprocessing", error))?;

        Ok(Self {
            control,
            transcript_calls,
            transcript_state,
            transcript_word,
            transcript_payload,
            relation_challenge,
            verifier_randomness,
            statement_input,
            statement_reference,
            statement_semantics,
            vm_claim_input,
            vm_claim_hash,
            vm_io_hash,
            vm_claim_reference,
            vm_claim_semantics,
            vm_public_logup_reference,
            vm_public_logup_input,
            vm_public_logup_control,
            vm_composition_reference,
            poseidon2_composition_reference,
            recursion_composition_references,
            vm_composition_input,
            vm_composition_control,
            query_position,
            merkle_root,
            trace_merkle,
            pcs_profiles: [vm_pcs_profile, poseidon2_pcs_profile, recursion_pcs_profile],
            pcs_references,
            pcs_input,
            fri_merkle,
            fri_profiles: [vm_fri_profile, poseidon2_fri_profile, recursion_fri_profile],
            fri_references,
            fri_control,
            fri_input,
            qm31_mul_schedule,
            qm31_inv_schedule,
            linear_ops_schedule,
        })
    }

    fn structural_log_sizes(&self) -> UniversalComponentLogSizes {
        [
            self.control.log_size(),
            self.transcript_calls.log_size(),
            self.transcript_calls.log_size(),
            self.transcript_state.log_size(),
            self.transcript_word.log_size(),
            self.transcript_payload.log_size(),
            4,
            4,
            self.relation_challenge.log_size(),
            self.verifier_randomness.log_size(),
            self.statement_input.log_size(),
            self.statement_semantics.log_size(),
            self.vm_claim_input.log_size(),
            self.vm_claim_hash.log_size(),
            self.vm_io_hash.log_size(),
            self.vm_claim_semantics.log_size(),
            self.vm_public_logup_input.log_size(),
            self.vm_public_logup_control.log_size(),
            self.vm_composition_input.log_size(),
            self.vm_composition_control.log_size(),
            self.query_position.raw_log_size(),
            self.query_position.mapping_log_size(),
            self.merkle_root.log_size(),
            self.trace_merkle.log_size(),
            self.pcs_input.log_size(),
            self.fri_merkle.leaf_log_size(),
            self.fri_merkle.node_log_size(),
            self.fri_merkle.anchor_log_size(),
            self.fri_control.log_size(),
            self.fri_input.log_size(),
            recursion_component_log_sizes()[30],
            recursion_component_log_sizes()[31],
            recursion_component_log_sizes()[32],
            4,
            4,
            16,
        ]
    }

    fn validate_capacities(
        &self,
        capacities: &UniversalComponentLogSizes,
    ) -> Result<(), UniversalWitnessError> {
        for (component, (required, capacity)) in self
            .structural_log_sizes()
            .into_iter()
            .zip(capacities.iter().copied())
            .enumerate()
        {
            if required > capacity {
                return Err(stage(
                    "universal component capacity",
                    format_args!(
                        "component {component} needs log size {required}, capacity is {capacity}"
                    ),
                ));
            }
        }
        Ok(())
    }

    pub(crate) fn preprocessed_components(
        &self,
        expected_log_sizes: &[u32],
    ) -> Result<[UniversalTrace; UNIVERSAL_COMPONENT_COUNT], UniversalWitnessError> {
        let mut components = core::array::from_fn(|_| Vec::new());
        components[0] = self.control.gen_columns();
        components[2] = self.transcript_calls.gen_columns();
        components[3] = self.transcript_state.gen_columns();
        components[4] = self.transcript_word.gen_columns();
        components[5] = self.transcript_payload.gen_columns();
        components[8] = self.relation_challenge.gen_columns();
        components[9] = self.verifier_randomness.gen_columns();
        components[10] = self.statement_input.gen_columns();
        components[11] = self.statement_semantics.gen_columns();
        components[12] = self.vm_claim_input.gen_columns();
        components[13] = self.vm_claim_hash.gen_columns();
        components[14] = self.vm_io_hash.gen_columns();
        components[15] = self.vm_claim_semantics.gen_columns();
        components[16] = self.vm_public_logup_input.gen_columns();
        components[17] = self.vm_public_logup_control.gen_columns();
        components[18] = self.vm_composition_input.gen_columns();
        components[19] = self.vm_composition_control.gen_columns();
        components[20] = self.query_position.gen_raw_columns();
        components[21] = self.query_position.gen_mapping_columns();
        components[22] = self.merkle_root.gen_columns();
        components[23] = self.trace_merkle.gen_columns();
        components[24] = self.pcs_input.gen_columns();
        components[25] = self.fri_merkle.gen_leaf_columns();
        components[26] = self.fri_merkle.gen_node_columns();
        components[27] = self.fri_merkle.gen_anchor_columns();
        components[28] = self.fri_control.gen_columns();
        components[29] = self.fri_input.gen_columns();
        components[30] = self.qm31_mul_schedule.gen_columns();
        components[31] = self.qm31_inv_schedule.gen_columns();
        components[32] = self.linear_ops_schedule.gen_columns();
        components[35] = prover::preprocessed::range_check_8_8::Table::gen_columns();

        let actual_count = components.iter().flatten().count();
        if actual_count != expected_log_sizes.len() {
            return Err(stage(
                "universal preprocessing log sizes",
                format_args!(
                    "materialized {actual_count} columns, compiled {} columns",
                    expected_log_sizes.len(),
                ),
            ));
        }
        let mut column_index = 0_usize;
        for component in &mut components {
            let columns = core::mem::take(component);
            *component = columns
                .into_iter()
                .map(|column| {
                    let expected = expected_log_sizes[column_index];
                    let current = column_index;
                    column_index += 1;
                    pad_preprocessed_column(column, expected, current)
                })
                .collect::<Result<Vec<_>, _>>()?;
        }
        Ok(components)
    }

    #[cfg(test)]
    fn reference_arithmetic_log_sizes(&self) -> Result<[[u32; 3]; 2], UniversalWitnessError> {
        Ok([
            self.reference_arithmetic_log_sizes_for_kind(ProofKind::SegmentLeaf)?,
            self.reference_arithmetic_log_sizes_for_kind(ProofKind::BinaryNode)?,
        ])
    }

    #[cfg(test)]
    fn reference_arithmetic_log_sizes_for_kind(
        &self,
        proof_kind: ProofKind,
    ) -> Result<[u32; 3], UniversalWitnessError> {
        let mut traces = CircuitTraces::default();
        crate::statement_semantics_lowering::lower_statement_semantics_circuit(
            &mut traces,
            STATEMENT_CIRCUIT_ID,
            &self.statement_reference,
            &self.statement_reference,
        )
        .map_err(|error| stage("statement reference lowering", error))?;
        if proof_kind == ProofKind::SegmentLeaf {
            crate::vm_public_claim_semantics_lowering::lower_vm_public_claim_semantics_circuit(
                &mut traces,
                VM_CLAIM_CIRCUIT_ID,
                &self.vm_claim_reference,
                &self.vm_claim_reference,
            )
            .map_err(|error| stage("VM claim reference lowering", error))?;
            crate::vm_public_logup_lowering::lower_vm_public_logup_circuit(
                &mut traces,
                VM_PUBLIC_LOGUP_CIRCUIT_ID,
                &self.vm_public_logup_reference,
                &self.vm_public_logup_reference,
            )
            .map_err(|error| stage("VM public-LogUp reference lowering", error))?;
            crate::vm_air_composition_lowering::lower_vm_air_composition_circuit(
                &mut traces,
                VM_COMPOSITION_CIRCUIT_ID,
                &self.vm_composition_reference,
                &self.vm_composition_reference,
            )
            .map_err(|error| stage("VM composition reference lowering", error))?;
            crate::vm_air_composition_lowering::lower_vm_air_composition_circuit(
                &mut traces,
                POSEIDON2_COMPOSITION_CIRCUIT_ID,
                &self.poseidon2_composition_reference,
                &self.poseidon2_composition_reference,
            )
            .map_err(|error| stage("Poseidon2 composition reference lowering", error))?;
        }
        if proof_kind == ProofKind::BinaryNode {
            for lane in self.recursion_composition_references.lanes() {
                crate::recursion_air_composition_lowering::lower_recursion_air_composition_circuit(
                    &mut traces,
                    lane.circuit_id,
                    lane.circuit,
                    lane.circuit,
                )
                .map_err(|error| stage("recursion composition reference lowering", error))?;
            }
        }
        let pcs_lanes = self.pcs_references.lanes();
        let pcs_lanes = if proof_kind == ProofKind::SegmentLeaf {
            &pcs_lanes[..2]
        } else {
            &pcs_lanes[2..]
        };
        for lane in pcs_lanes {
            crate::pcs_deep_lowering::lower_pcs_deep_circuit(
                &mut traces,
                lane.circuit_id,
                lane.circuit,
                lane.circuit,
            )
            .map_err(|error| stage("PCS reference lowering", error))?;
        }
        let fri_lanes = self.fri_references.lanes();
        let fri_lanes = if proof_kind == ProofKind::SegmentLeaf {
            &fri_lanes[..2]
        } else {
            &fri_lanes[2..]
        };
        for lane in fri_lanes {
            crate::fri_verifier_lowering::lower_fri_verifier_circuit(
                &mut traces,
                lane.circuit_id,
                lane.circuit,
                lane.circuit,
            )
            .map_err(|error| stage("FRI reference lowering", error))?;
        }
        Ok([
            natural_log_size(traces.qm31_mul.len()),
            natural_log_size(traces.qm31_inv.len()),
            natural_log_size(traces.linear_ops.len()),
        ])
    }
}

#[cfg(test)]
fn natural_log_size(rows: usize) -> u32 {
    u32::try_from(rows)
        .expect("supported witness row count fits u32")
        .next_power_of_two()
        .ilog2()
        .max(4)
}

fn recursion_pcs_profile(
    profile: &FrozenProtocolProfile,
) -> Result<PcsDeepProfile, UniversalWitnessError> {
    let program = profile.recursion_program();
    let log_blowup_factor = profile
        .manifest()
        .recursion_pcs()
        .config()
        .fri_config
        .log_blowup_factor;
    let mut offsets = program
        .column_log_sizes()
        .iter()
        .map(|columns| vec![Vec::new(); columns.len()])
        .collect::<Vec<_>>();
    for (coordinate, offset) in program
        .sample_coordinates()
        .iter()
        .zip(program.sample_point_offsets())
    {
        offsets[coordinate.tree][coordinate.column].push(*offset);
    }
    PcsDeepProfile::new(
        program
            .column_log_sizes()
            .iter()
            .map(|tree| {
                tree.iter()
                    .map(|log_size| log_size + log_blowup_factor)
                    .collect::<Vec<_>>()
            })
            .collect(),
        offsets,
        profile.manifest().recursion_shape().lifting_log_size(),
        profile
            .manifest()
            .recursion_pcs()
            .config()
            .fri_config
            .n_queries,
    )
    .map_err(|error| stage("recursion PCS circuit profile", error))
}

fn stage(stage: &'static str, error: impl fmt::Display) -> UniversalWitnessError {
    UniversalWitnessError {
        stage,
        detail: error.to_string(),
    }
}

fn ensure_zero_outputs(
    circuit: &'static str,
    nonzero_output_count: usize,
) -> Result<(), UniversalWitnessError> {
    if nonzero_output_count == 0 {
        Ok(())
    } else {
        Err(stage(
            circuit,
            format_args!("{nonzero_output_count} constraint outputs are nonzero"),
        ))
    }
}

/// A trusted profile or verifier input could not be materialized.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UniversalWitnessError {
    stage: &'static str,
    detail: String,
}

impl fmt::Display for UniversalWitnessError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}: {}", self.stage, self.detail)
    }
}

impl std::error::Error for UniversalWitnessError {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::profile::frozen_protocol_profile;
    use crate::recursion_air_program::assert_universal_constraints;
    use crate::test_fixtures::{job, leaf, state, two_empty};

    fn empty_statement() -> SpanStatement {
        let job = job(3, 12);
        SpanStatement::empty_leaf(job, 3).expect("slot three is canonical padding")
    }

    fn empty_witness(
        profile: &FrozenProtocolProfile,
        relations: &UniversalRelations,
    ) -> UniversalWitness {
        assemble_empty_leaf(profile, &empty_statement(), relations)
            .expect("canonical padding assembles")
    }

    #[test]
    fn canonical_empty_leaf_satisfies_the_complete_universal_air() {
        let profile = frozen_protocol_profile().expect("frozen profile is valid");
        let mut channel = prover::poseidon2_channel::Poseidon2M31Channel::default();
        let relations = UniversalRelations::draw(&mut channel);
        let witness = empty_witness(&profile, &relations);
        let accepted = assert_universal_constraints(
            witness.traces(),
            witness.preprocessing_ids(),
            &relations,
            witness.proof_kind(),
            witness.component_log_sizes(),
            witness.claimed_sums(),
        );
        assert_eq!(
            (
                witness.proof_kind(),
                witness.global_relation_sum(),
                accepted
            ),
            (
                ProofKind::EmptyLeaf,
                SecureField::zero(),
                UNIVERSAL_COMPONENT_COUNT,
            )
        );
    }

    #[test]
    fn empty_branch_rejects_an_executed_slot() {
        let profile = frozen_protocol_profile().expect("frozen profile is valid");
        let relations = UniversalRelations::dummy();
        let job = job(1, 1);
        let executed = leaf(job, 0, 0, 1, state(0), state(1));
        assert!(assemble_empty_leaf(&profile, &executed, &relations).is_err());
    }

    #[test]
    fn empty_branch_rejects_a_non_leaf_padding_span() {
        let profile = frozen_protocol_profile().expect("frozen profile is valid");
        let relations = UniversalRelations::dummy();
        let (_, _, folded_empty) = two_empty();
        assert!(assemble_empty_leaf(&profile, &folded_empty, &relations).is_err());
    }

    #[test]
    fn empty_branch_materializes_zero_for_an_inactive_transcript_column() {
        let profile = frozen_protocol_profile().expect("frozen profile is valid");
        let mut channel = prover::poseidon2_channel::Poseidon2M31Channel::default();
        let relations = UniversalRelations::draw(&mut channel);
        let witness = empty_witness(&profile, &relations);
        let values = witness.traces.0[1][0].values.clone().into_cpu_vec();
        assert_eq!(
            values,
            vec![BaseField::zero(); 1 << witness.component_log_sizes()[1]]
        );
    }

    #[test]
    fn structural_tables_fit_the_frozen_component_capacities() {
        let profile = frozen_protocol_profile().expect("frozen profile is valid");
        let preprocessing =
            UniversalPreprocessing::new(&profile).expect("universal preprocessing is valid");
        let capacities = recursion_component_log_sizes();
        let exceeded = preprocessing
            .structural_log_sizes()
            .into_iter()
            .zip(capacities)
            .enumerate()
            .filter_map(|(component, (required, capacity))| {
                (required > capacity).then_some((component, required, capacity))
            })
            .collect::<Vec<_>>();
        assert_eq!(exceeded, Vec::new());
    }

    #[test]
    fn arithmetic_capacities_cover_segment_and_binary_circuits() {
        let profile = frozen_protocol_profile().expect("frozen profile is valid");
        let preprocessing =
            UniversalPreprocessing::new(&profile).expect("universal preprocessing is valid");
        assert_eq!(
            preprocessing
                .reference_arithmetic_log_sizes()
                .expect("fixed references lower"),
            [[21, 15, 21], [22, 16, 22]]
        );
    }
}
