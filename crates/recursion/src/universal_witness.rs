//! Canonical assembly of the universal recursion witness.
//!
//! The trusted protocol profile owns every preprocessing layout and component
//! capacity. Assembly executes that schedule once, fills the 36 generated AIR
//! components in roster order, pads committed tables with their constrained
//! inactive rows, and derives all interaction claims from one relation draw.

use core::fmt;

use air::digest::M31Word;
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
    ControlPreprocessed, LEFT_RECURSION_VERIFIER_ID, RIGHT_RECURSION_VERIFIER_ID,
    SEGMENT_VERIFIER_ID,
};
use crate::fri_merkle_air::{
    FriMerkleOpeningSet, FriMerklePreprocessed, UniversalFriMerkleWitness,
};
use crate::fri_verifier_circuit::{
    FriVerifierCircuit, FriVerifierProfile, FriVerifierWitness, build_fri_verifier_circuit,
    build_fri_verifier_reference, restore_authenticated_query_values,
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
use crate::profile::{FrozenProtocolProfile, recursion_component_log_sizes};
use crate::protocol::CanonicalWords;
use crate::query_position_air::{
    QueryPositionKind, QueryPositionPreprocessed, UniversalRawQueryWitness,
};
use crate::recursion_air_program::{
    UNIVERSAL_COMPONENT_COUNT, UniversalComponentLogSizes, universal_preprocessed_column_ids,
};
use crate::relation_challenge_air::RelationChallengePreprocessed;
use crate::segment_leaf::VmSegmentLeafWire;
use crate::statement::{SPAN_STATEMENT_CANONICAL_WORDS, SpanStatement};
use crate::statement_input_air::{StatementInputPreprocessed, StatementInputWitness};
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
    VerifierPublicClaim, VerifierTranscriptExecution, execute_fixed_transcript,
};
use crate::transcript_state_air::TranscriptStatePreprocessed;
use crate::transcript_word_air::TranscriptWordPreprocessed;
use crate::universal_relations::UniversalRelations;
use crate::verifier_randomness_air::VerifierRandomnessPreprocessed;
use crate::vm_air_composition_circuit::{
    VmAirCompositionCircuit, VmAirCompositionWitness, build_vm_air_composition_circuit,
    build_vm_air_composition_reference,
};
use crate::vm_air_composition_control_air::VmAirCompositionControlPreprocessed;
use crate::vm_air_composition_input_air::VmAirCompositionInputPreprocessed;
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
use crate::wire::ProofKind;
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
}

/// Assembles every universal component for one authenticated VM segment.
pub fn assemble_segment_leaf(
    profile: &FrozenProtocolProfile,
    leaf: &VmSegmentLeafWire,
    relations: &UniversalRelations,
) -> Result<UniversalWitness, UniversalWitnessError> {
    let component_log_sizes = recursion_component_log_sizes();
    if profile.recursion_program().component_log_sizes() != &component_log_sizes {
        return Err(stage(
            "universal component capacities",
            "profile and assembler log sizes differ",
        ));
    }
    let preprocessing = UniversalPreprocessing::new(profile)?;
    preprocessing.validate_capacities(&component_log_sizes)?;

    let claim_digest =
        vm_public_claim_digest_from_words(leaf.public_claim_words(), profile.public_claim_shape())
            .map_err(|error| stage("VM public-claim digest", error))?;
    let transcript = execute_fixed_transcript(
        RecordingTranscriptBackend::default(),
        profile.vm_plan(),
        profile.manifest().protocol_id(),
        leaf.statement(),
        VerifierPublicClaim::Vm(claim_digest),
        leaf.proof(),
    )
    .map_err(|error| stage("VM verifier transcript", error))?;
    let relation_challenges = relation_challenge_words(&transcript, Relations::DESCRIPTORS.len())?;
    let composition_randomness = secure_draw_words(
        &transcript,
        VerifierStep::DrawCompositionRandomness,
        "composition randomness",
    )?;
    let oods_seed = secure_draw_words(&transcript, VerifierStep::DrawOodsPoint, "OODS point")?;
    let deep_randomness = secure_draw_words(
        &transcript,
        VerifierStep::DrawDeepRandomness,
        "DEEP randomness",
    )?;
    let fri_alphas = fri_alpha_values(&transcript, preprocessing.fri_profiles[0].layer_count())?;
    let raw_queries = raw_query_words(&transcript, preprocessing.query_position.vm_query_count())?;

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
            ),
            claimed_sums: &proof_claimed_sums,
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
    let mut fri_opening =
        FriMerkleOpeningSet::from_wire(&raw_queries, &leaf.proof().fri_layers[..]);
    let fri_routes = fri_routes(
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
    let mut authenticated_values = fri_opening
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
    restore_authenticated_query_values(
        &preprocessing.fri_profiles[0],
        &deep_answers,
        &mut authenticated_values,
        &fri_alphas,
        &raw_queries,
    )
    .map_err(|error| stage("VM FRI query reconstruction", error))?;
    for (layer, values) in fri_opening.layers.iter_mut().zip(&authenticated_values) {
        for (slot, value) in layer
            .queries
            .iter_mut()
            .flat_map(|query| query.values.iter_mut())
            .zip(values)
        {
            *slot = (*value).into();
        }
    }
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
    let last_layer_positions = last_layer_positions(
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
            fri_positions: &fri_routes.positions,
            fri_offsets: &fri_routes.offsets,
            last_layer_positions: &last_layer_positions,
            last_layer_coefficients: &last_layer_coefficients,
        },
    )
    .map_err(|error| stage("VM FRI verifier circuit", error))?;
    ensure_zero_outputs(
        "VM FRI verifier circuit",
        fri_circuit.nonzero_output_count(),
    )?;

    assemble_segment_components(
        leaf,
        profile,
        relations,
        preprocessing,
        transcript,
        raw_queries,
        fri_opening,
        statement_circuit,
        vm_claim_circuit,
        vm_public_logup_circuit,
        vm_composition_circuit,
        pcs_circuit,
        fri_circuit,
        component_log_sizes,
    )
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

#[allow(clippy::too_many_arguments)]
fn finalize_universal_witness(
    statement: &SpanStatement,
    relations: &UniversalRelations,
    preprocessing: UniversalPreprocessing,
    preprocessed_components: [UniversalTrace; UNIVERSAL_COMPONENT_COUNT],
    original_components: [UniversalTrace; UNIVERSAL_COMPONENT_COUNT],
    component_log_sizes: UniversalComponentLogSizes,
    expected_column_log_sizes: &TreeVec<Vec<u32>>,
) -> Result<UniversalWitness, UniversalWitnessError> {
    let proof_kind = ProofKind::SegmentLeaf;
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
            &preprocessed_components[17],
            proof_kind,
            &relations.control,
        );
    (interaction_components[18], claimed_sums[18]) =
        crate::vm_air_composition_input_air::gen_interaction_trace(
            &original_components[18],
            &preprocessed_components[18],
            proof_kind,
            &relations.relation_challenge,
            &relations.verifier_input,
            &relations.verifier_randomness,
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
    (interaction_components[30], claimed_sums[30]) =
        qm31_mul::gen_interaction_trace(&original_components[30], &relations.recursion);
    (interaction_components[31], claimed_sums[31]) =
        qm31_inv::gen_interaction_trace(&original_components[31], &relations.recursion);
    (interaction_components[32], claimed_sums[32]) =
        linear_ops::gen_interaction_trace(&original_components[32], &relations.recursion);
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

    for (component, trace) in interaction_components.iter().enumerate() {
        ensure_trace_log_size(
            trace,
            component_log_sizes[component],
            "universal interaction trace",
        )?;
    }

    let mut public_relation_sum =
        crate::statement_input_air::public_statement_terms(statement, &relations.statement_input)
            .map_err(|error| stage("public statement terms", error))?;
    public_relation_sum += crate::control_air::public_terminal_control_terms(
        preprocessing.transcript_calls.vm_plan(),
        SEGMENT_VERIFIER_ID,
        &relations.control,
    );
    public_relation_sum += crate::statement_semantics_lowering::public_statement_semantics_terms(
        STATEMENT_CIRCUIT_ID,
        &preprocessing.statement_reference,
        &relations.recursion,
    )
    .map_err(|error| stage("public statement-circuit terms", error))?;
    public_relation_sum +=
        crate::vm_public_claim_semantics_lowering::public_vm_public_claim_semantics_terms(
            VM_CLAIM_CIRCUIT_ID,
            &preprocessing.vm_claim_reference,
            &relations.recursion,
        )
        .map_err(|error| stage("public VM claim-circuit terms", error))?;
    public_relation_sum += crate::vm_public_logup_lowering::public_vm_public_logup_terms(
        VM_PUBLIC_LOGUP_CIRCUIT_ID,
        &preprocessing.vm_public_logup_reference,
        &relations.recursion,
    )
    .map_err(|error| stage("public VM LogUp-circuit terms", error))?;
    public_relation_sum += crate::vm_air_composition_lowering::public_vm_air_composition_terms(
        VM_COMPOSITION_CIRCUIT_ID,
        &preprocessing.vm_composition_reference,
        &relations.recursion,
    )
    .map_err(|error| stage("public VM composition-circuit terms", error))?;
    public_relation_sum += crate::pcs_deep_lowering::public_pcs_deep_terms(
        PCS_CIRCUIT_IDS[0],
        &preprocessing.pcs_references.segment,
        &relations.recursion,
    )
    .map_err(|error| stage("public PCS circuit terms", error))?;
    public_relation_sum += crate::fri_verifier_lowering::public_fri_verifier_terms(
        FRI_CIRCUIT_IDS[0],
        &preprocessing.fri_references.segment,
        &relations.recursion,
    )
    .map_err(|error| stage("public FRI circuit terms", error))?;

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
    ensure_universal_trace_layout(&traces, expected_column_log_sizes)?;
    let witness = UniversalWitness {
        proof_kind,
        traces,
        claimed_sums,
        public_relation_sum,
        component_log_sizes,
        preprocessing_ids,
    };
    let global_relation_sum = witness.global_relation_sum();
    if !global_relation_sum.is_zero() {
        return Err(stage(
            "universal relation closure",
            format_args!("global LogUp sum is nonzero: {global_relation_sum:?}"),
        ));
    }
    Ok(witness)
}

#[allow(clippy::too_many_arguments)]
fn assemble_segment_components(
    leaf: &VmSegmentLeafWire,
    profile: &FrozenProtocolProfile,
    relations: &UniversalRelations,
    preprocessing: UniversalPreprocessing,
    transcript: VerifierTranscriptExecution<RecordingTranscriptBackend>,
    raw_queries: Vec<M31Word>,
    fri_opening: FriMerkleOpeningSet,
    statement_circuit: StatementSemanticsCircuit,
    vm_claim_circuit: VmPublicClaimSemanticsCircuit,
    vm_public_logup_circuit: VmPublicLogupCircuit,
    vm_composition_circuit: VmAirCompositionCircuit,
    pcs_circuit: PcsDeepCircuit,
    fri_circuit: FriVerifierCircuit,
    component_log_sizes: UniversalComponentLogSizes,
) -> Result<UniversalWitness, UniversalWitnessError> {
    let proof_kind = ProofKind::SegmentLeaf;
    let transcript_witness = UniversalTranscriptWitness::Segment(&transcript);
    let transcript_trace = transcript.backend().trace();
    let mut poseidon2 = Poseidon2Table::new();
    let mut original_components: [UniversalTrace; UNIVERSAL_COMPONENT_COUNT] =
        core::array::from_fn(|_| Vec::new());

    let mut transcript_table = crate::transcript_air::TranscriptHashCallTable::new();
    crate::transcript_air::push_transcript_calls(
        &mut transcript_table,
        &mut poseidon2,
        SEGMENT_VERIFIER_ID,
        transcript_trace,
    )
    .map_err(|error| stage("transcript hash calls", error))?;

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
    push_pow_checks(
        &mut pow_table,
        SEGMENT_VERIFIER_ID,
        profile.vm_plan(),
        transcript_trace,
    )?;
    let mut pow_frame_table = crate::pow::PowFrameTable::new();
    crate::pow::push_pow_frames(
        &mut pow_frame_table,
        SEGMENT_VERIFIER_ID,
        profile.vm_plan(),
        transcript_trace,
    )
    .map_err(|error| stage("PoW frames", error))?;

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
        StatementInputWitness::Segment(leaf.statement()),
    )
    .map_err(|error| stage("statement inputs", error))?;
    let mut statement_semantics_table =
        crate::statement_semantics_input_air::StatementSemanticsInputTable::new();
    crate::statement_semantics_input_air::push_statement_semantics_inputs(
        &mut statement_semantics_table,
        &preprocessing.statement_semantics,
        &statement_circuit,
        proof_kind,
    )
    .map_err(|error| stage("statement-semantic inputs", error))?;

    let mut claim_table = crate::vm_public_claim_input_air::VmPublicClaimInputTable::new();
    crate::vm_public_claim_input_air::push_vm_public_claim_word_inputs(
        &mut claim_table,
        &preprocessing.vm_claim_input,
        proof_kind,
        leaf.public_claim_words(),
    )
    .map_err(|error| stage("VM public-claim inputs", error))?;
    let mut claim_hash_table = crate::vm_public_claim_hash_air::VmPublicClaimHashTable::new();
    crate::vm_public_claim_hash_air::push_vm_public_claim_word_hash(
        &mut claim_hash_table,
        &mut poseidon2,
        &preprocessing.vm_claim_hash,
        proof_kind,
        leaf.public_claim_words(),
    )
    .map_err(|error| stage("VM public-claim hash", error))?;
    let mut io_hash_table = crate::vm_public_io_hash_air::VmPublicIoHashTable::new();
    crate::vm_public_io_hash_air::push_vm_public_io_word_hashes(
        &mut io_hash_table,
        &mut poseidon2,
        &preprocessing.vm_io_hash,
        proof_kind,
        leaf.public_claim_words(),
    )
    .map_err(|error| stage("VM public-IO hashes", error))?;
    let mut claim_semantics_table =
        crate::vm_public_claim_semantics_input_air::VmPublicClaimSemanticsInputTable::new();
    crate::vm_public_claim_semantics_input_air::push_vm_public_claim_semantics_inputs(
        &mut claim_semantics_table,
        &preprocessing.vm_claim_semantics,
        &preprocessing.vm_claim_reference,
        &vm_claim_circuit,
        proof_kind,
    )
    .map_err(|error| stage("VM claim-semantic inputs", error))?;
    let mut public_logup_table = crate::vm_public_logup_input_air::VmPublicLogupInputTable::new();
    crate::vm_public_logup_input_air::push_vm_public_logup_inputs(
        &mut public_logup_table,
        &preprocessing.vm_public_logup_input,
        &preprocessing.vm_public_logup_reference,
        &vm_public_logup_circuit,
        proof_kind,
    )
    .map_err(|error| stage("VM public-LogUp inputs", error))?;
    let mut composition_table =
        crate::vm_air_composition_input_air::VmAirCompositionInputTable::new();
    crate::vm_air_composition_input_air::push_vm_air_composition_inputs(
        &mut composition_table,
        &preprocessing.vm_composition_input,
        &preprocessing.vm_composition_reference,
        &vm_composition_circuit,
        proof_kind,
    )
    .map_err(|error| stage("VM AIR-composition inputs", error))?;

    let mut query_bits_table = crate::query_position_air::QueryBitsTable::new();
    let mut query_mapping_table = crate::query_position_air::QueryMappingTable::new();
    crate::query_position_air::push_query_positions(
        &mut query_bits_table,
        &mut query_mapping_table,
        &preprocessing.query_position,
        UniversalRawQueryWitness::Segment(&raw_queries),
    )
    .map_err(|error| stage("query positions", error))?;

    let fri_commitments = fri_opening
        .layers
        .iter()
        .map(|layer| layer.commitment)
        .collect::<Vec<_>>();
    let roots = crate::merkle_root_air::MerkleRootSet {
        trace: &leaf.proof().commitments,
        fri: &fri_commitments,
    };
    let mut merkle_root_table = crate::merkle_root_air::MerkleRootTable::new();
    crate::merkle_root_air::push_merkle_roots(
        &mut merkle_root_table,
        &preprocessing.merkle_root,
        crate::merkle_root_air::UniversalMerkleRootWitness::Segment(roots),
    )
    .map_err(|error| stage("Merkle roots", error))?;

    let mut trace_merkle_table = crate::trace_merkle_air::TraceMerkleLeafTable::new();
    let trace_claims = crate::trace_merkle_air::push_trace_merkle_leaves(
        &mut trace_merkle_table,
        &mut poseidon2,
        &preprocessing.trace_merkle,
        &preprocessing.query_position,
        UniversalTraceOpeningWitness::Segment(TraceOpeningSet {
            queried_values: &leaf.proof().queried_values[..],
            raw_queries: &raw_queries,
        }),
    )
    .map_err(|error| stage("trace Merkle leaves", error))?;
    let mut merkle_path_table = merkle_path::MerklePathTable::new();
    crate::trace_merkle_air::push_trace_merkle_paths(
        &mut merkle_path_table,
        &mut poseidon2,
        &trace_claims,
        UniversalTracePathWitness::Segment(TracePathSet {
            roots: &leaf.proof().commitments,
            paths: &leaf.proof().trace_paths[..],
        }),
    )
    .map_err(|error| stage("trace Merkle paths", error))?;

    let pcs_references = preprocessing.pcs_references.lanes();
    let pcs_witnesses = [
        PcsDeepCircuitLane {
            verifier_id: SEGMENT_VERIFIER_ID,
            circuit_id: PCS_CIRCUIT_IDS[0],
            circuit: &pcs_circuit,
        },
        pcs_references[1],
        pcs_references[2],
    ];
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
        UniversalFriMerkleWitness::Segment(&fri_opening),
    )
    .map_err(|error| stage("FRI Merkle authentication", error))?;

    let inactive_queries =
        vec![M31Word::ZERO; preprocessing.query_position.recursion_query_count()];
    let query_lanes = [
        FriVerifierQueryLane {
            verifier_id: SEGMENT_VERIFIER_ID,
            raw_queries: &raw_queries,
        },
        FriVerifierQueryLane {
            verifier_id: LEFT_RECURSION_VERIFIER_ID,
            raw_queries: &inactive_queries,
        },
        FriVerifierQueryLane {
            verifier_id: RIGHT_RECURSION_VERIFIER_ID,
            raw_queries: &inactive_queries,
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
    let fri_witnesses = [
        FriVerifierCircuitLane {
            verifier_id: SEGMENT_VERIFIER_ID,
            circuit_id: FRI_CIRCUIT_IDS[0],
            circuit: &fri_circuit,
        },
        fri_references[1],
        fri_references[2],
    ];
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
        &statement_circuit,
    )
    .map_err(|error| stage("statement circuit lowering", error))?;
    crate::vm_public_claim_semantics_lowering::lower_vm_public_claim_semantics_circuit(
        &mut circuit_traces,
        VM_CLAIM_CIRCUIT_ID,
        &preprocessing.vm_claim_reference,
        &vm_claim_circuit,
    )
    .map_err(|error| stage("VM claim circuit lowering", error))?;
    crate::vm_public_logup_lowering::lower_vm_public_logup_circuit(
        &mut circuit_traces,
        VM_PUBLIC_LOGUP_CIRCUIT_ID,
        &preprocessing.vm_public_logup_reference,
        &vm_public_logup_circuit,
    )
    .map_err(|error| stage("VM public-LogUp circuit lowering", error))?;
    crate::vm_air_composition_lowering::lower_vm_air_composition_circuit(
        &mut circuit_traces,
        VM_COMPOSITION_CIRCUIT_ID,
        &preprocessing.vm_composition_reference,
        &vm_composition_circuit,
    )
    .map_err(|error| stage("VM AIR-composition circuit lowering", error))?;
    crate::pcs_deep_lowering::lower_pcs_deep_circuit(
        &mut circuit_traces,
        PCS_CIRCUIT_IDS[0],
        &preprocessing.pcs_references.segment,
        &pcs_circuit,
    )
    .map_err(|error| stage("PCS DEEP circuit lowering", error))?;
    crate::fri_verifier_lowering::lower_fri_verifier_circuit(
        &mut circuit_traces,
        FRI_CIRCUIT_IDS[0],
        &preprocessing.fri_references.segment,
        &fri_circuit,
    )
    .map_err(|error| stage("FRI verifier circuit lowering", error))?;

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

    finalize_universal_witness(
        leaf.statement(),
        relations,
        preprocessing,
        preprocessed_components,
        original_components,
        component_log_sizes,
        profile.recursion_program().column_log_sizes(),
    )
}

const STATEMENT_CIRCUIT_ID: u32 = 1;
const VM_CLAIM_CIRCUIT_ID: u32 = 2;
const VM_PUBLIC_LOGUP_CIRCUIT_ID: u32 = 3;
const VM_COMPOSITION_CIRCUIT_ID: u32 = 4;
const PCS_CIRCUIT_IDS: [u32; 3] = [10, 11, 12];
const FRI_CIRCUIT_IDS: [u32; 3] = [20, 21, 22];

struct PcsCircuitSet {
    segment: PcsDeepCircuit,
    left: PcsDeepCircuit,
    right: PcsDeepCircuit,
}

impl PcsCircuitSet {
    fn lanes(&self) -> [PcsDeepCircuitLane<'_>; 3] {
        [
            PcsDeepCircuitLane {
                verifier_id: SEGMENT_VERIFIER_ID,
                circuit_id: PCS_CIRCUIT_IDS[0],
                circuit: &self.segment,
            },
            PcsDeepCircuitLane {
                verifier_id: LEFT_RECURSION_VERIFIER_ID,
                circuit_id: PCS_CIRCUIT_IDS[1],
                circuit: &self.left,
            },
            PcsDeepCircuitLane {
                verifier_id: RIGHT_RECURSION_VERIFIER_ID,
                circuit_id: PCS_CIRCUIT_IDS[2],
                circuit: &self.right,
            },
        ]
    }
}

struct FriCircuitSet {
    segment: FriVerifierCircuit,
    left: FriVerifierCircuit,
    right: FriVerifierCircuit,
}

impl FriCircuitSet {
    fn lanes(&self) -> [FriVerifierCircuitLane<'_>; 3] {
        [
            FriVerifierCircuitLane {
                verifier_id: SEGMENT_VERIFIER_ID,
                circuit_id: FRI_CIRCUIT_IDS[0],
                circuit: &self.segment,
            },
            FriVerifierCircuitLane {
                verifier_id: LEFT_RECURSION_VERIFIER_ID,
                circuit_id: FRI_CIRCUIT_IDS[1],
                circuit: &self.left,
            },
            FriVerifierCircuitLane {
                verifier_id: RIGHT_RECURSION_VERIFIER_ID,
                circuit_id: FRI_CIRCUIT_IDS[2],
                circuit: &self.right,
            },
        ]
    }
}

/// Trusted preprocessing and inactive circuit structure for the full roster.
struct UniversalPreprocessing {
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
    vm_composition_input: VmAirCompositionInputPreprocessed,
    vm_composition_control: VmAirCompositionControlPreprocessed,
    query_position: QueryPositionPreprocessed,
    merkle_root: MerkleRootPreprocessed,
    trace_merkle: TraceMerklePreprocessed,
    pcs_profiles: [PcsDeepProfile; 2],
    pcs_references: PcsCircuitSet,
    pcs_input: PcsDeepInputPreprocessed,
    fri_merkle: FriMerklePreprocessed,
    fri_profiles: [FriVerifierProfile; 2],
    fri_references: FriCircuitSet,
    fri_control: FriVerifierControlPreprocessed,
    fri_input: FriVerifierInputPreprocessed,
}

impl UniversalPreprocessing {
    fn new(profile: &FrozenProtocolProfile) -> Result<Self, UniversalWitnessError> {
        let vm_plan = profile.vm_plan();
        let recursion_plan = profile.recursion_plan();
        let manifest = profile.manifest();
        let raw_manifest = manifest.manifest();
        let control = ControlPreprocessed::new(vm_plan, recursion_plan)
            .map_err(|error| stage("control preprocessing", error))?;
        let transcript_calls = TranscriptCallPreprocessed::new(vm_plan, recursion_plan)
            .map_err(|error| stage("transcript-call preprocessing", error))?;
        let transcript_state = TranscriptStatePreprocessed::new(&transcript_calls)
            .map_err(|error| stage("transcript-state preprocessing", error))?;
        let transcript_word = TranscriptWordPreprocessed::new(&transcript_calls)
            .map_err(|error| stage("transcript-word preprocessing", error))?;
        let transcript_payload =
            TranscriptPayloadPreprocessed::new(&transcript_calls, manifest.protocol_id())
                .map_err(|error| stage("transcript-payload preprocessing", error))?;
        let relation_challenge = RelationChallengePreprocessed::new(vm_plan, recursion_plan)
            .map_err(|error| stage("relation-challenge preprocessing", error))?;
        let verifier_randomness = VerifierRandomnessPreprocessed::new(vm_plan, recursion_plan)
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
        )
        .map_err(|error| stage("VM public-LogUp control preprocessing", error))?;

        let vm_composition_reference =
            build_vm_air_composition_reference(crate::profile::vm_component_log_sizes())
                .map_err(|error| stage("VM composition reference", error))?;
        let vm_composition_input = VmAirCompositionInputPreprocessed::new(
            &vm_composition_reference,
            VM_COMPOSITION_CIRCUIT_ID,
        )
        .map_err(|error| stage("VM composition input preprocessing", error))?;
        let vm_composition_control =
            VmAirCompositionControlPreprocessed::new(vm_plan, vm_composition_reference.profile())
                .map_err(|error| stage("VM composition control preprocessing", error))?;

        let query_position = QueryPositionPreprocessed::new(
            manifest.vm_pcs(),
            &raw_manifest.vm_proof_shape,
            manifest.recursion_pcs(),
            &raw_manifest.recursion_proof_shape,
        )
        .map_err(|error| stage("query-position preprocessing", error))?;
        let merkle_root = MerkleRootPreprocessed::new(
            manifest.vm_pcs(),
            &raw_manifest.vm_proof_shape,
            manifest.recursion_pcs(),
            &raw_manifest.recursion_proof_shape,
        )
        .map_err(|error| stage("Merkle-root preprocessing", error))?;
        let trace_merkle = TraceMerklePreprocessed::new(
            vm_plan,
            &raw_manifest.vm_proof_shape,
            &profile.vm_program().column_log_sizes().0,
            recursion_plan,
            &raw_manifest.recursion_proof_shape,
            &profile.recursion_program().column_log_sizes().0,
        )
        .map_err(|error| stage("trace-Merkle preprocessing", error))?;

        let vm_pcs_profile = PcsDeepProfile::from_vm(profile.vm_program(), profile.vm_layout())
            .map_err(|error| stage("VM PCS circuit profile", error))?;
        let recursion_pcs_profile = recursion_pcs_profile(profile)?;
        let pcs_references = PcsCircuitSet {
            segment: build_pcs_deep_reference(&vm_pcs_profile)
                .map_err(|error| stage("segment PCS reference", error))?,
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
            recursion_plan,
            &raw_manifest.recursion_proof_shape,
        )
        .map_err(|error| stage("FRI Merkle preprocessing", error))?;
        let vm_fri_profile =
            FriVerifierProfile::from_shape(manifest.vm_pcs(), &raw_manifest.vm_proof_shape)
                .map_err(|error| stage("VM FRI profile", error))?;
        let recursion_fri_profile = FriVerifierProfile::from_shape(
            manifest.recursion_pcs(),
            &raw_manifest.recursion_proof_shape,
        )
        .map_err(|error| stage("recursion FRI profile", error))?;
        let fri_references = FriCircuitSet {
            segment: build_fri_verifier_reference(&vm_fri_profile)
                .map_err(|error| stage("segment FRI reference", error))?,
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
            vm_composition_input,
            vm_composition_control,
            query_position,
            merkle_root,
            trace_merkle,
            pcs_profiles: [vm_pcs_profile, recursion_pcs_profile],
            pcs_references,
            pcs_input,
            fri_merkle,
            fri_profiles: [vm_fri_profile, recursion_fri_profile],
            fri_references,
            fri_control,
            fri_input,
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
            4,
            4,
            4,
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

    fn preprocessed_components(
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
        }
        let pcs_lanes = self.pcs_references.lanes();
        let pcs_lanes = if proof_kind == ProofKind::SegmentLeaf {
            &pcs_lanes[..1]
        } else {
            &pcs_lanes[1..]
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
            &fri_lanes[..1]
        } else {
            &fri_lanes[1..]
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

    #[test]
    fn structural_tables_fit_the_frozen_component_capacities() {
        let profile = frozen_protocol_profile().expect("frozen profile is valid");
        let preprocessing =
            UniversalPreprocessing::new(&profile).expect("universal preprocessing is valid");
        let capacities = recursion_component_log_sizes();
        assert!(
            preprocessing
                .structural_log_sizes()
                .into_iter()
                .zip(capacities)
                .all(|(required, capacity)| required <= capacity)
        );
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
