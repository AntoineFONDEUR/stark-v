//! End-to-end relation closure for the current protocol FRI verification route bridge.
//!
//! The test composes the trusted FRI control schedule, its routed-scalar
//! exports, the fixed FRI arithmetic circuit, tracked input ownership, and the
//! shared arithmetic tables under one independently drawn relation set. Route
//! words flow from the real control producer to the real input consumer, so a
//! disagreement between trusted query routing and the circuit's bit-derived
//! coordinates breaks either the circuit outputs or the closure. Only external
//! control-step, query-position, transcript, randomness, DEEP-answer, and
//! authenticated-value terms remain explicit verifier anchors.

use air::digest::M31Word;
use num_traits::Zero;
use prover::poseidon2_channel::Poseidon2M31Channel;
use stwo::core::circle::Coset;
use stwo::core::fields::FieldExpOps;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::SecureField;
use stwo::core::fri::{fold_circle_into_line, fold_coset};
use stwo::core::poly::circle::{CanonicCoset, CircleDomain};
use stwo::core::poly::line::LineDomain;
use stwo::core::utils::bit_reverse_index;
use stwo_constraint_framework::Relation;

use super::control_air::{
    ControlRelations, LEFT_RECURSION_VERIFIER_ID, RIGHT_RECURSION_VERIFIER_ID, SEGMENT_VERIFIER_ID,
};
use super::fri_merkle_air::FriMerkleRelations;
use super::fri_verifier_circuit::{
    FriVerifierCircuit, FriVerifierInputSource, FriVerifierProfile, FriVerifierWitness,
    build_fri_verifier_circuit, build_fri_verifier_reference,
};
use super::fri_verifier_control_air::{
    FriVerifierControlLane, FriVerifierControlPreprocessed, FriVerifierControlTable,
    FriVerifierQueryLane, gen_interaction_trace as gen_control_interaction,
    push_fri_verifier_control,
};
use super::fri_verifier_input_air::{
    FriVerifierCircuitLane, FriVerifierInputPreprocessed, FriVerifierInputTable,
    FriVerifierRouteRelations, gen_interaction_trace as gen_input_interaction,
    push_fri_verifier_inputs,
};
use super::fri_verifier_lowering::{lower_fri_verifier_circuit, public_fri_verifier_terms};
use super::kernel::{VerifierControlPlan, VerifierProgramSpec, VerifierSchema, VerifierStep};
use super::pcs_deep_input_air::PcsDeepRelations;
use super::protocol::{FixedProofShape, OptionalM31Word, PcsParameters};
use super::query_position_air::{
    QueryPositionKind, QueryPositionPreprocessed, QueryPositionRelations,
};
use super::transcript_payload_air::{VerifierInputKind, VerifierInputRelations};
use super::verifier_randomness_air::{VerifierRandomnessKind, VerifierRandomnessRelations};
use super::wire::ProofKind;
use crate::circuit::CircuitTraces;
use crate::relations::RecursionRelations;
use crate::{linear_ops, qm31_inv, qm31_mul};

const CIRCUIT_IDS: [u32; 3] = [311, 312, 313];
const RAW_QUERY: u32 = 93;

fn word(value: u16) -> M31Word {
    M31Word::from(value)
}

fn secure(seed: u32) -> SecureField {
    SecureField::from_m31_array([
        M31::from(seed),
        M31::from(seed + 1),
        M31::from(seed + 2),
        M31::from(seed + 3),
    ])
}

fn pcs_parameters() -> PcsParameters {
    PcsParameters {
        interaction_pow_bits: word(8),
        pow_bits: word(10),
        fri_log_blowup_factor: word(1),
        fri_n_queries: word(1),
        fri_log_last_layer_degree_bound: M31Word::ZERO,
        fri_fold_step: word(2),
        lifting_log_size: OptionalM31Word::Some(word(8)),
    }
}

fn shape() -> FixedProofShape<2, 4, 4> {
    FixedProofShape {
        claimed_sum_count: word(7),
        sampled_value_count: word(8),
        queried_value_count: word(4),
        trace_path_count: word(4),
        raw_query_count: word(1),
        last_layer_coefficient_count: word(1),
        table_log_sizes: [word(5), word(6)],
        tree_heights: [word(8), word(8), word(8), word(8)],
        fri_layer_fold_widths: [word(4), word(4), word(4), word(2)],
        fri_layer_tree_heights: [word(6), word(4), word(2), word(2)],
    }
}

fn plan(schema: VerifierSchema) -> VerifierControlPlan {
    let spec =
        VerifierProgramSpec::new(schema, 3, 5, 7, 4).expect("fixture verifier program is valid");
    VerifierControlPlan::new(spec, pcs_parameters(), &shape())
        .expect("fixture verifier plan is valid")
}

struct Fixture {
    vm_plan: VerifierControlPlan,
    recursion_plan: VerifierControlPlan,
    profile: FriVerifierProfile,
    query_preprocessed: QueryPositionPreprocessed,
}

impl Fixture {
    fn new() -> Self {
        let pcs = pcs_parameters().validate().expect("fixture PCS is valid");
        let profile =
            FriVerifierProfile::from_shape(pcs, &shape()).expect("fixture FRI profile is valid");
        let query_preprocessed = QueryPositionPreprocessed::new(pcs, &shape(), pcs, &shape())
            .expect("fixture query preprocessing is valid");
        Self {
            vm_plan: plan(VerifierSchema::Vm),
            recursion_plan: plan(VerifierSchema::Recursion),
            profile,
            query_preprocessed,
        }
    }

    fn control_preprocessing(&self) -> FriVerifierControlPreprocessed {
        FriVerifierControlPreprocessed::new([
            FriVerifierControlLane {
                verifier_id: SEGMENT_VERIFIER_ID,
                plan: &self.vm_plan,
                profile: &self.profile,
            },
            FriVerifierControlLane {
                verifier_id: LEFT_RECURSION_VERIFIER_ID,
                plan: &self.recursion_plan,
                profile: &self.profile,
            },
            FriVerifierControlLane {
                verifier_id: RIGHT_RECURSION_VERIFIER_ID,
                plan: &self.recursion_plan,
                profile: &self.profile,
            },
        ])
        .expect("fixture FRI control preprocessing is valid")
    }

    /// Every trusted route the segment lane exports for the fixture query.
    fn routed(&self, kind: QueryPositionKind, item: u32) -> (u32, u32) {
        self.query_preprocessed
            .evaluate_route(
                SEGMENT_VERIFIER_ID,
                kind,
                item,
                0,
                M31Word::try_from(RAW_QUERY).expect("fixture raw query is canonical"),
            )
            .expect("fixture route is preprocessed")
    }

    /// Builds the active segment circuit whose positions and offsets come from
    /// the trusted route evaluation instead of the circuit's own bit weights.
    fn routed_segment_circuit(&self) -> FriVerifierCircuit {
        let profile = &self.profile;
        let deep_answer = secure(101);
        let alphas = (0..profile.layer_count())
            .map(|layer| secure(131 + layer as u32 * 20))
            .collect::<Vec<_>>();
        let mut values = Vec::new();
        let mut positions = Vec::new();
        let mut offsets = Vec::new();
        let mut previous = deep_answer;
        let mut current_log = profile.lifting_log_size();
        for (layer, (&fold_step, &width)) in profile
            .fold_steps()
            .iter()
            .zip(profile.fold_widths())
            .enumerate()
        {
            let (current_position, offset) = self.routed(QueryPositionKind::FriFold, layer as u32);
            let subset_start = current_position & !((1 << fold_step) - 1);
            let mut subset = (0..width)
                .map(|index| secure(211 + layer as u32 * 31 + index as u32 * 5))
                .collect::<Vec<_>>();
            subset[offset as usize] = previous;
            let initial_index = bit_reverse_index(subset_start as usize, current_log);
            previous = if layer == 0 {
                let source = CanonicCoset::new(current_log).circle_domain();
                let initial = source.index_at(initial_index);
                let circle_domain = CircleDomain::new(Coset::new(initial, fold_step - 1));
                let line = fold_circle_into_line(&subset, circle_domain, alphas[layer]);
                if fold_step == 1 {
                    line[0]
                } else {
                    fold_coset(
                        line,
                        LineDomain::new(Coset::new(initial, fold_step - 1)),
                        alphas[layer] * alphas[layer],
                    )
                }
            } else {
                let source = LineDomain::new(Coset::half_odds(current_log));
                let initial = source.coset().index_at(initial_index);
                fold_coset(
                    subset.clone(),
                    LineDomain::new(Coset::new(initial, fold_step)),
                    alphas[layer],
                )
            };
            values.push(subset);
            positions.push(vec![
                M31Word::try_from(current_position).expect("position is canonical"),
            ]);
            offsets.push(vec![
                M31Word::try_from(offset).expect("offset is canonical"),
            ]);
            current_log -= fold_step;
        }
        let (last_position, _) = self.routed(QueryPositionKind::LastLayer, 0);
        let mut coefficients = vec![SecureField::zero(); profile.last_layer_coefficient_count()];
        coefficients[0] = previous;
        build_fri_verifier_circuit(
            profile,
            FriVerifierWitness {
                active: true,
                deep_answers: &[deep_answer],
                authenticated_values: &values,
                fri_alphas: &alphas,
                raw_queries: &[M31Word::try_from(RAW_QUERY).expect("raw query is canonical")],
                fri_positions: &positions,
                fri_offsets: &offsets,
                last_layer_positions: &[
                    M31Word::try_from(last_position).expect("last position is canonical")
                ],
                last_layer_coefficients: &coefficients,
            },
        )
        .expect("fixture FRI circuit is constructible")
    }

    fn reference_lanes_circuits(&self) -> [FriVerifierCircuit; 3] {
        core::array::from_fn(|_| {
            build_fri_verifier_reference(&self.profile).expect("reference is valid")
        })
    }
}

fn circuit_lanes(circuits: &[FriVerifierCircuit; 3]) -> [FriVerifierCircuitLane<'_>; 3] {
    [
        FriVerifierCircuitLane {
            verifier_id: SEGMENT_VERIFIER_ID,
            circuit_id: CIRCUIT_IDS[0],
            circuit: &circuits[0],
        },
        FriVerifierCircuitLane {
            verifier_id: LEFT_RECURSION_VERIFIER_ID,
            circuit_id: CIRCUIT_IDS[1],
            circuit: &circuits[1],
        },
        FriVerifierCircuitLane {
            verifier_id: RIGHT_RECURSION_VERIFIER_ID,
            circuit_id: CIRCUIT_IDS[2],
            circuit: &circuits[2],
        },
    ]
}

#[test]
fn trusted_routes_satisfy_the_fri_circuit_bit_arithmetic() {
    let fixture = Fixture::new();
    assert_eq!(fixture.routed_segment_circuit().nonzero_output_count(), 0);
}

#[test]
fn fri_route_bridge_closes_between_control_and_input_airs() {
    let fixture = Fixture::new();
    let control_preprocessing = fixture.control_preprocessing();
    let raw_words = [M31Word::try_from(RAW_QUERY).expect("raw query is canonical")];
    let mut control_table = FriVerifierControlTable::new();
    push_fri_verifier_control(
        &mut control_table,
        &control_preprocessing,
        &fixture.query_preprocessed,
        [
            FriVerifierQueryLane {
                verifier_id: SEGMENT_VERIFIER_ID,
                raw_queries: &raw_words,
            },
            FriVerifierQueryLane {
                verifier_id: LEFT_RECURSION_VERIFIER_ID,
                raw_queries: &raw_words,
            },
            FriVerifierQueryLane {
                verifier_id: RIGHT_RECURSION_VERIFIER_ID,
                raw_queries: &raw_words,
            },
        ],
        ProofKind::SegmentLeaf,
    )
    .expect("fixture routes materialize");

    let references = fixture.reference_lanes_circuits();
    let witnesses = [
        fixture.routed_segment_circuit(),
        build_fri_verifier_reference(&fixture.profile).expect("left reference is valid"),
        build_fri_verifier_reference(&fixture.profile).expect("right reference is valid"),
    ];
    let input_preprocessing = FriVerifierInputPreprocessed::new(circuit_lanes(&references))
        .expect("references own every circuit input");
    let mut input_table = FriVerifierInputTable::new();
    push_fri_verifier_inputs(
        &mut input_table,
        &input_preprocessing,
        circuit_lanes(&references),
        circuit_lanes(&witnesses),
        ProofKind::SegmentLeaf,
    )
    .expect("segment witness matches the universal input layout");

    let mut channel = Poseidon2M31Channel::default();
    let control_relations = ControlRelations::draw(&mut channel);
    let query_relations = QueryPositionRelations::draw(&mut channel);
    let route_relations = FriVerifierRouteRelations::draw(&mut channel);
    let verifier_input_relations = VerifierInputRelations::draw(&mut channel);
    let randomness_relations = VerifierRandomnessRelations::draw(&mut channel);
    let deep_relations = PcsDeepRelations::draw(&mut channel);
    let fri_merkle_relations = FriMerkleRelations::draw(&mut channel);
    let circuit_relations = RecursionRelations::draw(&mut channel);

    let (_, control_sum) = gen_control_interaction(
        &control_table.into_witness(),
        &control_preprocessing.gen_columns(),
        ProofKind::SegmentLeaf,
        &control_relations,
        &query_relations,
        &route_relations,
    );
    let (_, input_sum) = gen_input_interaction(
        &input_table.into_witness(),
        &input_preprocessing.gen_columns(),
        ProofKind::SegmentLeaf,
        &verifier_input_relations,
        &randomness_relations,
        &query_relations,
        &deep_relations,
        &fri_merkle_relations,
        &route_relations,
        &circuit_relations,
    );

    let schedule_sum = control_schedule_terms(&fixture, &control_relations, &query_relations);
    let semantic_sum = non_route_semantic_terms(
        SEGMENT_VERIFIER_ID,
        &witnesses[0],
        &verifier_input_relations,
        &randomness_relations,
        &query_relations,
        &deep_relations,
        &fri_merkle_relations,
    );

    let mut traces = CircuitTraces::default();
    let segment_reference = circuit_lanes(&references)[0];
    let segment_witness = circuit_lanes(&witnesses)[0];
    lower_fri_verifier_circuit(
        &mut traces,
        segment_reference.circuit_id,
        segment_reference.circuit,
        segment_witness.circuit,
    )
    .expect("valid segment FRI circuit lowers");
    let (_, mul_sum) =
        qm31_mul::gen_interaction_trace(&traces.qm31_mul.into_witness(), &circuit_relations);
    let (_, inverse_sum) =
        qm31_inv::gen_interaction_trace(&traces.qm31_inv.into_witness(), &circuit_relations);
    let (_, linear_sum) =
        linear_ops::gen_interaction_trace(&traces.linear_ops.into_witness(), &circuit_relations);
    let public_sum = public_fri_verifier_terms(
        segment_reference.circuit_id,
        segment_reference.circuit,
        &circuit_relations,
    )
    .expect("segment reference outputs are zero");

    assert!(
        (control_sum
            + input_sum
            + schedule_sum
            + semantic_sum
            + mul_sum
            + inverse_sum
            + linear_sum
            + public_sum)
            .is_zero()
    );
}

/// Emulates the universal schedule and atomic query-route producers the FRI
/// control adapter consumes for its active lane.
fn control_schedule_terms(
    fixture: &Fixture,
    control_relations: &ControlRelations,
    query_relations: &QueryPositionRelations,
) -> SecureField {
    let mut total = SecureField::zero();
    for (sequence, step) in fixture.vm_plan.steps().iter().copied().enumerate() {
        let route = match step {
            VerifierStep::EvaluateDeepQuotient { .. } => None,
            VerifierStep::FoldFri { layer, query, .. } => {
                Some((QueryPositionKind::FriFold, layer, query))
            }
            VerifierStep::VerifyLastLayer { query } => {
                Some((QueryPositionKind::LastLayer, 0, query))
            }
            _ => continue,
        };
        let encoded = step.encode();
        total += inverse_term(
            &control_relations.step,
            &[
                M31::from(SEGMENT_VERIFIER_ID),
                M31::from(u32::try_from(sequence).expect("fixture sequence fits u32")),
                M31::from(encoded.tag()),
                M31::from(encoded.args()[0]),
                M31::from(encoded.args()[1]),
                M31::from(encoded.args()[2]),
                M31::from(encoded.args()[3]),
            ],
        );
        if let Some((kind, item, query)) = route {
            let (position, offset) = fixture.routed(kind, item);
            total += inverse_term(
                &query_relations.position,
                &[
                    M31::from(SEGMENT_VERIFIER_ID),
                    M31::from(kind.as_u32()),
                    M31::from(item),
                    M31::from(query),
                    M31::from(position),
                    M31::from(offset),
                ],
            );
        }
    }
    total
}

/// Emulates every non-route semantic producer of the active input lane.
fn non_route_semantic_terms(
    verifier_id: u32,
    circuit: &FriVerifierCircuit,
    verifier_input_relations: &VerifierInputRelations,
    randomness_relations: &VerifierRandomnessRelations,
    query_relations: &QueryPositionRelations,
    deep_relations: &PcsDeepRelations,
    fri_merkle_relations: &FriMerkleRelations,
) -> SecureField {
    let arena = circuit.circuit().arena();
    circuit
        .input_bindings()
        .iter()
        .fold(SecureField::zero(), |sum, binding| {
            let value = arena.nodes[binding.node_id as usize].value.to_m31_array()[0];
            let term = match binding.source {
                FriVerifierInputSource::ActiveSelector
                | FriVerifierInputSource::FriPosition { .. }
                | FriVerifierInputSource::FriOffset { .. }
                | FriVerifierInputSource::LastLayerPosition { .. } => return sum,
                FriVerifierInputSource::DeepAnswerWord { query, word } => inverse_term(
                    &deep_relations.answer_word,
                    &[
                        M31::from(verifier_id),
                        M31::from(query),
                        M31::from(word),
                        value,
                    ],
                ),
                FriVerifierInputSource::AuthenticatedValueWord {
                    layer,
                    query,
                    offset,
                    word,
                } => inverse_term(
                    &fri_merkle_relations.value_word,
                    &[
                        M31::from(verifier_id),
                        M31::from(layer),
                        M31::from(query),
                        M31::from(offset),
                        M31::from(word),
                        value,
                    ],
                ),
                FriVerifierInputSource::FriAlphaWord { layer, word } => inverse_term(
                    &randomness_relations.word,
                    &[
                        M31::from(verifier_id),
                        M31::from(VerifierRandomnessKind::FriAlpha.as_u32()),
                        M31::from(layer),
                        M31::from(word),
                        value,
                    ],
                ),
                FriVerifierInputSource::QueryBit { query, bit } => inverse_term(
                    &query_relations.bit_value,
                    &[
                        M31::from(verifier_id),
                        M31::from(query),
                        M31::from(bit),
                        value,
                    ],
                ),
                FriVerifierInputSource::LastLayerCoefficientWord { coefficient, word } => {
                    inverse_term(
                        &verifier_input_relations.input_word,
                        &[
                            M31::from(verifier_id),
                            M31::from(VerifierInputKind::LastLayerCoefficient.as_u32()),
                            M31::from(coefficient),
                            M31::from(word),
                            value,
                        ],
                    )
                }
            };
            sum + term
        })
}

fn inverse_term<R: Relation<M31, SecureField>>(relation: &R, values: &[M31]) -> SecureField {
    let denominator: SecureField = relation.combine(values);
    denominator.inverse()
}
