//! Lowering and public anchors for fixed FRI verifier circuits.
//!
//! Shared arithmetic tables own every operation reachable from the designated
//! zero constraints. The input AIR supplies tracked nodes, while verifier
//! terms fix constants, operation identities, and every zero output. A witness
//! can therefore change values but cannot replace the native FRI fold graph.

use core::fmt;

use air::digest::M31Word;
use num_traits::Zero;
use stwo::core::fields::FieldExpOps;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::SecureField;
use stwo_constraint_framework::Relation;

use super::fri_verifier_circuit::FriVerifierCircuit;
use crate::circuit::CircuitTraces;
use crate::circuit::{limbs, lower_arena_operations, use_counts_for_outputs};
use crate::recorder::Op;
use crate::relations::{RecursionRelations, op_kind};

/// Lowers one structurally checked FRI circuit into shared arithmetic traces.
pub fn lower_fri_verifier_circuit(
    traces: &mut CircuitTraces,
    circuit_id: u32,
    reference: &FriVerifierCircuit,
    witness: &FriVerifierCircuit,
) -> Result<(), FriVerifierLoweringError> {
    validate_circuit_id(circuit_id)?;
    validate_structure(reference, witness)?;
    if witness.nonzero_output_count() != 0 {
        return Err(FriVerifierLoweringError::NonzeroConstraintOutput);
    }
    let arena = witness.circuit().arena();
    lower_arena_operations(traces, circuit_id, &arena, witness.circuit().outputs());
    Ok(())
}

/// Verifier contribution for constants, operation structure, and zero outputs.
pub fn public_fri_verifier_terms(
    circuit_id: u32,
    reference: &FriVerifierCircuit,
    relations: &RecursionRelations,
) -> Result<SecureField, FriVerifierLoweringError> {
    validate_circuit_id(circuit_id)?;
    if reference.nonzero_output_count() != 0 {
        return Err(FriVerifierLoweringError::ReferenceOutputIsNonzero);
    }
    let arena = reference.circuit().arena();
    let uses = use_counts_for_outputs(&arena, reference.circuit().outputs());
    let mut total = SecureField::zero();
    for (node_index, node) in arena.nodes.iter().enumerate() {
        let node_id = checked_node_id(node_index)?;
        match node.op {
            Op::Input => {}
            Op::Const => {
                if uses[node_index] != 0 {
                    total += wire_term(circuit_id, node_id, node.value, relations)
                        * SecureField::from(M31::from(uses[node_index]));
                }
            }
            operation => {
                let (kind, lhs, rhs) = operation_tuple(operation)?;
                let denominator: SecureField = relations.op_def.combine(&[
                    M31::from(circuit_id),
                    M31::from(node_id),
                    M31::from(kind),
                    M31::from(lhs),
                    M31::from(rhs),
                ]);
                total += denominator.inverse();
            }
        }
    }
    for output in reference.circuit().outputs() {
        total -= wire_term(
            circuit_id,
            checked_node_id(*output)?,
            SecureField::zero(),
            relations,
        );
    }
    Ok(total)
}

fn validate_circuit_id(circuit_id: u32) -> Result<(), FriVerifierLoweringError> {
    M31Word::try_from(circuit_id)
        .map(|_| ())
        .map_err(|_| FriVerifierLoweringError::CircuitIdNotCanonical { circuit_id })
}

fn validate_structure(
    reference: &FriVerifierCircuit,
    witness: &FriVerifierCircuit,
) -> Result<(), FriVerifierLoweringError> {
    if reference.profile() != witness.profile() {
        return Err(FriVerifierLoweringError::ProfileMismatch);
    }
    if reference.input_bindings() != witness.input_bindings() {
        return Err(FriVerifierLoweringError::InputLayoutMismatch);
    }
    if reference.circuit().outputs() != witness.circuit().outputs() {
        return Err(FriVerifierLoweringError::OutputLayoutMismatch);
    }
    let reference_arena = reference.circuit().arena();
    let witness_arena = witness.circuit().arena();
    if reference_arena.nodes.len() != witness_arena.nodes.len() {
        return Err(FriVerifierLoweringError::NodeCountMismatch {
            expected: reference_arena.nodes.len(),
            actual: witness_arena.nodes.len(),
        });
    }
    for (node_id, (expected, actual)) in reference_arena
        .nodes
        .iter()
        .zip(&witness_arena.nodes)
        .enumerate()
    {
        if expected.op != actual.op
            || (matches!(expected.op, Op::Const) && expected.value != actual.value)
        {
            return Err(FriVerifierLoweringError::NodeStructureMismatch { node_id });
        }
    }
    Ok(())
}

fn checked_node_id(node_id: usize) -> Result<u32, FriVerifierLoweringError> {
    u32::try_from(node_id).map_err(|_| FriVerifierLoweringError::NodeIdOutOfRange { node_id })
}

fn operation_tuple(operation: Op) -> Result<(u32, u32, u32), FriVerifierLoweringError> {
    let convert = |node_id| checked_node_id(node_id);
    match operation {
        Op::Add(lhs, rhs) => Ok((op_kind::ADD, convert(lhs)?, convert(rhs)?)),
        Op::Sub(lhs, rhs) => Ok((op_kind::SUB, convert(lhs)?, convert(rhs)?)),
        Op::Mul(lhs, rhs) => Ok((op_kind::MUL, convert(lhs)?, convert(rhs)?)),
        Op::Neg(lhs) => Ok((op_kind::NEG, convert(lhs)?, 0)),
        Op::Inverse(lhs) => Ok((op_kind::INVERSE, convert(lhs)?, 0)),
        Op::Input | Op::Const => Err(FriVerifierLoweringError::NonArithmeticOperation),
    }
}

fn wire_term(
    circuit_id: u32,
    node_id: u32,
    value: SecureField,
    relations: &RecursionRelations,
) -> SecureField {
    let value = limbs(value);
    let denominator: SecureField = relations.wire.combine(&[
        M31::from(circuit_id),
        M31::from(node_id),
        M31::from(value[0]),
        M31::from(value[1]),
        M31::from(value[2]),
        M31::from(value[3]),
    ]);
    denominator.inverse()
}

/// Invalid circuit identity, structure, or FRI fold witness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FriVerifierLoweringError {
    CircuitIdNotCanonical { circuit_id: u32 },
    ProfileMismatch,
    InputLayoutMismatch,
    OutputLayoutMismatch,
    NodeCountMismatch { expected: usize, actual: usize },
    NodeStructureMismatch { node_id: usize },
    NodeIdOutOfRange { node_id: usize },
    NonArithmeticOperation,
    NonzeroConstraintOutput,
    ReferenceOutputIsNonzero,
}

impl fmt::Display for FriVerifierLoweringError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for FriVerifierLoweringError {}

#[cfg(test)]
mod tests {
    use num_traits::One;
    use prover::poseidon2_channel::Poseidon2M31Channel;
    use stwo::core::circle::Coset;
    use stwo::core::fri::{fold_circle_into_line, fold_coset};
    use stwo::core::poly::circle::{CanonicCoset, CircleDomain};
    use stwo::core::poly::line::LineDomain;
    use stwo::core::utils::bit_reverse_index;

    use super::*;
    use crate::control_air::{
        LEFT_RECURSION_VERIFIER_ID, RIGHT_RECURSION_VERIFIER_ID, SEGMENT_VERIFIER_ID,
    };
    use crate::fri_merkle_air::FriMerkleRelations;
    use crate::fri_verifier_circuit::{
        FriVerifierInputSource, FriVerifierProfile, FriVerifierWitness, build_fri_verifier_circuit,
        build_fri_verifier_reference,
    };
    use crate::fri_verifier_input_air::{
        FriVerifierCircuitLane, FriVerifierInputPreprocessed, FriVerifierInputTable,
        FriVerifierRouteField, FriVerifierRouteRelations,
        gen_interaction_trace as gen_input_interaction_trace, push_fri_verifier_inputs,
    };
    use crate::pcs_deep_input_air::PcsDeepRelations;
    use crate::query_position_air::{QueryPositionKind, QueryPositionRelations};
    use crate::transcript_payload_air::{VerifierInputKind, VerifierInputRelations};
    use crate::verifier_randomness_air::{VerifierRandomnessKind, VerifierRandomnessRelations};
    use crate::wire::ProofKind;
    use crate::{linear_ops, qm31_inv, qm31_mul};

    const CIRCUIT_IDS: [u32; 3] = [301, 302, 303];

    struct CircuitSet {
        segment: FriVerifierCircuit,
        left: FriVerifierCircuit,
        right: FriVerifierCircuit,
    }

    impl CircuitSet {
        fn lanes(&self) -> [FriVerifierCircuitLane<'_>; 3] {
            [
                FriVerifierCircuitLane {
                    verifier_id: SEGMENT_VERIFIER_ID,
                    circuit_id: CIRCUIT_IDS[0],
                    circuit: &self.segment,
                },
                FriVerifierCircuitLane {
                    verifier_id: LEFT_RECURSION_VERIFIER_ID,
                    circuit_id: CIRCUIT_IDS[1],
                    circuit: &self.left,
                },
                FriVerifierCircuitLane {
                    verifier_id: RIGHT_RECURSION_VERIFIER_ID,
                    circuit_id: CIRCUIT_IDS[2],
                    circuit: &self.right,
                },
            ]
        }
    }

    fn secure(seed: u32) -> SecureField {
        SecureField::from_m31_array([
            M31::from(seed),
            M31::from(seed + 1),
            M31::from(seed + 2),
            M31::from(seed + 3),
        ])
    }

    fn profile() -> FriVerifierProfile {
        FriVerifierProfile::new(8, 1, 2, vec![4, 4, 2], 1).expect("fixture FRI profile is valid")
    }

    /// Builds an active single-query witness that satisfies every fold and
    /// last-layer constraint against STWO's native folding arithmetic.
    fn satisfying_circuit(profile: &FriVerifierProfile) -> FriVerifierCircuit {
        let raw = 93_u32;
        let deep_answer = secure(101);
        let alphas = vec![secure(131), secure(151), secure(173)];
        let mut values = Vec::new();
        let mut positions = Vec::new();
        let mut offsets = Vec::new();
        let mut previous = deep_answer;
        let mut folded_bits = 0_u32;
        let mut current_log = profile.lifting_log_size();
        for (layer, (&fold_step, &width)) in profile
            .fold_steps()
            .iter()
            .zip(profile.fold_widths())
            .enumerate()
        {
            let current_position = raw >> folded_bits;
            let offset = current_position & ((1 << fold_step) - 1);
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
            folded_bits += fold_step;
            current_log -= fold_step;
        }
        let last_position = raw >> folded_bits;
        let mut coefficients = vec![SecureField::zero(); profile.last_layer_coefficient_count()];
        coefficients[0] = previous;
        build_fri_verifier_circuit(
            profile,
            FriVerifierWitness {
                active: true,
                deep_answers: &[deep_answer],
                authenticated_values: &values,
                fri_alphas: &alphas,
                raw_queries: &[M31Word::try_from(raw).expect("raw query is canonical")],
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

    fn reference_set(profile: &FriVerifierProfile) -> CircuitSet {
        CircuitSet {
            segment: build_fri_verifier_reference(profile).expect("segment reference is valid"),
            left: build_fri_verifier_reference(profile).expect("left reference is valid"),
            right: build_fri_verifier_reference(profile).expect("right reference is valid"),
        }
    }

    fn segment_witness_set(profile: &FriVerifierProfile) -> CircuitSet {
        CircuitSet {
            segment: satisfying_circuit(profile),
            left: build_fri_verifier_reference(profile).expect("left reference is valid"),
            right: build_fri_verifier_reference(profile).expect("right reference is valid"),
        }
    }

    #[test]
    fn lowering_rejects_a_changed_last_layer_evaluation() {
        let profile = profile();
        let reference = build_fri_verifier_reference(&profile).expect("reference is valid");
        let deep_answers = vec![SecureField::zero(); profile.query_count()];
        let authenticated_values = profile
            .fold_widths()
            .iter()
            .map(|width| vec![SecureField::zero(); profile.query_count() * width])
            .collect::<Vec<_>>();
        let fri_alphas = vec![SecureField::zero(); profile.layer_count()];
        let raw_queries = vec![M31Word::ZERO; profile.query_count()];
        let fri_positions = profile
            .fold_widths()
            .iter()
            .map(|_| vec![M31Word::ZERO; profile.query_count()])
            .collect::<Vec<_>>();
        let fri_offsets = fri_positions.clone();
        let last_layer_positions = vec![M31Word::ZERO; profile.query_count()];
        let mut coefficients = vec![SecureField::zero(); profile.last_layer_coefficient_count()];
        coefficients[0] = SecureField::one();
        let broken = build_fri_verifier_circuit(
            &profile,
            FriVerifierWitness {
                active: true,
                deep_answers: &deep_answers,
                authenticated_values: &authenticated_values,
                fri_alphas: &fri_alphas,
                raw_queries: &raw_queries,
                fri_positions: &fri_positions,
                fri_offsets: &fri_offsets,
                last_layer_positions: &last_layer_positions,
                last_layer_coefficients: &coefficients,
            },
        )
        .expect("perturbed circuit is constructible");
        assert_eq!(
            lower_fri_verifier_circuit(
                &mut CircuitTraces::default(),
                CIRCUIT_IDS[0],
                &reference,
                &broken,
            ),
            Err(FriVerifierLoweringError::NonzeroConstraintOutput)
        );
    }

    #[test]
    fn lowered_fri_relations_close_exactly() {
        let profile = profile();
        let references = reference_set(&profile);
        let witnesses = segment_witness_set(&profile);
        let preprocessing = FriVerifierInputPreprocessed::new(references.lanes())
            .expect("references own every circuit input");
        let mut input_table = FriVerifierInputTable::new();
        push_fri_verifier_inputs(
            &mut input_table,
            &preprocessing,
            references.lanes(),
            witnesses.lanes(),
            ProofKind::SegmentLeaf,
        )
        .expect("segment witness matches the universal input layout");

        let mut channel = Poseidon2M31Channel::default();
        let verifier_input_relations = VerifierInputRelations::draw(&mut channel);
        let randomness_relations = VerifierRandomnessRelations::draw(&mut channel);
        let query_relations = QueryPositionRelations::draw(&mut channel);
        let deep_relations = PcsDeepRelations::draw(&mut channel);
        let fri_merkle_relations = FriMerkleRelations::draw(&mut channel);
        let route_relations = FriVerifierRouteRelations::draw(&mut channel);
        let circuit_relations = RecursionRelations::draw(&mut channel);
        let (_, input_sum) = gen_input_interaction_trace(
            &input_table.into_witness(),
            &preprocessing.gen_columns(),
            ProofKind::SegmentLeaf,
            &verifier_input_relations,
            &randomness_relations,
            &query_relations,
            &deep_relations,
            &fri_merkle_relations,
            &route_relations,
            &circuit_relations,
        );
        let semantic_sum = semantic_source_terms(
            SEGMENT_VERIFIER_ID,
            &witnesses.segment,
            &verifier_input_relations,
            &randomness_relations,
            &query_relations,
            &deep_relations,
            &fri_merkle_relations,
            &route_relations,
        );

        let mut traces = CircuitTraces::default();
        lower_fri_verifier_circuit(
            &mut traces,
            CIRCUIT_IDS[0],
            &references.segment,
            &witnesses.segment,
        )
        .expect("valid segment FRI circuit lowers");
        let (_, mul_sum) =
            qm31_mul::gen_interaction_trace(&traces.qm31_mul.into_witness(), &circuit_relations);
        let (_, inverse_sum) =
            qm31_inv::gen_interaction_trace(&traces.qm31_inv.into_witness(), &circuit_relations);
        let (_, linear_sum) = linear_ops::gen_interaction_trace(
            &traces.linear_ops.into_witness(),
            &circuit_relations,
        );
        let public_sum =
            public_fri_verifier_terms(CIRCUIT_IDS[0], &references.segment, &circuit_relations)
                .expect("segment reference outputs are zero");
        assert!(
            (input_sum + semantic_sum + mul_sum + inverse_sum + linear_sum + public_sum).is_zero()
        );
    }

    #[allow(clippy::too_many_arguments)]
    fn semantic_source_terms(
        verifier_id: u32,
        circuit: &FriVerifierCircuit,
        verifier_input_relations: &VerifierInputRelations,
        randomness_relations: &VerifierRandomnessRelations,
        query_relations: &QueryPositionRelations,
        deep_relations: &PcsDeepRelations,
        fri_merkle_relations: &FriMerkleRelations,
        route_relations: &FriVerifierRouteRelations,
    ) -> SecureField {
        let arena = circuit.circuit().arena();
        circuit
            .input_bindings()
            .iter()
            .fold(SecureField::zero(), |sum, binding| {
                let value = arena.nodes[binding.node_id as usize].value.to_m31_array()[0];
                let term = match binding.source {
                    FriVerifierInputSource::ActiveSelector => return sum,
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
                    FriVerifierInputSource::FriPosition { layer, query } => inverse_term(
                        &route_relations.word,
                        &[
                            M31::from(verifier_id),
                            M31::from(QueryPositionKind::FriFold.as_u32()),
                            M31::from(layer),
                            M31::from(query),
                            M31::from(FriVerifierRouteField::Position.as_u32()),
                            value,
                        ],
                    ),
                    FriVerifierInputSource::FriOffset { layer, query } => inverse_term(
                        &route_relations.word,
                        &[
                            M31::from(verifier_id),
                            M31::from(QueryPositionKind::FriFold.as_u32()),
                            M31::from(layer),
                            M31::from(query),
                            M31::from(FriVerifierRouteField::Offset.as_u32()),
                            value,
                        ],
                    ),
                    FriVerifierInputSource::LastLayerPosition { query } => inverse_term(
                        &route_relations.word,
                        &[
                            M31::from(verifier_id),
                            M31::from(QueryPositionKind::LastLayer.as_u32()),
                            M31::from(0_u32),
                            M31::from(query),
                            M31::from(FriVerifierRouteField::Position.as_u32()),
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
}
