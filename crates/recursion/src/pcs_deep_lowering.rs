//! Lowering and public anchors for fixed PCS DEEP circuits.
//!
//! Shared arithmetic tables own every operation reachable from the designated
//! zero constraints and preprocessing fixes their graph. The input AIR
//! supplies tracked nodes, while verifier anchors fix constants and every zero
//! output.

use core::fmt;

use air::digest::M31Word;
use num_traits::Zero;
use stwo::core::fields::FieldExpOps;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::SecureField;
use stwo_constraint_framework::Relation;

use super::pcs_deep_circuit::PcsDeepCircuit;
use crate::circuit::CircuitTraces;
use crate::circuit::{limbs, lower_arena_operations, use_counts_for_outputs};
use crate::recorder::Op;
use crate::relations::RecursionRelations;

/// Lowers one structurally checked DEEP circuit into shared arithmetic traces.
pub fn lower_pcs_deep_circuit(
    traces: &mut CircuitTraces,
    circuit_id: u32,
    reference: &PcsDeepCircuit,
    witness: &PcsDeepCircuit,
) -> Result<(), PcsDeepLoweringError> {
    validate_circuit_id(circuit_id)?;
    validate_structure(reference, witness)?;
    if witness.nonzero_output_count() != 0 {
        return Err(PcsDeepLoweringError::NonzeroConstraintOutput);
    }
    let arena = witness.circuit().arena();
    lower_arena_operations(traces, circuit_id, &arena, witness.circuit().outputs());
    Ok(())
}

/// Verifier contribution for constants and zero outputs.
pub fn public_pcs_deep_terms(
    circuit_id: u32,
    reference: &PcsDeepCircuit,
    relations: &RecursionRelations,
) -> Result<SecureField, PcsDeepLoweringError> {
    validate_circuit_id(circuit_id)?;
    if reference.nonzero_output_count() != 0 {
        return Err(PcsDeepLoweringError::ReferenceOutputIsNonzero);
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
            Op::Add(_, _) | Op::Sub(_, _) | Op::Mul(_, _) | Op::Neg(_) | Op::Inverse(_) => {}
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

fn validate_circuit_id(circuit_id: u32) -> Result<(), PcsDeepLoweringError> {
    M31Word::try_from(circuit_id)
        .map(|_| ())
        .map_err(|_| PcsDeepLoweringError::CircuitIdNotCanonical { circuit_id })
}

fn validate_structure(
    reference: &PcsDeepCircuit,
    witness: &PcsDeepCircuit,
) -> Result<(), PcsDeepLoweringError> {
    if reference.profile() != witness.profile() {
        return Err(PcsDeepLoweringError::ProfileMismatch);
    }
    if reference.input_bindings() != witness.input_bindings() {
        return Err(PcsDeepLoweringError::InputLayoutMismatch);
    }
    if reference.circuit().outputs() != witness.circuit().outputs() {
        return Err(PcsDeepLoweringError::OutputLayoutMismatch);
    }
    let reference_arena = reference.circuit().arena();
    let witness_arena = witness.circuit().arena();
    if reference_arena.nodes.len() != witness_arena.nodes.len() {
        return Err(PcsDeepLoweringError::NodeCountMismatch {
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
            return Err(PcsDeepLoweringError::NodeStructureMismatch { node_id });
        }
    }
    Ok(())
}

fn checked_node_id(node_id: usize) -> Result<u32, PcsDeepLoweringError> {
    u32::try_from(node_id).map_err(|_| PcsDeepLoweringError::NodeIdOutOfRange { node_id })
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

/// Invalid circuit identity, structure, or quotient witness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PcsDeepLoweringError {
    CircuitIdNotCanonical { circuit_id: u32 },
    ProfileMismatch,
    InputLayoutMismatch,
    OutputLayoutMismatch,
    NodeCountMismatch { expected: usize, actual: usize },
    NodeStructureMismatch { node_id: usize },
    NodeIdOutOfRange { node_id: usize },
    NonzeroConstraintOutput,
    ReferenceOutputIsNonzero,
}

impl fmt::Display for PcsDeepLoweringError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for PcsDeepLoweringError {}

#[cfg(test)]
mod tests {
    use num_traits::One;
    use prover::poseidon2_channel::Poseidon2M31Channel;
    use stwo::core::circle::CirclePointIndex;
    use stwo::core::fields::m31::BaseField;

    use super::*;
    use crate::control_air::{
        LEFT_RECURSION_VERIFIER_ID, RIGHT_RECURSION_VERIFIER_ID, SEGMENT_VERIFIER_ID,
    };
    use crate::pcs_deep_circuit::{
        PcsDeepInputSource, PcsDeepProfile, PcsDeepWitness, build_pcs_deep_circuit,
        build_pcs_deep_reference,
    };
    use crate::pcs_deep_input_air::{
        PcsDeepCircuitLane, PcsDeepInputPreprocessed, PcsDeepInputTable, PcsDeepRelations,
        gen_interaction_trace as gen_input_interaction_trace, push_pcs_deep_inputs,
    };
    use crate::query_position_air::{QueryPositionKind, QueryPositionRelations};
    use crate::trace_merkle_air::TraceMerkleRelations;
    use crate::transcript_payload_air::{VerifierInputKind, VerifierInputRelations};
    use crate::verifier_randomness_air::{VerifierRandomnessKind, VerifierRandomnessRelations};
    use crate::wire::ProofKind;
    use crate::{linear_ops, qm31_inv, qm31_mul};

    const CIRCUIT_IDS: [u32; 3] = [201, 202, 203];

    struct CircuitSet {
        segment: PcsDeepCircuit,
        left: PcsDeepCircuit,
        right: PcsDeepCircuit,
    }

    impl CircuitSet {
        fn lanes(&self) -> [PcsDeepCircuitLane<'_>; 3] {
            [
                PcsDeepCircuitLane {
                    verifier_id: SEGMENT_VERIFIER_ID,
                    circuit_id: CIRCUIT_IDS[0],
                    circuit: &self.segment,
                },
                PcsDeepCircuitLane {
                    verifier_id: LEFT_RECURSION_VERIFIER_ID,
                    circuit_id: CIRCUIT_IDS[1],
                    circuit: &self.left,
                },
                PcsDeepCircuitLane {
                    verifier_id: RIGHT_RECURSION_VERIFIER_ID,
                    circuit_id: CIRCUIT_IDS[2],
                    circuit: &self.right,
                },
            ]
        }
    }

    fn profile() -> PcsDeepProfile {
        PcsDeepProfile::new(
            vec![vec![4]],
            vec![vec![vec![CirclePointIndex::zero()]]],
            5,
            1,
        )
        .expect("fixture DEEP profile is valid")
    }

    fn reference_set(profile: &PcsDeepProfile) -> CircuitSet {
        CircuitSet {
            segment: build_pcs_deep_reference(profile).expect("segment reference is valid"),
            left: build_pcs_deep_reference(profile).expect("left reference is valid"),
            right: build_pcs_deep_reference(profile).expect("right reference is valid"),
        }
    }

    fn active_circuit(profile: &PcsDeepProfile, answer_delta: SecureField) -> PcsDeepCircuit {
        let sampled = [SecureField::zero()];
        let queried = [BaseField::zero()];
        let queries = [M31Word::from(3_u16)];
        let answers = [answer_delta];
        build_pcs_deep_circuit(
            profile,
            PcsDeepWitness {
                active: true,
                sampled_values: &sampled,
                queried_values: &queried,
                oods_seed: [17_u32, 29, 43, 71]
                    .map(|word| M31Word::try_from(word).expect("fixture word is canonical")),
                deep_randomness: [
                    M31Word::from(1_u16),
                    M31Word::ZERO,
                    M31Word::ZERO,
                    M31Word::ZERO,
                ],
                raw_queries: &queries,
                answers: &answers,
            },
        )
        .expect("fixture circuit denominators are nonzero")
    }

    fn segment_witness_set(profile: &PcsDeepProfile, answer_delta: SecureField) -> CircuitSet {
        CircuitSet {
            segment: active_circuit(profile, answer_delta),
            left: build_pcs_deep_reference(profile).expect("left reference is valid"),
            right: build_pcs_deep_reference(profile).expect("right reference is valid"),
        }
    }

    #[test]
    fn lowering_rejects_a_changed_first_fri_answer() {
        let profile = profile();
        let reference = build_pcs_deep_reference(&profile).expect("reference is valid");
        let witness = active_circuit(&profile, SecureField::one());
        assert_eq!(
            lower_pcs_deep_circuit(
                &mut CircuitTraces::default(),
                CIRCUIT_IDS[0],
                &reference,
                &witness,
            ),
            Err(PcsDeepLoweringError::NonzeroConstraintOutput)
        );
    }

    #[test]
    fn lowered_deep_relations_close_exactly() {
        let profile = profile();
        let references = reference_set(&profile);
        let witnesses = segment_witness_set(&profile, SecureField::zero());
        let preprocessing = PcsDeepInputPreprocessed::new(references.lanes())
            .expect("references own every circuit input");
        let mut input_table = PcsDeepInputTable::new();
        push_pcs_deep_inputs(
            &mut input_table,
            &preprocessing,
            references.lanes(),
            witnesses.lanes(),
            ProofKind::SegmentLeaf,
        )
        .expect("segment witness matches the universal input layout");

        let mut channel = Poseidon2M31Channel::default();
        let verifier_input_relations = VerifierInputRelations::draw(&mut channel);
        let trace_relations = TraceMerkleRelations::draw(&mut channel);
        let randomness_relations = VerifierRandomnessRelations::draw(&mut channel);
        let query_relations = QueryPositionRelations::draw(&mut channel);
        let deep_relations = PcsDeepRelations::draw(&mut channel);
        let circuit_relations = RecursionRelations::draw(&mut channel);
        let (_, input_sum) = gen_input_interaction_trace(
            &input_table.into_witness(),
            &preprocessing.gen_columns(),
            ProofKind::SegmentLeaf,
            &verifier_input_relations,
            &trace_relations,
            &randomness_relations,
            &query_relations,
            &deep_relations,
            &circuit_relations,
        );
        let semantic_sum = semantic_source_terms(
            SEGMENT_VERIFIER_ID,
            &witnesses.segment,
            &verifier_input_relations,
            &trace_relations,
            &randomness_relations,
            &query_relations,
            &deep_relations,
        );

        let mut traces = CircuitTraces::default();
        lower_pcs_deep_circuit(
            &mut traces,
            CIRCUIT_IDS[0],
            &references.segment,
            &witnesses.segment,
        )
        .expect("valid segment DEEP circuit lowers");
        let traces = traces
            .into_air_traces()
            .expect("lowered PCS DEEP schedules fit their traces");
        let (_, mul_sum) = qm31_mul::gen_interaction_trace(
            &traces.qm31_mul,
            &traces.qm31_mul_preprocessed,
            ProofKind::SegmentLeaf,
            &circuit_relations,
        );
        let (_, inverse_sum) = qm31_inv::gen_interaction_trace(
            &traces.qm31_inv,
            &traces.qm31_inv_preprocessed,
            ProofKind::SegmentLeaf,
            &circuit_relations,
        );
        let (_, linear_sum) = linear_ops::gen_interaction_trace(
            &traces.linear_ops,
            &traces.linear_ops_preprocessed,
            ProofKind::SegmentLeaf,
            &circuit_relations,
        );
        let public_sum =
            public_pcs_deep_terms(CIRCUIT_IDS[0], &references.segment, &circuit_relations)
                .expect("segment reference outputs are zero");
        assert!(
            (input_sum + semantic_sum + mul_sum + inverse_sum + linear_sum + public_sum).is_zero()
        );
    }

    fn semantic_source_terms(
        verifier_id: u32,
        circuit: &PcsDeepCircuit,
        verifier_input_relations: &VerifierInputRelations,
        trace_relations: &TraceMerkleRelations,
        randomness_relations: &VerifierRandomnessRelations,
        query_relations: &QueryPositionRelations,
        deep_relations: &PcsDeepRelations,
    ) -> SecureField {
        let arena = circuit.circuit().arena();
        circuit
            .input_bindings()
            .iter()
            .fold(SecureField::zero(), |sum, binding| {
                let value = arena.nodes[binding.node_id as usize].value.to_m31_array()[0];
                let term = match binding.source {
                    PcsDeepInputSource::ActiveSelector => return sum,
                    PcsDeepInputSource::SampledValueWord { sample, word } => inverse_term(
                        &verifier_input_relations.input_word,
                        &[
                            M31::from(verifier_id),
                            M31::from(VerifierInputKind::SampledValue.as_u32()),
                            M31::from(sample),
                            M31::from(word),
                            value,
                        ],
                    ),
                    PcsDeepInputSource::QueriedValue {
                        tree,
                        column,
                        query,
                    } => inverse_term(
                        &trace_relations.value,
                        &[
                            M31::from(verifier_id),
                            M31::from(tree),
                            M31::from(column),
                            M31::from(query),
                            value,
                        ],
                    ),
                    PcsDeepInputSource::OodsSeedWord { word } => inverse_term(
                        &randomness_relations.word,
                        &[
                            M31::from(verifier_id),
                            M31::from(VerifierRandomnessKind::OodsPoint.as_u32()),
                            M31::from(0),
                            M31::from(word),
                            value,
                        ],
                    ),
                    PcsDeepInputSource::DeepRandomnessWord { word } => inverse_term(
                        &randomness_relations.word,
                        &[
                            M31::from(verifier_id),
                            M31::from(VerifierRandomnessKind::DeepRandomness.as_u32()),
                            M31::from(0),
                            M31::from(word),
                            value,
                        ],
                    ),
                    PcsDeepInputSource::QueryBit { query, bit } => inverse_term(
                        &query_relations.bit_value,
                        &[
                            M31::from(verifier_id),
                            M31::from(query),
                            M31::from(bit),
                            value,
                        ],
                    ),
                    PcsDeepInputSource::QueryPosition { query } => inverse_term(
                        &query_relations.position,
                        &[
                            M31::from(verifier_id),
                            M31::from(QueryPositionKind::Deep.as_u32()),
                            M31::from(0),
                            M31::from(query),
                            value,
                            M31::from(0),
                        ],
                    ),
                    PcsDeepInputSource::AnswerWord { query, word } => -inverse_term(
                        &deep_relations.answer_word,
                        &[
                            M31::from(verifier_id),
                            M31::from(query),
                            M31::from(word),
                            value,
                        ],
                    ),
                };
                sum + term
            })
    }

    fn inverse_term<R: Relation<M31, SecureField>>(relation: &R, values: &[M31]) -> SecureField {
        let denominator: SecureField = relation.combine(values);
        denominator.inverse()
    }
}
