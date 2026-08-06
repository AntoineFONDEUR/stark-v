//! Lowering and public anchors for the VM AIR-composition circuit.
//!
//! Shared multiplication, inverse, and linear-operation tables own arithmetic
//! rows and bind their fixed graph through preprocessing. Verifier anchors fix
//! constants and the zero composition-equality output, while the dedicated
//! input AIR owns every input node.

use core::fmt;

use crate::circuit::CircuitTraces;
use crate::circuit::lower_arena_operations;
use crate::recorder::Op;
use air::digest::M31Word;

use super::vm_air_composition_circuit::VmAirCompositionCircuit;

/// Lowers one structurally validated zero-equality circuit into shared traces.
pub fn lower_vm_air_composition_circuit(
    traces: &mut CircuitTraces,
    circuit_id: u32,
    reference: &VmAirCompositionCircuit,
    witness: &VmAirCompositionCircuit,
) -> Result<(), VmAirCompositionLoweringError> {
    validate_circuit_id(circuit_id)?;
    validate_structure(reference, witness)?;
    if witness.nonzero_output_count() != 0 {
        return Err(VmAirCompositionLoweringError::NonzeroCompositionEquality);
    }
    let arena = witness.circuit().arena();
    lower_arena_operations(traces, circuit_id, &arena, witness.circuit().outputs());
    Ok(())
}

fn validate_circuit_id(circuit_id: u32) -> Result<(), VmAirCompositionLoweringError> {
    M31Word::try_from(circuit_id)
        .map(|_| ())
        .map_err(|_| VmAirCompositionLoweringError::CircuitIdNotCanonical { circuit_id })
}

fn validate_structure(
    reference: &VmAirCompositionCircuit,
    witness: &VmAirCompositionCircuit,
) -> Result<(), VmAirCompositionLoweringError> {
    if reference.profile() != witness.profile() {
        return Err(VmAirCompositionLoweringError::ProfileMismatch);
    }
    if reference.input_bindings() != witness.input_bindings() {
        return Err(VmAirCompositionLoweringError::InputLayoutMismatch);
    }
    if reference.circuit().outputs() != witness.circuit().outputs() {
        return Err(VmAirCompositionLoweringError::OutputLayoutMismatch);
    }
    let reference_arena = reference.circuit().arena();
    let witness_arena = witness.circuit().arena();
    if reference_arena.nodes.len() != witness_arena.nodes.len() {
        return Err(VmAirCompositionLoweringError::NodeCountMismatch {
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
            return Err(VmAirCompositionLoweringError::NodeStructureMismatch { node_id });
        }
    }
    Ok(())
}

/// Invalid circuit identity, structure, or composition-equality witness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VmAirCompositionLoweringError {
    CircuitIdNotCanonical { circuit_id: u32 },
    ProfileMismatch,
    InputLayoutMismatch,
    OutputLayoutMismatch,
    NodeCountMismatch { expected: usize, actual: usize },
    NodeStructureMismatch { node_id: usize },
    NonzeroCompositionEquality,
}

impl fmt::Display for VmAirCompositionLoweringError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for VmAirCompositionLoweringError {}

#[cfg(test)]
mod tests {
    use air::digest::M31Word;
    use num_traits::Zero;
    use prover::components::{COMPONENT_COUNT, COMPONENT_NAMES};
    use prover::poseidon2_channel::Poseidon2M31Channel;
    use prover::relations::Relations;
    use stwo::core::channel::Channel;
    use stwo::core::fields::FieldExpOps;
    use stwo::core::fields::m31::{BaseField, M31};
    use stwo::core::fields::qm31::SecureField;
    use stwo_constraint_framework::Relation;

    use super::*;
    use crate::air_relation_parameters::{
        RELATION_CHALLENGE_WORD_COUNT, RelationChallengeCircuit, bind_relation_parameters,
    };
    use crate::control_air::SEGMENT_VERIFIER_ID;
    use crate::oods_circuit::oods_point_from_seed;
    use crate::recorder::Rec;
    use crate::relation_challenge_air::{
        AIR_EVALUATION_CHALLENGE_SCOPE, RelationChallengeRelations,
    };
    use crate::relations::RecursionRelations;
    use crate::statement_input_air::StatementInputRelations;
    use crate::transcript_payload_air::{VerifierInputKind, VerifierInputRelations};
    use crate::verifier_randomness_air::{VerifierRandomnessKind, VerifierRandomnessRelations};
    use crate::vm_air_composition_circuit::{
        VmAirCompositionInputSource, VmAirCompositionWitness, build_vm_air_composition_circuit,
        build_vm_air_composition_reference,
    };
    use crate::vm_air_composition_input_air::{
        VmAirCompositionInputPreprocessed, VmAirCompositionInputTable,
        gen_interaction_trace as gen_input_interaction_trace, push_vm_air_composition_inputs,
    };
    use crate::vm_air_program::VmAirProgram;
    use crate::wire::ProofKind;
    use crate::{linear_ops, qm31_inv, qm31_mul};

    const CIRCUIT_ID: u32 = 47;

    fn component_log_sizes() -> [u32; COMPONENT_COUNT] {
        core::array::from_fn(|index| match COMPONENT_NAMES[index] {
            "bitwise" => 18,
            "range_check_20" | "range_check_8_8_4" => 20,
            "range_check_8_11" => 19,
            "range_check_8_8" => 16,
            "range_check_m31" => 15,
            _ => 6,
        })
    }

    fn circuits(
        composition_delta: SecureField,
    ) -> (VmAirCompositionCircuit, VmAirCompositionCircuit) {
        let program = VmAirProgram::new(component_log_sizes()).expect("fixture profile is valid");
        let reference = build_vm_air_composition_reference(component_log_sizes())
            .expect("fixture reference is constructible");
        let mut samples = vec![SecureField::zero(); program.sample_coordinates().len()];
        let claimed_sums = vec![SecureField::zero(); COMPONENT_COUNT];
        let challenges = Relations::DESCRIPTORS
            .iter()
            .enumerate()
            .map(|(challenge, _)| {
                core::array::from_fn(|word| {
                    M31Word::from(
                        u16::try_from(2 + challenge * RELATION_CHALLENGE_WORD_COUNT + word)
                            .expect("fixture relation word fits u16"),
                    )
                })
            })
            .collect::<Vec<_>>();
        let relation_circuits = challenges
            .iter()
            .map(|words| {
                RelationChallengeCircuit::new(
                    words.map(|word| Rec::from(BaseField::from(word.as_u32()))),
                )
            })
            .collect::<Vec<_>>();
        let parameters = bind_relation_parameters(&Relations::DESCRIPTORS, &relation_circuits)
            .expect("fixture supplies every relation draw");
        let composition_randomness = [2_u16, 3, 5, 7].map(M31Word::from);
        let composition_randomness_value = SecureField::from_m31_array(
            composition_randomness.map(|word| M31::from(word.as_u32())),
        );
        let oods_words = [11_u16, 13, 17, 19].map(M31Word::from);
        let oods_seed =
            SecureField::from_m31_array(oods_words.map(|word| M31::from(word.as_u32())));
        let oods_point = oods_point_from_seed(Rec::from(oods_seed))
            .expect("fixture OODS seed maps outside the composition coset");
        let evaluation = program
            .evaluate(
                &samples.iter().copied().map(Rec::from).collect::<Vec<_>>(),
                &claimed_sums
                    .iter()
                    .copied()
                    .map(Rec::from)
                    .collect::<Vec<_>>(),
                &parameters,
                Rec::from(composition_randomness_value),
                &oods_point,
            )
            .expect("complete fixture evaluates");
        let composition_tree = program
            .sample_coordinates()
            .iter()
            .map(|coordinate| coordinate.tree)
            .max()
            .expect("VM program samples its composition tree");
        let first_left_coordinate = program
            .sample_coordinates()
            .iter()
            .position(|coordinate| {
                coordinate.tree == composition_tree
                    && coordinate.column == 0
                    && coordinate.point == 0
            })
            .expect("split composition has a first left coordinate");
        samples[first_left_coordinate] = evaluation.air_value.value() + composition_delta;
        let witness = build_vm_air_composition_circuit(
            component_log_sizes(),
            VmAirCompositionWitness {
                segment_selector: true,
                sampled_values: &samples,
                claimed_sums: &claimed_sums,
                relation_challenges: &challenges,
                composition_randomness,
                oods_point: oods_words,
            },
        )
        .expect("fixture witness has the fixed composition structure");
        (reference, witness)
    }

    fn circuit_relation_sum(mut channel: Poseidon2M31Channel) -> SecureField {
        let (reference, witness) = circuits(SecureField::zero());
        let circuit_relations = RecursionRelations::draw(&mut channel);
        let challenge_relations = RelationChallengeRelations::draw(&mut channel);
        let verifier_input_relations = VerifierInputRelations::draw(&mut channel);
        let randomness_relations = VerifierRandomnessRelations::draw(&mut channel);
        let statement_relations = StatementInputRelations::draw(&mut channel);
        let input_preprocessing = VmAirCompositionInputPreprocessed::new(&reference, CIRCUIT_ID)
            .expect("reference input ownership is canonical");
        let mut input_table = VmAirCompositionInputTable::new();
        push_vm_air_composition_inputs(
            &mut input_table,
            &input_preprocessing,
            &reference,
            &witness,
            ProofKind::SegmentLeaf,
        )
        .expect("fixture composition inputs materialize");
        let (_, input_sum) = gen_input_interaction_trace(
            &input_table.into_witness(),
            &input_preprocessing.gen_columns(),
            ProofKind::SegmentLeaf,
            &challenge_relations,
            &verifier_input_relations,
            &randomness_relations,
            &statement_relations,
            &circuit_relations,
        );

        let source_sum = input_source_terms(
            &witness,
            &challenge_relations,
            &verifier_input_relations,
            &randomness_relations,
        );
        let mut traces = CircuitTraces::default();
        lower_vm_air_composition_circuit(&mut traces, CIRCUIT_ID, &reference, &witness)
            .expect("valid composition circuit lowers");
        let traces = traces
            .into_air_traces()
            .expect("lowered composition schedules fit their traces");
        let (_, mul_sum) = qm31_mul::gen_interaction_trace(
            &traces.qm31_mul,
            &traces.qm31_mul_preprocessed,
            ProofKind::SegmentLeaf,
            &circuit_relations,
        );
        let (_, inv_sum) = qm31_inv::gen_interaction_trace(
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
        // The composition-input AIR owns the fixed constants and zero output,
        // so its interaction sum already includes every public graph anchor.
        input_sum + source_sum + mul_sum + inv_sum + linear_sum
    }

    fn input_source_terms(
        circuit: &VmAirCompositionCircuit,
        challenge_relations: &RelationChallengeRelations,
        verifier_input_relations: &VerifierInputRelations,
        randomness_relations: &VerifierRandomnessRelations,
    ) -> SecureField {
        let arena = circuit.circuit().arena();
        circuit
            .input_bindings()
            .iter()
            .filter_map(|binding| {
                let value = arena.nodes[binding.node_id as usize].value.to_m31_array()[0];
                let denominator: SecureField = match binding.source {
                    VmAirCompositionInputSource::SampledValueWord {
                        item_index,
                        word_index,
                    } => verifier_input_relations.input_word.combine(&[
                        M31::from(SEGMENT_VERIFIER_ID),
                        M31::from(VerifierInputKind::SampledValue.as_u32()),
                        M31::from(item_index),
                        M31::from(word_index),
                        value,
                    ]),
                    VmAirCompositionInputSource::ClaimedSumWord {
                        item_index,
                        word_index,
                    } => verifier_input_relations.input_word.combine(&[
                        M31::from(SEGMENT_VERIFIER_ID),
                        M31::from(VerifierInputKind::AirClaimedSum.as_u32()),
                        M31::from(item_index),
                        M31::from(word_index),
                        value,
                    ]),
                    VmAirCompositionInputSource::RelationChallengeWord {
                        challenge,
                        word_index,
                    } => challenge_relations.word.combine(&[
                        M31::from(SEGMENT_VERIFIER_ID),
                        M31::from(AIR_EVALUATION_CHALLENGE_SCOPE),
                        M31::from(challenge),
                        M31::from(word_index),
                        value,
                    ]),
                    VmAirCompositionInputSource::CompositionRandomnessWord { word_index } => {
                        randomness_relations.word.combine(&[
                            M31::from(SEGMENT_VERIFIER_ID),
                            M31::from(VerifierRandomnessKind::CompositionRandomness.as_u32()),
                            M31::from(0),
                            M31::from(word_index),
                            value,
                        ])
                    }
                    VmAirCompositionInputSource::OodsPointWord { word_index } => {
                        randomness_relations.word.combine(&[
                            M31::from(SEGMENT_VERIFIER_ID),
                            M31::from(VerifierRandomnessKind::OodsPoint.as_u32()),
                            M31::from(0),
                            M31::from(word_index),
                            value,
                        ])
                    }
                    VmAirCompositionInputSource::SegmentSelector => return None,
                };
                Some(denominator.inverse())
            })
            .fold(SecureField::zero(), |sum, term| sum + term)
    }

    #[test]
    fn lowered_composition_relations_close_exactly() {
        assert_eq!(
            circuit_relation_sum(Poseidon2M31Channel::default()),
            SecureField::zero()
        );
    }

    #[test]
    fn composition_closure_is_challenge_independent() {
        let baseline = circuit_relation_sum(Poseidon2M31Channel::default());
        let mut changed = Poseidon2M31Channel::default();
        changed.mix_u32s(&[1]);
        assert_eq!(circuit_relation_sum(changed), baseline);
    }

    #[test]
    fn lowering_rejects_a_nonzero_composition_equality() {
        let (reference, witness) = circuits(SecureField::from(M31::from(1)));
        assert_eq!(
            lower_vm_air_composition_circuit(
                &mut CircuitTraces::default(),
                CIRCUIT_ID,
                &reference,
                &witness,
            ),
            Err(VmAirCompositionLoweringError::NonzeroCompositionEquality)
        );
    }
}
