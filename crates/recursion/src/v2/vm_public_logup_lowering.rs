//! Lowering and public anchors for the VM public-LogUp circuit.
//!
//! Shared multiplication, inverse, and linear-operation tables own arithmetic
//! rows. Verifier terms fix constants, operation definitions, and the zero
//! global-sum output, while the dedicated input AIR owns every input node.

use core::fmt;

use air::digest::M31Word;
use num_traits::Zero;
use stwo::core::fields::FieldExpOps;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::SecureField;
use stwo_constraint_framework::Relation;

use crate::circuit::{limbs, lower_arena_operations, use_counts_for_outputs};
use crate::prover::RecursionTraces;
use crate::recorder::Op;
use crate::relations::{RecursionRelations, op_kind};

use super::vm_public_logup_circuit::VmPublicLogupCircuit;

/// Lowers one structurally validated zero-sum circuit into shared traces.
pub fn lower_vm_public_logup_circuit(
    traces: &mut RecursionTraces,
    circuit_id: u32,
    reference: &VmPublicLogupCircuit,
    witness: &VmPublicLogupCircuit,
) -> Result<(), VmPublicLogupLoweringError> {
    validate_circuit_id(circuit_id)?;
    validate_structure(reference, witness)?;
    if witness.nonzero_output_count() != 0 {
        return Err(VmPublicLogupLoweringError::NonzeroGlobalSum);
    }
    let arena = witness.circuit().arena();
    lower_arena_operations(traces, circuit_id, &arena, witness.circuit().outputs());
    Ok(())
}

/// Verifier contribution for constants, operation structure, and zero output.
pub fn public_vm_public_logup_terms(
    circuit_id: u32,
    reference: &VmPublicLogupCircuit,
    relations: &RecursionRelations,
) -> Result<SecureField, VmPublicLogupLoweringError> {
    validate_circuit_id(circuit_id)?;
    if reference.nonzero_output_count() != 0 {
        return Err(VmPublicLogupLoweringError::ReferenceOutputIsNonzero);
    }
    let arena = reference.circuit().arena();
    let uses = use_counts_for_outputs(&arena, reference.circuit().outputs());
    let mut total = SecureField::zero();
    for (node_id, node) in arena.nodes.iter().enumerate() {
        let node_id = checked_node_id(node_id)?;
        match node.op {
            Op::Input => {}
            Op::Const => {
                if uses[node_id as usize] != 0 {
                    total += wire_term(circuit_id, node_id, node.value, relations)
                        * SecureField::from(M31::from(uses[node_id as usize]));
                }
            }
            op => {
                let (kind, lhs, rhs) = operation_tuple(op)?;
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

fn validate_circuit_id(circuit_id: u32) -> Result<(), VmPublicLogupLoweringError> {
    M31Word::try_from(circuit_id)
        .map(|_| ())
        .map_err(|_| VmPublicLogupLoweringError::CircuitIdNotCanonical { circuit_id })
}

fn validate_structure(
    reference: &VmPublicLogupCircuit,
    witness: &VmPublicLogupCircuit,
) -> Result<(), VmPublicLogupLoweringError> {
    if reference.shape() != witness.shape() {
        return Err(VmPublicLogupLoweringError::ShapeMismatch);
    }
    if reference.claimed_sum_count() != witness.claimed_sum_count()
        || reference.public_term_count() != witness.public_term_count()
    {
        return Err(VmPublicLogupLoweringError::CountMismatch);
    }
    if reference.input_bindings() != witness.input_bindings() {
        return Err(VmPublicLogupLoweringError::InputLayoutMismatch);
    }
    if reference.circuit().outputs() != witness.circuit().outputs() {
        return Err(VmPublicLogupLoweringError::OutputLayoutMismatch);
    }
    let reference_arena = reference.circuit().arena();
    let witness_arena = witness.circuit().arena();
    if reference_arena.nodes.len() != witness_arena.nodes.len() {
        return Err(VmPublicLogupLoweringError::NodeCountMismatch {
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
            return Err(VmPublicLogupLoweringError::NodeStructureMismatch { node_id });
        }
    }
    Ok(())
}

fn checked_node_id(node_id: usize) -> Result<u32, VmPublicLogupLoweringError> {
    u32::try_from(node_id).map_err(|_| VmPublicLogupLoweringError::NodeIdOutOfRange { node_id })
}

fn operation_tuple(op: Op) -> Result<(u32, u32, u32), VmPublicLogupLoweringError> {
    let convert = |node_id| checked_node_id(node_id);
    match op {
        Op::Add(lhs, rhs) => Ok((op_kind::ADD, convert(lhs)?, convert(rhs)?)),
        Op::Sub(lhs, rhs) => Ok((op_kind::SUB, convert(lhs)?, convert(rhs)?)),
        Op::Mul(lhs, rhs) => Ok((op_kind::MUL, convert(lhs)?, convert(rhs)?)),
        Op::Neg(lhs) => Ok((op_kind::NEG, convert(lhs)?, 0)),
        Op::Inverse(lhs) => Ok((op_kind::INVERSE, convert(lhs)?, 0)),
        Op::Input | Op::Const => Err(VmPublicLogupLoweringError::NonArithmeticOperation),
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

/// Invalid circuit identity, structure, or global-sum witness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VmPublicLogupLoweringError {
    CircuitIdNotCanonical { circuit_id: u32 },
    ShapeMismatch,
    CountMismatch,
    InputLayoutMismatch,
    OutputLayoutMismatch,
    NodeCountMismatch { expected: usize, actual: usize },
    NodeStructureMismatch { node_id: usize },
    NodeIdOutOfRange { node_id: usize },
    NonArithmeticOperation,
    NonzeroGlobalSum,
    ReferenceOutputIsNonzero,
}

impl fmt::Display for VmPublicLogupLoweringError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for VmPublicLogupLoweringError {}

#[cfg(test)]
mod tests {
    use prover::poseidon2_channel::Poseidon2M31Channel;
    use prover::relations::Relations;
    use rstest::rstest;

    use super::*;
    use crate::v2::control_air::SEGMENT_VERIFIER_ID;
    use crate::v2::relation_challenge_air::{
        RelationChallengeRelations, VM_PUBLIC_LOGUP_CHALLENGE_SCOPE,
    };
    use crate::v2::transcript_payload_air::{VerifierInputKind, VerifierInputRelations};
    use crate::v2::vm_public_claim::{canonical_vm_public_claim_words, tests as claim_tests};
    use crate::v2::vm_public_claim_input_air::{
        VM_PUBLIC_LOGUP_SCOPE, VmPublicClaimInputRelations,
    };
    use crate::v2::vm_public_logup_circuit::{
        VmPublicLogupChallengeWords, VmPublicLogupInputSource, VmPublicLogupWitness,
        build_vm_public_logup_circuit, build_vm_public_logup_reference,
    };
    use crate::v2::vm_public_logup_input_air::{
        VmPublicLogupInputPreprocessed, VmPublicLogupInputTable,
        gen_interaction_trace as gen_input_interaction_trace, push_vm_public_logup_inputs,
    };
    use crate::v2::wire::ProofKind;
    use crate::{linear_ops, qm31_inv, qm31_mul};

    const CIRCUIT_ID: u32 = 41;

    fn circuits(claimed_sum_delta: SecureField) -> (VmPublicLogupCircuit, VmPublicLogupCircuit) {
        let shape = claim_tests::shape();
        let reference =
            build_vm_public_logup_reference(shape, 1).expect("fixture reference is representable");
        let claim = canonical_vm_public_claim_words(&claim_tests::public_data(), shape)
            .expect("fixture claim is canonical");
        let mut channel = Poseidon2M31Channel::default();
        let vm_relations = Relations::draw(&mut channel);
        let claimed_sum = -claim_tests::public_data().logup_sum(&vm_relations) + claimed_sum_delta;
        let witness = build_vm_public_logup_circuit(
            shape,
            1,
            VmPublicLogupWitness {
                segment_selector: true,
                claim_words: &claim,
                relation_challenges: VmPublicLogupChallengeWords::from_relations(&vm_relations),
                claimed_sums: &[claimed_sum],
            },
        )
        .expect("fixture selected denominators are nonzero");
        (reference, witness)
    }

    fn circuit_relation_sum(mut channel: Poseidon2M31Channel) -> SecureField {
        let (reference, witness) = circuits(SecureField::zero());
        let circuit_relations = RecursionRelations::draw(&mut channel);
        let claim_relations = VmPublicClaimInputRelations::draw(&mut channel);
        let challenge_relations = RelationChallengeRelations::draw(&mut channel);
        let verifier_input_relations = VerifierInputRelations::draw(&mut channel);
        let input_preprocessing = VmPublicLogupInputPreprocessed::new(&reference, CIRCUIT_ID)
            .expect("reference input ownership is canonical");
        let mut input_table = VmPublicLogupInputTable::new();
        push_vm_public_logup_inputs(
            &mut input_table,
            &input_preprocessing,
            &reference,
            &witness,
            ProofKind::SegmentLeaf,
        )
        .expect("fixture public LogUp inputs materialize");
        let (_, input_sum) = gen_input_interaction_trace(
            &input_table.into_witness(),
            &input_preprocessing.gen_columns(),
            ProofKind::SegmentLeaf,
            &claim_relations,
            &challenge_relations,
            &verifier_input_relations,
            &circuit_relations,
        );

        let source_sum = input_source_terms(
            &witness,
            &claim_relations,
            &challenge_relations,
            &verifier_input_relations,
        );
        let mut traces = RecursionTraces::default();
        lower_vm_public_logup_circuit(&mut traces, CIRCUIT_ID, &reference, &witness)
            .expect("valid public LogUp circuit lowers");
        let (_, mul_sum) =
            qm31_mul::gen_interaction_trace(&traces.qm31_mul.into_witness(), &circuit_relations);
        let (_, inv_sum) =
            qm31_inv::gen_interaction_trace(&traces.qm31_inv.into_witness(), &circuit_relations);
        let (_, linear_sum) = linear_ops::gen_interaction_trace(
            &traces.linear_ops.into_witness(),
            &circuit_relations,
        );
        let public_sum = public_vm_public_logup_terms(CIRCUIT_ID, &reference, &circuit_relations)
            .expect("reference has a zero global output");
        input_sum + source_sum + mul_sum + inv_sum + linear_sum + public_sum
    }

    fn input_source_terms(
        circuit: &VmPublicLogupCircuit,
        claim_relations: &VmPublicClaimInputRelations,
        challenge_relations: &RelationChallengeRelations,
        verifier_input_relations: &VerifierInputRelations,
    ) -> SecureField {
        let arena = circuit.circuit().arena();
        circuit
            .input_bindings()
            .iter()
            .filter_map(|binding| {
                let value = arena.nodes[binding.node_id as usize].value.to_m31_array()[0];
                let denominator: SecureField = match binding.source {
                    VmPublicLogupInputSource::ClaimWord { index } => claim_relations
                        .claim_word
                        .combine(&[M31::from(VM_PUBLIC_LOGUP_SCOPE), M31::from(index), value]),
                    VmPublicLogupInputSource::ClaimByte {
                        word_index,
                        byte_index,
                    } => claim_relations.claim_byte.combine(&[
                        M31::from(word_index),
                        M31::from(byte_index),
                        value,
                    ]),
                    VmPublicLogupInputSource::RelationChallengeWord {
                        challenge,
                        word_index,
                    } => challenge_relations.word.combine(&[
                        M31::from(SEGMENT_VERIFIER_ID),
                        M31::from(VM_PUBLIC_LOGUP_CHALLENGE_SCOPE),
                        M31::from(challenge),
                        M31::from(word_index),
                        value,
                    ]),
                    VmPublicLogupInputSource::ClaimedSumWord {
                        item_index,
                        limb_index,
                    } => verifier_input_relations.input_word.combine(&[
                        M31::from(SEGMENT_VERIFIER_ID),
                        M31::from(VerifierInputKind::ClaimedSum.as_u32()),
                        M31::from(item_index),
                        M31::from(limb_index),
                        value,
                    ]),
                    VmPublicLogupInputSource::SegmentSelector => return None,
                };
                Some(denominator.inverse())
            })
            .fold(SecureField::zero(), |sum, term| sum + term)
    }

    #[rstest]
    fn lowered_public_logup_relations_close_exactly() {
        assert_eq!(
            circuit_relation_sum(Poseidon2M31Channel::default()),
            SecureField::zero()
        );
    }

    #[rstest]
    fn public_logup_closure_is_challenge_independent() {
        use stwo::core::channel::Channel;

        let baseline = circuit_relation_sum(Poseidon2M31Channel::default());
        let mut changed = Poseidon2M31Channel::default();
        changed.mix_u32s(&[1]);
        assert_eq!(circuit_relation_sum(changed), baseline);
    }

    #[rstest]
    fn lowering_rejects_a_nonzero_global_sum() {
        let (reference, witness) = circuits(SecureField::from(M31::from(1)));
        assert_eq!(
            lower_vm_public_logup_circuit(
                &mut RecursionTraces::default(),
                CIRCUIT_ID,
                &reference,
                &witness,
            ),
            Err(VmPublicLogupLoweringError::NonzeroGlobalSum)
        );
    }
}
