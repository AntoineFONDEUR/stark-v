//! Lowering and public anchors for the VM claim semantic circuit.
//!
//! Arithmetic nodes reuse the recursion multiplication and linear operation
//! tables. Verifier terms fix constants, operation definitions, and every zero
//! output, while the dedicated input AIR owns claim, statement, selector, and
//! private input nodes.

use core::fmt;

use air::digest::M31Word;
use num_traits::Zero;
use stwo::core::fields::FieldExpOps;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::SecureField;
use stwo_constraint_framework::Relation;

use crate::circuit::CircuitTraces;
use crate::circuit::{limbs, lower_arena_operations, use_counts_for_outputs};
use crate::recorder::Op;
use crate::relations::{RecursionRelations, op_kind};

use super::vm_public_claim_semantics_circuit::VmPublicClaimSemanticsCircuit;

/// Lowers one structurally validated zero-output circuit into shared traces.
pub fn lower_vm_public_claim_semantics_circuit(
    traces: &mut CircuitTraces,
    circuit_id: u32,
    reference: &VmPublicClaimSemanticsCircuit,
    witness: &VmPublicClaimSemanticsCircuit,
) -> Result<(), VmPublicClaimSemanticsLoweringError> {
    M31Word::try_from(circuit_id)
        .map_err(|_| VmPublicClaimSemanticsLoweringError::CircuitIdNotCanonical { circuit_id })?;
    validate_structure(reference, witness)?;
    if witness.nonzero_output_count() != 0 {
        return Err(VmPublicClaimSemanticsLoweringError::NonzeroConstraintOutput);
    }
    let arena = witness.circuit().arena();
    lower_arena_operations(traces, circuit_id, &arena, witness.circuit().outputs());
    Ok(())
}

/// Verifier contribution for constants, operation structure, and zero outputs.
pub fn public_vm_public_claim_semantics_terms(
    circuit_id: u32,
    reference: &VmPublicClaimSemanticsCircuit,
    relations: &RecursionRelations,
) -> Result<SecureField, VmPublicClaimSemanticsLoweringError> {
    M31Word::try_from(circuit_id)
        .map_err(|_| VmPublicClaimSemanticsLoweringError::CircuitIdNotCanonical { circuit_id })?;
    if reference.nonzero_output_count() != 0 {
        return Err(VmPublicClaimSemanticsLoweringError::ReferenceOutputIsNonzero);
    }
    let arena = reference.circuit().arena();
    let uses = use_counts_for_outputs(&arena, reference.circuit().outputs());
    let mut total = SecureField::zero();
    for (node_id, node) in arena.nodes.iter().enumerate() {
        let node_id = u32::try_from(node_id)
            .map_err(|_| VmPublicClaimSemanticsLoweringError::NodeIdOutOfRange { node_id })?;
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
        let output = u32::try_from(*output).map_err(|_| {
            VmPublicClaimSemanticsLoweringError::NodeIdOutOfRange { node_id: *output }
        })?;
        total -= wire_term(circuit_id, output, SecureField::zero(), relations);
    }
    Ok(total)
}

fn validate_structure(
    reference: &VmPublicClaimSemanticsCircuit,
    witness: &VmPublicClaimSemanticsCircuit,
) -> Result<(), VmPublicClaimSemanticsLoweringError> {
    if reference.shape() != witness.shape() {
        return Err(VmPublicClaimSemanticsLoweringError::ShapeMismatch);
    }
    if reference.input_bindings() != witness.input_bindings() {
        return Err(VmPublicClaimSemanticsLoweringError::InputLayoutMismatch);
    }
    if reference.circuit().outputs() != witness.circuit().outputs() {
        return Err(VmPublicClaimSemanticsLoweringError::OutputLayoutMismatch);
    }
    let reference_arena = reference.circuit().arena();
    let witness_arena = witness.circuit().arena();
    if reference_arena.nodes.len() != witness_arena.nodes.len() {
        return Err(VmPublicClaimSemanticsLoweringError::NodeCountMismatch {
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
            return Err(VmPublicClaimSemanticsLoweringError::NodeStructureMismatch { node_id });
        }
    }
    Ok(())
}

fn operation_tuple(op: Op) -> Result<(u32, u32, u32), VmPublicClaimSemanticsLoweringError> {
    let convert = |node_id: usize| {
        u32::try_from(node_id)
            .map_err(|_| VmPublicClaimSemanticsLoweringError::NodeIdOutOfRange { node_id })
    };
    match op {
        Op::Add(lhs, rhs) => Ok((op_kind::ADD, convert(lhs)?, convert(rhs)?)),
        Op::Sub(lhs, rhs) => Ok((op_kind::SUB, convert(lhs)?, convert(rhs)?)),
        Op::Mul(lhs, rhs) => Ok((op_kind::MUL, convert(lhs)?, convert(rhs)?)),
        Op::Neg(lhs) => Ok((op_kind::NEG, convert(lhs)?, 0)),
        Op::Inverse(lhs) => Ok((op_kind::INVERSE, convert(lhs)?, 0)),
        Op::Input | Op::Const => Err(VmPublicClaimSemanticsLoweringError::NonArithmeticOperation),
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

/// Invalid circuit identity, structure, or zero-output witness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VmPublicClaimSemanticsLoweringError {
    CircuitIdNotCanonical { circuit_id: u32 },
    ShapeMismatch,
    InputLayoutMismatch,
    OutputLayoutMismatch,
    NodeCountMismatch { expected: usize, actual: usize },
    NodeStructureMismatch { node_id: usize },
    NodeIdOutOfRange { node_id: usize },
    NonArithmeticOperation,
    NonzeroConstraintOutput,
    ReferenceOutputIsNonzero,
}

impl fmt::Display for VmPublicClaimSemanticsLoweringError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for VmPublicClaimSemanticsLoweringError {}

#[cfg(test)]
mod tests {
    use prover::poseidon2_channel::Poseidon2M31Channel;
    use rstest::rstest;

    use super::*;
    use crate::statement::SPAN_STATEMENT_CANONICAL_WORDS;
    use crate::statement_input_air::{StatementInputRelations, VM_CLAIM_STATEMENT_SCOPE};
    use crate::vm_public_claim::tests::shape;
    use crate::vm_public_claim_input_air::{VM_CLAIM_SEMANTICS_SCOPE, VmPublicClaimInputRelations};
    use crate::vm_public_claim_semantics_circuit::tests::{valid_digests, valid_words};
    use crate::vm_public_claim_semantics_circuit::{
        VmPublicClaimSemanticsWitness, build_vm_public_claim_semantics_circuit,
    };
    use crate::vm_public_claim_semantics_input_air::{
        VmPublicClaimSemanticsInputPreprocessed, VmPublicClaimSemanticsInputTable,
        gen_interaction_trace as gen_input_interaction_trace,
        push_vm_public_claim_semantics_inputs,
    };
    use crate::vm_public_io_hash_air::VmPublicIoHashRelations;
    use crate::wire::ProofKind;
    use crate::{linear_ops, qm31_mul};

    const CIRCUIT_ID: u32 = 19;

    fn circuits() -> (
        VmPublicClaimSemanticsCircuit,
        VmPublicClaimSemanticsCircuit,
        Vec<M31Word>,
        [M31Word; SPAN_STATEMENT_CANONICAL_WORDS],
    ) {
        let shape = shape();
        let (claim, statement) = valid_words();
        let zero_claim = vec![M31Word::ZERO; claim.len()];
        let zero_statement = [M31Word::ZERO; SPAN_STATEMENT_CANONICAL_WORDS];
        let zero_digest = [M31Word::ZERO; 8];
        let (input_digest, output_digest) = valid_digests();
        let reference = build_vm_public_claim_semantics_circuit(
            shape,
            VmPublicClaimSemanticsWitness {
                segment_selector: false,
                claim_words: &zero_claim,
                statement_words: &zero_statement,
                input_digest: &zero_digest,
                output_digest: &zero_digest,
            },
        )
        .expect("fixture reference widths are fixed");
        let witness = build_vm_public_claim_semantics_circuit(
            shape,
            VmPublicClaimSemanticsWitness {
                segment_selector: true,
                claim_words: &claim,
                statement_words: &statement,
                input_digest: &input_digest,
                output_digest: &output_digest,
            },
        )
        .expect("fixture witness widths are fixed");
        (reference, witness, claim, statement)
    }

    fn circuit_relation_sum(mut channel: Poseidon2M31Channel) -> SecureField {
        let (reference, witness, claim, statement) = circuits();
        let relations = RecursionRelations::draw(&mut channel);
        let claim_relations = VmPublicClaimInputRelations::draw(&mut channel);
        let statement_relations = StatementInputRelations::draw(&mut channel);
        let io_hash_relations = VmPublicIoHashRelations::draw(&mut channel);
        let input_preprocessing =
            VmPublicClaimSemanticsInputPreprocessed::new(&reference, CIRCUIT_ID)
                .expect("reference input ownership is canonical");
        let mut input_table = VmPublicClaimSemanticsInputTable::new();
        push_vm_public_claim_semantics_inputs(
            &mut input_table,
            &input_preprocessing,
            &reference,
            &witness,
            ProofKind::SegmentLeaf,
        )
        .expect("fixture semantic inputs materialize");
        let (_, input_sum) = gen_input_interaction_trace(
            &input_table.into_witness(),
            &input_preprocessing.gen_columns(),
            ProofKind::SegmentLeaf,
            &claim_relations,
            &statement_relations,
            &relations,
            &io_hash_relations,
        );

        let mut traces = CircuitTraces::default();
        lower_vm_public_claim_semantics_circuit(&mut traces, CIRCUIT_ID, &reference, &witness)
            .expect("valid VM claim semantic circuit lowers");
        let (_, mul_sum) =
            qm31_mul::gen_interaction_trace(&traces.qm31_mul.into_witness(), &relations);
        let (_, linear_sum) =
            linear_ops::gen_interaction_trace(&traces.linear_ops.into_witness(), &relations);
        let public_sum = public_vm_public_claim_semantics_terms(CIRCUIT_ID, &reference, &relations)
            .expect("reference circuit has zero outputs");
        input_sum
            + mul_sum
            + linear_sum
            + public_sum
            + claim_source_terms(&claim, &claim_relations)
            + statement_source_terms(&statement, &statement_relations)
            + io_digest_source_terms(&io_hash_relations)
    }

    fn claim_source_terms(
        words: &[M31Word],
        relations: &VmPublicClaimInputRelations,
    ) -> SecureField {
        words
            .iter()
            .copied()
            .enumerate()
            .fold(SecureField::zero(), |sum, (index, word)| {
                let denominator: SecureField = relations.claim_word.combine(&[
                    M31::from(VM_CLAIM_SEMANTICS_SCOPE),
                    M31::from(u32::try_from(index).expect("claim index fits u32")),
                    M31::from(word.as_u32()),
                ]);
                sum + denominator.inverse()
            })
    }

    fn statement_source_terms(
        words: &[M31Word; SPAN_STATEMENT_CANONICAL_WORDS],
        relations: &StatementInputRelations,
    ) -> SecureField {
        words
            .iter()
            .copied()
            .enumerate()
            .fold(SecureField::zero(), |sum, (index, word)| {
                let denominator: SecureField = relations.statement_word.combine(&[
                    M31::from(VM_CLAIM_STATEMENT_SCOPE),
                    M31::from(u32::try_from(index).expect("statement index fits u32")),
                    M31::from(word.as_u32()),
                ]);
                sum + denominator.inverse()
            })
    }

    fn io_digest_source_terms(relations: &VmPublicIoHashRelations) -> SecureField {
        let (input_digest, output_digest) = valid_digests();
        [input_digest, output_digest]
            .into_iter()
            .enumerate()
            .flat_map(|(io_kind, digest)| {
                digest.into_iter().enumerate().map(move |(limb, word)| {
                    let denominator: SecureField = relations.digest.combine(&[
                        M31::from(u32::try_from(io_kind).expect("IO kind fits u32")),
                        M31::from(u32::try_from(limb).expect("digest limb fits u32")),
                        M31::from(word.as_u32()),
                    ]);
                    denominator.inverse()
                })
            })
            .fold(SecureField::zero(), |sum, term| sum + term)
    }

    #[rstest]
    fn lowered_vm_claim_semantic_relations_close_exactly() {
        assert_eq!(
            circuit_relation_sum(Poseidon2M31Channel::default()),
            SecureField::zero()
        );
    }

    #[rstest]
    fn vm_claim_semantic_closure_is_challenge_independent() {
        let baseline = circuit_relation_sum(Poseidon2M31Channel::default());
        let mut changed = Poseidon2M31Channel::default();
        use stwo::core::channel::Channel;
        changed.mix_u32s(&[1]);
        assert_eq!(circuit_relation_sum(changed), baseline);
    }

    #[rstest]
    fn lowering_rejects_a_nonzero_vm_claim_constraint() {
        let (reference, _, mut claim, statement) = circuits();
        let (input_digest, output_digest) = valid_digests();
        claim[super::super::vm_public_claim::canonical_layout::PROGRAM_ROOT_START] =
            M31Word::from(99);
        let invalid = build_vm_public_claim_semantics_circuit(
            shape(),
            VmPublicClaimSemanticsWitness {
                segment_selector: true,
                claim_words: &claim,
                statement_words: &statement,
                input_digest: &input_digest,
                output_digest: &output_digest,
            },
        )
        .expect("fixture invalid witness widths are fixed");
        assert_eq!(
            lower_vm_public_claim_semantics_circuit(
                &mut CircuitTraces::default(),
                CIRCUIT_ID,
                &reference,
                &invalid,
            ),
            Err(VmPublicClaimSemanticsLoweringError::NonzeroConstraintOutput)
        );
    }
}
