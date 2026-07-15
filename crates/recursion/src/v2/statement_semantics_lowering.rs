//! Lowering and public anchors for the fixed statement-semantics circuit.
//!
//! Arithmetic nodes reuse the recursion multiplication, inverse, and linear
//! operation tables. Input nodes are supplied by `statement_semantics_input_air`,
//! constants are emitted by verifier-computed terms, operation definitions
//! are fixed by the reference circuit, and every designated output is
//! publicly consumed at zero.

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

use super::statement_semantics_circuit::StatementSemanticsCircuit;

/// Lowers one validated statement circuit into the shared arithmetic traces.
pub fn lower_statement_semantics_circuit(
    traces: &mut RecursionTraces,
    circuit_id: u32,
    reference: &StatementSemanticsCircuit,
    witness: &StatementSemanticsCircuit,
) -> Result<(), StatementSemanticsLoweringError> {
    M31Word::try_from(circuit_id)
        .map_err(|_| StatementSemanticsLoweringError::CircuitIdNotCanonical { circuit_id })?;
    validate_structure(reference, witness)?;
    if witness.nonzero_output_count() != 0 {
        return Err(StatementSemanticsLoweringError::NonzeroConstraintOutput);
    }
    let arena = witness.circuit().arena();
    lower_arena_operations(traces, circuit_id, &arena, witness.circuit().outputs());
    Ok(())
}

/// Verifier contribution for circuit constants, structure, and zero outputs.
pub fn public_statement_semantics_terms(
    circuit_id: u32,
    reference: &StatementSemanticsCircuit,
    relations: &RecursionRelations,
) -> Result<SecureField, StatementSemanticsLoweringError> {
    M31Word::try_from(circuit_id)
        .map_err(|_| StatementSemanticsLoweringError::CircuitIdNotCanonical { circuit_id })?;
    if reference.nonzero_output_count() != 0 {
        return Err(StatementSemanticsLoweringError::ReferenceOutputIsNonzero);
    }
    let arena = reference.circuit().arena();
    let uses = use_counts_for_outputs(&arena, reference.circuit().outputs());
    let mut total = SecureField::zero();
    for (node_id, node) in arena.nodes.iter().enumerate() {
        let node_id_u32 = u32::try_from(node_id)
            .map_err(|_| StatementSemanticsLoweringError::NodeIdOutOfRange { node_id })?;
        match node.op {
            Op::Input => {}
            Op::Const => {
                if uses[node_id] != 0 {
                    total += wire_term(circuit_id, node_id_u32, node.value, relations)
                        * SecureField::from(M31::from(uses[node_id]));
                }
            }
            op => {
                let (kind, lhs, rhs) = operation_tuple(op)?;
                let denominator: SecureField = relations.op_def.combine(&[
                    M31::from(circuit_id),
                    M31::from(node_id_u32),
                    M31::from(kind),
                    M31::from(lhs),
                    M31::from(rhs),
                ]);
                total += denominator.inverse();
            }
        }
    }
    for output in reference.circuit().outputs() {
        let output = u32::try_from(*output)
            .map_err(|_| StatementSemanticsLoweringError::NodeIdOutOfRange { node_id: *output })?;
        total -= wire_term(circuit_id, output, SecureField::zero(), relations);
    }
    Ok(total)
}

fn validate_structure(
    reference: &StatementSemanticsCircuit,
    witness: &StatementSemanticsCircuit,
) -> Result<(), StatementSemanticsLoweringError> {
    if reference.input_bindings() != witness.input_bindings() {
        return Err(StatementSemanticsLoweringError::InputLayoutMismatch);
    }
    if reference.circuit().outputs() != witness.circuit().outputs() {
        return Err(StatementSemanticsLoweringError::OutputLayoutMismatch);
    }
    let reference_arena = reference.circuit().arena();
    let witness_arena = witness.circuit().arena();
    if reference_arena.nodes.len() != witness_arena.nodes.len() {
        return Err(StatementSemanticsLoweringError::NodeCountMismatch {
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
            return Err(StatementSemanticsLoweringError::NodeStructureMismatch { node_id });
        }
    }
    Ok(())
}

fn operation_tuple(op: Op) -> Result<(u32, u32, u32), StatementSemanticsLoweringError> {
    let convert = |node_id: usize| {
        u32::try_from(node_id)
            .map_err(|_| StatementSemanticsLoweringError::NodeIdOutOfRange { node_id })
    };
    match op {
        Op::Add(lhs, rhs) => Ok((op_kind::ADD, convert(lhs)?, convert(rhs)?)),
        Op::Sub(lhs, rhs) => Ok((op_kind::SUB, convert(lhs)?, convert(rhs)?)),
        Op::Mul(lhs, rhs) => Ok((op_kind::MUL, convert(lhs)?, convert(rhs)?)),
        Op::Neg(lhs) => Ok((op_kind::NEG, convert(lhs)?, 0)),
        Op::Inverse(lhs) => Ok((op_kind::INVERSE, convert(lhs)?, 0)),
        Op::Input | Op::Const => Err(StatementSemanticsLoweringError::NonArithmeticOperation),
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

/// Invalid statement circuit structure, witness, or public anchor.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StatementSemanticsLoweringError {
    CircuitIdNotCanonical { circuit_id: u32 },
    NonzeroConstraintOutput,
    ReferenceOutputIsNonzero,
    InputLayoutMismatch,
    OutputLayoutMismatch,
    NodeCountMismatch { expected: usize, actual: usize },
    NodeStructureMismatch { node_id: usize },
    NodeIdOutOfRange { node_id: usize },
    NonArithmeticOperation,
}

impl fmt::Display for StatementSemanticsLoweringError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::CircuitIdNotCanonical { circuit_id } => {
                write!(
                    formatter,
                    "statement semantics circuit id {circuit_id} is not canonical M31"
                )
            }
            Self::NonzeroConstraintOutput => {
                write!(
                    formatter,
                    "statement semantics circuit has a nonzero constraint output"
                )
            }
            Self::ReferenceOutputIsNonzero => {
                write!(formatter, "reference statement semantics output is nonzero")
            }
            Self::InputLayoutMismatch => {
                write!(formatter, "statement circuit input layout changed")
            }
            Self::OutputLayoutMismatch => {
                write!(formatter, "statement circuit output layout changed")
            }
            Self::NodeCountMismatch { expected, actual } => write!(
                formatter,
                "statement circuit has {actual} nodes, expected {expected}"
            ),
            Self::NodeStructureMismatch { node_id } => {
                write!(
                    formatter,
                    "statement circuit node {node_id} changed structure"
                )
            }
            Self::NodeIdOutOfRange { node_id } => {
                write!(
                    formatter,
                    "statement circuit node id {node_id} does not fit u32"
                )
            }
            Self::NonArithmeticOperation => {
                write!(
                    formatter,
                    "input or constant requested as an arithmetic operation"
                )
            }
        }
    }
}

impl std::error::Error for StatementSemanticsLoweringError {}

#[cfg(test)]
mod tests {
    use prover::poseidon2_channel::Poseidon2M31Channel;
    use rstest::rstest;

    use super::*;
    use crate::linear_ops;
    use crate::qm31_mul;
    use crate::v2::statement::{SPAN_STATEMENT_CANONICAL_WORDS, SpanStatement};
    use crate::v2::statement_input_air::{PARENT_STATEMENT_SCOPE, StatementInputRelations};
    use crate::v2::statement_semantics_circuit::{
        StatementSemanticsCircuitWitness, StatementWords, build_statement_semantics_circuit,
        statement_words,
    };
    use crate::v2::statement_semantics_input_air::{
        StatementSemanticsInputPreprocessed, StatementSemanticsInputTable,
        gen_interaction_trace as gen_input_interaction_trace, push_statement_semantics_inputs,
        register_range_check_multiplicities,
    };
    use crate::v2::wire::ProofKind;

    const CIRCUIT_ID: u32 = 7;

    fn zero_words() -> StatementWords {
        [M31Word::ZERO; SPAN_STATEMENT_CANONICAL_WORDS]
    }

    fn zero_circuit() -> StatementSemanticsCircuit {
        let segment = zero_words();
        let left = zero_words();
        let right = zero_words();
        let parent = zero_words();
        build_statement_semantics_circuit(StatementSemanticsCircuitWitness {
            segment_selector: false,
            binary_selector: false,
            empty_selector: false,
            segment: &segment,
            left: &left,
            right: &right,
            parent: &parent,
        })
    }

    fn valid_binary_circuit() -> StatementSemanticsCircuit {
        let (left, right, parent) = crate::v2::test_fixtures::two_executed();
        let segment = zero_words();
        let left = statement_words(&left).expect("left statement width is canonical");
        let right = statement_words(&right).expect("right statement width is canonical");
        let parent = statement_words(&parent).expect("parent statement width is canonical");
        build_statement_semantics_circuit(StatementSemanticsCircuitWitness {
            segment_selector: false,
            binary_selector: true,
            empty_selector: false,
            segment: &segment,
            left: &left,
            right: &right,
            parent: &parent,
        })
    }

    fn valid_empty_statement() -> SpanStatement {
        let job = crate::v2::test_fixtures::job(3, 12);
        SpanStatement::empty_leaf(job, 3).expect("slot three is suffix padding")
    }

    fn valid_segment_statement() -> SpanStatement {
        let job = crate::v2::test_fixtures::job(3, 12);
        crate::v2::test_fixtures::leaf(
            job,
            1,
            4,
            4,
            crate::v2::test_fixtures::state(1),
            crate::v2::test_fixtures::state(2),
        )
    }

    fn valid_segment_circuit(statement: &SpanStatement) -> StatementSemanticsCircuit {
        let zero = zero_words();
        let segment = statement_words(statement).expect("segment statement width is canonical");
        build_statement_semantics_circuit(StatementSemanticsCircuitWitness {
            segment_selector: true,
            binary_selector: false,
            empty_selector: false,
            segment: &segment,
            left: &zero,
            right: &zero,
            parent: &segment,
        })
    }

    fn valid_empty_circuit(statement: &SpanStatement) -> StatementSemanticsCircuit {
        let zero = zero_words();
        let parent = statement_words(statement).expect("empty statement width is canonical");
        build_statement_semantics_circuit(StatementSemanticsCircuitWitness {
            segment_selector: false,
            binary_selector: false,
            empty_selector: true,
            segment: &zero,
            left: &zero,
            right: &zero,
            parent: &parent,
        })
    }

    fn parent_statement_terms(
        statement: &SpanStatement,
        relations: &StatementInputRelations,
    ) -> SecureField {
        statement_words(statement)
            .expect("empty statement width is canonical")
            .into_iter()
            .enumerate()
            .fold(SecureField::zero(), |sum, (index, word)| {
                let index = u32::try_from(index).expect("statement word index fits u32");
                let denominator: SecureField = relations.statement_word.combine(&[
                    M31::from(PARENT_STATEMENT_SCOPE),
                    M31::from(index),
                    M31::from(word.as_u32()),
                ]);
                sum + denominator.inverse()
            })
    }

    fn circuit_relation_sum(mut channel: Poseidon2M31Channel) -> SecureField {
        let statement = valid_empty_statement();
        let reference = zero_circuit();
        let witness = valid_empty_circuit(&statement);
        let relations = RecursionRelations::draw(&mut channel);
        let statement_relations = StatementInputRelations::draw(&mut channel);
        let vm_relations = prover::relations::Relations::draw(&mut channel);

        let input_preprocessing = StatementSemanticsInputPreprocessed::new(&reference, CIRCUIT_ID)
            .expect("reference circuit has canonical input ownership");
        let mut input_table = StatementSemanticsInputTable::new();
        push_statement_semantics_inputs(
            &mut input_table,
            &input_preprocessing,
            &witness,
            ProofKind::EmptyLeaf,
        )
        .expect("empty statement inputs are generated");
        let input_trace = input_table.into_witness();
        let input_preprocessed = input_preprocessing.gen_columns();
        let mut counters = prover::relations::Counters::new();
        register_range_check_multiplicities(
            &input_trace,
            &input_preprocessed,
            ProofKind::EmptyLeaf,
            &mut counters,
        );
        let range_trace = counters.range_check_8_8.into_trace();
        let (_, range_sum) =
            prover::components::lookups::range_check_8_8::witness::gen_interaction_trace(
                &range_trace,
                &vm_relations,
            );
        let (_, input_sum) = gen_input_interaction_trace(
            &input_trace,
            &input_preprocessed,
            ProofKind::EmptyLeaf,
            &statement_relations,
            &relations,
            &vm_relations,
        );

        let mut traces = RecursionTraces::default();
        lower_statement_semantics_circuit(&mut traces, CIRCUIT_ID, &reference, &witness)
            .expect("valid empty statement circuit lowers");
        let qm31_mul_trace = traces.qm31_mul.into_witness();
        let linear_ops_trace = traces.linear_ops.into_witness();
        let (_, mul_sum) = qm31_mul::gen_interaction_trace(&qm31_mul_trace, &relations);
        let (_, linear_sum) = linear_ops::gen_interaction_trace(&linear_ops_trace, &relations);
        let public_sum = public_statement_semantics_terms(CIRCUIT_ID, &reference, &relations)
            .expect("reference circuit has zero outputs");
        input_sum
            + mul_sum
            + linear_sum
            + public_sum
            + parent_statement_terms(&statement, &statement_relations)
            + range_sum
    }

    #[rstest]
    fn lowered_circuit_relations_close_exactly() {
        assert_eq!(
            circuit_relation_sum(Poseidon2M31Channel::default()),
            SecureField::zero()
        );
    }

    #[rstest]
    fn circuit_relation_closure_is_challenge_independent() {
        let baseline = circuit_relation_sum(Poseidon2M31Channel::default());
        let mut changed = Poseidon2M31Channel::default();
        use stwo::core::channel::Channel;
        changed.mix_u32s(&[1]);
        assert_eq!(circuit_relation_sum(changed), baseline);
    }

    #[rstest]
    fn lowering_rejects_a_nonzero_statement_constraint() {
        let reference = zero_circuit();
        let zero = zero_words();
        let invalid = build_statement_semantics_circuit(StatementSemanticsCircuitWitness {
            segment_selector: true,
            binary_selector: false,
            empty_selector: false,
            segment: &zero,
            left: &zero,
            right: &zero,
            parent: &zero,
        });
        let mut traces = RecursionTraces::default();
        assert_eq!(
            lower_statement_semantics_circuit(&mut traces, CIRCUIT_ID, &reference, &invalid,),
            Err(StatementSemanticsLoweringError::NonzeroConstraintOutput)
        );
    }

    #[rstest]
    fn valid_binary_fold_lowers_into_shared_arithmetic_tables() {
        let reference = valid_binary_circuit();
        let witness = valid_binary_circuit();
        let mut traces = RecursionTraces::default();
        assert_eq!(
            lower_statement_semantics_circuit(&mut traces, CIRCUIT_ID, &reference, &witness,),
            Ok(())
        );
    }

    #[rstest]
    fn valid_empty_leaf_lowers_into_shared_arithmetic_tables() {
        let statement = valid_empty_statement();
        let reference = zero_circuit();
        let witness = valid_empty_circuit(&statement);
        let mut traces = RecursionTraces::default();
        assert_eq!(
            lower_statement_semantics_circuit(&mut traces, CIRCUIT_ID, &reference, &witness,),
            Ok(())
        );
    }

    #[rstest]
    fn valid_segment_leaf_lowers_into_shared_arithmetic_tables() {
        let statement = valid_segment_statement();
        let reference = zero_circuit();
        let witness = valid_segment_circuit(&statement);
        let mut traces = RecursionTraces::default();
        assert_eq!(
            lower_statement_semantics_circuit(&mut traces, CIRCUIT_ID, &reference, &witness,),
            Ok(())
        );
    }

    #[rstest]
    fn verifier_terms_reject_a_nonzero_reference_circuit() {
        assert_eq!(
            public_statement_semantics_terms(
                CIRCUIT_ID,
                &build_statement_semantics_circuit(StatementSemanticsCircuitWitness {
                    segment_selector: true,
                    binary_selector: false,
                    empty_selector: false,
                    segment: &zero_words(),
                    left: &zero_words(),
                    right: &zero_words(),
                    parent: &zero_words(),
                }),
                &RecursionRelations::dummy(),
            ),
            Err(StatementSemanticsLoweringError::ReferenceOutputIsNonzero)
        );
    }
}
