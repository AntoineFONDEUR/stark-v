//! Lowering of the fixed recursion AIR-composition circuit.
//!
//! The existing arithmetic DSL components own every operation row and their
//! verifier preprocessing fixes the graph. Input and zero-output ownership is
//! provided by the shared composition-input DSL component.

use core::fmt;

use air::digest::M31Word;

use crate::circuit::{CircuitTraces, lower_arena_operations};
use crate::recorder::Op;
use crate::recursion_air_composition_circuit::RecursionAirCompositionCircuit;

/// Lowers one structurally checked child-composition circuit.
pub fn lower_recursion_air_composition_circuit(
    traces: &mut CircuitTraces,
    circuit_id: u32,
    reference: &RecursionAirCompositionCircuit,
    witness: &RecursionAirCompositionCircuit,
) -> Result<(), RecursionAirCompositionLoweringError> {
    M31Word::try_from(circuit_id)
        .map_err(|_| RecursionAirCompositionLoweringError::CircuitIdNotCanonical { circuit_id })?;
    validate_structure(reference, witness)?;
    if witness.nonzero_output_count() != 0 {
        return Err(RecursionAirCompositionLoweringError::NonzeroCompositionEquality);
    }
    let arena = witness.circuit().arena();
    lower_arena_operations(traces, circuit_id, &arena, witness.circuit().outputs());
    Ok(())
}

fn validate_structure(
    reference: &RecursionAirCompositionCircuit,
    witness: &RecursionAirCompositionCircuit,
) -> Result<(), RecursionAirCompositionLoweringError> {
    if reference.input_bindings() != witness.input_bindings() {
        return Err(RecursionAirCompositionLoweringError::InputLayoutMismatch);
    }
    if reference.circuit().outputs() != witness.circuit().outputs() {
        return Err(RecursionAirCompositionLoweringError::OutputLayoutMismatch);
    }
    let reference_arena = reference.circuit().arena();
    let witness_arena = witness.circuit().arena();
    if reference_arena.nodes.len() != witness_arena.nodes.len() {
        return Err(RecursionAirCompositionLoweringError::NodeCountMismatch {
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
            return Err(RecursionAirCompositionLoweringError::NodeStructureMismatch { node_id });
        }
    }
    Ok(())
}

/// Invalid recursion-composition identity, graph, or equality witness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RecursionAirCompositionLoweringError {
    CircuitIdNotCanonical { circuit_id: u32 },
    InputLayoutMismatch,
    OutputLayoutMismatch,
    NodeCountMismatch { expected: usize, actual: usize },
    NodeStructureMismatch { node_id: usize },
    NonzeroCompositionEquality,
}

impl fmt::Display for RecursionAirCompositionLoweringError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for RecursionAirCompositionLoweringError {}
