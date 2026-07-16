//! AIR evaluation with verifier-supplied relation coefficients.
//!
//! Native proving stores Fiat-Shamir relation elements inside each component.
//! Recursive verification instead represents those elements as circuit wires.
//! These traits let macro-generated components reuse their constraint body
//! while handing relation tuples to an evaluator that owns the coefficients.

use stwo_constraint_framework::{EvalAtRow, FrameworkEval};

/// Row evaluator that combines a named relation with its own coefficients.
pub trait DynamicRelationEvalAtRow: EvalAtRow {
    fn add_to_named_relation(
        &mut self,
        relation: &'static str,
        multiplicity: Self::EF,
        values: &[Self::F],
    );
}

/// Component evaluator whose relation coefficients are supplied by the row evaluator.
pub trait DynamicRelationFrameworkEval: FrameworkEval {
    fn evaluate_dynamic_relations<E: DynamicRelationEvalAtRow>(&self, eval: E) -> E;
}
