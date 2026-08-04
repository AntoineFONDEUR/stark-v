//! Circuit evaluation for formal STWO AIR expressions.
//!
//! The compiler evaluates the `ExprEvaluator` output produced by an AIR's
//! existing `FrameworkEval::evaluate` implementation over recursion circuit
//! wires. Formal columns and parameters are supplied by the verifier binding;
//! named intermediates are recomputed in their declared order, so they cannot
//! become independent witness inputs.

use core::fmt;
use std::collections::{HashMap, HashSet};

use stwo_constraint_framework::expr::assignment::ExprVariables;
use stwo_constraint_framework::expr::{ColumnExpr, ExprEvaluator};

use crate::recorder::{Rec, Recorder};

/// Circuit values assigned to every external formal AIR variable.
#[derive(Clone, Debug, Default)]
pub struct AirExpressionInputs {
    pub columns: HashMap<(usize, usize, isize), Rec>,
    pub base_parameters: HashMap<String, Rec>,
    pub extension_parameters: HashMap<String, Rec>,
}

/// Evaluates every formal constraint while recomputing named intermediates.
pub fn evaluate_air_expressions(
    expressions: &ExprEvaluator,
    inputs: &AirExpressionInputs,
) -> Result<Vec<Rec>, AirExpressionError> {
    reject_preassigned_intermediates(expressions, inputs)?;
    let column_keys = inputs
        .columns
        .keys()
        .copied()
        .map(ColumnExpr::from)
        .collect::<HashSet<_>>();
    let mut base_parameters = inputs.base_parameters.clone();
    let mut extension_parameters = inputs.extension_parameters.clone();
    let intermediate_count = expressions
        .intermediates
        .len()
        .checked_add(expressions.ext_intermediates.len())
        .ok_or(AirExpressionError::IntermediateCountOverflow)?;

    for index in 0..intermediate_count {
        let name = format!("intermediate{index}");
        match (
            expressions.intermediates.get(&name),
            expressions.ext_intermediates.get(&name),
        ) {
            (Some(expression), None) => {
                validate_variables(
                    &expression.collect_variables(),
                    &column_keys,
                    &base_parameters,
                    &extension_parameters,
                )?;
                let value =
                    expression.eval_expr::<Recorder, _, _>(&inputs.columns, &base_parameters);
                base_parameters.insert(name, value);
            }
            (None, Some(expression)) => {
                validate_variables(
                    &expression.collect_variables(),
                    &column_keys,
                    &base_parameters,
                    &extension_parameters,
                )?;
                let value = expression.eval_expr::<Recorder, _, _, _>(
                    &inputs.columns,
                    &base_parameters,
                    &extension_parameters,
                );
                extension_parameters.insert(name, value);
            }
            (Some(_), Some(_)) => {
                return Err(AirExpressionError::AmbiguousIntermediate { name });
            }
            (None, None) => {
                return Err(AirExpressionError::IntermediateOrderGap { index });
            }
        }
    }

    expressions
        .constraints
        .iter()
        .map(|expression| {
            validate_variables(
                &expression.collect_variables(),
                &column_keys,
                &base_parameters,
                &extension_parameters,
            )?;
            Ok(expression.eval_expr::<Recorder, _, _, _>(
                &inputs.columns,
                &base_parameters,
                &extension_parameters,
            ))
        })
        .collect()
}

/// Appends one component's constraints in STWO composition order.
pub fn accumulate_air_constraints(
    mut accumulator: Rec,
    random_coefficient: Rec,
    denominator_inverse: Rec,
    constraints: impl IntoIterator<Item = Rec>,
) -> Rec {
    for constraint in constraints {
        accumulator =
            accumulator * random_coefficient.clone() + denominator_inverse.clone() * constraint;
    }
    accumulator
}

fn reject_preassigned_intermediates(
    expressions: &ExprEvaluator,
    inputs: &AirExpressionInputs,
) -> Result<(), AirExpressionError> {
    let intermediate_count = expressions
        .intermediates
        .len()
        .checked_add(expressions.ext_intermediates.len())
        .ok_or(AirExpressionError::IntermediateCountOverflow)?;
    for index in 0..intermediate_count {
        let name = format!("intermediate{index}");
        if inputs.base_parameters.contains_key(&name)
            || inputs.extension_parameters.contains_key(&name)
        {
            return Err(AirExpressionError::PreassignedIntermediate { name });
        }
    }
    Ok(())
}

fn validate_variables(
    variables: &ExprVariables,
    columns: &HashSet<ColumnExpr>,
    base_parameters: &HashMap<String, Rec>,
    extension_parameters: &HashMap<String, Rec>,
) -> Result<(), AirExpressionError> {
    if !variables.cols.is_subset(columns) {
        return Err(AirExpressionError::ColumnMissing);
    }
    if let Some(name) = variables
        .params
        .iter()
        .find(|name| !base_parameters.contains_key(*name))
    {
        return Err(AirExpressionError::BaseParameterMissing { name: name.clone() });
    }
    if let Some(name) = variables
        .ext_params
        .iter()
        .find(|name| !extension_parameters.contains_key(*name))
    {
        return Err(AirExpressionError::ExtensionParameterMissing { name: name.clone() });
    }
    Ok(())
}

/// Invalid formal-variable assignment or intermediate program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AirExpressionError {
    IntermediateCountOverflow,
    PreassignedIntermediate { name: String },
    AmbiguousIntermediate { name: String },
    IntermediateOrderGap { index: usize },
    ColumnMissing,
    BaseParameterMissing { name: String },
    ExtensionParameterMissing { name: String },
}

impl fmt::Display for AirExpressionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for AirExpressionError {}

#[cfg(test)]
mod tests {
    use stwo::core::fields::m31::BaseField;
    use stwo::core::fields::qm31::SecureField;
    use stwo_constraint_framework::FrameworkEval;

    use super::*;
    use crate::recorder::CircuitBuilder;

    fn lui_expressions() -> ExprEvaluator {
        prover::components::lui::air::Eval {
            log_size: 6,
            relations: prover::relations::Relations::dummy(),
        }
        .evaluate(ExprEvaluator::new())
    }

    fn external_inputs(
        expressions: &ExprEvaluator,
    ) -> (
        AirExpressionInputs,
        stwo_constraint_framework::expr::assignment::ExprVarAssignment,
    ) {
        let assignment = expressions.random_assignment();
        let mut builder = CircuitBuilder::default();
        let columns = assignment
            .0
            .iter()
            .map(|(coordinate, value)| {
                let (_, input) = builder.input((*value).into());
                (*coordinate, input)
            })
            .collect();
        let base_parameters = assignment
            .1
            .iter()
            .filter(|(name, _)| !name.starts_with("intermediate"))
            .map(|(name, value)| {
                let (_, input) = builder.input((*value).into());
                (name.clone(), input)
            })
            .collect();
        let extension_parameters = assignment
            .2
            .iter()
            .filter(|(name, _)| !name.starts_with("intermediate"))
            .map(|(name, value)| {
                let (_, input) = builder.input(*value);
                (name.clone(), input)
            })
            .collect();
        (
            AirExpressionInputs {
                columns,
                base_parameters,
                extension_parameters,
            },
            assignment,
        )
    }

    #[test]
    fn formal_air_constraints_match_the_expression_oracle() {
        let expressions = lui_expressions();
        let (inputs, assignment) = external_inputs(&expressions);
        let actual = evaluate_air_expressions(&expressions, &inputs)
            .expect("complete formal assignment evaluates")
            .into_iter()
            .map(|value| value.value())
            .collect::<Vec<_>>();
        let expected = expressions
            .constraints
            .iter()
            .map(|expression| expression.assign(&assignment))
            .collect::<Vec<SecureField>>();
        assert_eq!(actual, expected);
    }

    #[test]
    fn named_intermediate_cannot_become_a_witness_input() {
        let expressions = lui_expressions();
        let (mut inputs, _) = external_inputs(&expressions);
        inputs
            .base_parameters
            .insert("intermediate0".into(), Rec::from(BaseField::from(7)));
        assert_eq!(
            evaluate_air_expressions(&expressions, &inputs),
            Err(AirExpressionError::PreassignedIntermediate {
                name: "intermediate0".into()
            })
        );
    }

    #[test]
    fn missing_formal_column_is_rejected_before_expression_indexing() {
        let expressions = lui_expressions();
        let (mut inputs, _) = external_inputs(&expressions);
        let coordinate = *inputs
            .columns
            .keys()
            .next()
            .expect("LUI uses at least one formal column");
        inputs.columns.remove(&coordinate);
        assert_eq!(
            evaluate_air_expressions(&expressions, &inputs),
            Err(AirExpressionError::ColumnMissing)
        );
    }

    #[test]
    fn missing_claimed_sum_parameter_is_rejected() {
        let expressions = lui_expressions();
        let (mut inputs, _) = external_inputs(&expressions);
        inputs.extension_parameters.remove("claimed_sum");
        assert_eq!(
            evaluate_air_expressions(&expressions, &inputs),
            Err(AirExpressionError::ExtensionParameterMissing {
                name: "claimed_sum".into()
            })
        );
    }

    #[test]
    fn every_formal_constraint_depends_on_circuit_nodes() {
        let expressions = lui_expressions();
        let (inputs, _) = external_inputs(&expressions);
        let constraints = evaluate_air_expressions(&expressions, &inputs)
            .expect("complete formal assignment evaluates");
        assert!(
            constraints
                .iter()
                .all(|constraint| matches!(constraint, Rec::Node { .. }))
        );
    }

    #[test]
    fn constraint_accumulation_matches_stwo_composition_order() {
        let expressions = lui_expressions();
        let (inputs, assignment) = external_inputs(&expressions);
        let constraints = evaluate_air_expressions(&expressions, &inputs)
            .expect("complete formal assignment evaluates");
        let random_coefficient = SecureField::from_m31_array([
            BaseField::from(2),
            BaseField::from(3),
            BaseField::from(5),
            BaseField::from(7),
        ]);
        let denominator_inverse = SecureField::from(BaseField::from(11));
        let actual = accumulate_air_constraints(
            Rec::from(SecureField::from(BaseField::from(13))),
            Rec::from(random_coefficient),
            Rec::from(denominator_inverse),
            constraints,
        )
        .value();
        let expected = expressions.constraints.iter().fold(
            SecureField::from(BaseField::from(13)),
            |accumulator, constraint| {
                accumulator * random_coefficient
                    + denominator_inverse * constraint.assign(&assignment)
            },
        );
        assert_eq!(actual, expected);
    }
}
