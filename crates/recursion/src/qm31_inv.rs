//! Macro-defined QM31 inverse component and witness helpers.
//!
//! The macro frame constrains `a * inv = enabler` in extension-field limbs, so
//! enabled rows prove a nonzero inverse while zero padding remains valid.
//! Circuit rows additionally bind the input and output through `op_def` and
//! `wire`.

use stwo::core::fields::FieldExpOps;
use stwo::core::fields::qm31::QM31;

use crate::relations::{RecursionRelations, SharedPrimitiveRelations};

stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [],
    embedded_component: true,
    embedded_relations: crate::relations::SharedPrimitiveRelations,
    logup_batch: 2,
    embedded_dynamic_component: true,

    relation op_def(5);
    relation wire(6);

    fn qm31_inv(
        a_0, a_1, a_2, a_3,
        inv_0, inv_1, inv_2, inv_3,
        circuit_id, node_id, lhs_id, uses, in_circuit,
    ) {
        constrain in_circuit * (1 - in_circuit);
        constrain in_circuit * (1 - enabler);

        constrain a_0 * inv_0 - a_1 * inv_1
            + 2 * (a_2 * inv_2 - a_3 * inv_3) - (a_2 * inv_3 + a_3 * inv_2)
            - enabler;
        constrain a_0 * inv_1 + a_1 * inv_0
            + (a_2 * inv_2 - a_3 * inv_3) + 2 * (a_2 * inv_3 + a_3 * inv_2);
        constrain a_0 * inv_2 - a_1 * inv_3 + a_2 * inv_0 - a_3 * inv_1;
        constrain a_0 * inv_3 + a_1 * inv_2 + a_2 * inv_1 + a_3 * inv_0;

        consume(in_circuit) op_def(
            circuit_id,
            node_id,
            constant(crate::relations::op_kind::INVERSE),
            lhs_id,
            0,
        );
        consume(in_circuit) wire(circuit_id, lhs_id, a_0, a_1, a_2, a_3);
        emit(uses * in_circuit) wire(
            circuit_id,
            node_id,
            inv_0,
            inv_1,
            inv_2,
            inv_3,
        );

        return (inv_0, inv_1, inv_2, inv_3);
    }
}

pub use component::air::{Component, Eval};

/// Generate the interaction trace from the macro-defined relation entries.
pub fn gen_interaction_trace(
    trace: &[stwo::prover::poly::circle::CircleEvaluation<
        stwo::prover::backend::simd::SimdBackend,
        stwo::core::fields::m31::BaseField,
        stwo::prover::poly::BitReversedOrder,
    >],
    recursion_relations: &RecursionRelations,
) -> (
    stwo::core::ColumnVec<
        stwo::prover::poly::circle::CircleEvaluation<
            stwo::prover::backend::simd::SimdBackend,
            stwo::core::fields::m31::BaseField,
            stwo::prover::poly::BitReversedOrder,
        >,
    >,
    QM31,
) {
    component::witness::gen_interaction_trace(
        trace,
        &SharedPrimitiveRelations::for_circuit(recursion_relations),
    )
}

/// Record `a^-1` in the trace table and return it.
///
/// Panics if `a` is zero (zero has no inverse).
pub fn push_inv(table: &mut Qm31InvTable, a: QM31) -> QM31 {
    let inv = a.inverse();
    let a = a.to_m31_array();
    let limbs = inv.to_m31_array();
    table.push(
        a[0].0, a[1].0, a[2].0, a[3].0, limbs[0].0, limbs[1].0, limbs[2].0, limbs[3].0, 0, 0, 0, 0,
        0,
    );
    inv
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::{One, Zero};
    use rand::rngs::SmallRng;
    use rand::{Rng, SeedableRng};
    use stwo::core::pcs::TreeVec;
    use stwo::core::poly::circle::CanonicCoset;
    use stwo_constraint_framework::{FrameworkEval, assert_constraints_on_polys};

    fn random_nonzero_qm31(rng: &mut SmallRng) -> QM31 {
        loop {
            let value = QM31::from_u32_unchecked(
                rng.gen_range(0..(1 << 30)),
                rng.gen_range(0..(1 << 30)),
                rng.gen_range(0..(1 << 30)),
                rng.gen_range(0..(1 << 30)),
            );
            if !value.is_zero() {
                return value;
            }
        }
    }

    fn assert_table_satisfies_constraints(table: Qm31InvTable) {
        let recursion_relations = crate::relations::RecursionRelations::dummy();
        let trace = table.into_witness();
        let log_size = trace
            .first()
            .map(|t| t.domain.log_size())
            .expect("empty trace");
        let (interaction, claimed_sum) = gen_interaction_trace(&trace, &recursion_relations);
        let traces = TreeVec::new(vec![vec![], trace, interaction]);
        let trace_polys = traces.map_cols(|c| c.interpolate());
        let eval = Eval {
            log_size,
            relations: SharedPrimitiveRelations::for_circuit(&recursion_relations),
        };
        assert_constraints_on_polys(
            &trace_polys,
            CanonicCoset::new(log_size),
            |e| {
                eval.evaluate(e);
            },
            claimed_sum,
        );
    }

    #[test]
    fn test_qm31_inv_constraints_hold_on_random_inverses() {
        let mut rng = SmallRng::seed_from_u64(0);
        let mut table = Qm31InvTable::new();
        for _ in 0..100 {
            let a = random_nonzero_qm31(&mut rng);
            let inv = push_inv(&mut table, a);
            assert_eq!(a * inv, QM31::one());
        }
        assert_table_satisfies_constraints(table);
    }

    #[test]
    #[should_panic]
    fn test_qm31_inv_constraints_reject_wrong_inverse() {
        let mut rng = SmallRng::seed_from_u64(1);
        let mut table = Qm31InvTable::new();
        let a = random_nonzero_qm31(&mut rng);
        let a_limbs = a.to_m31_array();
        let inv = a.inverse().to_m31_array();
        // Corrupt one inverse limb.
        table.push(
            a_limbs[0].0,
            a_limbs[1].0,
            a_limbs[2].0,
            a_limbs[3].0,
            inv[0].0 + 1,
            inv[1].0,
            inv[2].0,
            inv[3].0,
            0,
            0,
            0,
            0,
            0,
        );
        assert_table_satisfies_constraints(table);
    }

    #[test]
    fn test_qm31_inv_constraint_degrees_within_bound() {
        use stwo_constraint_framework::expr::ExprEvaluator;
        let eval = Eval {
            log_size: 4,
            relations: SharedPrimitiveRelations::for_circuit(
                &crate::relations::RecursionRelations::dummy(),
            ),
        };
        let expr_eval = eval.evaluate(ExprEvaluator::new());
        let degrees = expr_eval.constraint_degree_bounds();
        // 1 enabler + 2 wiring flags + 4 limb constraints + 2 logup batches
        assert_eq!(degrees.len(), 9);
        // Limb constraints stay degree 2; logup batches reach degree 3.
        assert!(degrees.iter().all(|&d| d <= 3));
    }
}
