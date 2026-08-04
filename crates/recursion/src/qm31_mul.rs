//! Macro-defined QM31 multiplication component and witness helpers.
//!
//! One `define_air_fns!` frame owns the table layout, extension-field limb
//! constraints, circuit-wire relations, concrete row fill, AIR evaluator, and
//! interaction trace. Standalone arithmetic rows leave `in_circuit` clear;
//! circuit-lowering rows bind their operands and result through `op_def` and
//! `wire`.

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

    fn qm31_mul(
        a_0, a_1, a_2, a_3,
        b_0, b_1, b_2, b_3,
        c_0, c_1, c_2, c_3,
        circuit_id, node_id, lhs_id, rhs_id, uses, in_circuit,
    ) {
        constrain in_circuit * (1 - in_circuit);
        constrain in_circuit * (1 - enabler);

        constrain a_0 * b_0 - a_1 * b_1
            + 2 * (a_2 * b_2 - a_3 * b_3) - (a_2 * b_3 + a_3 * b_2)
            - c_0;
        constrain a_0 * b_1 + a_1 * b_0
            + (a_2 * b_2 - a_3 * b_3) + 2 * (a_2 * b_3 + a_3 * b_2)
            - c_1;
        constrain a_0 * b_2 - a_1 * b_3 + a_2 * b_0 - a_3 * b_1 - c_2;
        constrain a_0 * b_3 + a_1 * b_2 + a_2 * b_1 + a_3 * b_0 - c_3;

        consume(in_circuit) op_def(
            circuit_id,
            node_id,
            constant(crate::relations::op_kind::MUL),
            lhs_id,
            rhs_id,
        );
        consume(in_circuit) wire(circuit_id, lhs_id, a_0, a_1, a_2, a_3);
        consume(in_circuit) wire(circuit_id, rhs_id, b_0, b_1, b_2, b_3);
        emit(uses * in_circuit) wire(circuit_id, node_id, c_0, c_1, c_2, c_3);

        return (c_0, c_1, c_2, c_3);
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

/// Record `a * b` in the trace table and return the product.
pub fn push_mul(table: &mut Qm31MulTable, a: QM31, b: QM31) -> QM31 {
    let c = a * b;
    let a = a.to_m31_array();
    let b = b.to_m31_array();
    let limbs = c.to_m31_array();
    table.push(
        a[0].0, a[1].0, a[2].0, a[3].0, b[0].0, b[1].0, b[2].0, b[3].0, limbs[0].0, limbs[1].0,
        limbs[2].0, limbs[3].0, 0, 0, 0, 0, 0, 0,
    );
    c
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::SmallRng;
    use rand::{Rng, SeedableRng};
    use stwo::core::pcs::TreeVec;
    use stwo::core::poly::circle::CanonicCoset;
    use stwo_constraint_framework::{FrameworkEval, assert_constraints_on_polys};

    fn random_qm31(rng: &mut SmallRng) -> QM31 {
        QM31::from_u32_unchecked(
            rng.gen_range(0..(1 << 30)),
            rng.gen_range(0..(1 << 30)),
            rng.gen_range(0..(1 << 30)),
            rng.gen_range(0..(1 << 30)),
        )
    }

    fn assert_table_satisfies_constraints(table: Qm31MulTable) {
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
    fn test_qm31_mul_constraints_hold_on_random_products() {
        let mut rng = SmallRng::seed_from_u64(0);
        let mut table = Qm31MulTable::new();
        for _ in 0..100 {
            let a = random_qm31(&mut rng);
            let b = random_qm31(&mut rng);
            let expected = a * b;
            assert_eq!(push_mul(&mut table, a, b), expected);
        }
        assert_table_satisfies_constraints(table);
    }

    #[test]
    #[should_panic]
    fn test_qm31_mul_constraints_reject_wrong_product() {
        let mut rng = SmallRng::seed_from_u64(1);
        let mut table = Qm31MulTable::new();
        let a = random_qm31(&mut rng);
        let b = random_qm31(&mut rng);
        let a_limbs = a.to_m31_array();
        let b_limbs = b.to_m31_array();
        let c = (a * b).to_m31_array();
        // Corrupt one product limb.
        table.push(
            a_limbs[0].0,
            a_limbs[1].0,
            a_limbs[2].0,
            a_limbs[3].0,
            b_limbs[0].0,
            b_limbs[1].0,
            b_limbs[2].0,
            b_limbs[3].0,
            c[0].0 + 1,
            c[1].0,
            c[2].0,
            c[3].0,
            0,
            0,
            0,
            0,
            0,
            0,
        );
        assert_table_satisfies_constraints(table);
    }

    #[test]
    fn test_qm31_mul_constraint_degrees_within_bound() {
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
