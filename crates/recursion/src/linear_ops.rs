//! Macro-defined linear circuit-node component and witness helpers.
//!
//! Each enabled row proves one QM31 add, subtract, or negate node. The
//! operation definition consumes its operands through `wire`, then emits the
//! result once per recorded downstream use.

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

    fn linear_ops(
        circuit_id, node_id, is_add, is_sub, is_neg,
        lhs_id, rhs_id,
        lhs_0, lhs_1, lhs_2, lhs_3,
        rhs_0, rhs_1, rhs_2, rhs_3,
        out_0, out_1, out_2, out_3,
        uses,
    ) {
        constrain is_add * (1 - is_add);
        constrain is_sub * (1 - is_sub);
        constrain is_neg * (1 - is_neg);
        constrain is_add + is_sub + is_neg - enabler;

        constrain is_add * (lhs_0 + rhs_0)
            + is_sub * (lhs_0 - rhs_0) - is_neg * lhs_0 - out_0;
        constrain is_add * (lhs_1 + rhs_1)
            + is_sub * (lhs_1 - rhs_1) - is_neg * lhs_1 - out_1;
        constrain is_add * (lhs_2 + rhs_2)
            + is_sub * (lhs_2 - rhs_2) - is_neg * lhs_2 - out_2;
        constrain is_add * (lhs_3 + rhs_3)
            + is_sub * (lhs_3 - rhs_3) - is_neg * lhs_3 - out_3;

        consume op_def(
            circuit_id,
            node_id,
            is_add * constant(crate::relations::op_kind::ADD)
                + is_sub * constant(crate::relations::op_kind::SUB)
                + is_neg * constant(crate::relations::op_kind::NEG),
            lhs_id,
            rhs_id,
        );
        consume wire(circuit_id, lhs_id, lhs_0, lhs_1, lhs_2, lhs_3);
        consume(is_add + is_sub) wire(
            circuit_id,
            rhs_id,
            rhs_0,
            rhs_1,
            rhs_2,
            rhs_3,
        );
        emit(uses) wire(circuit_id, node_id, out_0, out_1, out_2, out_3);

        return (out_0, out_1, out_2, out_3);
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

#[cfg(test)]
mod tests {
    use super::*;
    use stwo::core::pcs::TreeVec;
    use stwo::core::poly::circle::CanonicCoset;
    use stwo_constraint_framework::{FrameworkEval, assert_constraints_on_polys};

    fn assert_table_satisfies_constraints(table: LinearOpsTable) {
        let recursion_relations = RecursionRelations::dummy();
        let trace = table.into_witness();
        let log_size = trace
            .first()
            .map(|column| column.domain.log_size())
            .expect("linear operation trace has committed columns");
        let (interaction, claimed_sum) = gen_interaction_trace(&trace, &recursion_relations);
        let traces = TreeVec::new(vec![vec![], trace, interaction]);
        let trace_polys = traces.map_cols(|column| column.interpolate());
        let eval = Eval {
            log_size,
            relations: SharedPrimitiveRelations::for_circuit(&recursion_relations),
        };
        assert_constraints_on_polys(
            &trace_polys,
            CanonicCoset::new(log_size),
            |row| {
                eval.evaluate(row);
            },
            claimed_sum,
        );
    }

    #[test]
    #[should_panic]
    fn test_linear_ops_constraints_reject_wrong_addition_result() {
        let mut table = LinearOpsTable::new();
        // An enabled addition row cannot claim an output unrelated to its inputs.
        table.push(1, 2, 1, 0, 0, 3, 4, 5, 0, 0, 0, 7, 0, 0, 0, 13, 0, 0, 0, 1);
        assert_table_satisfies_constraints(table);
    }
}
