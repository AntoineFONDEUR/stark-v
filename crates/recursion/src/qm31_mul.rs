//! QM31 multiplication component: witness generation and AIR evaluation.
//!
//! The constraints live in the `define_component_tables!` invocation in
//! `lib.rs`; this module only wires them into a `FrameworkEval` and fills the
//! trace table from actual QM31 products, so stwo's field arithmetic is the
//! oracle the AIR is tested against.

use stwo::core::ColumnVec;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::QM31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, RelationEntry,
};

use crate::Qm31MulTable;
use crate::prover_columns::Qm31MulColumns;
use crate::relations::{RecursionRelations, op_kind};

pub type Component = FrameworkComponent<Eval>;

#[derive(Clone)]
pub struct Eval {
    pub log_size: u32,
    pub recursion_relations: RecursionRelations,
}

impl FrameworkEval for Eval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let cols = Qm31MulColumns::from_eval(&mut eval);
        for constraint in cols.constraints() {
            eval.add_constraint(constraint);
        }
        // Circuit wiring: rows with in_circuit set implement one Mul node of
        // a recorded composition circuit.
        eval.add_to_relation(RelationEntry::new(
            &self.recursion_relations.op_def,
            -E::EF::from(cols.in_circuit.clone()),
            &[
                cols.circuit_id.clone(),
                cols.node_id.clone(),
                E::F::from(BaseField::from(op_kind::MUL)),
                cols.lhs_id.clone(),
                cols.rhs_id.clone(),
            ],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.recursion_relations.wire,
            -E::EF::from(cols.in_circuit.clone()),
            &[
                cols.circuit_id.clone(),
                cols.lhs_id.clone(),
                cols.a_0.clone(),
                cols.a_1.clone(),
                cols.a_2.clone(),
                cols.a_3.clone(),
            ],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.recursion_relations.wire,
            -E::EF::from(cols.in_circuit.clone()),
            &[
                cols.circuit_id.clone(),
                cols.rhs_id.clone(),
                cols.b_0.clone(),
                cols.b_1.clone(),
                cols.b_2.clone(),
                cols.b_3.clone(),
            ],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.recursion_relations.wire,
            E::EF::from(cols.uses.clone() * cols.in_circuit.clone()),
            &[
                cols.circuit_id.clone(),
                cols.node_id.clone(),
                cols.c_0.clone(),
                cols.c_1.clone(),
                cols.c_2.clone(),
                cols.c_3.clone(),
            ],
        ));
        eval.finalize_logup_in_pairs();
        eval
    }
}

/// Generate the interaction trace and the claimed sum of the wiring entries.
pub fn gen_interaction_trace(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    recursion_relations: &RecursionRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    let cols = Qm31MulColumns::from_iter(trace.iter().map(|eval| &eval.values.data));
    let simd_size = cols.enabler.len();
    let log_size = trace[0].domain.log_size();
    let mut logup_gen = LogupTraceGenerator::new(log_size);

    let neg_in_circuit: Vec<PackedQM31> = (0..simd_size)
        .map(|i| -PackedQM31::from(cols.in_circuit[i]))
        .collect();
    let pos_uses: Vec<PackedQM31> = (0..simd_size)
        .map(|i| PackedQM31::from(cols.uses[i] * cols.in_circuit[i]))
        .collect();
    let mul_kind =
        stwo::prover::backend::simd::m31::PackedM31::broadcast(BaseField::from(op_kind::MUL));
    let kind: Vec<_> = (0..simd_size).map(|_| mul_kind).collect();

    let def_denom = combine!(
        recursion_relations.op_def,
        [
            cols.circuit_id,
            cols.node_id,
            &kind,
            cols.lhs_id,
            cols.rhs_id
        ]
    );
    let lhs_denom = combine!(
        recursion_relations.wire,
        [
            cols.circuit_id,
            cols.lhs_id,
            cols.a_0,
            cols.a_1,
            cols.a_2,
            cols.a_3
        ]
    );
    let rhs_denom = combine!(
        recursion_relations.wire,
        [
            cols.circuit_id,
            cols.rhs_id,
            cols.b_0,
            cols.b_1,
            cols.b_2,
            cols.b_3
        ]
    );
    let out_denom = combine!(
        recursion_relations.wire,
        [
            cols.circuit_id,
            cols.node_id,
            cols.c_0,
            cols.c_1,
            cols.c_2,
            cols.c_3
        ]
    );

    write_pair!(
        &neg_in_circuit,
        &def_denom,
        &neg_in_circuit,
        &lhs_denom,
        logup_gen
    );
    write_pair!(
        &neg_in_circuit,
        &rhs_denom,
        &pos_uses,
        &out_denom,
        logup_gen
    );
    logup_gen.finalize_last()
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
    use stwo_constraint_framework::assert_constraints_on_polys;

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
            recursion_relations,
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
            recursion_relations: crate::relations::RecursionRelations::dummy(),
        };
        let expr_eval = eval.evaluate(ExprEvaluator::new());
        let degrees = expr_eval.constraint_degree_bounds();
        // 1 enabler + 2 wiring flags + 4 limb constraints + 2 logup batches
        assert_eq!(degrees.len(), 9);
        // Limb constraints stay degree 2; logup batches reach degree 3.
        assert!(degrees.iter().all(|&d| d <= 3));
    }
}
