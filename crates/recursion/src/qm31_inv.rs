//! QM31 inverse component: witness generation and AIR evaluation.
//!
//! The constraints live in the `define_component_tables!` invocation in
//! `lib.rs`: `a * inv = enabler` limb-by-limb, so padding rows hold and
//! enabled rows force `a` to be invertible. Witness generation computes the
//! inverse with stwo's field arithmetic, which the tests use as the oracle.

use stwo::core::ColumnVec;
use stwo::core::fields::FieldExpOps;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::QM31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, RelationEntry,
};

use crate::Qm31InvTable;
use crate::prover_columns::Qm31InvColumns;
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
        let cols = Qm31InvColumns::from_eval(&mut eval);
        for constraint in cols.constraints() {
            eval.add_constraint(constraint);
        }
        // Circuit wiring: rows with in_circuit set implement one Inverse
        // node of a recorded composition circuit.
        eval.add_to_relation(RelationEntry::new(
            &self.recursion_relations.op_def,
            -E::EF::from(cols.in_circuit.clone()),
            &[
                cols.circuit_id.clone(),
                cols.node_id.clone(),
                E::F::from(BaseField::from(op_kind::INVERSE)),
                cols.lhs_id.clone(),
                E::F::from(BaseField::from(0u32)),
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
            E::EF::from(cols.uses.clone() * cols.in_circuit.clone()),
            &[
                cols.circuit_id.clone(),
                cols.node_id.clone(),
                cols.inv_0.clone(),
                cols.inv_1.clone(),
                cols.inv_2.clone(),
                cols.inv_3.clone(),
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
    let cols = Qm31InvColumns::from_iter(trace.iter().map(|eval| &eval.values.data));
    let simd_size = cols.enabler.len();
    let log_size = trace[0].domain.log_size();
    let mut logup_gen = LogupTraceGenerator::new(log_size);

    let neg_in_circuit: Vec<PackedQM31> = (0..simd_size)
        .map(|i| -PackedQM31::from(cols.in_circuit[i]))
        .collect();
    let pos_uses: Vec<PackedQM31> = (0..simd_size)
        .map(|i| PackedQM31::from(cols.uses[i] * cols.in_circuit[i]))
        .collect();
    let inv_kind =
        stwo::prover::backend::simd::m31::PackedM31::broadcast(BaseField::from(op_kind::INVERSE));
    let kind: Vec<_> = (0..simd_size).map(|_| inv_kind).collect();
    let zero = stwo::prover::backend::simd::m31::PackedM31::broadcast(BaseField::from(0u32));
    let zero_col: Vec<_> = (0..simd_size).map(|_| zero).collect();

    let def_denom = combine!(
        recursion_relations.op_def,
        [cols.circuit_id, cols.node_id, &kind, cols.lhs_id, &zero_col]
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
    let out_denom = combine!(
        recursion_relations.wire,
        [
            cols.circuit_id,
            cols.node_id,
            cols.inv_0,
            cols.inv_1,
            cols.inv_2,
            cols.inv_3
        ]
    );

    write_pair!(
        &neg_in_circuit,
        &def_denom,
        &neg_in_circuit,
        &lhs_denom,
        logup_gen
    );
    write_col!(&pos_uses, &out_denom, logup_gen);
    logup_gen.finalize_last()
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
    use stwo_constraint_framework::assert_constraints_on_polys;

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
