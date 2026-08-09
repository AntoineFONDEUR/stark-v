//! Macro-defined QM31 multiplication component and witness helpers.
//!
//! One `define_air_fns!` frame owns the table layout, extension-field limb
//! constraints, circuit-wire relations, concrete row fill, AIR evaluator, and
//! interaction trace. Standalone arithmetic rows leave `in_circuit` clear;
//! circuit-lowering rows bind their operands and result through a fixed
//! preprocessing schedule and `wire`.

use simd::AlignedVec;
use stwo::core::ColumnVec;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::QM31;
use stwo::core::poly::circle::CanonicCoset;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;

use crate::circuit::Qm31MulScheduleRow;
use crate::relations::{RecursionRelations, SharedPrimitiveRelations};
use crate::wire::ProofKind;

/// Fixed multiplication graph committed by the universal preprocessing tree.
pub struct Qm31MulPreprocessed {
    log_size: u32,
    rows: [Vec<Qm31MulScheduleRow>; 3],
}

impl Qm31MulPreprocessed {
    pub fn new(log_size: u32, rows: Vec<Qm31MulScheduleRow>) -> Result<Self, &'static str> {
        Self::new_for_modes(log_size, [rows.clone(), rows.clone(), rows])
    }

    pub fn new_for_modes(
        log_size: u32,
        rows: [Vec<Qm31MulScheduleRow>; 3],
    ) -> Result<Self, &'static str> {
        if rows
            .iter()
            .any(|mode_rows| mode_rows.len() > (1_usize << log_size))
        {
            return Err("multiplication schedule exceeds its component capacity");
        }
        Ok(Self { log_size, rows })
    }

    pub fn gen_columns(
        &self,
    ) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
        let size = 1_usize << self.log_size;
        let mut columns = (0..18)
            .map(|_| {
                let mut column = AlignedVec::with_capacity(size);
                column.resize(size, 0);
                column
            })
            .collect::<Vec<_>>();
        for (mode, rows) in self.rows.iter().enumerate() {
            let offset = mode * 6;
            for (index, row) in rows.iter().copied().enumerate() {
                columns[offset][index] = 1;
                columns[offset + 1][index] = row.circuit_id;
                columns[offset + 2][index] = row.node_id;
                columns[offset + 3][index] = row.lhs_id;
                columns[offset + 4][index] = row.rhs_id;
                columns[offset + 5][index] = row.uses;
            }
        }
        let domain = CanonicCoset::new(self.log_size).circle_domain();
        columns
            .into_iter()
            .map(|column| CircleEvaluation::new(domain, BaseColumn::from(column)))
            .collect()
    }
}

stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [],
    embedded_component: true,
    embedded_relations: crate::relations::SharedPrimitiveRelations,
    logup_batch: 2,
    embedded_dynamic_component: true,
    embedded_preprocessed: {
        segment_mask: "recursion_qm31_mul_segment_mask",
        segment_circuit_id: "recursion_qm31_mul_segment_circuit_id",
        segment_node_id: "recursion_qm31_mul_segment_node_id",
        segment_lhs_id: "recursion_qm31_mul_segment_lhs_id",
        segment_rhs_id: "recursion_qm31_mul_segment_rhs_id",
        segment_uses: "recursion_qm31_mul_segment_uses",
        binary_mask: "recursion_qm31_mul_binary_mask",
        binary_circuit_id: "recursion_qm31_mul_binary_circuit_id",
        binary_node_id: "recursion_qm31_mul_binary_node_id",
        binary_lhs_id: "recursion_qm31_mul_binary_lhs_id",
        binary_rhs_id: "recursion_qm31_mul_binary_rhs_id",
        binary_uses: "recursion_qm31_mul_binary_uses",
        empty_mask: "recursion_qm31_mul_empty_mask",
        empty_circuit_id: "recursion_qm31_mul_empty_circuit_id",
        empty_node_id: "recursion_qm31_mul_empty_node_id",
        empty_lhs_id: "recursion_qm31_mul_empty_lhs_id",
        empty_rhs_id: "recursion_qm31_mul_empty_rhs_id",
        empty_uses: "recursion_qm31_mul_empty_uses",
    },
    embedded_params: [segment_active, binary_active, empty_active],

    relation wire(6);

    fn qm31_mul(
        a_0, a_1, a_2, a_3,
        b_0, b_1, b_2, b_3,
        c_0, c_1, c_2, c_3,
        circuit_id, node_id, lhs_id, rhs_id, uses, in_circuit,
        segment_mask, segment_circuit_id, segment_node_id,
        segment_lhs_id, segment_rhs_id, segment_uses,
        binary_mask, binary_circuit_id, binary_node_id,
        binary_lhs_id, binary_rhs_id, binary_uses,
        empty_mask, empty_circuit_id, empty_node_id,
        empty_lhs_id, empty_rhs_id, empty_uses,
        segment_active, binary_active, empty_active,
    ) {
        let schedule_mask = segment_active * segment_mask
            + binary_active * binary_mask + empty_active * empty_mask;
        let schedule_circuit_id = segment_active * segment_circuit_id
            + binary_active * binary_circuit_id + empty_active * empty_circuit_id;
        let schedule_node_id = segment_active * segment_node_id
            + binary_active * binary_node_id + empty_active * empty_node_id;
        let schedule_lhs_id = segment_active * segment_lhs_id
            + binary_active * binary_lhs_id + empty_active * empty_lhs_id;
        let schedule_rhs_id = segment_active * segment_rhs_id
            + binary_active * binary_rhs_id + empty_active * empty_rhs_id;
        let schedule_uses = segment_active * segment_uses
            + binary_active * binary_uses + empty_active * empty_uses;

        constrain in_circuit * (1 - in_circuit);
        constrain in_circuit * (1 - enabler);
        constrain in_circuit - schedule_mask;
        constrain in_circuit * (circuit_id - schedule_circuit_id);
        constrain in_circuit * (node_id - schedule_node_id);
        constrain in_circuit * (lhs_id - schedule_lhs_id);
        constrain in_circuit * (rhs_id - schedule_rhs_id);
        constrain in_circuit * (uses - schedule_uses);

        constrain a_0 * b_0 - a_1 * b_1
            + 2 * (a_2 * b_2 - a_3 * b_3) - (a_2 * b_3 + a_3 * b_2)
            - c_0;
        constrain a_0 * b_1 + a_1 * b_0
            + (a_2 * b_2 - a_3 * b_3) + 2 * (a_2 * b_3 + a_3 * b_2)
            - c_1;
        constrain a_0 * b_2 - a_1 * b_3 + a_2 * b_0 - a_3 * b_1 - c_2;
        constrain a_0 * b_3 + a_1 * b_2 + a_2 * b_1 + a_3 * b_0 - c_3;

        consume(in_circuit) wire(circuit_id, lhs_id, a_0, a_1, a_2, a_3);
        consume(in_circuit) wire(circuit_id, rhs_id, b_0, b_1, b_2, b_3);
        emit(uses * in_circuit) wire(circuit_id, node_id, c_0, c_1, c_2, c_3);

        return (c_0, c_1, c_2, c_3);
    }
}

pub use component::air::{Component, Eval};

/// Construct the generated evaluator for one universal proof kind.
pub fn eval_for_proof_kind(
    log_size: u32,
    proof_kind: ProofKind,
    recursion_relations: &RecursionRelations,
) -> Eval {
    Eval {
        log_size,
        segment_active: BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        binary_active: BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode)),
        empty_active: BaseField::from(u32::from(proof_kind == ProofKind::EmptyLeaf)),
        relations: SharedPrimitiveRelations::for_circuit(recursion_relations),
    }
}

/// Generate the interaction trace from the macro-defined relation entries.
pub fn gen_interaction_trace(
    trace: &[stwo::prover::poly::circle::CircleEvaluation<
        stwo::prover::backend::simd::SimdBackend,
        stwo::core::fields::m31::BaseField,
        stwo::prover::poly::BitReversedOrder,
    >],
    preprocessed: &[stwo::prover::poly::circle::CircleEvaluation<
        stwo::prover::backend::simd::SimdBackend,
        stwo::core::fields::m31::BaseField,
        stwo::prover::poly::BitReversedOrder,
    >],
    proof_kind: ProofKind,
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
        preprocessed,
        BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode)),
        BaseField::from(u32::from(proof_kind == ProofKind::EmptyLeaf)),
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
        let preprocessed = Qm31MulPreprocessed::new(log_size, vec![])
            .expect("empty standalone schedule fits")
            .gen_columns();
        let (interaction, claimed_sum) = gen_interaction_trace(
            &trace,
            &preprocessed,
            ProofKind::SegmentLeaf,
            &recursion_relations,
        );
        let traces = TreeVec::new(vec![preprocessed, trace, interaction]);
        let trace_polys = traces.map_cols(|c| c.interpolate());
        let eval = eval_for_proof_kind(log_size, ProofKind::SegmentLeaf, &recursion_relations);
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
        let relations = crate::relations::RecursionRelations::dummy();
        let eval = eval_for_proof_kind(4, ProofKind::SegmentLeaf, &relations);
        let expr_eval = eval.evaluate(ExprEvaluator::new());
        let degrees = expr_eval.constraint_degree_bounds();
        // Enabling, six fixed-schedule bindings, four limb constraints, and LogUp.
        assert_eq!(degrees.len(), 15);
        // Limb constraints stay degree 2; logup batches reach degree 3.
        assert!(degrees.iter().all(|&d| d <= 3));
    }
}
