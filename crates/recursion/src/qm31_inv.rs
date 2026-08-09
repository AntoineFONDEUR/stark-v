//! Macro-defined QM31 inverse component and witness helpers.
//!
//! The macro frame constrains `a * inv = enabler` in extension-field limbs, so
//! enabled rows prove a nonzero inverse while zero padding remains valid.
//! Circuit rows additionally bind the input and output through a fixed
//! preprocessing schedule and `wire`.

use simd::AlignedVec;
use stwo::core::ColumnVec;
use stwo::core::fields::FieldExpOps;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::QM31;
use stwo::core::poly::circle::CanonicCoset;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;

use crate::circuit::Qm31InvScheduleRow;
use crate::relations::{RecursionRelations, SharedPrimitiveRelations};
use crate::wire::ProofKind;

/// Fixed inversion graph committed by the universal preprocessing tree.
pub struct Qm31InvPreprocessed {
    log_size: u32,
    rows: [Vec<Qm31InvScheduleRow>; 3],
}

impl Qm31InvPreprocessed {
    pub fn new(log_size: u32, rows: Vec<Qm31InvScheduleRow>) -> Result<Self, &'static str> {
        Self::new_for_modes(log_size, [rows.clone(), rows.clone(), rows])
    }

    pub fn new_for_modes(
        log_size: u32,
        rows: [Vec<Qm31InvScheduleRow>; 3],
    ) -> Result<Self, &'static str> {
        if rows
            .iter()
            .any(|mode_rows| mode_rows.len() > (1_usize << log_size))
        {
            return Err("inversion schedule exceeds its component capacity");
        }
        Ok(Self { log_size, rows })
    }

    pub fn gen_columns(
        &self,
    ) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
        let size = 1_usize << self.log_size;
        let mut columns = (0..15)
            .map(|_| {
                let mut column = AlignedVec::with_capacity(size);
                column.resize(size, 0);
                column
            })
            .collect::<Vec<_>>();
        for (mode, rows) in self.rows.iter().enumerate() {
            let offset = mode * 5;
            for (index, row) in rows.iter().copied().enumerate() {
                columns[offset][index] = 1;
                columns[offset + 1][index] = row.circuit_id;
                columns[offset + 2][index] = row.node_id;
                columns[offset + 3][index] = row.lhs_id;
                columns[offset + 4][index] = row.uses;
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
        segment_mask: "recursion_qm31_inv_segment_mask",
        segment_circuit_id: "recursion_qm31_inv_segment_circuit_id",
        segment_node_id: "recursion_qm31_inv_segment_node_id",
        segment_lhs_id: "recursion_qm31_inv_segment_lhs_id",
        segment_uses: "recursion_qm31_inv_segment_uses",
        binary_mask: "recursion_qm31_inv_binary_mask",
        binary_circuit_id: "recursion_qm31_inv_binary_circuit_id",
        binary_node_id: "recursion_qm31_inv_binary_node_id",
        binary_lhs_id: "recursion_qm31_inv_binary_lhs_id",
        binary_uses: "recursion_qm31_inv_binary_uses",
        empty_mask: "recursion_qm31_inv_empty_mask",
        empty_circuit_id: "recursion_qm31_inv_empty_circuit_id",
        empty_node_id: "recursion_qm31_inv_empty_node_id",
        empty_lhs_id: "recursion_qm31_inv_empty_lhs_id",
        empty_uses: "recursion_qm31_inv_empty_uses",
    },
    embedded_params: [segment_active, binary_active, empty_active],

    relation wire(6);

    fn qm31_inv(
        a_0, a_1, a_2, a_3,
        inv_0, inv_1, inv_2, inv_3,
        circuit_id, node_id, lhs_id, uses, in_circuit,
        segment_mask, segment_circuit_id, segment_node_id, segment_lhs_id, segment_uses,
        binary_mask, binary_circuit_id, binary_node_id, binary_lhs_id, binary_uses,
        empty_mask, empty_circuit_id, empty_node_id, empty_lhs_id, empty_uses,
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
        let schedule_uses = segment_active * segment_uses
            + binary_active * binary_uses + empty_active * empty_uses;

        constrain in_circuit * (1 - in_circuit);
        constrain in_circuit * (1 - enabler);
        constrain in_circuit - schedule_mask;
        constrain in_circuit * (circuit_id - schedule_circuit_id);
        constrain in_circuit * (node_id - schedule_node_id);
        constrain in_circuit * (lhs_id - schedule_lhs_id);
        constrain in_circuit * (uses - schedule_uses);

        constrain a_0 * inv_0 - a_1 * inv_1
            + 2 * (a_2 * inv_2 - a_3 * inv_3) - (a_2 * inv_3 + a_3 * inv_2)
            - enabler;
        constrain a_0 * inv_1 + a_1 * inv_0
            + (a_2 * inv_2 - a_3 * inv_3) + 2 * (a_2 * inv_3 + a_3 * inv_2);
        constrain a_0 * inv_2 - a_1 * inv_3 + a_2 * inv_0 - a_3 * inv_1;
        constrain a_0 * inv_3 + a_1 * inv_2 + a_2 * inv_1 + a_3 * inv_0;

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
        let preprocessed = Qm31InvPreprocessed::new(log_size, vec![])
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
        let relations = crate::relations::RecursionRelations::dummy();
        let eval = eval_for_proof_kind(4, ProofKind::SegmentLeaf, &relations);
        let expr_eval = eval.evaluate(ExprEvaluator::new());
        let degrees = expr_eval.constraint_degree_bounds();
        // Enabling, five fixed-schedule bindings, four limb constraints, and LogUp.
        assert_eq!(degrees.len(), 13);
        // Limb constraints stay degree 2; logup batches reach degree 3.
        assert!(degrees.iter().all(|&d| d <= 3));
    }
}
