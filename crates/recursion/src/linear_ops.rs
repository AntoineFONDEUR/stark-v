//! Macro-defined linear circuit-node component and witness helpers.
//!
//! Each enabled row proves one verifier-scheduled QM31 add, subtract, or negate
//! node. The operation consumes its operands through `wire`, then emits the
//! result once per recorded downstream use.

use simd::AlignedVec;
use stwo::core::ColumnVec;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::QM31;
use stwo::core::poly::circle::CanonicCoset;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;

use crate::circuit::LinearOpsScheduleRow;
use crate::relations::{RecursionRelations, SharedPrimitiveRelations};
use crate::wire::ProofKind;

/// Fixed linear-operation graph committed by universal preprocessing.
pub struct LinearOpsPreprocessed {
    log_size: u32,
    rows: [Vec<LinearOpsScheduleRow>; 3],
}

impl LinearOpsPreprocessed {
    pub fn new(log_size: u32, rows: Vec<LinearOpsScheduleRow>) -> Result<Self, &'static str> {
        Self::new_for_modes(log_size, [rows.clone(), rows.clone(), rows])
    }

    pub fn new_for_modes(
        log_size: u32,
        rows: [Vec<LinearOpsScheduleRow>; 3],
    ) -> Result<Self, &'static str> {
        if rows
            .iter()
            .any(|mode_rows| mode_rows.len() > (1_usize << log_size))
        {
            return Err("linear-operation schedule exceeds its component capacity");
        }
        Ok(Self { log_size, rows })
    }

    pub fn gen_columns(
        &self,
    ) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
        let size = 1_usize << self.log_size;
        let mut columns = (0..27)
            .map(|_| {
                let mut column = AlignedVec::with_capacity(size);
                column.resize(size, 0);
                column
            })
            .collect::<Vec<_>>();
        for (mode, rows) in self.rows.iter().enumerate() {
            let offset = mode * 9;
            for (index, row) in rows.iter().copied().enumerate() {
                columns[offset][index] = 1;
                columns[offset + 1][index] = row.circuit_id;
                columns[offset + 2][index] = row.node_id;
                columns[offset + 3][index] = row.is_add;
                columns[offset + 4][index] = row.is_sub;
                columns[offset + 5][index] = row.is_neg;
                columns[offset + 6][index] = row.lhs_id;
                columns[offset + 7][index] = row.rhs_id;
                columns[offset + 8][index] = row.uses;
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
        segment_mask: "recursion_linear_ops_segment_mask",
        segment_circuit_id: "recursion_linear_ops_segment_circuit_id",
        segment_node_id: "recursion_linear_ops_segment_node_id",
        segment_is_add: "recursion_linear_ops_segment_is_add",
        segment_is_sub: "recursion_linear_ops_segment_is_sub",
        segment_is_neg: "recursion_linear_ops_segment_is_neg",
        segment_lhs_id: "recursion_linear_ops_segment_lhs_id",
        segment_rhs_id: "recursion_linear_ops_segment_rhs_id",
        segment_uses: "recursion_linear_ops_segment_uses",
        binary_mask: "recursion_linear_ops_binary_mask",
        binary_circuit_id: "recursion_linear_ops_binary_circuit_id",
        binary_node_id: "recursion_linear_ops_binary_node_id",
        binary_is_add: "recursion_linear_ops_binary_is_add",
        binary_is_sub: "recursion_linear_ops_binary_is_sub",
        binary_is_neg: "recursion_linear_ops_binary_is_neg",
        binary_lhs_id: "recursion_linear_ops_binary_lhs_id",
        binary_rhs_id: "recursion_linear_ops_binary_rhs_id",
        binary_uses: "recursion_linear_ops_binary_uses",
        empty_mask: "recursion_linear_ops_empty_mask",
        empty_circuit_id: "recursion_linear_ops_empty_circuit_id",
        empty_node_id: "recursion_linear_ops_empty_node_id",
        empty_is_add: "recursion_linear_ops_empty_is_add",
        empty_is_sub: "recursion_linear_ops_empty_is_sub",
        empty_is_neg: "recursion_linear_ops_empty_is_neg",
        empty_lhs_id: "recursion_linear_ops_empty_lhs_id",
        empty_rhs_id: "recursion_linear_ops_empty_rhs_id",
        empty_uses: "recursion_linear_ops_empty_uses",
    },
    embedded_params: [segment_active, binary_active, empty_active],

    relation wire(6);

    fn linear_ops(
        circuit_id, node_id, is_add, is_sub, is_neg,
        lhs_id, rhs_id,
        lhs_0, lhs_1, lhs_2, lhs_3,
        rhs_0, rhs_1, rhs_2, rhs_3,
        out_0, out_1, out_2, out_3,
        uses,
        segment_mask, segment_circuit_id, segment_node_id,
        segment_is_add, segment_is_sub, segment_is_neg,
        segment_lhs_id, segment_rhs_id, segment_uses,
        binary_mask, binary_circuit_id, binary_node_id,
        binary_is_add, binary_is_sub, binary_is_neg,
        binary_lhs_id, binary_rhs_id, binary_uses,
        empty_mask, empty_circuit_id, empty_node_id,
        empty_is_add, empty_is_sub, empty_is_neg,
        empty_lhs_id, empty_rhs_id, empty_uses,
        segment_active, binary_active, empty_active,
    ) {
        let schedule_mask = segment_active * segment_mask
            + binary_active * binary_mask + empty_active * empty_mask;
        let schedule_circuit_id = segment_active * segment_circuit_id
            + binary_active * binary_circuit_id + empty_active * empty_circuit_id;
        let schedule_node_id = segment_active * segment_node_id
            + binary_active * binary_node_id + empty_active * empty_node_id;
        let schedule_is_add = segment_active * segment_is_add
            + binary_active * binary_is_add + empty_active * empty_is_add;
        let schedule_is_sub = segment_active * segment_is_sub
            + binary_active * binary_is_sub + empty_active * empty_is_sub;
        let schedule_is_neg = segment_active * segment_is_neg
            + binary_active * binary_is_neg + empty_active * empty_is_neg;
        let schedule_lhs_id = segment_active * segment_lhs_id
            + binary_active * binary_lhs_id + empty_active * empty_lhs_id;
        let schedule_rhs_id = segment_active * segment_rhs_id
            + binary_active * binary_rhs_id + empty_active * empty_rhs_id;
        let schedule_uses = segment_active * segment_uses
            + binary_active * binary_uses + empty_active * empty_uses;

        constrain is_add * (1 - is_add);
        constrain is_sub * (1 - is_sub);
        constrain is_neg * (1 - is_neg);
        constrain is_add + is_sub + is_neg - enabler;
        constrain enabler - schedule_mask;
        constrain enabler * (circuit_id - schedule_circuit_id);
        constrain enabler * (node_id - schedule_node_id);
        constrain enabler * (is_add - schedule_is_add);
        constrain enabler * (is_sub - schedule_is_sub);
        constrain enabler * (is_neg - schedule_is_neg);
        constrain enabler * (lhs_id - schedule_lhs_id);
        constrain enabler * (rhs_id - schedule_rhs_id);
        constrain enabler * (uses - schedule_uses);

        constrain is_add * (lhs_0 + rhs_0)
            + is_sub * (lhs_0 - rhs_0) - is_neg * lhs_0 - out_0;
        constrain is_add * (lhs_1 + rhs_1)
            + is_sub * (lhs_1 - rhs_1) - is_neg * lhs_1 - out_1;
        constrain is_add * (lhs_2 + rhs_2)
            + is_sub * (lhs_2 - rhs_2) - is_neg * lhs_2 - out_2;
        constrain is_add * (lhs_3 + rhs_3)
            + is_sub * (lhs_3 - rhs_3) - is_neg * lhs_3 - out_3;

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

#[cfg(test)]
mod tests {
    use super::*;
    use stwo::core::pcs::TreeVec;
    use stwo::core::poly::circle::CanonicCoset;
    use stwo_constraint_framework::{FrameworkEval, assert_constraints_on_polys};

    fn assert_table_satisfies_constraints(
        table: LinearOpsTable,
        schedule: Vec<LinearOpsScheduleRow>,
    ) {
        let recursion_relations = RecursionRelations::dummy();
        let trace = table.into_witness();
        let log_size = trace
            .first()
            .map(|column| column.domain.log_size())
            .expect("linear operation trace has committed columns");
        let preprocessed = LinearOpsPreprocessed::new(log_size, schedule)
            .expect("linear operation schedule fits")
            .gen_columns();
        let (interaction, claimed_sum) = gen_interaction_trace(
            &trace,
            &preprocessed,
            ProofKind::SegmentLeaf,
            &recursion_relations,
        );
        let traces = TreeVec::new(vec![preprocessed, trace, interaction]);
        let trace_polys = traces.map_cols(|column| column.interpolate());
        let eval = eval_for_proof_kind(log_size, ProofKind::SegmentLeaf, &recursion_relations);
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
        assert_table_satisfies_constraints(
            table,
            vec![LinearOpsScheduleRow {
                circuit_id: 1,
                node_id: 2,
                is_add: 1,
                is_sub: 0,
                is_neg: 0,
                lhs_id: 3,
                rhs_id: 4,
                uses: 1,
            }],
        );
    }
}
