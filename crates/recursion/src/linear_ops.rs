//! Linear circuit-node component: witness generation and AIR evaluation.
//!
//! Each enabled row implements one add/sub/neg node of a recorded
//! composition circuit: the limb arithmetic is
//! constrained in the DSL, the node's structure is discharged against the
//! public `op_def` claims, operands are consumed and the result emitted
//! through the `wire` relation with multiplicity equal to the node's use
//! count.

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

use crate::prover_columns::LinearOpsColumns;
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
        let cols = LinearOpsColumns::from_eval(&mut eval);
        for constraint in cols.constraints() {
            eval.add_constraint(constraint);
        }
        let kind = cols.is_add.clone() * E::F::from(BaseField::from(op_kind::ADD))
            + cols.is_sub.clone() * E::F::from(BaseField::from(op_kind::SUB))
            + cols.is_neg.clone() * E::F::from(BaseField::from(op_kind::NEG));

        // Structure: this row is the canonical node (cid, node, kind, lhs, rhs).
        eval.add_to_relation(RelationEntry::new(
            &self.recursion_relations.op_def,
            -E::EF::from(cols.enabler.clone()),
            &[
                cols.circuit_id.clone(),
                cols.node_id.clone(),
                kind,
                cols.lhs_id.clone(),
                cols.rhs_id.clone(),
            ],
        ));
        // Operands.
        eval.add_to_relation(RelationEntry::new(
            &self.recursion_relations.wire,
            -E::EF::from(cols.enabler.clone()),
            &[
                cols.circuit_id.clone(),
                cols.lhs_id.clone(),
                cols.lhs_0.clone(),
                cols.lhs_1.clone(),
                cols.lhs_2.clone(),
                cols.lhs_3.clone(),
            ],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.recursion_relations.wire,
            -E::EF::from(cols.is_add.clone() + cols.is_sub.clone()),
            &[
                cols.circuit_id.clone(),
                cols.rhs_id.clone(),
                cols.rhs_0.clone(),
                cols.rhs_1.clone(),
                cols.rhs_2.clone(),
                cols.rhs_3.clone(),
            ],
        ));
        // Result, once per use.
        eval.add_to_relation(RelationEntry::new(
            &self.recursion_relations.wire,
            E::EF::from(cols.uses.clone()),
            &[
                cols.circuit_id.clone(),
                cols.node_id.clone(),
                cols.out_0.clone(),
                cols.out_1.clone(),
                cols.out_2.clone(),
                cols.out_3.clone(),
            ],
        ));
        eval.finalize_logup_in_pairs();
        eval
    }
}

/// Generate the interaction trace and the claimed sum of the four entries.
pub fn gen_interaction_trace(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    recursion_relations: &RecursionRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    let cols = LinearOpsColumns::from_iter(trace.iter().map(|eval| &eval.values.data));
    let simd_size = cols.enabler.len();
    let log_size = trace[0].domain.log_size();
    let mut logup_gen = LogupTraceGenerator::new(log_size);

    let neg_enabler: Vec<PackedQM31> = (0..simd_size)
        .map(|i| -PackedQM31::from(cols.enabler[i]))
        .collect();
    let neg_binary: Vec<PackedQM31> = (0..simd_size)
        .map(|i| -PackedQM31::from(cols.is_add[i] + cols.is_sub[i]))
        .collect();
    let pos_uses: Vec<PackedQM31> = (0..simd_size)
        .map(|i| PackedQM31::from(cols.uses[i]))
        .collect();

    let add = stwo::prover::backend::simd::m31::PackedM31::broadcast(BaseField::from(op_kind::ADD));
    let sub = stwo::prover::backend::simd::m31::PackedM31::broadcast(BaseField::from(op_kind::SUB));
    let neg = stwo::prover::backend::simd::m31::PackedM31::broadcast(BaseField::from(op_kind::NEG));
    let kind: Vec<_> = (0..simd_size)
        .map(|i| cols.is_add[i] * add + cols.is_sub[i] * sub + cols.is_neg[i] * neg)
        .collect();

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
            cols.lhs_0,
            cols.lhs_1,
            cols.lhs_2,
            cols.lhs_3
        ]
    );
    let rhs_denom = combine!(
        recursion_relations.wire,
        [
            cols.circuit_id,
            cols.rhs_id,
            cols.rhs_0,
            cols.rhs_1,
            cols.rhs_2,
            cols.rhs_3
        ]
    );
    let out_denom = combine!(
        recursion_relations.wire,
        [
            cols.circuit_id,
            cols.node_id,
            cols.out_0,
            cols.out_1,
            cols.out_2,
            cols.out_3
        ]
    );

    write_pair!(
        &neg_enabler,
        &def_denom,
        &neg_enabler,
        &lhs_denom,
        logup_gen
    );
    write_pair!(&neg_binary, &rhs_denom, &pos_uses, &out_denom, logup_gen);
    logup_gen.finalize_last()
}
