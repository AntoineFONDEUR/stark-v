//! Merkle hash-step component: witness generation and AIR evaluation.
//!
//! Each enabled row claims `parent = permute(left || right)[..8]` through one
//! atomic 32-word `poseidon2_io` tuple. The permutation constraints live
//! solely in the reused `prover::components::poseidon2` component, whose
//! witness table carries one matching io row per hash step. Keeping input and
//! output in the same tuple prevents different hash calls from exchanging
//! otherwise valid outputs.

use air::poseidon2::{T, poseidon2_traced_state};
use air::trace::Poseidon2Table;
use prover::relations::Relations;
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

use crate::MerklePathTable;
use crate::prover_columns::MerklePathColumns;
use crate::relations::RecursionRelations;

pub type Component = FrameworkComponent<Eval>;

#[derive(Clone)]
pub struct Eval {
    pub log_size: u32,
    pub relations: Relations,
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
        let cols = MerklePathColumns::from_eval(&mut eval);
        for constraint in cols.constraints() {
            eval.add_constraint(constraint);
        }
        // Consume one complete permutation call emitted by the poseidon2
        // component. The second output half is retained solely to make the
        // call identity atomic; the Merkle digest is the first eight words.
        eval.add_to_relation(RelationEntry::new(
            &self.relations.poseidon2_io,
            -E::EF::from(cols.enabler.clone()),
            &[
                cols.left_0.clone(),
                cols.left_1.clone(),
                cols.left_2.clone(),
                cols.left_3.clone(),
                cols.left_4.clone(),
                cols.left_5.clone(),
                cols.left_6.clone(),
                cols.left_7.clone(),
                cols.right_0.clone(),
                cols.right_1.clone(),
                cols.right_2.clone(),
                cols.right_3.clone(),
                cols.right_4.clone(),
                cols.right_5.clone(),
                cols.right_6.clone(),
                cols.right_7.clone(),
                cols.parent_0.clone(),
                cols.parent_1.clone(),
                cols.parent_2.clone(),
                cols.parent_3.clone(),
                cols.parent_4.clone(),
                cols.parent_5.clone(),
                cols.parent_6.clone(),
                cols.parent_7.clone(),
                cols.output_8.clone(),
                cols.output_9.clone(),
                cols.output_10.clone(),
                cols.output_11.clone(),
                cols.output_12.clone(),
                cols.output_13.clone(),
                cols.output_14.clone(),
                cols.output_15.clone(),
            ],
        ));
        // Consume this row's own node claim (emitted by the parent row, or
        // by the public root terms for the top of a path).
        eval.add_to_relation(RelationEntry::new(
            &self.recursion_relations.merkle_node,
            -E::EF::from(cols.enabler.clone()),
            &[
                cols.tree_id.clone(),
                cols.depth.clone(),
                cols.index.clone(),
                cols.parent_0.clone(),
                cols.parent_1.clone(),
                cols.parent_2.clone(),
                cols.parent_3.clone(),
                cols.parent_4.clone(),
                cols.parent_5.clone(),
                cols.parent_6.clone(),
                cols.parent_7.clone(),
            ],
        ));
        // Emit the on-path child claim (consumed by the next row down);
        // suppressed at the bottom of a path.
        let two = E::F::from(stwo::core::fields::m31::BaseField::from_u32_unchecked(2));
        let one = E::F::from(stwo::core::fields::m31::BaseField::from_u32_unchecked(1));
        eval.add_to_relation(RelationEntry::new(
            &self.recursion_relations.merkle_node,
            E::EF::from(cols.enabler.clone() * (one - cols.is_leaf.clone())),
            &[
                cols.tree_id.clone(),
                cols.depth.clone()
                    + E::F::from(stwo::core::fields::m31::BaseField::from_u32_unchecked(1)),
                cols.index.clone() * two + cols.direction.clone(),
                cols.child_0.clone(),
                cols.child_1.clone(),
                cols.child_2.clone(),
                cols.child_3.clone(),
                cols.child_4.clone(),
                cols.child_5.clone(),
                cols.child_6.clone(),
                cols.child_7.clone(),
            ],
        ));
        eval.finalize_logup_in_pairs();
        eval
    }
}

/// One step of a decommitment path, top (root) to bottom (leaf side).
#[derive(Clone, Copy, Debug)]
pub struct PathStep {
    /// 0 if the on-path child is the left input, 1 if the right.
    pub direction: u32,
    /// The sibling digest (the off-path input to the hash).
    pub sibling: [u32; 8],
}

/// Record one hash step of a path at `(tree_id, depth, index)` whose node
/// value is `parent`: pushes the binding row here and the wide permutation
/// row into the poseidon2 witness table, returning the on-path child digest
/// the caller continues with.
#[allow(clippy::too_many_arguments)]
pub fn push_path_step(
    table: &mut MerklePathTable,
    poseidon2: &mut Poseidon2Table,
    tree_id: u32,
    depth: u32,
    index: u32,
    child: [u32; 8],
    step: PathStep,
    is_leaf: bool,
) -> [u32; 8] {
    let (left, right) = if step.direction == 0 {
        (child, step.sibling)
    } else {
        (step.sibling, child)
    };
    let mut state = [0u32; T];
    state[..8].copy_from_slice(&left);
    state[8..].copy_from_slice(&right);
    let out = poseidon2_traced_state(poseidon2, state, false, true);
    let parent: [u32; 8] = out[..8].try_into().expect("8 words");
    table.push(
        tree_id,
        depth,
        index,
        step.direction,
        is_leaf as u32,
        left[0],
        left[1],
        left[2],
        left[3],
        left[4],
        left[5],
        left[6],
        left[7],
        right[0],
        right[1],
        right[2],
        right[3],
        right[4],
        right[5],
        right[6],
        right[7],
        parent[0],
        parent[1],
        parent[2],
        parent[3],
        parent[4],
        parent[5],
        parent[6],
        parent[7],
        out[8],
        out[9],
        out[10],
        out[11],
        out[12],
        out[13],
        out[14],
        out[15],
        child[0],
        child[1],
        child[2],
        child[3],
        child[4],
        child[5],
        child[6],
        child[7],
    );
    parent
}

/// Generate the interaction trace and the claimed sum of the atomic hash
/// call plus the two path-chain entries.
pub fn gen_interaction_trace(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    relations: &Relations,
    recursion_relations: &RecursionRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    let cols = MerklePathColumns::from_iter(trace.iter().map(|eval| &eval.values.data));
    let simd_size = cols.enabler.len();
    let log_size = trace[0].domain.log_size();
    let mut logup_gen = LogupTraceGenerator::new(log_size);

    let neg_enabler: Vec<PackedQM31> = (0..simd_size)
        .map(|i| -PackedQM31::from(cols.enabler[i]))
        .collect();

    let hash_io_denom = combine!(
        relations.poseidon2_io,
        [
            cols.left_0,
            cols.left_1,
            cols.left_2,
            cols.left_3,
            cols.left_4,
            cols.left_5,
            cols.left_6,
            cols.left_7,
            cols.right_0,
            cols.right_1,
            cols.right_2,
            cols.right_3,
            cols.right_4,
            cols.right_5,
            cols.right_6,
            cols.right_7,
            cols.parent_0,
            cols.parent_1,
            cols.parent_2,
            cols.parent_3,
            cols.parent_4,
            cols.parent_5,
            cols.parent_6,
            cols.parent_7,
            cols.output_8,
            cols.output_9,
            cols.output_10,
            cols.output_11,
            cols.output_12,
            cols.output_13,
            cols.output_14,
            cols.output_15
        ]
    );

    // Per-row node-claim tuples: own claim consumed, child claim emitted.
    let one = stwo::prover::backend::simd::m31::PackedM31::broadcast(BaseField::from(1));
    let two = stwo::prover::backend::simd::m31::PackedM31::broadcast(BaseField::from(2));
    let depth_plus_1: Vec<_> = (0..simd_size).map(|i| cols.depth[i] + one).collect();
    let child_index: Vec<_> = (0..simd_size)
        .map(|i| cols.index[i] * two + cols.direction[i])
        .collect();
    let child_enabler: Vec<PackedQM31> = (0..simd_size)
        .map(|i| PackedQM31::from(cols.enabler[i] * (one - cols.is_leaf[i])))
        .collect();

    let own_denom = combine!(
        recursion_relations.merkle_node,
        [
            cols.tree_id,
            cols.depth,
            cols.index,
            cols.parent_0,
            cols.parent_1,
            cols.parent_2,
            cols.parent_3,
            cols.parent_4,
            cols.parent_5,
            cols.parent_6,
            cols.parent_7
        ]
    );
    let child_denom = combine!(
        recursion_relations.merkle_node,
        [
            cols.tree_id,
            &depth_plus_1,
            &child_index,
            cols.child_0,
            cols.child_1,
            cols.child_2,
            cols.child_3,
            cols.child_4,
            cols.child_5,
            cols.child_6,
            cols.child_7
        ]
    );

    write_pair!(
        &neg_enabler,
        &hash_io_denom,
        &neg_enabler,
        &own_denom,
        logup_gen
    );
    let mut child_col = logup_gen.new_col();
    for (vec_row, (&numerator, &denominator)) in
        child_enabler.iter().zip(child_denom.iter()).enumerate()
    {
        child_col.write_frac(vec_row, numerator, denominator);
    }
    child_col.finalize_col();
    logup_gen.finalize_last()
}
