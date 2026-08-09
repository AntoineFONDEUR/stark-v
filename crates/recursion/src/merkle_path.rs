//! Macro-defined Merkle hash-step component and witness helpers.
//!
//! Each enabled row consumes one complete Poseidon2 call and one claim for
//! its parent node. Non-leaf rows emit the selected child claim consumed by
//! the next path row, keeping the tree identifier, depth, and index bound to
//! the digest throughout the path.

use air::poseidon2::{T, poseidon2_traced_state};
use air::trace::Poseidon2Table;
use prover::relations::Relations;
use stwo::core::fields::qm31::QM31;

use crate::relations::{RecursionRelations, SharedPrimitiveRelations};

stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [],
    embedded_component: true,
    embedded_relations: crate::relations::SharedPrimitiveRelations,
    logup_batch: 2,
    embedded_dynamic_component: true,

    relation poseidon2_io(32);
    relation merkle_node(11);

    fn merkle_path(
        tree_id, depth, index, direction, is_leaf,
        left_0, left_1, left_2, left_3, left_4, left_5, left_6, left_7,
        right_0, right_1, right_2, right_3, right_4, right_5, right_6, right_7,
        parent_0, parent_1, parent_2, parent_3, parent_4, parent_5, parent_6, parent_7,
        output_8, output_9, output_10, output_11,
        output_12, output_13, output_14, output_15,
        child_0, child_1, child_2, child_3, child_4, child_5, child_6, child_7,
    ) {
        constrain direction * (1 - direction);
        constrain is_leaf * (1 - is_leaf);
        constrain left_0 + direction * (right_0 - left_0) - child_0;
        constrain left_1 + direction * (right_1 - left_1) - child_1;
        constrain left_2 + direction * (right_2 - left_2) - child_2;
        constrain left_3 + direction * (right_3 - left_3) - child_3;
        constrain left_4 + direction * (right_4 - left_4) - child_4;
        constrain left_5 + direction * (right_5 - left_5) - child_5;
        constrain left_6 + direction * (right_6 - left_6) - child_6;
        constrain left_7 + direction * (right_7 - left_7) - child_7;

        consume poseidon2_io(
            left_0, left_1, left_2, left_3, left_4, left_5, left_6, left_7,
            right_0, right_1, right_2, right_3, right_4, right_5, right_6, right_7,
            parent_0, parent_1, parent_2, parent_3,
            parent_4, parent_5, parent_6, parent_7,
            output_8, output_9, output_10, output_11,
            output_12, output_13, output_14, output_15,
        );
        consume merkle_node(
            tree_id,
            depth,
            index,
            parent_0, parent_1, parent_2, parent_3,
            parent_4, parent_5, parent_6, parent_7,
        );
        emit(enabler * (1 - is_leaf)) merkle_node(
            tree_id,
            depth + 1,
            index * 2 + direction,
            child_0, child_1, child_2, child_3,
            child_4, child_5, child_6, child_7,
        );

        return (
            parent_0, parent_1, parent_2, parent_3,
            parent_4, parent_5, parent_6, parent_7,
        );
    }
}

pub use component::air::{Component, Eval};

/// One step of a decommitment path, top (root) to bottom (leaf side).
#[derive(Clone, Copy, Debug)]
pub struct PathStep {
    /// 0 if the on-path child is the left input, 1 if the right.
    pub direction: u32,
    /// The sibling digest (the off-path input to the hash).
    pub sibling: [u32; 8],
}

/// Record one hash step and its matching wide Poseidon2 permutation row.
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
    let parent: [u32; 8] = out[..8]
        .try_into()
        .expect("Poseidon2 digest has eight words");
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

/// Generate the interaction trace from the macro-defined relation entries.
pub fn gen_interaction_trace(
    trace: &[stwo::prover::poly::circle::CircleEvaluation<
        stwo::prover::backend::simd::SimdBackend,
        stwo::core::fields::m31::BaseField,
        stwo::prover::poly::BitReversedOrder,
    >],
    relations: &Relations,
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
        &SharedPrimitiveRelations::for_merkle(relations, recursion_relations),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use stwo::core::pcs::TreeVec;
    use stwo::core::poly::circle::CanonicCoset;
    use stwo_constraint_framework::{FrameworkEval, assert_constraints_on_polys};

    fn assert_table_satisfies_constraints(table: MerklePathTable) {
        let vm_relations = Relations::dummy();
        let recursion_relations = RecursionRelations::dummy();
        let trace = table.into_witness();
        let log_size = trace
            .first()
            .map(|column| column.domain.log_size())
            .expect("Merkle path trace has committed columns");
        let (interaction, claimed_sum) =
            gen_interaction_trace(&trace, &vm_relations, &recursion_relations);
        let traces = TreeVec::new(vec![vec![], trace, interaction]);
        let trace_polys = traces.map_cols(|column| column.interpolate());
        let eval = Eval {
            log_size,
            relations: SharedPrimitiveRelations::for_merkle(&vm_relations, &recursion_relations),
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
    fn test_merkle_path_constraints_reject_child_from_wrong_branch() {
        let mut table = MerklePathTable::new();
        // Direction zero selects the left digest, so a different child is invalid.
        table.push(
            1, 0, 0, 0, 1, // Path coordinates and flags.
            1, 0, 0, 0, 0, 0, 0, 0, // Left digest.
            0, 0, 0, 0, 0, 0, 0, 0, // Right digest.
            0, 0, 0, 0, 0, 0, 0, 0, // Parent digest.
            0, 0, 0, 0, 0, 0, 0, 0, // Unused Poseidon2 output half.
            2, 0, 0, 0, 0, 0, 0, 0, // Claimed child digest.
        );
        assert_table_satisfies_constraints(table);
    }
}
