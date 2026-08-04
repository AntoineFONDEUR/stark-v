//! AIR components and protocol types for binary recursive proving.
//!
//! The crate defines one verifier circuit that accepts either a stark-v
//! segment proof or two proofs produced by this same circuit. It does not yet
//! expose a complete recursive prover or root-verifier API; `docs/recursion.md`
//! tracks the remaining integration work.
//!
//! The live roster still contains hand-written `FrameworkEval` components
//! backed by `define_component_tables!`. They are migration debt, not the
//! accepted recursion architecture: every roster component must move to
//! `define_air!` or `define_air_fns!` before integration continues.
#![allow(clippy::too_many_arguments)] // generated table push takes one arg per column

pub mod air_expression_circuit;
pub mod air_relation_parameters;
pub mod circuit;
pub mod control_air;
mod dynamic_logup;
pub mod fri_merkle_air;
pub mod fri_verifier_circuit;
pub mod fri_verifier_control_air;
pub mod fri_verifier_input_air;
pub mod fri_verifier_lowering;
pub mod kernel;
pub mod linear_ops;
pub mod merkle_path;
pub mod merkle_root_air;
pub mod oods_circuit;
pub mod pcs_deep_circuit;
pub mod pcs_deep_input_air;
pub mod pcs_deep_lowering;
pub mod pow;
pub mod protocol;
pub mod qm31_inv;
pub mod qm31_mul;
pub mod query_position_air;
pub mod recorder;
pub mod recursion_air_program;
pub mod relation_challenge_air;
pub mod relations;
pub mod statement;
pub mod statement_input_air;
pub mod statement_semantics_circuit;
pub mod statement_semantics_input_air;
pub mod statement_semantics_lowering;
pub mod trace_merkle_air;
pub mod transcript;
pub mod transcript_air;
pub mod transcript_binding_air;
pub mod transcript_layout;
pub mod transcript_payload_air;
pub mod transcript_program;
pub mod transcript_state_air;
pub mod transcript_word_air;
pub mod universal_relations;
pub mod verifier_randomness_air;
pub mod vm_air_composition_circuit;
pub mod vm_air_composition_control_air;
pub mod vm_air_composition_input_air;
pub mod vm_air_composition_lowering;
pub mod vm_air_program;
pub mod vm_pcs_layout;
pub mod vm_public_claim;
pub mod vm_public_claim_hash_air;
pub mod vm_public_claim_input_air;
pub mod vm_public_claim_semantics_circuit;
pub mod vm_public_claim_semantics_input_air;
pub mod vm_public_claim_semantics_lowering;
pub mod vm_public_io_hash_air;
pub mod vm_public_logup_circuit;
pub mod vm_public_logup_control_air;
pub mod vm_public_logup_input_air;
pub mod vm_public_logup_lowering;
pub mod wire;

#[cfg(test)]
mod fri_verifier_binding_tests;
#[cfg(test)]
pub(crate) mod test_fixtures;
#[cfg(test)]
mod vm_leaf_binding_tests;

// combine!/write_pair! are used by witness modules.
#[macro_use]
extern crate stwo_macros;

use stwo_macros::define_component_tables;

define_component_tables! {
    // QM31 multiplication: c = a * b over the degree-4 extension of M31.
    //
    // QM31 = CM31[u] / (u^2 - (2 + i)) with CM31 = M31[i] / (i^2 + 1).
    // Writing a = (a_0 + a_1 i) + (a_2 + a_3 i) u (likewise b, c) and
    // expanding (A + B u)(C + D u) = (AC + (2 + i) BD) + (AD + BC) u gives
    // the four limb constraints below. Every constraint is degree 2 and
    // vanishes on all-zero padding rows.
    qm31_mul: {
        committed: {
            a_0, a_1, a_2, a_3,
            b_0, b_1, b_2, b_3,
            c_0, c_1, c_2, c_3,
            // Circuit wiring (composition-check lowering): when in_circuit is
            // set, this row implements node `node_id` of circuit `circuit_id`,
            // consuming its operands and emitting its value `uses` times
            // through the wire relation.
            circuit_id, node_id, lhs_id, rhs_id, uses, in_circuit,
        },
        constraints: {
            in_circuit * (1 - in_circuit),
            // Wiring rows are real rows.
            in_circuit * (1 - enabler),
            // Re(first): Re(AC) + Re((2 + i) BD)
            a_0 * b_0 - a_1 * b_1
                + 2 * (a_2 * b_2 - a_3 * b_3) - (a_2 * b_3 + a_3 * b_2)
                - c_0,
            // Im(first): Im(AC) + Im((2 + i) BD)
            a_0 * b_1 + a_1 * b_0
                + (a_2 * b_2 - a_3 * b_3) + 2 * (a_2 * b_3 + a_3 * b_2)
                - c_1,
            // Re(second): Re(AD) + Re(BC)
            a_0 * b_2 - a_1 * b_3 + a_2 * b_0 - a_3 * b_1 - c_2,
            // Im(second): Im(AD) + Im(BC)
            a_0 * b_3 + a_1 * b_2 + a_2 * b_1 + a_3 * b_0 - c_3,
        },
    },

    // One Merkle hash step over 8-word digests: parent = permute(left || right)[..8].
    // The permutation itself is proven by the reused stark-v poseidon2
    // component; this table binds the complete 16-word input and 16-word
    // output in one atomic relation tuple. The unused output half remains in
    // the witness because omitting it would split a permutation call into
    // input and output claims that can be permuted independently.
    // Path chaining: each row consumes its own node claim
    // (tree_id, depth, index, parent) and emits the on-path child claim
    // (tree_id, depth + 1, 2*index + direction, child) through the
    // merkle_node relation; `is_leaf` suppresses the child emission at the
    // bottom of a path, and roots are anchored by public claim terms.
    merkle_path: {
        committed: {
            tree_id, depth, index, direction, is_leaf,
            left_0, left_1, left_2, left_3, left_4, left_5, left_6, left_7,
            right_0, right_1, right_2, right_3, right_4, right_5, right_6, right_7,
            parent_0, parent_1, parent_2, parent_3, parent_4, parent_5, parent_6, parent_7,
            output_8, output_9, output_10, output_11,
            output_12, output_13, output_14, output_15,
            child_0, child_1, child_2, child_3, child_4, child_5, child_6, child_7,
        },
        constraints: {
            direction * (1 - direction),
            is_leaf * (1 - is_leaf),
            // child = direction ? right : left, limb-wise
            left_0 + direction * (right_0 - left_0) - child_0,
            left_1 + direction * (right_1 - left_1) - child_1,
            left_2 + direction * (right_2 - left_2) - child_2,
            left_3 + direction * (right_3 - left_3) - child_3,
            left_4 + direction * (right_4 - left_4) - child_4,
            left_5 + direction * (right_5 - left_5) - child_5,
            left_6 + direction * (right_6 - left_6) - child_6,
            left_7 + direction * (right_7 - left_7) - child_7,
        },
    },

    // Linear circuit nodes (composition-check lowering): add, sub, neg over
    // QM31 values, one node per row, wired through op_def and wire claims.
    // Mul/inverse nodes live in qm31_mul/qm31_inv; inputs, constants, and
    // the output are public claim terms.
    linear_ops: {
        committed: {
            circuit_id, node_id, is_add, is_sub, is_neg,
            lhs_id, rhs_id,
            lhs_0, lhs_1, lhs_2, lhs_3,
            rhs_0, rhs_1, rhs_2, rhs_3,
            out_0, out_1, out_2, out_3,
            uses,
        },
        constraints: {
            is_add * (1 - is_add),
            is_sub * (1 - is_sub),
            is_neg * (1 - is_neg),
            // Exactly one kind per enabled row.
            is_add + is_sub + is_neg - enabler,
            // out = lhs + rhs / lhs - rhs / -lhs, limb-wise per kind.
            is_add * (lhs_0 + rhs_0) + is_sub * (lhs_0 - rhs_0) - is_neg * lhs_0 - out_0,
            is_add * (lhs_1 + rhs_1) + is_sub * (lhs_1 - rhs_1) - is_neg * lhs_1 - out_1,
            is_add * (lhs_2 + rhs_2) + is_sub * (lhs_2 - rhs_2) - is_neg * lhs_2 - out_2,
            is_add * (lhs_3 + rhs_3) + is_sub * (lhs_3 - rhs_3) - is_neg * lhs_3 - out_3,
        },
    },

    // QM31 inverse: inv = a^-1, asserted as a * inv = 1 with the same limb
    // expansion as qm31_mul. The right-hand side is `enabler` for limb 0 so
    // all-zero padding rows satisfy the constraints, and enabled rows force
    // `a` to be invertible.
    qm31_inv: {
        committed: {
            a_0, a_1, a_2, a_3,
            inv_0, inv_1, inv_2, inv_3,
            // Circuit wiring, as in qm31_mul (rhs unused for the unary inverse).
            circuit_id, node_id, lhs_id, uses, in_circuit,
        },
        constraints: {
            in_circuit * (1 - in_circuit),
            in_circuit * (1 - enabler),
            a_0 * inv_0 - a_1 * inv_1
                + 2 * (a_2 * inv_2 - a_3 * inv_3) - (a_2 * inv_3 + a_3 * inv_2)
                - enabler,
            a_0 * inv_1 + a_1 * inv_0
                + (a_2 * inv_2 - a_3 * inv_3) + 2 * (a_2 * inv_3 + a_3 * inv_2),
            a_0 * inv_2 - a_1 * inv_3 + a_2 * inv_0 - a_3 * inv_1,
            a_0 * inv_3 + a_1 * inv_2 + a_2 * inv_1 + a_3 * inv_0,
        },
    },
}
