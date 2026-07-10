//! Recursive verifier AIR components (docs/recursion.md, M3+).
//!
//! Building blocks for the native stwo AIR that verifies stark-v proofs.
//! Tables, derived columns, and constraints are declared once through
//! `define_component_tables!` — the same DSL as the opcode tables — keeping a
//! single source of definition for the whole recursion stack.
#![allow(clippy::too_many_arguments)] // generated table push takes one arg per column

pub mod aggregate;
pub mod aggregate_tree;
pub mod binding;
pub mod boundary;
pub mod channel_replay;
pub mod circle_double;
pub mod circuit;
pub mod final_proof;
pub mod fri_fold;
pub mod linear_ops;
pub mod logup_sum;
pub mod merkle_path;
pub mod node;
pub mod openings;
pub mod prover;
pub mod qm31_inv;
pub mod qm31_mul;
pub mod recorder;
pub mod relations;
pub mod transcript;
pub mod v2;

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

    // FRI line fold: folded = (f(x) + f(-x)) + alpha * (f(x) - f(-x)) * x^-1,
    // i.e. stwo's `ibutterfly` followed by the alpha combination. The odd
    // part t = (f(x) - f(-x)) * x^-1 is a witness column so every constraint
    // stays degree 2; x^-1 is bound to x by x * x_inv = enabler. f, alpha,
    // t, and folded are QM31 values as 4 M31 limbs; x is a base-field domain
    // coordinate.
    fri_fold_line: {
        committed: {
            x, x_inv,
            f_x_0, f_x_1, f_x_2, f_x_3,
            f_neg_x_0, f_neg_x_1, f_neg_x_2, f_neg_x_3,
            t_0, t_1, t_2, t_3,
            alpha_0, alpha_1, alpha_2, alpha_3,
            folded_0, folded_1, folded_2, folded_3,
        },
        constraints: {
            // x_inv is the inverse of x on enabled rows
            x * x_inv - enabler,
            // t = (f(x) - f(-x)) * x_inv, limb-wise (x_inv is a base scalar)
            (f_x_0 - f_neg_x_0) * x_inv - t_0,
            (f_x_1 - f_neg_x_1) * x_inv - t_1,
            (f_x_2 - f_neg_x_2) * x_inv - t_2,
            (f_x_3 - f_neg_x_3) * x_inv - t_3,
            // folded = (f(x) + f(-x)) + alpha * t, with alpha * t expanded
            // over the extension tower exactly as in qm31_mul
            f_x_0 + f_neg_x_0
                + alpha_0 * t_0 - alpha_1 * t_1
                + 2 * (alpha_2 * t_2 - alpha_3 * t_3) - (alpha_2 * t_3 + alpha_3 * t_2)
                - folded_0,
            f_x_1 + f_neg_x_1
                + alpha_0 * t_1 + alpha_1 * t_0
                + (alpha_2 * t_2 - alpha_3 * t_3) + 2 * (alpha_2 * t_3 + alpha_3 * t_2)
                - folded_1,
            f_x_2 + f_neg_x_2
                + alpha_0 * t_2 - alpha_1 * t_3 + alpha_2 * t_0 - alpha_3 * t_1
                - folded_2,
            f_x_3 + f_neg_x_3
                + alpha_0 * t_3 + alpha_1 * t_2 + alpha_2 * t_1 + alpha_3 * t_0
                - folded_3,
        },
    },

    // Circle point doubling over QM31: r = 2p on the unit circle
    // x^2 + y^2 = 1, i.e. r_x = 2 p_x^2 - 1 and r_y = 2 p_x p_y. The squares
    // and products expand over the extension tower exactly as in qm31_mul;
    // the `- 1` lands on limb 0 as `- enabler` so padding rows hold.
    circle_double: {
        committed: {
            p_x_0, p_x_1, p_x_2, p_x_3,
            p_y_0, p_y_1, p_y_2, p_y_3,
            r_x_0, r_x_1, r_x_2, r_x_3,
            r_y_0, r_y_1, r_y_2, r_y_3,
        },
        constraints: {
            // r_x = 2 * p_x^2 - 1
            2 * (p_x_0 * p_x_0 - p_x_1 * p_x_1
                    + 2 * (p_x_2 * p_x_2 - p_x_3 * p_x_3) - 2 * (p_x_2 * p_x_3))
                - enabler - r_x_0,
            2 * (2 * (p_x_0 * p_x_1)
                    + (p_x_2 * p_x_2 - p_x_3 * p_x_3) + 4 * (p_x_2 * p_x_3))
                - r_x_1,
            2 * (2 * (p_x_0 * p_x_2) - 2 * (p_x_1 * p_x_3)) - r_x_2,
            2 * (2 * (p_x_0 * p_x_3) + 2 * (p_x_1 * p_x_2)) - r_x_3,
            // r_y = 2 * p_x * p_y
            2 * (p_x_0 * p_y_0 - p_x_1 * p_y_1
                    + 2 * (p_x_2 * p_y_2 - p_x_3 * p_y_3) - (p_x_2 * p_y_3 + p_x_3 * p_y_2))
                - r_y_0,
            2 * (p_x_0 * p_y_1 + p_x_1 * p_y_0
                    + (p_x_2 * p_y_2 - p_x_3 * p_y_3) + 2 * (p_x_2 * p_y_3 + p_x_3 * p_y_2))
                - r_y_1,
            2 * (p_x_0 * p_y_2 - p_x_1 * p_y_3 + p_x_2 * p_y_0 - p_x_3 * p_y_1) - r_y_2,
            2 * (p_x_0 * p_y_3 + p_x_1 * p_y_2 + p_x_2 * p_y_1 + p_x_3 * p_y_0) - r_y_3,
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

    // One sponge absorption step of a Fiat-Shamir channel replay: the
    // permutation input is prev_state with the absorbed chunk added into the
    // rate, and the (input, output) pair is bound atomically through the
    // poseidon2_io relation; states chain through sponge_step and the
    // absorbed data is anchored through sponge_data public claims. No hash
    // constraint lives here.
    channel_replay: {
        committed: {
            channel_id, step,
            prev_0, prev_1, prev_2, prev_3, prev_4, prev_5, prev_6, prev_7,
            prev_8, prev_9, prev_10, prev_11, prev_12, prev_13, prev_14, prev_15,
            chunk_0, chunk_1, chunk_2, chunk_3, chunk_4, chunk_5, chunk_6, chunk_7,
            out_0, out_1, out_2, out_3, out_4, out_5, out_6, out_7,
            out_8, out_9, out_10, out_11, out_12, out_13, out_14, out_15,
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

    // LogUp sum of inverses: each row contributes enabler / term to the
    // component's claimed sum, the in-AIR form of the verifier's LogUp-sum
    // check. The fraction lives in the interaction trace; this table only
    // carries the term limbs (fraction emission is not a polynomial
    // constraint, see logup_sum.rs).
    logup_sum: {
        committed: {
            term_0, term_1, term_2, term_3,
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
