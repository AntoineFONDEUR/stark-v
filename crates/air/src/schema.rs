//! Unified zkVM AIR schema: relations, preprocessed lookups, and trace tables.

stwo_macros::define_air! {
    relations: {
        registers_state: pc, clock;
        memory_access: addr_space, addr, clock, limb_0, limb_1, limb_2, limb_3;
        program_access: addr, value_0, value_1, value_2, value_3;
        merkle: index, depth, value, root;
        poseidon2: state0, state1, state2, state3, state4, state5, state6, state7,
            state8, state9, state10, state11, state12, state13, state14, state15;
        poseidon2_io: in0, in1, in2, in3, in4, in5, in6, in7,
            in8, in9, in10, in11, in12, in13, in14, in15,
            out0, out1, out2, out3, out4, out5, out6, out7,
            out8, out9, out10, out11, out12, out13, out14, out15;
    }
    preprocessed: {
        bitwise: a, b, result, op_id;
        range_check_20: value;
        range_check_8_11: limb_0, limb_1;
        range_check_8_8_4: limb_0, limb_1, limb_2;
        range_check_8_8: limb_0, limb_1;
        range_check_m31: lsl, msl;
    }
    clock_gap: {
        bound_by: range_check_20,
        relation: memory_access,
    }
    // Fn-DSL tables folded into the `Tracer` (defined via `define_air_fns!`).
    // The runner fills them like any opcode table; their components plug into
    // the prover via `components! { ... name: module ... }`.
    external: {
        poseidon2: crate::poseidon2,
        lui: crate::opcodes::lui,
        auipc: crate::opcodes::auipc,
        jal: crate::opcodes::jal,
        jalr: crate::opcodes::jalr,
        base_alu_imm: crate::opcodes::base_alu_imm,
        base_alu_reg: crate::opcodes::base_alu_reg,
        branch_eq: crate::opcodes::branch_eq,
        mul: crate::opcodes::mul,
        mulh: crate::opcodes::mulh,
        lt_reg: crate::opcodes::lt_reg,
        lt_imm: crate::opcodes::lt_imm,
        shifts_reg: crate::opcodes::shifts_reg,
        shifts_imm: crate::opcodes::shifts_imm,
        branch_lt: crate::opcodes::branch_lt,
        div: crate::opcodes::div,
        load_store: crate::opcodes::load_store,
    }
    trace: {
        // base_alu_reg migrated to crate::opcodes::base_alu_reg (external:).

        // ==========================================================================
        // 2. Base ALU Imm (addi/xori/ori/andi) - airs.md Section 2
        // ==========================================================================
        // base_alu_imm migrated to crate::opcodes::base_alu_imm (external:).

        // ==========================================================================
        // 3. Shifts Reg (sll/srl/sra) - airs.md Section 3
        // ==========================================================================
        // shifts_reg migrated to crate::opcodes::shifts_reg (external:).

        // ==========================================================================
        // 4. Shifts Imm (slli/srli/srai) - airs.md Section 4
        // ==========================================================================
        // shifts_imm migrated to crate::opcodes::shifts_imm (external:).

        // ==========================================================================
        // 5. Less Than Reg (slt/sltu) - airs.md Section 5
        // ==========================================================================
        // lt_reg migrated to crate::opcodes::lt_reg (external:).

        // ==========================================================================
        // 6. Less Than Imm (slti/sltiu) - airs.md Section 6
        // ==========================================================================
        // lt_imm migrated to crate::opcodes::lt_imm (external:).

        // ==========================================================================
        // 7. Branch Equal (beq/bne) - airs.md Section 7
        // ==========================================================================
        // branch_eq migrated to crate::opcodes::branch_eq (external:).

        // ==========================================================================
        // 8. Branch Less Than (blt/bltu/bge/bgeu) - airs.md Section 8
        // ==========================================================================
        // branch_lt migrated to crate::opcodes::branch_lt (external:).

        // LUI (airs.md Section 9) is migrated to a felt function:
        // `crate::opcodes::lui`, folded in via the `external:` section.

        // ==========================================================================
        // 10. AUIPC - airs.md Section 10
        // ==========================================================================
        // AUIPC migrated to crate::opcodes::auipc (external:).

        // ==========================================================================
        // 11. JALR - airs.md Section 11
        // ==========================================================================
        // JALR migrated to crate::opcodes::jalr (external:).

        // ==========================================================================
        // 12. JAL - airs.md Section 12
        // ==========================================================================
        // JAL migrated to crate::opcodes::jal (external:).

        // ==========================================================================
        // 13. Load/Store (lb/lbu/lh/lhu/lw/sb/sh/sw) - airs.md Section 13
        // ==========================================================================
        // load_store migrated to crate::opcodes::load_store (external:).

        // ==========================================================================
        // 14. MUL - airs.md Section 14
        // ==========================================================================
        // mul migrated to crate::opcodes::mul (external:).

        // ==========================================================================
        // 15. MULH (mulh/mulhsu/mulhu) - airs.md Section 15
        // ==========================================================================
        // mulh migrated to crate::opcodes::mulh (external:).

        // ==========================================================================
        // 16. DIV (div/divu/rem/remu) - airs.md Section 16
        // ==========================================================================
        // div migrated to crate::opcodes::div (external:).

        // ==========================================================================
        // 17. Program commitment table
        // ==========================================================================
        program: {
            committed: {
                addr, value_0, value_1, value_2, value_3, multiplicity, root,
            },
            lookups: {
                // Emit each fetched instruction `multiplicity` times (consumed by
                // the opcode components' program accesses).
                multiplicity * program_access(addr, value_0, value_1, value_2, value_3),
                // The four instruction limbs are leaves of the program
                // commitment tree at consecutive indices.
                -enabler * merkle(addr, constant(crate::MAX_TREE_HEIGHT - 1), value_0, root),
                -enabler * merkle(addr + 1, constant(crate::MAX_TREE_HEIGHT - 1), value_1, root),
                -enabler * merkle(addr + 2, constant(crate::MAX_TREE_HEIGHT - 1), value_2, root),
                -enabler * merkle(addr + 3, constant(crate::MAX_TREE_HEIGHT - 1), value_3, root),
            },
        },

        // ==========================================================================
        // 18. Memory commitment table (initial/final)
        // ==========================================================================
        memory: {
            committed: {
                addr, clock,
                value_0, value_1, value_2, value_3,
                multiplicity, root,
            },
            constraints: {
                // multiplicity is -1 (final state emission), 0 (padding), or 1
                // (initial state consumption).
                multiplicity * (multiplicity * multiplicity - 1),
            },
            lookups: {
                // Committed memory words are bytes.
                - enabler * range_check_8_8(value_0, value_1),
                - enabler * range_check_8_8(value_2, value_3),
                // Anchor the boundary memory state (RW_AS = 1): +1 emits the
                // initial value, -1 consumes the final one.
                multiplicity * memory_access(1, addr, clock, value_0, value_1, value_2, value_3),
                // The four word limbs are leaves of the memory commitment tree.
                -enabler * merkle(addr, constant(crate::MAX_TREE_HEIGHT - 1), value_0, root),
                -enabler * merkle(addr + 1, constant(crate::MAX_TREE_HEIGHT - 1), value_1, root),
                -enabler * merkle(addr + 2, constant(crate::MAX_TREE_HEIGHT - 1), value_2, root),
                -enabler * merkle(addr + 3, constant(crate::MAX_TREE_HEIGHT - 1), value_3, root),
            },
        },

        // ==========================================================================
        // 19. Merkle tree nodes
        // ==========================================================================
        merkle: {
            committed: {
                index, depth,
                lhs, rhs, cur,
                lhs_mult, rhs_mult, cur_mult,
                root,
            },
            constraints: {
                // Node multiplicities are 0, 1, or 2 (a node can be shared by
                // two children paths).
                lhs_mult * (lhs_mult - 1) * (lhs_mult - 2),
                rhs_mult * (rhs_mult - 1) * (rhs_mult - 2),
                cur_mult * (cur_mult - 1) * (cur_mult - 2),
            },
            lookups: {
                // Emit the two children claims, consume the parent claim
                // (index halves, depth decreases toward the root).
                lhs_mult * merkle(index, depth, lhs, root),
                rhs_mult * merkle(index + 1, depth, rhs, root),
                -cur_mult * merkle(index * inv(2), depth - 1, cur, root),
                // The parent is the Poseidon2 hash of the two children.
                enabler * poseidon2(lhs, rhs),
                -enabler * poseidon2(cur),
            },
        },

    }
}
