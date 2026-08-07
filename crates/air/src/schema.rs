//! Unified zkVM AIR schema: relations, preprocessed lookups, and trace tables.

stwo_macros::define_air! {
    relations: {
        registers_state: pc, clock;
        memory_access: addr_space, addr, clock, limb_0, limb_1, limb_2, limb_3;
        program_access: addr, value_0, value_1, value_2, value_3;
        merkle: index, depth,
            value_0, value_1, value_2, value_3, value_4, value_5, value_6, value_7,
            root_0, root_1, root_2, root_3, root_4, root_5, root_6, root_7;
        poseidon2: state0, state1, state2, state3, state4, state5, state6, state7,
            state8, state9, state10, state11, state12, state13, state14, state15;
        poseidon2_io: in0, in1, in2, in3, in4, in5, in6, in7,
            in8, in9, in10, in11, in12, in13, in14, in15,
            out0, out1, out2, out3, out4, out5, out6, out7,
            out8, out9, out10, out11, out12, out13, out14, out15;
        journal: step, clock, state0, state1, state2, state3, state4, state5, state6, state7;
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
    // The component router assigns each table to a constituent proof.
    external: {
        auipc: crate::opcodes::auipc,
        base_alu_imm: crate::opcodes::base_alu_imm,
        base_alu_reg: crate::opcodes::base_alu_reg,
        branch_eq: crate::opcodes::branch_eq,
        branch_lt: crate::opcodes::branch_lt,
        div: crate::opcodes::div,
        jal: crate::opcodes::jal,
        jalr: crate::opcodes::jalr,
        load_store: crate::opcodes::load_store,
        lt_imm: crate::opcodes::lt_imm,
        lt_reg: crate::opcodes::lt_reg,
        mul: crate::opcodes::mul,
        mulh: crate::opcodes::mulh,
        poseidon2: crate::poseidon2,
        shifts_imm: crate::opcodes::shifts_imm,
        shifts_reg: crate::opcodes::shifts_reg,
        lui: crate::opcodes::lui,
    }
    trace: {

        // ==========================================================================
        // COMMIT syscall
        // ==========================================================================
        commit: {
            committed: {
                clock, pc, selector, argument, journal_step, journal_prev_clock,
                journal_prev_0, journal_prev_1, journal_prev_2, journal_prev_3,
                journal_prev_4, journal_prev_5, journal_prev_6, journal_prev_7,
                journal_next_0, journal_next_1, journal_next_2, journal_next_3,
                journal_next_4, journal_next_5, journal_next_6, journal_next_7,
                journal_next_8, journal_next_9, journal_next_10, journal_next_11,
                journal_next_12, journal_next_13, journal_next_14, journal_next_15,
            },
            derived: {
                pc_next: pc + 4,
                clock_next: clock + 1,
                selector_clock_diff: clock - selector_clock_prev,
                argument_clock_diff: clock - argument_clock_prev,
                journal_step_next: journal_step + 1,
                journal_clock_diff_minus_one: clock - journal_prev_clock - 1,
            },
            constraints: {
                // The shared ECALL instruction is a COMMIT only when a7 selects it.
                enabler * (selector_addr - constant(17)),
                enabler * (selector_next_0 - constant(crate::instructions::COMMIT_SYSCALL_ID)),
                enabler * selector_next_1,
                enabler * selector_next_2,
                enabler * selector_next_3,
                // Selector and argument accesses are reads, not hidden writes.
                enabler * (selector_prev_0 - selector_next_0),
                enabler * (selector_prev_1 - selector_next_1),
                enabler * (selector_prev_2 - selector_next_2),
                enabler * (selector_prev_3 - selector_next_3),
                enabler * (argument_addr - constant(10)),
                enabler * (argument_prev_0 - argument_next_0),
                enabler * (argument_prev_1 - argument_next_1),
                enabler * (argument_prev_2 - argument_next_2),
                enabler * (argument_prev_3 - argument_next_3),
            },
            lookups: {
                -enabler * program_access(
                    pc, constant(crate::instructions::Opcode::Ecall as u32), 0, 0, 0,
                ),
                -enabler * registers_state(pc, clock),
                enabler * registers_state(pc_next, clock_next),
                // Read a7 (REG_AS = 0) to authenticate the syscall selector.
                -enabler * memory_access(
                    0, selector_addr, selector_clock_prev,
                    selector_prev_0, selector_prev_1, selector_prev_2, selector_prev_3,
                ),
                enabler * memory_access(
                    0, selector_addr, clock,
                    selector_next_0, selector_next_1, selector_next_2, selector_next_3,
                ),
                -enabler * range_check_20(selector_clock_diff),
                // Read a0 to bind the committed word to the register file.
                -enabler * memory_access(
                    0, argument_addr, argument_clock_prev,
                    argument_prev_0, argument_prev_1, argument_prev_2, argument_prev_3,
                ),
                enabler * memory_access(
                    0, argument_addr, clock,
                    argument_next_0, argument_next_1, argument_next_2, argument_next_3,
                ),
                -enabler * range_check_20(argument_clock_diff),
                // Journal ordinals follow execution order, so valid COMMIT
                // rows cannot choose an independent ordering.
                -enabler * range_check_20(journal_step),
                -enabler * range_check_20(journal_prev_clock),
                -enabler * range_check_20(clock),
                -enabler * range_check_20(journal_clock_diff_minus_one),
                // The committed word is absorbed as four bytes after the
                // previous digest under a journal-specific domain word.
                -enabler * poseidon2_io(
                    journal_prev_0, journal_prev_1, journal_prev_2, journal_prev_3,
                    journal_prev_4, journal_prev_5, journal_prev_6, journal_prev_7,
                    argument_next_0, argument_next_1, argument_next_2, argument_next_3,
                    constant(crate::instructions::COMMIT_HASH_DOMAIN), 0, 0, 0,
                    journal_next_0, journal_next_1, journal_next_2, journal_next_3,
                    journal_next_4, journal_next_5, journal_next_6, journal_next_7,
                    journal_next_8, journal_next_9, journal_next_10, journal_next_11,
                    journal_next_12, journal_next_13, journal_next_14, journal_next_15,
                ),
                -enabler * journal(
                    journal_step, journal_prev_clock,
                    journal_prev_0, journal_prev_1, journal_prev_2, journal_prev_3,
                    journal_prev_4, journal_prev_5, journal_prev_6, journal_prev_7,
                ),
                enabler * journal(
                    journal_step_next, clock,
                    journal_next_0, journal_next_1, journal_next_2, journal_next_3,
                    journal_next_4, journal_next_5, journal_next_6, journal_next_7,
                ),
            },
        },

        // ==========================================================================
        // Program commitment table
        // ==========================================================================
        program: {
            committed: {
                addr, value_0, value_1, value_2, value_3, multiplicity,
                root_0, root_1, root_2, root_3, root_4, root_5, root_6, root_7,
            },
            lookups: {
                // Emit each fetched instruction `multiplicity` times (consumed by
                // the opcode components' program accesses).
                multiplicity * program_access(addr, value_0, value_1, value_2, value_3),
                // The four instruction limbs are leaves of the program
                // commitment tree at consecutive indices.
                -enabler * merkle(
                    addr, constant(crate::MAX_TREE_HEIGHT - 1),
                    value_0, 0, 0, 0, 0, 0, 0, 0,
                    root_0, root_1, root_2, root_3, root_4, root_5, root_6, root_7,
                ),
                -enabler * merkle(
                    addr + 1, constant(crate::MAX_TREE_HEIGHT - 1),
                    value_1, 0, 0, 0, 0, 0, 0, 0,
                    root_0, root_1, root_2, root_3, root_4, root_5, root_6, root_7,
                ),
                -enabler * merkle(
                    addr + 2, constant(crate::MAX_TREE_HEIGHT - 1),
                    value_2, 0, 0, 0, 0, 0, 0, 0,
                    root_0, root_1, root_2, root_3, root_4, root_5, root_6, root_7,
                ),
                -enabler * merkle(
                    addr + 3, constant(crate::MAX_TREE_HEIGHT - 1),
                    value_3, 0, 0, 0, 0, 0, 0, 0,
                    root_0, root_1, root_2, root_3, root_4, root_5, root_6, root_7,
                ),
            },
        },

        // ==========================================================================
        // Memory commitment table (initial/final)
        // ==========================================================================
        memory: {
            committed: {
                addr, clock,
                value_0, value_1, value_2, value_3,
                multiplicity,
                root_0, root_1, root_2, root_3, root_4, root_5, root_6, root_7,
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
                -enabler * merkle(
                    addr, constant(crate::MAX_TREE_HEIGHT - 1),
                    value_0, 0, 0, 0, 0, 0, 0, 0,
                    root_0, root_1, root_2, root_3, root_4, root_5, root_6, root_7,
                ),
                -enabler * merkle(
                    addr + 1, constant(crate::MAX_TREE_HEIGHT - 1),
                    value_1, 0, 0, 0, 0, 0, 0, 0,
                    root_0, root_1, root_2, root_3, root_4, root_5, root_6, root_7,
                ),
                -enabler * merkle(
                    addr + 2, constant(crate::MAX_TREE_HEIGHT - 1),
                    value_2, 0, 0, 0, 0, 0, 0, 0,
                    root_0, root_1, root_2, root_3, root_4, root_5, root_6, root_7,
                ),
                -enabler * merkle(
                    addr + 3, constant(crate::MAX_TREE_HEIGHT - 1),
                    value_3, 0, 0, 0, 0, 0, 0, 0,
                    root_0, root_1, root_2, root_3, root_4, root_5, root_6, root_7,
                ),
            },
        },

        // ==========================================================================
        // Merkle tree nodes
        // ==========================================================================
        merkle: {
            committed: {
                index, depth,
                lhs_0, lhs_1, lhs_2, lhs_3, lhs_4, lhs_5, lhs_6, lhs_7,
                rhs_0, rhs_1, rhs_2, rhs_3, rhs_4, rhs_5, rhs_6, rhs_7,
                cur_0, cur_1, cur_2, cur_3, cur_4, cur_5, cur_6, cur_7,
                output_8, output_9, output_10, output_11,
                output_12, output_13, output_14, output_15,
                lhs_mult, rhs_mult, cur_mult,
                root_0, root_1, root_2, root_3, root_4, root_5, root_6, root_7,
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
                lhs_mult * merkle(
                    index, depth,
                    lhs_0, lhs_1, lhs_2, lhs_3, lhs_4, lhs_5, lhs_6, lhs_7,
                    root_0, root_1, root_2, root_3, root_4, root_5, root_6, root_7,
                ),
                rhs_mult * merkle(
                    index + 1, depth,
                    rhs_0, rhs_1, rhs_2, rhs_3, rhs_4, rhs_5, rhs_6, rhs_7,
                    root_0, root_1, root_2, root_3, root_4, root_5, root_6, root_7,
                ),
                -cur_mult * merkle(
                    index * inv(2), depth - 1,
                    cur_0, cur_1, cur_2, cur_3, cur_4, cur_5, cur_6, cur_7,
                    root_0, root_1, root_2, root_3, root_4, root_5, root_6, root_7,
                ),
                // Bind both children and the complete permutation output in
                // one relation entry so no output limb can be spliced from a
                // different Poseidon2 call.
                -enabler * poseidon2_io(
                    lhs_0, lhs_1, lhs_2, lhs_3, lhs_4, lhs_5, lhs_6, lhs_7,
                    rhs_0, rhs_1, rhs_2, rhs_3, rhs_4, rhs_5, rhs_6, rhs_7,
                    cur_0, cur_1, cur_2, cur_3, cur_4, cur_5, cur_6, cur_7,
                    output_8, output_9, output_10, output_11,
                    output_12, output_13, output_14, output_15,
                ),
            },
        },

    }
}
