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
        // 16. DIV (div/divu/rem/remu)
        // ==========================================================================
        div: {
            committed: {
                clock, pc, rd, rs1, rs2,
                zero_divisor, r_zero,
                q_0, q_1, q_2, q_3,
                r_0, r_1, r_2, r_3,
                b_sign, c_sign, q_sign, sign_xor,
                c_sum_inv, r_sum_inv,
                r_abs_0, r_abs_1, r_abs_2, r_abs_3,
                r_inv_0, r_inv_1, r_inv_2, r_inv_3,
                lt_marker_0, lt_marker_1, lt_marker_2, lt_marker_3,
                lt_diff,
                opcode_div_flag, opcode_divu_flag, opcode_rem_flag, opcode_remu_flag,
            },
            derived: {
                expected_opcode_id: opcode_div_flag * constant(crate::instructions::Opcode::Div as u32)
                    + opcode_divu_flag * constant(crate::instructions::Opcode::Divu as u32)
                    + opcode_rem_flag * constant(crate::instructions::Opcode::Rem as u32)
                    + opcode_remu_flag * constant(crate::instructions::Opcode::Remu as u32),
                is_div: opcode_div_flag + opcode_divu_flag,
                is_signed: opcode_div_flag + opcode_rem_flag,
                special_case: zero_divisor + r_zero,
                valid_not_zero_divisor: enabler - zero_divisor,
                valid_not_special: enabler - special_case,
                q_sum: q_0 + q_1 + q_2 + q_3,
                c_sum: rs2_next_0 + rs2_next_1 + rs2_next_2 + rs2_next_3,
                r_sum: r_0 + r_1 + r_2 + r_3,
                c_sign_factor: 1 - 2 * c_sign,
                // |r| vs |c| limb differences under the divisor sign
                diff_0: c_sign_factor * (rs2_next_0 - r_abs_0),
                diff_1: c_sign_factor * (rs2_next_1 - r_abs_1),
                diff_2: c_sign_factor * (rs2_next_2 - r_abs_2),
                diff_3: c_sign_factor * (rs2_next_3 - r_abs_3),
                // Result selection: quotient for div/divu, remainder for rem/remu
                a_0: is_div * q_0 + (1 - is_div) * r_0,
                a_1: is_div * q_1 + (1 - is_div) * r_1,
                a_2: is_div * q_2 + (1 - is_div) * r_2,
                a_3: is_div * q_3 + (1 - is_div) * r_3,
                // Carry chain of r + |r| = 2^32 (two's complement negation)
                carry_lt_0: (r_0 + r_abs_0) * inv(pow2(8)),
                carry_lt_1: (carry_lt_0 + r_1 + r_abs_1) * inv(pow2(8)),
                carry_lt_2: (carry_lt_1 + r_2 + r_abs_2) * inv(pow2(8)),
                carry_lt_3: (carry_lt_2 + r_3 + r_abs_3) * inv(pow2(8)),
                // Comparison scan prefixes, seeded by the special cases
                prefix_3: special_case + lt_marker_3,
                prefix_2: prefix_3 + lt_marker_2,
                prefix_1: prefix_2 + lt_marker_1,
                prefix_0: prefix_1 + lt_marker_0,
                lt_diff_minus_1: lt_diff - 1,
                // Sign-extension limbs (64-bit two's complement): every limb
                // above the low four equals sign * 0xFF. The remainder's sign is
                // the dividend's, except r = 0 which extends with zeros; the
                // zero-divisor case (r = b) keeps b's sign through b_sign.
                c_hi: 255 * c_sign,
                q_hi: 255 * q_sign,
                b_hi: 255 * b_sign,
                r_hi: 255 * b_sign * (1 - r_zero),
                // Schoolbook carries of rs1 = rs2 * q + r over the sign-extended
                // limbs: carry_k integral and below 2^11 makes the
                // limb equations an exact 64-bit identity, which pins (q, r) to
                // the dividend (the overflow case is exact too: q_sign = 0 reads
                // 0x80000000 as +2^31).
                carry_0: (rs2_next_0 * q_0 + r_0 - rs1_next_0) * inv(pow2(8)),
                carry_1: (carry_0 + rs2_next_0 * q_1 + rs2_next_1 * q_0 + r_1 - rs1_next_1)
                        * inv(pow2(8)),
                carry_2: (carry_1 + rs2_next_0 * q_2 + rs2_next_1 * q_1 + rs2_next_2 * q_0 + r_2
                        - rs1_next_2) * inv(pow2(8)),
                carry_3: (carry_2 + rs2_next_0 * q_3 + rs2_next_1 * q_2 + rs2_next_2 * q_1
                        + rs2_next_3 * q_0 + r_3 - rs1_next_3) * inv(pow2(8)),
                carry_4: (carry_3 + rs2_next_0 * q_hi + rs2_next_1 * q_3 + rs2_next_2 * q_2
                        + rs2_next_3 * q_1 + c_hi * q_0 + r_hi - b_hi) * inv(pow2(8)),
                carry_5: (carry_4 + (rs2_next_0 + rs2_next_1) * q_hi + rs2_next_2 * q_3
                        + rs2_next_3 * q_2 + c_hi * (q_0 + q_1) + r_hi - b_hi)
                        * inv(pow2(8)),
                carry_6: (carry_5 + (c_sum - rs2_next_3) * q_hi + rs2_next_3 * q_3
                        + c_hi * (q_sum - q_3) + r_hi - b_hi) * inv(pow2(8)),
                carry_7: (carry_6 + c_sum * q_hi + c_hi * q_sum + r_hi - b_hi) * inv(pow2(8)),
                // Sign bits bound to the operands' top limbs under signed
                // opcodes: 2 * (top_limb - sign * 2^7) is a byte iff the sign
                // bit matches (without this, a sign lie with r = 0 slips past
                // the special-case-gated comparison scan).
                b_sign_check: 2 * is_signed * (rs1_next_3 - b_sign * pow2(7)),
                c_sign_check: 2 * is_signed * (rs2_next_3 - c_sign * pow2(7)),
                pc_next: pc + 4,
                clock_next: clock + 1,
                rs1_clock_diff: clock - rs1_clock_prev,
                rs2_clock_diff: clock - rs2_clock_prev,
                rd_clock_diff: clock - rd_clock_prev,
            },
            constraints: {
                zero_divisor * (1 - zero_divisor),
                r_zero * (1 - r_zero),
                b_sign * (1 - b_sign),
                c_sign * (1 - c_sign),
                q_sign * (1 - q_sign),
                sign_xor * (1 - sign_xor),
                lt_marker_0 * (1 - lt_marker_0),
                lt_marker_1 * (1 - lt_marker_1),
                lt_marker_2 * (1 - lt_marker_2),
                lt_marker_3 * (1 - lt_marker_3),
                special_case * (1 - special_case),
                valid_not_zero_divisor * (1 - valid_not_zero_divisor),
                valid_not_special * (1 - valid_not_special),
                // Zero divisor: all-one quotient, zero divisor limbs
                zero_divisor * rs2_next_0,
                zero_divisor * rs2_next_1,
                zero_divisor * rs2_next_2,
                zero_divisor * rs2_next_3,
                zero_divisor * (q_0 - (pow2(8) - 1)),
                zero_divisor * (q_1 - (pow2(8) - 1)),
                zero_divisor * (q_2 - (pow2(8) - 1)),
                zero_divisor * (q_3 - (pow2(8) - 1)),
                valid_not_zero_divisor * (c_sum * c_sum_inv - 1),
                // Zero remainder detection
                r_zero * r_0,
                r_zero * r_1,
                r_zero * r_2,
                r_zero * r_3,
                valid_not_special * (r_sum * r_sum_inv - 1),
                // Signs only under signed opcodes; sign_xor = b_sign XOR c_sign
                (1 - is_signed) * b_sign,
                (1 - is_signed) * c_sign,
                enabler * (sign_xor - b_sign - c_sign + 2 * b_sign * c_sign),
                // Quotient sign selection
                (1 - zero_divisor) * q_sum * (q_sign - sign_xor),
                (1 - zero_divisor) * (q_sign - sign_xor) * q_sign,
                // Absolute remainder: identity without sign flip, two's
                // complement otherwise
                (1 - sign_xor) * (r_abs_0 - r_0),
                sign_xor * carry_lt_0 * (carry_lt_0 - 1),
                sign_xor * (1 - carry_lt_0) * r_abs_0,
                sign_xor * ((r_abs_0 - pow2(8)) * r_inv_0 - 1),
                (1 - sign_xor) * (r_abs_1 - r_1),
                sign_xor * (carry_lt_1 - carry_lt_0) * (carry_lt_1 - 1),
                sign_xor * (1 - carry_lt_1) * r_abs_1,
                sign_xor * ((r_abs_1 - pow2(8)) * r_inv_1 - 1),
                (1 - sign_xor) * (r_abs_2 - r_2),
                sign_xor * (carry_lt_2 - carry_lt_1) * (carry_lt_2 - 1),
                sign_xor * (1 - carry_lt_2) * r_abs_2,
                sign_xor * ((r_abs_2 - pow2(8)) * r_inv_2 - 1),
                (1 - sign_xor) * (r_abs_3 - r_3),
                sign_xor * (carry_lt_3 - carry_lt_2) * (carry_lt_3 - 1),
                sign_xor * (1 - carry_lt_3) * r_abs_3,
                sign_xor * ((r_abs_3 - pow2(8)) * r_inv_3 - 1),
                // < scan from the most significant limb. The enabler gate is
                // omitted: diff and lt_diff vanish on padding rows, and without
                // it the constraints stay within the degree-3 bound (diff is
                // already quadratic).
                (1 - prefix_3) * diff_3,
                lt_marker_3 * (lt_diff - diff_3),
                (1 - prefix_2) * diff_2,
                lt_marker_2 * (lt_diff - diff_2),
                (1 - prefix_1) * diff_1,
                lt_marker_1 * (lt_diff - diff_1),
                (1 - prefix_0) * diff_0,
                lt_marker_0 * (lt_diff - diff_0),
                enabler * (1 - prefix_0),
            },
            lookups: {
                // Quadratic carry denominators: every fraction must stay in a
                // singleton batch to hold the constraint degree bound.
                batch: 1,
                // Program access (R-type): Program(pc, opcode, rd_idx, rs1_idx, rs2_idx)
                -enabler * program_access(pc, expected_opcode_id, rd_addr, rs1_addr, rs2_addr),
                -enabler * registers_state(pc, clock),
                enabler * registers_state(pc_next, clock_next),
                // Read rs1 (REG_AS = 0).
                -enabler * memory_access(0, rs1_addr, rs1_clock_prev, rs1_prev_0, rs1_prev_1, rs1_prev_2, rs1_prev_3),
                enabler * memory_access(0, rs1_addr, clock, rs1_next_0, rs1_next_1, rs1_next_2, rs1_next_3),
                - enabler * range_check_20(rs1_clock_diff),
                // Read rs2.
                -enabler * memory_access(0, rs2_addr, rs2_clock_prev, rs2_prev_0, rs2_prev_1, rs2_prev_2, rs2_prev_3),
                enabler * memory_access(0, rs2_addr, clock, rs2_next_0, rs2_next_1, rs2_next_2, rs2_next_3),
                - enabler * range_check_20(rs2_clock_diff),
                // Quotient and remainder limbs are bytes and the rs1 = rs2*q + r
                // schoolbook carries fit 11 bits.
                - enabler * range_check_8_11(q_0, carry_0),
                - enabler * range_check_8_11(q_1, carry_1),
                - enabler * range_check_8_11(q_2, carry_2),
                - enabler * range_check_8_11(q_3, carry_3),
                - enabler * range_check_8_11(r_0, carry_4),
                - enabler * range_check_8_11(r_1, carry_5),
                - enabler * range_check_8_11(r_2, carry_6),
                - enabler * range_check_8_11(r_3, carry_7),
                // b_sign / c_sign match the operands' top bits.
                - enabler * range_check_8_8(b_sign_check, c_sign_check),
                // |r| < |c| on regular divisions: the comparison scan difference
                // is > 0.
                - valid_not_special * range_check_20(lt_diff_minus_1),
                // Write rd := the division result under the special-case rules.
                -enabler * memory_access(0, rd_addr, rd_clock_prev, rd_prev_0, rd_prev_1, rd_prev_2, rd_prev_3),
                enabler * memory_access(0, rd_addr, clock, a_0, a_1, a_2, a_3),
                - enabler * range_check_20(rd_clock_diff),
            },
        },

        // ==========================================================================
        // 17. COMMIT syscall
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
        // 18. Program commitment table
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
        // 19. Memory commitment table (initial/final)
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
        // 20. Merkle tree nodes
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
