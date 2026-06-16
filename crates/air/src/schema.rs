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
    }
    trace: {
        base_alu_reg: {
            committed: {
                clock, pc, rd, rs1, rs2,
                opcode_add_flag, opcode_sub_flag, opcode_xor_flag, opcode_or_flag, opcode_and_flag,
            },
            derived: {
                expected_opcode_id: opcode_add_flag * constant(crate::instructions::Opcode::Add as u32)
                    + opcode_sub_flag * constant(crate::instructions::Opcode::Sub as u32)
                    + opcode_xor_flag * constant(crate::instructions::Opcode::Xor as u32)
                    + opcode_or_flag * constant(crate::instructions::Opcode::Or as u32)
                    + opcode_and_flag * constant(crate::instructions::Opcode::And as u32),
                is_bitwise: opcode_xor_flag + opcode_or_flag + opcode_and_flag,
                // Preprocessed bitwise table id: and=0, or=1, xor=2
                bitwise_id: 2 * opcode_xor_flag + opcode_or_flag,
                pc_next: pc + 4,
                clock_next: clock + 1,
                rs1_clock_diff: clock - rs1_clock_prev,
                rs2_clock_diff: clock - rs2_clock_prev,
                rd_clock_diff: clock - rd_clock_prev,
                // Carry chains of rd = rs1 + rs2 and rs1 = rd + rs2 over 8-bit
                // limbs; each carry is 0 or 1 under the active opcode
                carry_add_0: (rs1_next_0 + rs2_next_0 - rd_next_0) * inv(pow2(8)),
                carry_add_1: (rs1_next_1 + rs2_next_1 + carry_add_0 - rd_next_1) * inv(pow2(8)),
                carry_add_2: (rs1_next_2 + rs2_next_2 + carry_add_1 - rd_next_2) * inv(pow2(8)),
                carry_add_3: (rs1_next_3 + rs2_next_3 + carry_add_2 - rd_next_3) * inv(pow2(8)),
                carry_sub_0: (rd_next_0 + rs2_next_0 - rs1_next_0) * inv(pow2(8)),
                carry_sub_1: (rd_next_1 + rs2_next_1 - rs1_next_1 + carry_sub_0) * inv(pow2(8)),
                carry_sub_2: (rd_next_2 + rs2_next_2 - rs1_next_2 + carry_sub_1) * inv(pow2(8)),
                carry_sub_3: (rd_next_3 + rs2_next_3 - rs1_next_3 + carry_sub_2) * inv(pow2(8)),
            },
            constraints: {
                opcode_add_flag * carry_add_0 * (1 - carry_add_0),
                opcode_add_flag * carry_add_1 * (1 - carry_add_1),
                opcode_add_flag * carry_add_2 * (1 - carry_add_2),
                opcode_add_flag * carry_add_3 * (1 - carry_add_3),
                opcode_sub_flag * carry_sub_0 * (1 - carry_sub_0),
                opcode_sub_flag * carry_sub_1 * (1 - carry_sub_1),
                opcode_sub_flag * carry_sub_2 * (1 - carry_sub_2),
                opcode_sub_flag * carry_sub_3 * (1 - carry_sub_3),
            },
            lookups: {
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
                // Bitwise limbs (xor/or/and): Bitwise(rs1[i], rs2[i], rd[i], op id).
                - is_bitwise * bitwise(rs1_next_0, rs2_next_0, rd_next_0, bitwise_id),
                - is_bitwise * bitwise(rs1_next_1, rs2_next_1, rd_next_1, bitwise_id),
                - is_bitwise * bitwise(rs1_next_2, rs2_next_2, rd_next_2, bitwise_id),
                - is_bitwise * bitwise(rs1_next_3, rs2_next_3, rd_next_3, bitwise_id),
                // rd byte ranges (spec 1.3): add/sub carry equations alone admit
                // non-canonical limbs.
                - enabler * range_check_8_8(rd_next_0, rd_next_1),
                - enabler * range_check_8_8(rd_next_2, rd_next_3),
                // Write rd.
                -enabler * memory_access(0, rd_addr, rd_clock_prev, rd_prev_0, rd_prev_1, rd_prev_2, rd_prev_3),
                enabler * memory_access(0, rd_addr, clock, rd_next_0, rd_next_1, rd_next_2, rd_next_3),
                - enabler * range_check_20(rd_clock_diff),
            },
        },

        // ==========================================================================
        // 2. Base ALU Imm (addi/xori/ori/andi) - airs.md Section 2
        // ==========================================================================
        base_alu_imm: {
            committed: {
                clock, pc, rd, rs1,
                imm_0, imm_1, imm_msb,
                opcode_add_flag, opcode_xor_flag, opcode_or_flag, opcode_and_flag,
            },
            derived: {
                // Opcode id encoded in the program segment, selected by the active flag
                expected_opcode_id: opcode_add_flag * constant(crate::instructions::Opcode::Addi as u32)
                    + opcode_xor_flag * constant(crate::instructions::Opcode::Xori as u32)
                    + opcode_or_flag * constant(crate::instructions::Opcode::Ori as u32)
                    + opcode_and_flag * constant(crate::instructions::Opcode::Andi as u32),
                // I-type immediate: imm_0 (8 bits) + imm_1 (3 bits) + sign bit (airs.md 2.2)
                imm: imm_0 + pow2(8) * imm_1 + pow2(11) * imm_msb,
                // Sign-extended immediate limbs; limb 0 is imm_0 and limb 3 equals limb 2
                sext_imm_1: imm_1 + ((1 << 3) * ((1 << 5) - 1)) * imm_msb,
                sext_imm_2: ((1 << 8) - 1) * imm_msb,
                is_bitwise: opcode_xor_flag + opcode_or_flag + opcode_and_flag,
                // Preprocessed bitwise table id: and=0, or=1, xor=2
                bitwise_id: 2 * opcode_xor_flag + opcode_or_flag,
                imm_1_shifted: pow2(8) * imm_1,
                pc_next: pc + 4,
                clock_next: clock + 1,
                rs1_clock_diff: clock - rs1_clock_prev,
                rd_clock_diff: clock - rd_clock_prev,
                // Carry chain of rd = rs1 + sext_imm over 8-bit limbs; each carry is 0 or 1
                carry_0: (rs1_next_0 + imm_0 - rd_next_0) * inv(pow2(8)),
                carry_1: (rs1_next_1 + sext_imm_1 + carry_0 - rd_next_1) * inv(pow2(8)),
                carry_2: (rs1_next_2 + sext_imm_2 + carry_1 - rd_next_2) * inv(pow2(8)),
                carry_3: (rs1_next_3 + sext_imm_2 + carry_2 - rd_next_3) * inv(pow2(8)),
            },
            constraints: {
                imm_msb * (1 - imm_msb),
                opcode_add_flag * carry_0 * (1 - carry_0),
                opcode_add_flag * carry_1 * (1 - carry_1),
                opcode_add_flag * carry_2 * (1 - carry_2),
                opcode_add_flag * carry_3 * (1 - carry_3),
            },
            lookups: {
                // Program access (I-type): Program(pc, opcode, rd_idx, rs1_idx, imm)
                -enabler * program_access(pc, expected_opcode_id, rd_addr, rs1_addr, imm),
                // I-type immediate limb ranges: imm_0 is 8 bits, imm_1 is 3 bits.
                - enabler * range_check_8_11(imm_0, imm_1_shifted),
                -enabler * registers_state(pc, clock),
                enabler * registers_state(pc_next, clock_next),
                // Read rs1 (REG_AS = 0).
                -enabler * memory_access(0, rs1_addr, rs1_clock_prev, rs1_prev_0, rs1_prev_1, rs1_prev_2, rs1_prev_3),
                enabler * memory_access(0, rs1_addr, clock, rs1_next_0, rs1_next_1, rs1_next_2, rs1_next_3),
                - enabler * range_check_20(rs1_clock_diff),
                // Bitwise limbs (xor/or/and): Bitwise(rs1[i], sext_imm[i], rd[i], op id).
                - is_bitwise * bitwise(rs1_next_0, imm_0, rd_next_0, bitwise_id),
                - is_bitwise * bitwise(rs1_next_1, sext_imm_1, rd_next_1, bitwise_id),
                - is_bitwise * bitwise(rs1_next_2, sext_imm_2, rd_next_2, bitwise_id),
                - is_bitwise * bitwise(rs1_next_3, sext_imm_2, rd_next_3, bitwise_id),
                // rd byte ranges.
                - enabler * range_check_8_8(rd_next_0, rd_next_1),
                - enabler * range_check_8_8(rd_next_2, rd_next_3),
                // Write rd.
                -enabler * memory_access(0, rd_addr, rd_clock_prev, rd_prev_0, rd_prev_1, rd_prev_2, rd_prev_3),
                enabler * memory_access(0, rd_addr, clock, rd_next_0, rd_next_1, rd_next_2, rd_next_3),
                - enabler * range_check_20(rd_clock_diff),
            },
        },

        // ==========================================================================
        // 3. Shifts Reg (sll/srl/sra) - airs.md Section 3
        // ==========================================================================
        shifts_reg: {
            committed: {
                clock, pc, rd, rs1, rs2,
                rs1_sign,
                opcode_sll_flag, opcode_srl_flag, opcode_sra_flag,
                bit_multiplier_left, bit_multiplier_right,
                bit_shift_marker_0, bit_shift_marker_1, bit_shift_marker_2, bit_shift_marker_3,
                bit_shift_marker_4, bit_shift_marker_5, bit_shift_marker_6, bit_shift_marker_7,
                limb_shift_marker_0, limb_shift_marker_1, limb_shift_marker_2, limb_shift_marker_3,
                bit_shift_carry_0, bit_shift_carry_1, bit_shift_carry_2, bit_shift_carry_3,
            },
            derived: {
                expected_opcode_id: opcode_sll_flag * constant(crate::instructions::Opcode::Sll as u32)
                    + opcode_srl_flag * constant(crate::instructions::Opcode::Srl as u32)
                    + opcode_sra_flag * constant(crate::instructions::Opcode::Sra as u32),
                right_shift: opcode_srl_flag + opcode_sra_flag,
                // Hot-one decoded shift quantities (airs.md 3.2)
                bit_multiplier: bit_shift_marker_0 + 2 * bit_shift_marker_1 + 4 * bit_shift_marker_2
                    + 8 * bit_shift_marker_3 + 16 * bit_shift_marker_4 + 32 * bit_shift_marker_5
                    + 64 * bit_shift_marker_6 + 128 * bit_shift_marker_7,
                bit_shift: bit_shift_marker_1 + 2 * bit_shift_marker_2 + 3 * bit_shift_marker_3
                    + 4 * bit_shift_marker_4 + 5 * bit_shift_marker_5 + 6 * bit_shift_marker_6
                    + 7 * bit_shift_marker_7,
                limb_shift: limb_shift_marker_1 + 2 * limb_shift_marker_2 + 3 * limb_shift_marker_3,
                shift_amount: pow2(3) * limb_shift + bit_shift,
                bit_marker_sum: bit_shift_marker_0 + bit_shift_marker_1 + bit_shift_marker_2 + bit_shift_marker_3
                    + bit_shift_marker_4 + bit_shift_marker_5 + bit_shift_marker_6
                    + bit_shift_marker_7,
                limb_marker_sum: limb_shift_marker_0 + limb_shift_marker_1 + limb_shift_marker_2
                    + limb_shift_marker_3,
                // Shift amount comes from the low 5 bits of rs2 (airs.md 3.3)
                // 7 - (rs2_next_0 - shift_amount) / 2^5: in range iff the shift
                // amount is rs2's low 5 bits (the field division by 32 explodes
                // otherwise) - spec 3.3.
                shift_check: (pow2(3) - 1) - (rs2_next_0 - shift_amount) * inv(pow2(5)),
                pc_next: pc + 4,
                clock_next: clock + 1,
                rs1_clock_diff: clock - rs1_clock_prev,
                rs2_clock_diff: clock - rs2_clock_prev,
                rd_clock_diff: clock - rd_clock_prev,
            },
            constraints: {
                rs1_sign * (1 - rs1_sign),
                bit_shift_marker_0 * (1 - bit_shift_marker_0),
                bit_shift_marker_1 * (1 - bit_shift_marker_1),
                bit_shift_marker_2 * (1 - bit_shift_marker_2),
                bit_shift_marker_3 * (1 - bit_shift_marker_3),
                bit_shift_marker_4 * (1 - bit_shift_marker_4),
                bit_shift_marker_5 * (1 - bit_shift_marker_5),
                bit_shift_marker_6 * (1 - bit_shift_marker_6),
                bit_shift_marker_7 * (1 - bit_shift_marker_7),
                limb_shift_marker_0 * (1 - limb_shift_marker_0),
                limb_shift_marker_1 * (1 - limb_shift_marker_1),
                limb_shift_marker_2 * (1 - limb_shift_marker_2),
                limb_shift_marker_3 * (1 - limb_shift_marker_3),
                // Exactly one bit marker and one limb marker fire on enabled rows
                bit_marker_sum - enabler,
                limb_marker_sum - enabler,
                bit_multiplier_left - opcode_sll_flag * bit_multiplier,
                bit_multiplier_right - right_shift * bit_multiplier,
                // Left shift by 8*i + b: rd limbs below i vanish, limb i carries
                // out, higher limbs chain the carries (airs.md 3.3)
                opcode_sll_flag * limb_shift_marker_0 * (rd_next_0 + pow2(8) * bit_shift_carry_0)
                    - limb_shift_marker_0 * rs1_next_0 * bit_multiplier_left,
                opcode_sll_flag * limb_shift_marker_0 * (rd_next_1 - (bit_shift_carry_0 - pow2(8) * bit_shift_carry_1))
                    - limb_shift_marker_0 * rs1_next_1 * bit_multiplier_left,
                opcode_sll_flag * limb_shift_marker_0 * (rd_next_2 - (bit_shift_carry_1 - pow2(8) * bit_shift_carry_2))
                    - limb_shift_marker_0 * rs1_next_2 * bit_multiplier_left,
                opcode_sll_flag * limb_shift_marker_0 * (rd_next_3 - (bit_shift_carry_2 - pow2(8) * bit_shift_carry_3))
                    - limb_shift_marker_0 * rs1_next_3 * bit_multiplier_left,
                opcode_sll_flag * limb_shift_marker_1 * rd_next_0,
                opcode_sll_flag * limb_shift_marker_1 * (rd_next_1 + pow2(8) * bit_shift_carry_0)
                    - limb_shift_marker_1 * rs1_next_0 * bit_multiplier_left,
                opcode_sll_flag * limb_shift_marker_1 * (rd_next_2 - (bit_shift_carry_0 - pow2(8) * bit_shift_carry_1))
                    - limb_shift_marker_1 * rs1_next_1 * bit_multiplier_left,
                opcode_sll_flag * limb_shift_marker_1 * (rd_next_3 - (bit_shift_carry_1 - pow2(8) * bit_shift_carry_2))
                    - limb_shift_marker_1 * rs1_next_2 * bit_multiplier_left,
                opcode_sll_flag * limb_shift_marker_2 * rd_next_0,
                opcode_sll_flag * limb_shift_marker_2 * rd_next_1,
                opcode_sll_flag * limb_shift_marker_2 * (rd_next_2 + pow2(8) * bit_shift_carry_0)
                    - limb_shift_marker_2 * rs1_next_0 * bit_multiplier_left,
                opcode_sll_flag * limb_shift_marker_2 * (rd_next_3 - (bit_shift_carry_0 - pow2(8) * bit_shift_carry_1))
                    - limb_shift_marker_2 * rs1_next_1 * bit_multiplier_left,
                opcode_sll_flag * limb_shift_marker_3 * rd_next_0,
                opcode_sll_flag * limb_shift_marker_3 * rd_next_1,
                opcode_sll_flag * limb_shift_marker_3 * rd_next_2,
                opcode_sll_flag * limb_shift_marker_3 * (rd_next_3 + pow2(8) * bit_shift_carry_0)
                    - limb_shift_marker_3 * rs1_next_0 * bit_multiplier_left,
                // Right shift: high limbs sign-fill, limb 3-i takes the top, lower
                // limbs chain carries downward
                limb_shift_marker_0 * (bit_shift_carry_1 * right_shift * pow2(8)
                    + right_shift * (rs1_next_0 - bit_shift_carry_0)
                    - rd_next_0 * bit_multiplier_right),
                limb_shift_marker_0 * (bit_shift_carry_2 * right_shift * pow2(8)
                    + right_shift * (rs1_next_1 - bit_shift_carry_1)
                    - rd_next_1 * bit_multiplier_right),
                limb_shift_marker_0 * (bit_shift_carry_3 * right_shift * pow2(8)
                    + right_shift * (rs1_next_2 - bit_shift_carry_2)
                    - rd_next_2 * bit_multiplier_right),
                limb_shift_marker_0 * (rs1_sign * (bit_multiplier_right - 1) * pow2(8)
                    + right_shift * (rs1_next_3 - bit_shift_carry_3)
                    - rd_next_3 * bit_multiplier_right),
                limb_shift_marker_1 * (bit_shift_carry_2 * right_shift * pow2(8)
                    + right_shift * (rs1_next_1 - bit_shift_carry_1)
                    - rd_next_0 * bit_multiplier_right),
                limb_shift_marker_1 * (bit_shift_carry_3 * right_shift * pow2(8)
                    + right_shift * (rs1_next_2 - bit_shift_carry_2)
                    - rd_next_1 * bit_multiplier_right),
                limb_shift_marker_1 * (rs1_sign * (bit_multiplier_right - 1) * pow2(8)
                    + right_shift * (rs1_next_3 - bit_shift_carry_3)
                    - rd_next_2 * bit_multiplier_right),
                right_shift * limb_shift_marker_1 * (rd_next_3 - rs1_sign * (pow2(8) - 1)),
                limb_shift_marker_2 * (bit_shift_carry_3 * right_shift * pow2(8)
                    + right_shift * (rs1_next_2 - bit_shift_carry_2)
                    - rd_next_0 * bit_multiplier_right),
                limb_shift_marker_2 * (rs1_sign * (bit_multiplier_right - 1) * pow2(8)
                    + right_shift * (rs1_next_3 - bit_shift_carry_3)
                    - rd_next_1 * bit_multiplier_right),
                right_shift * limb_shift_marker_2 * (rd_next_2 - rs1_sign * (pow2(8) - 1)),
                right_shift * limb_shift_marker_2 * (rd_next_3 - rs1_sign * (pow2(8) - 1)),
                limb_shift_marker_3 * (rs1_sign * (bit_multiplier_right - 1) * pow2(8)
                    + right_shift * (rs1_next_3 - bit_shift_carry_3)
                    - rd_next_0 * bit_multiplier_right),
                right_shift * limb_shift_marker_3 * (rd_next_1 - rs1_sign * (pow2(8) - 1)),
                right_shift * limb_shift_marker_3 * (rd_next_2 - rs1_sign * (pow2(8) - 1)),
                right_shift * limb_shift_marker_3 * (rd_next_3 - rs1_sign * (pow2(8) - 1)),
            },
            lookups: {
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
                // The decoded shift amount matches rs2's low 5 bits.
                - enabler * range_check_20(shift_check),
                // Shift carries stay below 2^bit_shift (spec 3.3): otherwise the
                // shift equations absorb arbitrary errors into the carries.
                - enabler * range_check_8_8(
                    bit_multiplier - enabler - bit_shift_carry_0,
                    bit_multiplier - enabler - bit_shift_carry_1),
                - enabler * range_check_8_8(
                    bit_multiplier - enabler - bit_shift_carry_2,
                    bit_multiplier - enabler - bit_shift_carry_3),
                // rd byte ranges.
                - enabler * range_check_8_8(rd_next_0, rd_next_1),
                - enabler * range_check_8_8(rd_next_2, rd_next_3),
                // Write rd.
                -enabler * memory_access(0, rd_addr, rd_clock_prev, rd_prev_0, rd_prev_1, rd_prev_2, rd_prev_3),
                enabler * memory_access(0, rd_addr, clock, rd_next_0, rd_next_1, rd_next_2, rd_next_3),
                - enabler * range_check_20(rd_clock_diff),
            },
        },

        // ==========================================================================
        // 4. Shifts Imm (slli/srli/srai) - airs.md Section 4
        // ==========================================================================
        shifts_imm: {
            committed: {
                clock, pc, rd, rs1,
                rs1_sign, imm_truncated,
                opcode_sll_flag, opcode_srl_flag, opcode_sra_flag,
                bit_multiplier_left, bit_multiplier_right,
                bit_shift_marker_0, bit_shift_marker_1, bit_shift_marker_2, bit_shift_marker_3,
                bit_shift_marker_4, bit_shift_marker_5, bit_shift_marker_6, bit_shift_marker_7,
                limb_shift_marker_0, limb_shift_marker_1, limb_shift_marker_2, limb_shift_marker_3,
                bit_shift_carry_0, bit_shift_carry_1, bit_shift_carry_2, bit_shift_carry_3,
            },
            derived: {
                expected_opcode_id: opcode_sll_flag * constant(crate::instructions::Opcode::Slli as u32)
                    + opcode_srl_flag * constant(crate::instructions::Opcode::Srli as u32)
                    + opcode_sra_flag * constant(crate::instructions::Opcode::Srai as u32),
                right_shift: opcode_srl_flag + opcode_sra_flag,
                // Hot-one decoded shift quantities (airs.md 4.2)
                bit_multiplier: bit_shift_marker_0 + 2 * bit_shift_marker_1 + 4 * bit_shift_marker_2
                    + 8 * bit_shift_marker_3 + 16 * bit_shift_marker_4 + 32 * bit_shift_marker_5
                    + 64 * bit_shift_marker_6 + 128 * bit_shift_marker_7,
                bit_shift: bit_shift_marker_1 + 2 * bit_shift_marker_2 + 3 * bit_shift_marker_3
                    + 4 * bit_shift_marker_4 + 5 * bit_shift_marker_5 + 6 * bit_shift_marker_6
                    + 7 * bit_shift_marker_7,
                limb_shift: limb_shift_marker_1 + 2 * limb_shift_marker_2 + 3 * limb_shift_marker_3,
                shift_amount: pow2(3) * limb_shift + bit_shift,
                bit_marker_sum: bit_shift_marker_0 + bit_shift_marker_1 + bit_shift_marker_2 + bit_shift_marker_3
                    + bit_shift_marker_4 + bit_shift_marker_5 + bit_shift_marker_6
                    + bit_shift_marker_7,
                limb_marker_sum: limb_shift_marker_0 + limb_shift_marker_1 + limb_shift_marker_2
                    + limb_shift_marker_3,
                pc_next: pc + 4,
                clock_next: clock + 1,
                rs1_clock_diff: clock - rs1_clock_prev,
                rd_clock_diff: clock - rd_clock_prev,
            },
            constraints: {
                rs1_sign * (1 - rs1_sign),
                bit_shift_marker_0 * (1 - bit_shift_marker_0),
                bit_shift_marker_1 * (1 - bit_shift_marker_1),
                bit_shift_marker_2 * (1 - bit_shift_marker_2),
                bit_shift_marker_3 * (1 - bit_shift_marker_3),
                bit_shift_marker_4 * (1 - bit_shift_marker_4),
                bit_shift_marker_5 * (1 - bit_shift_marker_5),
                bit_shift_marker_6 * (1 - bit_shift_marker_6),
                bit_shift_marker_7 * (1 - bit_shift_marker_7),
                limb_shift_marker_0 * (1 - limb_shift_marker_0),
                limb_shift_marker_1 * (1 - limb_shift_marker_1),
                limb_shift_marker_2 * (1 - limb_shift_marker_2),
                limb_shift_marker_3 * (1 - limb_shift_marker_3),
                bit_marker_sum - enabler,
                limb_marker_sum - enabler,
                bit_multiplier_left - opcode_sll_flag * bit_multiplier,
                bit_multiplier_right - right_shift * bit_multiplier,
                // The immediate encodes the decoded shift amount (airs.md 4.3)
                imm_truncated - shift_amount,
                // Left shift by 8*i + b (airs.md 4.3)
                opcode_sll_flag * limb_shift_marker_0 * (rd_next_0 + pow2(8) * bit_shift_carry_0)
                    - limb_shift_marker_0 * rs1_next_0 * bit_multiplier_left,
                opcode_sll_flag * limb_shift_marker_0 * (rd_next_1 - (bit_shift_carry_0 - pow2(8) * bit_shift_carry_1))
                    - limb_shift_marker_0 * rs1_next_1 * bit_multiplier_left,
                opcode_sll_flag * limb_shift_marker_0 * (rd_next_2 - (bit_shift_carry_1 - pow2(8) * bit_shift_carry_2))
                    - limb_shift_marker_0 * rs1_next_2 * bit_multiplier_left,
                opcode_sll_flag * limb_shift_marker_0 * (rd_next_3 - (bit_shift_carry_2 - pow2(8) * bit_shift_carry_3))
                    - limb_shift_marker_0 * rs1_next_3 * bit_multiplier_left,
                opcode_sll_flag * limb_shift_marker_1 * rd_next_0,
                opcode_sll_flag * limb_shift_marker_1 * (rd_next_1 + pow2(8) * bit_shift_carry_0)
                    - limb_shift_marker_1 * rs1_next_0 * bit_multiplier_left,
                opcode_sll_flag * limb_shift_marker_1 * (rd_next_2 - (bit_shift_carry_0 - pow2(8) * bit_shift_carry_1))
                    - limb_shift_marker_1 * rs1_next_1 * bit_multiplier_left,
                opcode_sll_flag * limb_shift_marker_1 * (rd_next_3 - (bit_shift_carry_1 - pow2(8) * bit_shift_carry_2))
                    - limb_shift_marker_1 * rs1_next_2 * bit_multiplier_left,
                opcode_sll_flag * limb_shift_marker_2 * rd_next_0,
                opcode_sll_flag * limb_shift_marker_2 * rd_next_1,
                opcode_sll_flag * limb_shift_marker_2 * (rd_next_2 + pow2(8) * bit_shift_carry_0)
                    - limb_shift_marker_2 * rs1_next_0 * bit_multiplier_left,
                opcode_sll_flag * limb_shift_marker_2 * (rd_next_3 - (bit_shift_carry_0 - pow2(8) * bit_shift_carry_1))
                    - limb_shift_marker_2 * rs1_next_1 * bit_multiplier_left,
                opcode_sll_flag * limb_shift_marker_3 * rd_next_0,
                opcode_sll_flag * limb_shift_marker_3 * rd_next_1,
                opcode_sll_flag * limb_shift_marker_3 * rd_next_2,
                opcode_sll_flag * limb_shift_marker_3 * (rd_next_3 + pow2(8) * bit_shift_carry_0)
                    - limb_shift_marker_3 * rs1_next_0 * bit_multiplier_left,
                // Right shift with sign fill
                limb_shift_marker_0 * (bit_shift_carry_1 * right_shift * pow2(8)
                    + right_shift * (rs1_next_0 - bit_shift_carry_0)
                    - rd_next_0 * bit_multiplier_right),
                limb_shift_marker_0 * (bit_shift_carry_2 * right_shift * pow2(8)
                    + right_shift * (rs1_next_1 - bit_shift_carry_1)
                    - rd_next_1 * bit_multiplier_right),
                limb_shift_marker_0 * (bit_shift_carry_3 * right_shift * pow2(8)
                    + right_shift * (rs1_next_2 - bit_shift_carry_2)
                    - rd_next_2 * bit_multiplier_right),
                limb_shift_marker_0 * (rs1_sign * (bit_multiplier_right - 1) * pow2(8)
                    + right_shift * (rs1_next_3 - bit_shift_carry_3)
                    - rd_next_3 * bit_multiplier_right),
                limb_shift_marker_1 * (bit_shift_carry_2 * right_shift * pow2(8)
                    + right_shift * (rs1_next_1 - bit_shift_carry_1)
                    - rd_next_0 * bit_multiplier_right),
                limb_shift_marker_1 * (bit_shift_carry_3 * right_shift * pow2(8)
                    + right_shift * (rs1_next_2 - bit_shift_carry_2)
                    - rd_next_1 * bit_multiplier_right),
                limb_shift_marker_1 * (rs1_sign * (bit_multiplier_right - 1) * pow2(8)
                    + right_shift * (rs1_next_3 - bit_shift_carry_3)
                    - rd_next_2 * bit_multiplier_right),
                right_shift * limb_shift_marker_1 * (rd_next_3 - rs1_sign * (pow2(8) - 1)),
                limb_shift_marker_2 * (bit_shift_carry_3 * right_shift * pow2(8)
                    + right_shift * (rs1_next_2 - bit_shift_carry_2)
                    - rd_next_0 * bit_multiplier_right),
                limb_shift_marker_2 * (rs1_sign * (bit_multiplier_right - 1) * pow2(8)
                    + right_shift * (rs1_next_3 - bit_shift_carry_3)
                    - rd_next_1 * bit_multiplier_right),
                right_shift * limb_shift_marker_2 * (rd_next_2 - rs1_sign * (pow2(8) - 1)),
                right_shift * limb_shift_marker_2 * (rd_next_3 - rs1_sign * (pow2(8) - 1)),
                limb_shift_marker_3 * (rs1_sign * (bit_multiplier_right - 1) * pow2(8)
                    + right_shift * (rs1_next_3 - bit_shift_carry_3)
                    - rd_next_0 * bit_multiplier_right),
                right_shift * limb_shift_marker_3 * (rd_next_1 - rs1_sign * (pow2(8) - 1)),
                right_shift * limb_shift_marker_3 * (rd_next_2 - rs1_sign * (pow2(8) - 1)),
                right_shift * limb_shift_marker_3 * (rd_next_3 - rs1_sign * (pow2(8) - 1)),
            },
            lookups: {
                // Program access (I-type): Program(pc, opcode, rd_idx, rs1_idx, imm)
                -enabler * program_access(pc, expected_opcode_id, rd_addr, rs1_addr, imm_truncated),
                -enabler * registers_state(pc, clock),
                enabler * registers_state(pc_next, clock_next),
                // Read rs1 (REG_AS = 0).
                -enabler * memory_access(0, rs1_addr, rs1_clock_prev, rs1_prev_0, rs1_prev_1, rs1_prev_2, rs1_prev_3),
                enabler * memory_access(0, rs1_addr, clock, rs1_next_0, rs1_next_1, rs1_next_2, rs1_next_3),
                - enabler * range_check_20(rs1_clock_diff),
                // Shift carries stay below 2^bit_shift (spec 4.3).
                - enabler * range_check_8_8(
                    bit_multiplier - enabler - bit_shift_carry_0,
                    bit_multiplier - enabler - bit_shift_carry_1),
                - enabler * range_check_8_8(
                    bit_multiplier - enabler - bit_shift_carry_2,
                    bit_multiplier - enabler - bit_shift_carry_3),
                // rd byte ranges.
                - enabler * range_check_8_8(rd_next_0, rd_next_1),
                - enabler * range_check_8_8(rd_next_2, rd_next_3),
                // Write rd.
                -enabler * memory_access(0, rd_addr, rd_clock_prev, rd_prev_0, rd_prev_1, rd_prev_2, rd_prev_3),
                enabler * memory_access(0, rd_addr, clock, rd_next_0, rd_next_1, rd_next_2, rd_next_3),
                - enabler * range_check_20(rd_clock_diff),
            },
        },

        // ==========================================================================
        // 5. Less Than Reg (slt/sltu) - airs.md Section 5
        // ==========================================================================
        lt_reg: {
            committed: {
                clock, pc, rd, rs1, rs2,
                cmp_result, rs1_msl_felt, rs2_msl_felt,
                opcode_slt_flag, opcode_sltu_flag,
                diff_marker_0, diff_marker_1, diff_marker_2, diff_marker_3,
                diff_val,
            },
            derived: {
                expected_opcode_id: opcode_slt_flag * constant(crate::instructions::Opcode::Slt as u32)
                    + opcode_sltu_flag * constant(crate::instructions::Opcode::Sltu as u32),
                pc_next: pc + 4,
                clock_next: clock + 1,
                rs1_clock_diff: clock - rs1_clock_prev,
                rs2_clock_diff: clock - rs2_clock_prev,
                rd_clock_diff: clock - rd_clock_prev,
                // Most-significant-limb gaps: zero for unsigned interpretation,
                // 2^8 when the sign adjustment applies (airs.md 5.2)
                rs1_msl_gap: rs1_next_3 - rs1_msl_felt,
                rs2_msl_gap: rs2_next_3 - rs2_msl_felt,
                // Signed-shifted most significant limbs for the range check
                rs1_msl_shifted: rs1_msl_felt + opcode_slt_flag * pow2(7),
                rs2_msl_shifted: rs2_msl_felt + opcode_slt_flag * pow2(7),
                // Sum of the difference markers: at most one fires
                prefix_sum_final: diff_marker_0 + diff_marker_1 + diff_marker_2 + diff_marker_3,
                // Sign of the comparison: +1 if cmp_result else -1
                cmp_sign: 2 * cmp_result - 1,
            },
            constraints: {
                cmp_result * (1 - cmp_result),
                diff_marker_0 * (1 - diff_marker_0),
                diff_marker_1 * (1 - diff_marker_1),
                diff_marker_2 * (1 - diff_marker_2),
                diff_marker_3 * (1 - diff_marker_3),
                rs1_msl_gap * (pow2(8) - rs1_msl_gap),
                rs2_msl_gap * (pow2(8) - rs2_msl_gap),
                // Comparison scan from the most significant limb down: limbs
                // above the first difference are equal, and the marked limb's
                // difference equals diff_val (airs.md 5.3)
                (1 - diff_marker_3) * (cmp_sign * (rs2_msl_felt - rs1_msl_felt)),
                diff_marker_3 * (diff_val - cmp_sign * (rs2_msl_felt - rs1_msl_felt)),
                (1 - diff_marker_3 - diff_marker_2) * (cmp_sign * (rs2_next_2 - rs1_next_2)),
                diff_marker_2 * (diff_val - cmp_sign * (rs2_next_2 - rs1_next_2)),
                (1 - diff_marker_3 - diff_marker_2 - diff_marker_1)
                        * (cmp_sign * (rs2_next_1 - rs1_next_1)),
                diff_marker_1 * (diff_val - cmp_sign * (rs2_next_1 - rs1_next_1)),
                (1 - prefix_sum_final) * (cmp_sign * (rs2_next_0 - rs1_next_0)),
                diff_marker_0 * (diff_val - cmp_sign * (rs2_next_0 - rs1_next_0)),
                prefix_sum_final * (1 - prefix_sum_final),
                // Equal operands compare as not-less-than
                (1 - prefix_sum_final) * cmp_result,
            },
            lookups: {
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
                // Most significant limbs shifted into unsigned range under the
                // signed-comparison convention.
                - enabler * range_check_8_8(rs1_msl_shifted, rs2_msl_shifted),
                // When the comparison scan fired, the limb difference is > 0.
                - prefix_sum_final * range_check_20(diff_val - 1),
                // Write rd := cmp_result (a single bit in limb 0).
                -enabler * memory_access(0, rd_addr, rd_clock_prev, rd_prev_0, rd_prev_1, rd_prev_2, rd_prev_3),
                enabler * memory_access(0, rd_addr, clock, cmp_result, 0, 0, 0),
                - enabler * range_check_20(rd_clock_diff),
            },
        },

        // ==========================================================================
        // 6. Less Than Imm (slti/sltiu) - airs.md Section 6
        // ==========================================================================
        lt_imm: {
            committed: {
                clock, pc, rd, rs1,
                cmp_result, rs1_msl_felt,
                imm_0, imm_1, imm_msb,
                opcode_slti_flag, opcode_sltiu_flag,
                diff_marker_0, diff_marker_1, diff_marker_2, diff_marker_3,
                diff_val,
            },
            derived: {
                expected_opcode_id: opcode_slti_flag * constant(crate::instructions::Opcode::Slti as u32)
                    + opcode_sltiu_flag * constant(crate::instructions::Opcode::Sltiu as u32),
                // I-type immediate (airs.md 6.2)
                imm: imm_0 + pow2(8) * imm_1 + pow2(11) * imm_msb,
                // Sign-extended immediate limbs; limb 0 is imm_0, limb 3 = limb 2
                sext_imm_1: imm_1 + (pow2(8) - pow2(3)) * imm_msb,
                sext_imm_2: (pow2(8) - 1) * imm_msb,
                // Most significant limb of the comparison operand under the
                // active signedness
                sext_imm_msl_felt: opcode_sltiu_flag * sext_imm_2 - opcode_slti_flag * imm_msb,
                rs1_msl_gap: rs1_next_3 - rs1_msl_felt,
                rs1_msl_shifted: rs1_msl_felt + opcode_slti_flag * pow2(7),
                imm_1_doubled: 2 * imm_1,
                prefix_sum_final: diff_marker_0 + diff_marker_1 + diff_marker_2 + diff_marker_3,
                cmp_sign: 2 * cmp_result - 1,
                pc_next: pc + 4,
                clock_next: clock + 1,
                rs1_clock_diff: clock - rs1_clock_prev,
                rd_clock_diff: clock - rd_clock_prev,
            },
            constraints: {
                imm_msb * (1 - imm_msb),
                rs1_msl_gap * (pow2(8) - rs1_msl_gap),
                diff_marker_0 * (1 - diff_marker_0),
                diff_marker_1 * (1 - diff_marker_1),
                diff_marker_2 * (1 - diff_marker_2),
                diff_marker_3 * (1 - diff_marker_3),
                // Comparison scan from the most significant limb down (airs.md 6.3)
                (1 - diff_marker_3) * (cmp_sign * (sext_imm_msl_felt - rs1_msl_felt)),
                diff_marker_3 * (diff_val - cmp_sign * (sext_imm_msl_felt - rs1_msl_felt)),
                (1 - diff_marker_3 - diff_marker_2) * (cmp_sign * (sext_imm_2 - rs1_next_2)),
                diff_marker_2 * (diff_val - cmp_sign * (sext_imm_2 - rs1_next_2)),
                (1 - diff_marker_3 - diff_marker_2 - diff_marker_1)
                        * (cmp_sign * (sext_imm_1 - rs1_next_1)),
                diff_marker_1 * (diff_val - cmp_sign * (sext_imm_1 - rs1_next_1)),
                (1 - prefix_sum_final) * (cmp_sign * (imm_0 - rs1_next_0)),
                diff_marker_0 * (diff_val - cmp_sign * (imm_0 - rs1_next_0)),
                prefix_sum_final * (1 - prefix_sum_final),
                (1 - prefix_sum_final) * cmp_result,
                cmp_result * (1 - cmp_result),
            },
            lookups: {
                // Program access (I-type): Program(pc, opcode, rd_idx, rs1_idx, imm)
                -enabler * program_access(pc, expected_opcode_id, rd_addr, rs1_addr, imm),
                // Immediate limb ranges and the sign-shifted most significant limb.
                - enabler * range_check_8_8_4(rs1_msl_shifted, imm_0, imm_1_doubled),
                -enabler * registers_state(pc, clock),
                enabler * registers_state(pc_next, clock_next),
                // Read rs1 (REG_AS = 0).
                -enabler * memory_access(0, rs1_addr, rs1_clock_prev, rs1_prev_0, rs1_prev_1, rs1_prev_2, rs1_prev_3),
                enabler * memory_access(0, rs1_addr, clock, rs1_next_0, rs1_next_1, rs1_next_2, rs1_next_3),
                - enabler * range_check_20(rs1_clock_diff),
                // When the comparison scan fired, the limb difference is > 0.
                - prefix_sum_final * range_check_20(diff_val - 1),
                // Write rd := cmp_result (a single bit in limb 0).
                -enabler * memory_access(0, rd_addr, rd_clock_prev, rd_prev_0, rd_prev_1, rd_prev_2, rd_prev_3),
                enabler * memory_access(0, rd_addr, clock, cmp_result, 0, 0, 0),
                - enabler * range_check_20(rd_clock_diff),
            },
        },

        // ==========================================================================
        // 7. Branch Equal (beq/bne) - airs.md Section 7
        // ==========================================================================
        branch_eq: {
            committed: {
                clock, pc, rs1, rs2,
                imm_felt, cmp_result,
                diff_inv_marker_0, diff_inv_marker_1, diff_inv_marker_2, diff_inv_marker_3,
                opcode_beq_flag, opcode_bne_flag,
            },
            derived: {
                expected_opcode_id: opcode_beq_flag * constant(crate::instructions::Opcode::Beq as u32)
                    + opcode_bne_flag * constant(crate::instructions::Opcode::Bne as u32),
                // 1 when the operands must be equal under the active opcode
                cmp_eq: cmp_result * opcode_beq_flag + (1 - cmp_result) * opcode_bne_flag,
                // Inverse witness sum: cmp_eq plus marked limb differences must
                // be 1 on enabled rows (proves inequality when cmp_eq = 0)
                diff_inv_sum: cmp_eq
                    + (rs1_next_0 - rs2_next_0) * diff_inv_marker_0
                    + (rs1_next_1 - rs2_next_1) * diff_inv_marker_1
                    + (rs1_next_2 - rs2_next_2) * diff_inv_marker_2
                    + (rs1_next_3 - rs2_next_3) * diff_inv_marker_3,
                // Conditional branch target (airs.md 7.2)
                to_pc: pc + imm_felt * cmp_result + 4 * (1 - cmp_result),
                clock_next: clock + 1,
                rs1_clock_diff: clock - rs1_clock_prev,
                rs2_clock_diff: clock - rs2_clock_prev,
            },
            constraints: {
                cmp_result * (1 - cmp_result),
                // Equality forced limb-wise when cmp_eq fires
                cmp_eq * (rs1_next_0 - rs2_next_0),
                cmp_eq * (rs1_next_1 - rs2_next_1),
                cmp_eq * (rs1_next_2 - rs2_next_2),
                cmp_eq * (rs1_next_3 - rs2_next_3),
                enabler * (1 - diff_inv_sum),
            },
            lookups: {
                // Program access (B-type): Program(pc, opcode, rs1_idx, rs2_idx, imm)
                -enabler * program_access(pc, expected_opcode_id, rs1_addr, rs2_addr, imm_felt),
                // Read rs1 (REG_AS = 0).
                -enabler * memory_access(0, rs1_addr, rs1_clock_prev, rs1_prev_0, rs1_prev_1, rs1_prev_2, rs1_prev_3),
                enabler * memory_access(0, rs1_addr, clock, rs1_next_0, rs1_next_1, rs1_next_2, rs1_next_3),
                - enabler * range_check_20(rs1_clock_diff),
                // Read rs2.
                -enabler * memory_access(0, rs2_addr, rs2_clock_prev, rs2_prev_0, rs2_prev_1, rs2_prev_2, rs2_prev_3),
                enabler * memory_access(0, rs2_addr, clock, rs2_next_0, rs2_next_1, rs2_next_2, rs2_next_3),
                - enabler * range_check_20(rs2_clock_diff),
                // Conditional branch: pc moves to the selected target.
                -enabler * registers_state(pc, clock),
                enabler * registers_state(to_pc, clock_next),
            },
        },

        // ==========================================================================
        // 8. Branch Less Than (blt/bltu/bge/bgeu) - airs.md Section 8
        // ==========================================================================
        branch_lt: {
            committed: {
                clock, pc, rs1, rs2,
                rs1_msl_felt, rs2_msl_felt,
                imm_felt, cmp_result, cmp_lt,
                diff_marker_0, diff_marker_1, diff_marker_2, diff_marker_3,
                diff_val, branch_target,
                opcode_blt_flag, opcode_bltu_flag, opcode_bge_flag, opcode_bgeu_flag,
            },
            derived: {
                expected_opcode_id: opcode_blt_flag * constant(crate::instructions::Opcode::Blt as u32)
                    + opcode_bltu_flag * constant(crate::instructions::Opcode::Bltu as u32)
                    + opcode_bge_flag * constant(crate::instructions::Opcode::Bge as u32)
                    + opcode_bgeu_flag * constant(crate::instructions::Opcode::Bgeu as u32),
                lt: opcode_blt_flag + opcode_bltu_flag,
                ge: opcode_bge_flag + opcode_bgeu_flag,
                signed: opcode_blt_flag + opcode_bge_flag,
                rs1_msl_gap: rs1_next_3 - rs1_msl_felt,
                rs2_msl_gap: rs2_next_3 - rs2_msl_felt,
                rs1_msl_shifted: rs1_msl_felt + signed * pow2(7),
                rs2_msl_shifted: rs2_msl_felt + signed * pow2(7),
                prefix_sum_final: diff_marker_0 + diff_marker_1 + diff_marker_2 + diff_marker_3,
                lt_sign: 2 * cmp_lt - 1,
                clock_next: clock + 1,
                rs1_clock_diff: clock - rs1_clock_prev,
                rs2_clock_diff: clock - rs2_clock_prev,
            },
            constraints: {
                cmp_result * (1 - cmp_result),
                diff_marker_0 * (1 - diff_marker_0),
                diff_marker_1 * (1 - diff_marker_1),
                diff_marker_2 * (1 - diff_marker_2),
                diff_marker_3 * (1 - diff_marker_3),
                // Branch target, gated by enabler (airs.md 8.2)
                enabler * (branch_target - (pc + imm_felt * cmp_result + 4 * (1 - cmp_result))),
                rs1_msl_gap * (pow2(8) - rs1_msl_gap),
                rs2_msl_gap * (pow2(8) - rs2_msl_gap),
                // Comparison scan from the most significant limb down
                (1 - diff_marker_3) * (lt_sign * (rs2_msl_felt - rs1_msl_felt)),
                diff_marker_3 * (diff_val - lt_sign * (rs2_msl_felt - rs1_msl_felt)),
                (1 - diff_marker_3 - diff_marker_2) * (lt_sign * (rs2_next_2 - rs1_next_2)),
                diff_marker_2 * (diff_val - lt_sign * (rs2_next_2 - rs1_next_2)),
                (1 - diff_marker_3 - diff_marker_2 - diff_marker_1)
                        * (lt_sign * (rs2_next_1 - rs1_next_1)),
                diff_marker_1 * (diff_val - lt_sign * (rs2_next_1 - rs1_next_1)),
                (1 - prefix_sum_final) * (lt_sign * (rs2_next_0 - rs1_next_0)),
                diff_marker_0 * (diff_val - lt_sign * (rs2_next_0 - rs1_next_0)),
                prefix_sum_final * (1 - prefix_sum_final),
                (1 - prefix_sum_final) * cmp_lt,
                // cmp_lt selects less-than under lt opcodes, not-less-than
                // under ge opcodes
                cmp_lt - (cmp_result * lt + (1 - cmp_result) * ge),
            },
            lookups: {
                // Program access (B-type): Program(pc, opcode, rs1_idx, rs2_idx, imm)
                -enabler * program_access(pc, expected_opcode_id, rs1_addr, rs2_addr, imm_felt),
                // Conditional branch: pc moves to the selected target.
                -enabler * registers_state(pc, clock),
                enabler * registers_state(branch_target, clock_next),
                // Read rs1 (REG_AS = 0).
                -enabler * memory_access(0, rs1_addr, rs1_clock_prev, rs1_prev_0, rs1_prev_1, rs1_prev_2, rs1_prev_3),
                enabler * memory_access(0, rs1_addr, clock, rs1_next_0, rs1_next_1, rs1_next_2, rs1_next_3),
                - enabler * range_check_20(rs1_clock_diff),
                // Read rs2.
                -enabler * memory_access(0, rs2_addr, rs2_clock_prev, rs2_prev_0, rs2_prev_1, rs2_prev_2, rs2_prev_3),
                enabler * memory_access(0, rs2_addr, clock, rs2_next_0, rs2_next_1, rs2_next_2, rs2_next_3),
                - enabler * range_check_20(rs2_clock_diff),
                // Most significant limbs shifted into unsigned range under the
                // signed-comparison convention.
                - enabler * range_check_8_8(rs1_msl_shifted, rs2_msl_shifted),
                // When the comparison scan fired, the limb difference is > 0.
                - prefix_sum_final * range_check_20(diff_val - 1),
            },
        },

        // ==========================================================================
        // 9. LUI - airs.md Section 9
        // ==========================================================================
        lui: {
            committed: {
                clock, pc, rd,
                imm_0, imm_1, imm_2,
            },
            derived: {
                // imm = imm_0 + 2^4 * imm_1 + 2^12 * imm_2 (U-type immediate, airs.md 9.2)
                imm: imm_0 + pow2(4) * imm_1 + pow2(12) * imm_2,
                pc_next: pc + 4,
                clock_next: clock + 1,
                // Limb 1 of the value written to rd: imm << 12 has limbs (0, imm_0 * 2^4, imm_1, imm_2)
                rd_val_1: imm_0 * pow2(4),
                rd_clock_diff: clock - rd_clock_prev,
            },
            lookups: {
                // Program access (U-type): Program(pc, LUI, rd_idx, imm, 0)
                -enabler * program_access(pc, constant(crate::instructions::Opcode::Lui as u32), rd_addr, imm, 0),
                // Register state transition: clock advances, pc steps by 4.
                -enabler * registers_state(pc, clock),
                enabler * registers_state(pc_next, clock_next),
                // U-type immediate limb ranges.
                - enabler * range_check_8_8_4(imm_1, imm_2, imm_0),
                // Write to rd (REG_AS = 0): rd := imm << 12.
                -enabler * memory_access(0, rd_addr, rd_clock_prev, rd_prev_0, rd_prev_1, rd_prev_2, rd_prev_3),
                enabler * memory_access(0, rd_addr, clock, 0, rd_val_1, imm_1, imm_2),
                - enabler * range_check_20(rd_clock_diff),
            },
        },

        // ==========================================================================
        // 10. AUIPC - airs.md Section 10
        // ==========================================================================
        auipc: {
            committed: {
                clock, pc, rd,
                imm_felt,
            },
            derived: {
                rd_felt: rd_next_0 + pow2(8) * rd_next_1 + pow2(16) * rd_next_2 + pow2(24) * rd_next_3,
                pc_next: pc + 4,
                clock_next: clock + 1,
                rd_clock_diff: clock - rd_clock_prev,
            },
            constraints: {
                // rd = pc + imm (airs.md 10.2)
                rd_felt - (pc + imm_felt),
            },
            lookups: {
                // Program access (U-type): Program(pc, AUIPC, rd_idx, imm, 0)
                -enabler * program_access(pc, constant(crate::instructions::Opcode::Auipc as u32), rd_addr, imm_felt, 0),
                -enabler * registers_state(pc, clock),
                enabler * registers_state(pc_next, clock_next),
                // rd = pc + imm is an M31: middle limbs are bytes, outer pair is
                // checked as an M31 split.
                - enabler * range_check_8_8(rd_next_1, rd_next_2),
                - enabler * range_check_m31(rd_next_0, rd_next_3),
                // Write to rd (REG_AS = 0).
                -enabler * memory_access(0, rd_addr, rd_clock_prev, rd_prev_0, rd_prev_1, rd_prev_2, rd_prev_3),
                enabler * memory_access(0, rd_addr, clock, rd_next_0, rd_next_1, rd_next_2, rd_next_3),
                - enabler * range_check_20(rd_clock_diff),
            },
        },

        // ==========================================================================
        // 11. JALR - airs.md Section 11
        // ==========================================================================
        jalr: {
            committed: {
                clock, pc, rd, rs1,
                to_pc_over_two, to_pc_lsb,
                imm_felt,
            },
            derived: {
                rs1_felt: rs1_next_0 + pow2(8) * rs1_next_1 + pow2(16) * rs1_next_2 + pow2(24) * rs1_next_3,
                rd_felt: rd_next_0 + pow2(8) * rd_next_1 + pow2(16) * rd_next_2 + pow2(24) * rd_next_3,
                // Jump target, even-aligned (airs.md 11.2)
                jump_target: 2 * to_pc_over_two,
                clock_next: clock + 1,
                rs1_clock_diff: clock - rs1_clock_prev,
                rd_clock_diff: clock - rd_clock_prev,
            },
            constraints: {
                to_pc_lsb * (1 - to_pc_lsb),
                // 2 * to_pc_over_two + to_pc_lsb = rs1 + imm
                2 * to_pc_over_two + to_pc_lsb - (rs1_felt + imm_felt),
                // rd = pc + 4, gated by rd_addr (x0 writes discarded)
                enabler * rd_addr * (rd_felt - (pc + 4)),
            },
            lookups: {
                // Program access (I-type): Program(pc, JALR, rd_idx, rs1_idx, imm)
                -enabler * program_access(pc, constant(crate::instructions::Opcode::Jalr as u32), rd_addr, rs1_addr, imm_felt),
                // Read rs1 (REG_AS = 0).
                -enabler * memory_access(0, rs1_addr, rs1_clock_prev, rs1_prev_0, rs1_prev_1, rs1_prev_2, rs1_prev_3),
                enabler * memory_access(0, rs1_addr, clock, rs1_next_0, rs1_next_1, rs1_next_2, rs1_next_3),
                - enabler * range_check_20(rs1_clock_diff),
                // rs1 is an M31 (the jump target must be a valid pc).
                - enabler * range_check_m31(rs1_next_0, rs1_next_3),
                // Jump: pc moves to the even-aligned target.
                -enabler * registers_state(pc, clock),
                enabler * registers_state(jump_target, clock_next),
                // rd = pc + 4 is an M31.
                - enabler * range_check_8_8(rd_next_1, rd_next_2),
                - enabler * range_check_m31(rd_next_0, rd_next_3),
                // Write rd.
                -enabler * memory_access(0, rd_addr, rd_clock_prev, rd_prev_0, rd_prev_1, rd_prev_2, rd_prev_3),
                enabler * memory_access(0, rd_addr, clock, rd_next_0, rd_next_1, rd_next_2, rd_next_3),
                - enabler * range_check_20(rd_clock_diff),
            },
        },

        // ==========================================================================
        // 12. JAL - airs.md Section 12
        // ==========================================================================
        jal: {
            committed: {
                clock, pc, rd,
                imm_felt,
            },
            derived: {
                rd_felt: rd_next_0 + pow2(8) * rd_next_1 + pow2(16) * rd_next_2 + pow2(24) * rd_next_3,
                jump_target: pc + imm_felt,
                clock_next: clock + 1,
                rd_clock_diff: clock - rd_clock_prev,
            },
            lookups: {
                // Program access (U-type): Program(pc, JAL, rd_idx, imm, 0)
                -enabler * program_access(pc, constant(crate::instructions::Opcode::Jal as u32), rd_addr, imm_felt, 0),
                // Unconditional jump: pc moves to pc + imm.
                -enabler * registers_state(pc, clock),
                enabler * registers_state(jump_target, clock_next),
                // rd = pc + 4 is an M31.
                - enabler * range_check_8_8(rd_next_1, rd_next_2),
                - enabler * range_check_m31(rd_next_0, rd_next_3),
                // Write to rd (REG_AS = 0).
                -enabler * memory_access(0, rd_addr, rd_clock_prev, rd_prev_0, rd_prev_1, rd_prev_2, rd_prev_3),
                enabler * memory_access(0, rd_addr, clock, rd_next_0, rd_next_1, rd_next_2, rd_next_3),
                - enabler * range_check_20(rd_clock_diff),
            },
            constraints: {
                // rd = pc + 4, gated by enabler (padding) and rd_addr (x0
                // writes are discarded, airs.md 12.2)
                enabler * rd_addr * (rd_felt - (pc + 4)),
            },
        },

        // ==========================================================================
        // 13. Load/Store (lb/lbu/lh/lhu/lw/sb/sh/sw) - airs.md Section 13
        // ==========================================================================
        load_store: {
            committed: {
                clock, pc, dst, rs1, src,
                r2_idx, imm_felt, src_msb,
                shift_amount,
                src_addr_selector, dst_addr_selector,
                marker_0, marker_1, marker_2, marker_3,
                opcode_lb_flag, opcode_lh_flag, opcode_lbu_flag, opcode_lhu_flag, opcode_lw_flag,
                opcode_sb_flag, opcode_sh_flag, opcode_sw_flag,
            },
            derived: {
                expected_opcode_id: opcode_lb_flag * constant(crate::instructions::Opcode::Lb as u32)
                    + opcode_lh_flag * constant(crate::instructions::Opcode::Lh as u32)
                    + opcode_lbu_flag * constant(crate::instructions::Opcode::Lbu as u32)
                    + opcode_lhu_flag * constant(crate::instructions::Opcode::Lhu as u32)
                    + opcode_lw_flag * constant(crate::instructions::Opcode::Lw as u32)
                    + opcode_sb_flag * constant(crate::instructions::Opcode::Sb as u32)
                    + opcode_sh_flag * constant(crate::instructions::Opcode::Sh as u32)
                    + opcode_sw_flag * constant(crate::instructions::Opcode::Sw as u32),
                opcode_b_flag: opcode_lbu_flag + opcode_lb_flag + opcode_sb_flag,
                opcode_h_flag: opcode_lhu_flag + opcode_lh_flag + opcode_sh_flag,
                opcode_w_flag: opcode_lw_flag + opcode_sw_flag,
                is_signed: opcode_lb_flag + opcode_lh_flag,
                load_b_flag: opcode_lb_flag + opcode_lbu_flag,
                load_h_flag: opcode_lh_flag + opcode_lhu_flag,
                is_store: opcode_sb_flag + opcode_sh_flag + opcode_sw_flag,
                is_load: enabler - is_store,
                // Memory address space selectors: registers are 0, RW memory 1
                src_as: is_load,
                dst_as: is_store,
                mem_addr: rs1_next_0 + pow2(8) * rs1_next_1 + pow2(16) * rs1_next_2
                    + pow2(24) * rs1_next_3 + imm_felt,
                sum_markers: marker_0 + marker_1 + marker_2 + marker_3,
                shift_id: marker_1 + 2 * marker_2 + 3 * marker_3,
                // Sign-extension fill byte for signed loads
                signed_mask: is_signed * src_msb * (pow2(8) - 1),
                // Selected aligned memory address over 4, for the range check
                aligned_addr_quarter: (src_addr_selector + dst_addr_selector - r2_idx) * inv(4),
                pc_next: pc + 4,
                clock_next: clock + 1,
                rs1_clock_diff: clock - rs1_clock_prev,
                src_clock_diff: clock - src_clock_prev,
                dst_clock_diff: clock - dst_clock_prev,
            },
            constraints: {
                marker_0 * (1 - marker_0),
                marker_1 * (1 - marker_1),
                marker_2 * (1 - marker_2),
                marker_3 * (1 - marker_3),
                // Shift amount: byte ops use shift_id, half-word ops (shift_id 1
                // or 5) use (shift_id - 1) / 2 (airs.md 13.3)
                shift_amount - (opcode_b_flag * shift_id
                    + opcode_h_flag * (shift_id - 1) * inv(2)),
                // Load/store dependent source and destination addresses
                src_addr_selector
                    - (is_load * (mem_addr - shift_amount) + is_store * r2_idx),
                dst_addr_selector
                    - (is_load * r2_idx + is_store * (mem_addr - shift_amount)),
                opcode_b_flag * (1 - sum_markers),
                opcode_h_flag * (2 - sum_markers),
                opcode_h_flag * (1 - shift_id) * (5 - shift_id),
                // Byte loads sign-extend the upper bytes
                load_b_flag * (signed_mask - dst_next_1),
                load_b_flag * (signed_mask - dst_next_2),
                load_b_flag * (signed_mask - dst_next_3),
                // Byte selection: loads pull memory byte i into register byte 0,
                // stores push register byte 0 into memory byte i
                load_b_flag * (dst_next_0 - src_next_0) * marker_0,
                opcode_sb_flag * (dst_next_0 - src_next_0) * marker_0,
                load_b_flag * (dst_next_0 - src_next_1) * marker_1,
                opcode_sb_flag * (dst_next_1 - src_next_0) * marker_1,
                load_b_flag * (dst_next_0 - src_next_2) * marker_2,
                opcode_sb_flag * (dst_next_2 - src_next_0) * marker_2,
                load_b_flag * (dst_next_0 - src_next_3) * marker_3,
                opcode_sb_flag * (dst_next_3 - src_next_0) * marker_3,
                // Half-word loads sign-extend the upper half
                load_h_flag * (signed_mask - dst_next_2),
                load_h_flag * (signed_mask - dst_next_3),
                // Half-word selection by shift_id (1 = low half, 5 = high half)
                load_h_flag * (5 - shift_id) * inv(4) * (dst_next_0 - src_next_0),
                load_h_flag * (5 - shift_id) * inv(4) * (dst_next_1 - src_next_1),
                load_h_flag * (shift_id - 1) * inv(4) * (dst_next_0 - src_next_2),
                load_h_flag * (shift_id - 1) * inv(4) * (dst_next_1 - src_next_3),
                opcode_sh_flag * (5 - shift_id) * inv(4) * (dst_next_0 - src_next_0),
                opcode_sh_flag * (5 - shift_id) * inv(4) * (dst_next_1 - src_next_1),
                opcode_sh_flag * (shift_id - 1) * inv(4) * (dst_next_2 - src_next_0),
                opcode_sh_flag * (shift_id - 1) * inv(4) * (dst_next_3 - src_next_1),
                // Word ops copy all bytes
                opcode_w_flag * (dst_next_0 - src_next_0),
                opcode_w_flag * (dst_next_1 - src_next_1),
                opcode_w_flag * (dst_next_2 - src_next_2),
                opcode_w_flag * (dst_next_3 - src_next_3),
            },
            lookups: {
                // Program access (I-type for loads, S-type for stores):
                // Program(pc, opcode, rs1_idx, r2_idx, imm)
                -enabler * program_access(pc, expected_opcode_id, rs1_addr, r2_idx, imm_felt),
                -enabler * registers_state(pc, clock),
                enabler * registers_state(pc_next, clock_next),
                // Read rs1, the base address (REG_AS = 0).
                -enabler * memory_access(0, rs1_addr, rs1_clock_prev, rs1_prev_0, rs1_prev_1, rs1_prev_2, rs1_prev_3),
                enabler * memory_access(0, rs1_addr, clock, rs1_next_0, rs1_next_1, rs1_next_2, rs1_next_3),
                - enabler * range_check_20(rs1_clock_diff),
                // The aligned address is a multiple of 4 within the address space.
                - enabler * range_check_20(aligned_addr_quarter),
                // The base address is an M31.
                - enabler * range_check_m31(rs1_next_0, rs1_next_3),
                // Read the source (memory word for loads, register for stores).
                -enabler * memory_access(src_as, src_addr_selector, src_clock_prev, src_prev_0, src_prev_1, src_prev_2, src_prev_3),
                enabler * memory_access(src_as, src_addr_selector, clock, src_next_0, src_next_1, src_next_2, src_next_3),
                - enabler * range_check_20(src_clock_diff),
                // Write the destination (register for loads, memory for stores).
                -enabler * memory_access(dst_as, dst_addr_selector, dst_clock_prev, dst_prev_0, dst_prev_1, dst_prev_2, dst_prev_3),
                enabler * memory_access(dst_as, dst_addr_selector, clock, dst_next_0, dst_next_1, dst_next_2, dst_next_3),
                - enabler * range_check_20(dst_clock_diff),
            },
        },

        // ==========================================================================
        // 14. MUL - airs.md Section 14
        // ==========================================================================
        mul: {
            committed: {
                clock, pc, rd, rs1, rs2,
            },
            derived: {
                pc_next: pc + 4,
                clock_next: clock + 1,
                rs1_clock_diff: clock - rs1_clock_prev,
                rs2_clock_diff: clock - rs2_clock_prev,
                rd_clock_diff: clock - rd_clock_prev,
                // Schoolbook carry chain of rd = (rs1 * rs2) mod 2^32 over 8-bit
                // limbs (airs.md 14.2); each carry is range-checked, not boolean
                carry_0: (rs1_next_0 * rs2_next_0 - rd_next_0) * inv(pow2(8)),
                carry_1: (carry_0 + rs1_next_1 * rs2_next_0 + rs1_next_0 * rs2_next_1 - rd_next_1)
                        * inv(pow2(8)),
                carry_2: (carry_1 + rs1_next_2 * rs2_next_0 + rs1_next_1 * rs2_next_1
                        + rs1_next_0 * rs2_next_2 - rd_next_2) * inv(pow2(8)),
                carry_3: (carry_2 + rs1_next_3 * rs2_next_0 + rs1_next_2 * rs2_next_1
                        + rs1_next_1 * rs2_next_2 + rs1_next_0 * rs2_next_3 - rd_next_3)
                        * inv(pow2(8)),
            },
            lookups: {
                // Quadratic carry denominators: every fraction must stay in a
                // singleton batch to hold the constraint degree bound.
                batch: 1,
                // Program access (R-type): Program(pc, MUL, rd_idx, rs1_idx, rs2_idx)
                -enabler * program_access(pc, constant(crate::instructions::Opcode::Mul as u32), rd_addr, rs1_addr, rs2_addr),
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
                // rd limbs are bytes and schoolbook carries fit 11 bits (the
                // limb-1 carry honestly reaches 509 for 0xFFFFFFFF operands, so
                // 8 bits is not enough).
                - enabler * range_check_8_11(rd_next_0, carry_0),
                - enabler * range_check_8_11(rd_next_1, carry_1),
                - enabler * range_check_8_11(rd_next_2, carry_2),
                - enabler * range_check_8_11(rd_next_3, carry_3),
                // Write rd.
                -enabler * memory_access(0, rd_addr, rd_clock_prev, rd_prev_0, rd_prev_1, rd_prev_2, rd_prev_3),
                enabler * memory_access(0, rd_addr, clock, rd_next_0, rd_next_1, rd_next_2, rd_next_3),
                - enabler * range_check_20(rd_clock_diff),
            },
        },

        // ==========================================================================
        // 15. MULH (mulh/mulhsu/mulhu) - airs.md Section 15
        // ==========================================================================
        mulh: {
            committed: {
                clock, pc, rd, rs1, rs2,
                rd_high_0, rd_high_1, rd_high_2, rd_high_3,
                rs1_sign, rs2_sign,
                opcode_mulh_flag, opcode_mulhsu_flag, opcode_mulhu_flag,
            },
            derived: {
                expected_opcode_id: opcode_mulh_flag * constant(crate::instructions::Opcode::Mulh as u32)
                    + opcode_mulhsu_flag * constant(crate::instructions::Opcode::Mulhsu as u32)
                    + opcode_mulhu_flag * constant(crate::instructions::Opcode::Mulhu as u32),
                pc_next: pc + 4,
                clock_next: clock + 1,
                rs1_clock_diff: clock - rs1_clock_prev,
                rs2_clock_diff: clock - rs2_clock_prev,
                rd_clock_diff: clock - rd_clock_prev,
                // Sign-extended 64-bit operands: top limbs gain the sign bit,
                // limbs 4..7 are the sign fill (airs.md 15.2)
                rs1_top: rs1_next_3 + rs1_sign * pow2(7),
                rs2_top: rs2_next_3 + rs2_sign * pow2(7),
                rs1_fill: rs1_sign * (pow2(8) - 1),
                rs2_fill: rs2_sign * (pow2(8) - 1),
                carry_0: (rs1_next_0 * rs2_next_0 - rd_high_0) * inv(pow2(8)),
                carry_1: (carry_0 + rs1_next_0 * rs2_next_1 + rs1_next_1 * rs2_next_0 - rd_high_1) * inv(pow2(8)),
                carry_2: (carry_1 + rs1_next_0 * rs2_next_2 + rs1_next_1 * rs2_next_1 + rs1_next_2 * rs2_next_0 - rd_high_2) * inv(pow2(8)),
                carry_3: (carry_2 + rs1_next_0 * rs2_top + rs1_next_1 * rs2_next_2 + rs1_next_2 * rs2_next_1 + rs1_top * rs2_next_0 - rd_high_3) * inv(pow2(8)),
                carry_4: (carry_3 + rs1_next_0 * rs2_fill + rs1_next_1 * rs2_top + rs1_next_2 * rs2_next_2 + rs1_top * rs2_next_1 + rs1_fill * rs2_next_0 - rd_next_0) * inv(pow2(8)),
                carry_5: (carry_4 + rs1_next_0 * rs2_fill + rs1_next_1 * rs2_fill + rs1_next_2 * rs2_top + rs1_top * rs2_next_2 + rs1_fill * rs2_next_1 + rs1_fill * rs2_next_0 - rd_next_1) * inv(pow2(8)),
                carry_6: (carry_5 + rs1_next_0 * rs2_fill + rs1_next_1 * rs2_fill + rs1_next_2 * rs2_fill + rs1_top * rs2_top + rs1_fill * rs2_next_2 + rs1_fill * rs2_next_1 + rs1_fill * rs2_next_0 - rd_next_2) * inv(pow2(8)),
                carry_7: (carry_6 + rs1_next_0 * rs2_fill + rs1_next_1 * rs2_fill + rs1_next_2 * rs2_fill + rs1_top * rs2_fill + rs1_fill * rs2_top + rs1_fill * rs2_next_2 + rs1_fill * rs2_next_1 + rs1_fill * rs2_next_0 - rd_next_3) * inv(pow2(8)),
            },
            constraints: {
                rs1_sign * (1 - rs1_sign),
                rs2_sign * (1 - rs2_sign),
                // Unsigned operands force their sign bits to zero
                (opcode_mulhsu_flag + opcode_mulhu_flag) * rs2_sign,
                opcode_mulhu_flag * rs1_sign,
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
                // 64-bit product carries and both result halves are bytes.
                // Result limbs (both halves) are bytes and the 64-bit schoolbook
                // carries fit 11 bits (up to 8 partial products per limb exceed
                // 8 bits for maximal operands).
                - enabler * range_check_8_11(rd_next_0, carry_0),
                - enabler * range_check_8_11(rd_next_1, carry_1),
                - enabler * range_check_8_11(rd_next_2, carry_2),
                - enabler * range_check_8_11(rd_next_3, carry_3),
                - enabler * range_check_8_11(rd_high_0, carry_4),
                - enabler * range_check_8_11(rd_high_1, carry_5),
                - enabler * range_check_8_11(rd_high_2, carry_6),
                - enabler * range_check_8_11(rd_high_3, carry_7),
                // Write rd.
                -enabler * memory_access(0, rd_addr, rd_clock_prev, rd_prev_0, rd_prev_1, rd_prev_2, rd_prev_3),
                enabler * memory_access(0, rd_addr, clock, rd_next_0, rd_next_1, rd_next_2, rd_next_3),
                - enabler * range_check_20(rd_clock_diff),
            },
        },

        // ==========================================================================
        // 16. DIV (div/divu/rem/remu) - airs.md Section 16
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
                // |r| vs |c| limb differences under the divisor sign (airs.md 16.2)
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
                // limbs (airs.md 16.2): carry_k integral and below 2^11 makes the
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
                // Zero divisor: all-one quotient, zero divisor limbs (airs.md 16.3)
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
                // schoolbook carries fit 11 bits (airs.md 16.3).
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
