//! Immediate shift opcodes (slli/srli/srai) as a felt function (airs.md
//! Section 4). The truncated immediate encodes the decoded shift amount;
//! one-hot bit/limb markers chain the shifted-byte carries with sign fill on
//! arithmetic right shifts. The flag sum is the row activity indicator
//! `enabler()`.

stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [],
    embedded_component: true,

    relation program_access(5);
    relation registers_state(2);
    relation memory_access(7);
    relation range_check_20(1);
    relation range_check_8_8(2);

    fn shifts_imm(
        clock,
        pc,
        rd_addr,
        rd_prev_0,
        rd_prev_1,
        rd_prev_2,
        rd_prev_3,
        rd_clock_prev,
        rd_next_0,
        rd_next_1,
        rd_next_2,
        rd_next_3,
        rs1_addr,
        rs1_prev_0,
        rs1_prev_1,
        rs1_prev_2,
        rs1_prev_3,
        rs1_clock_prev,
        rs1_next_0,
        rs1_next_1,
        rs1_next_2,
        rs1_next_3,
        rs1_sign,
        imm_truncated,
        opcode_sll_flag,
        opcode_srl_flag,
        opcode_sra_flag,
        bit_multiplier_left,
        bit_multiplier_right,
        bit_shift_marker_0,
        bit_shift_marker_1,
        bit_shift_marker_2,
        bit_shift_marker_3,
        bit_shift_marker_4,
        bit_shift_marker_5,
        bit_shift_marker_6,
        bit_shift_marker_7,
        limb_shift_marker_0,
        limb_shift_marker_1,
        limb_shift_marker_2,
        limb_shift_marker_3,
        bit_shift_carry_0,
        bit_shift_carry_1,
        bit_shift_carry_2,
        bit_shift_carry_3
    ) {
        let row_enabler = opcode_sll_flag + opcode_srl_flag + opcode_sra_flag;
        let expected_opcode_id = opcode_sll_flag * constant(crate::instructions::Opcode::Slli as u32)
                    + opcode_srl_flag * constant(crate::instructions::Opcode::Srli as u32)
                    + opcode_sra_flag * constant(crate::instructions::Opcode::Srai as u32);
        let right_shift = opcode_srl_flag + opcode_sra_flag;
        let bit_multiplier = bit_shift_marker_0 + 2 * bit_shift_marker_1 + 4 * bit_shift_marker_2
                    + 8 * bit_shift_marker_3 + 16 * bit_shift_marker_4 + 32 * bit_shift_marker_5
                    + 64 * bit_shift_marker_6 + 128 * bit_shift_marker_7;
        let bit_shift = bit_shift_marker_1 + 2 * bit_shift_marker_2 + 3 * bit_shift_marker_3
                    + 4 * bit_shift_marker_4 + 5 * bit_shift_marker_5 + 6 * bit_shift_marker_6
                    + 7 * bit_shift_marker_7;
        let limb_shift = limb_shift_marker_1 + 2 * limb_shift_marker_2 + 3 * limb_shift_marker_3;
        let shift_amount = pow2(3) * limb_shift + bit_shift;
        let bit_marker_sum = bit_shift_marker_0 + bit_shift_marker_1 + bit_shift_marker_2 + bit_shift_marker_3
                    + bit_shift_marker_4 + bit_shift_marker_5 + bit_shift_marker_6
                    + bit_shift_marker_7;
        let limb_marker_sum = limb_shift_marker_0 + limb_shift_marker_1 + limb_shift_marker_2
                    + limb_shift_marker_3;
        let pc_next = pc + 4;
        let clock_next = clock + 1;
        let rs1_clock_diff = clock - rs1_clock_prev;
        let rd_clock_diff = clock - rd_clock_prev;

        constrain rs1_sign * (1 - rs1_sign);
        constrain bit_shift_marker_0 * (1 - bit_shift_marker_0);
        constrain bit_shift_marker_1 * (1 - bit_shift_marker_1);
        constrain bit_shift_marker_2 * (1 - bit_shift_marker_2);
        constrain bit_shift_marker_3 * (1 - bit_shift_marker_3);
        constrain bit_shift_marker_4 * (1 - bit_shift_marker_4);
        constrain bit_shift_marker_5 * (1 - bit_shift_marker_5);
        constrain bit_shift_marker_6 * (1 - bit_shift_marker_6);
        constrain bit_shift_marker_7 * (1 - bit_shift_marker_7);
        constrain limb_shift_marker_0 * (1 - limb_shift_marker_0);
        constrain limb_shift_marker_1 * (1 - limb_shift_marker_1);
        constrain limb_shift_marker_2 * (1 - limb_shift_marker_2);
        constrain limb_shift_marker_3 * (1 - limb_shift_marker_3);
        constrain bit_marker_sum - row_enabler;
        constrain limb_marker_sum - row_enabler;
        constrain bit_multiplier_left - opcode_sll_flag * bit_multiplier;
        constrain bit_multiplier_right - right_shift * bit_multiplier;
        constrain imm_truncated - shift_amount;
        constrain opcode_sll_flag * limb_shift_marker_0 * (rd_next_0 + pow2(8) * bit_shift_carry_0)
                    - limb_shift_marker_0 * rs1_next_0 * bit_multiplier_left;
        constrain opcode_sll_flag * limb_shift_marker_0 * (rd_next_1 - (bit_shift_carry_0 - pow2(8) * bit_shift_carry_1))
                    - limb_shift_marker_0 * rs1_next_1 * bit_multiplier_left;
        constrain opcode_sll_flag * limb_shift_marker_0 * (rd_next_2 - (bit_shift_carry_1 - pow2(8) * bit_shift_carry_2))
                    - limb_shift_marker_0 * rs1_next_2 * bit_multiplier_left;
        constrain opcode_sll_flag * limb_shift_marker_0 * (rd_next_3 - (bit_shift_carry_2 - pow2(8) * bit_shift_carry_3))
                    - limb_shift_marker_0 * rs1_next_3 * bit_multiplier_left;
        constrain opcode_sll_flag * limb_shift_marker_1 * rd_next_0;
        constrain opcode_sll_flag * limb_shift_marker_1 * (rd_next_1 + pow2(8) * bit_shift_carry_0)
                    - limb_shift_marker_1 * rs1_next_0 * bit_multiplier_left;
        constrain opcode_sll_flag * limb_shift_marker_1 * (rd_next_2 - (bit_shift_carry_0 - pow2(8) * bit_shift_carry_1))
                    - limb_shift_marker_1 * rs1_next_1 * bit_multiplier_left;
        constrain opcode_sll_flag * limb_shift_marker_1 * (rd_next_3 - (bit_shift_carry_1 - pow2(8) * bit_shift_carry_2))
                    - limb_shift_marker_1 * rs1_next_2 * bit_multiplier_left;
        constrain opcode_sll_flag * limb_shift_marker_2 * rd_next_0;
        constrain opcode_sll_flag * limb_shift_marker_2 * rd_next_1;
        constrain opcode_sll_flag * limb_shift_marker_2 * (rd_next_2 + pow2(8) * bit_shift_carry_0)
                    - limb_shift_marker_2 * rs1_next_0 * bit_multiplier_left;
        constrain opcode_sll_flag * limb_shift_marker_2 * (rd_next_3 - (bit_shift_carry_0 - pow2(8) * bit_shift_carry_1))
                    - limb_shift_marker_2 * rs1_next_1 * bit_multiplier_left;
        constrain opcode_sll_flag * limb_shift_marker_3 * rd_next_0;
        constrain opcode_sll_flag * limb_shift_marker_3 * rd_next_1;
        constrain opcode_sll_flag * limb_shift_marker_3 * rd_next_2;
        constrain opcode_sll_flag * limb_shift_marker_3 * (rd_next_3 + pow2(8) * bit_shift_carry_0)
                    - limb_shift_marker_3 * rs1_next_0 * bit_multiplier_left;
        constrain limb_shift_marker_0 * (bit_shift_carry_1 * right_shift * pow2(8)
                    + right_shift * (rs1_next_0 - bit_shift_carry_0)
                    - rd_next_0 * bit_multiplier_right);
        constrain limb_shift_marker_0 * (bit_shift_carry_2 * right_shift * pow2(8)
                    + right_shift * (rs1_next_1 - bit_shift_carry_1)
                    - rd_next_1 * bit_multiplier_right);
        constrain limb_shift_marker_0 * (bit_shift_carry_3 * right_shift * pow2(8)
                    + right_shift * (rs1_next_2 - bit_shift_carry_2)
                    - rd_next_2 * bit_multiplier_right);
        constrain limb_shift_marker_0 * (rs1_sign * (bit_multiplier_right - 1) * pow2(8)
                    + right_shift * (rs1_next_3 - bit_shift_carry_3)
                    - rd_next_3 * bit_multiplier_right);
        constrain limb_shift_marker_1 * (bit_shift_carry_2 * right_shift * pow2(8)
                    + right_shift * (rs1_next_1 - bit_shift_carry_1)
                    - rd_next_0 * bit_multiplier_right);
        constrain limb_shift_marker_1 * (bit_shift_carry_3 * right_shift * pow2(8)
                    + right_shift * (rs1_next_2 - bit_shift_carry_2)
                    - rd_next_1 * bit_multiplier_right);
        constrain limb_shift_marker_1 * (rs1_sign * (bit_multiplier_right - 1) * pow2(8)
                    + right_shift * (rs1_next_3 - bit_shift_carry_3)
                    - rd_next_2 * bit_multiplier_right);
        constrain right_shift * limb_shift_marker_1 * (rd_next_3 - rs1_sign * (pow2(8) - 1));
        constrain limb_shift_marker_2 * (bit_shift_carry_3 * right_shift * pow2(8)
                    + right_shift * (rs1_next_2 - bit_shift_carry_2)
                    - rd_next_0 * bit_multiplier_right);
        constrain limb_shift_marker_2 * (rs1_sign * (bit_multiplier_right - 1) * pow2(8)
                    + right_shift * (rs1_next_3 - bit_shift_carry_3)
                    - rd_next_1 * bit_multiplier_right);
        constrain right_shift * limb_shift_marker_2 * (rd_next_2 - rs1_sign * (pow2(8) - 1));
        constrain right_shift * limb_shift_marker_2 * (rd_next_3 - rs1_sign * (pow2(8) - 1));
        constrain limb_shift_marker_3 * (rs1_sign * (bit_multiplier_right - 1) * pow2(8)
                    + right_shift * (rs1_next_3 - bit_shift_carry_3)
                    - rd_next_0 * bit_multiplier_right);
        constrain right_shift * limb_shift_marker_3 * (rd_next_1 - rs1_sign * (pow2(8) - 1));
        constrain right_shift * limb_shift_marker_3 * (rd_next_2 - rs1_sign * (pow2(8) - 1));
        constrain right_shift * limb_shift_marker_3 * (rd_next_3 - rs1_sign * (pow2(8) - 1));

        consume program_access(pc, expected_opcode_id, rd_addr, rs1_addr, imm_truncated);
        consume registers_state(pc, clock);
        emit registers_state(pc_next, clock_next);
        consume memory_access(constant(0), rs1_addr, rs1_clock_prev, rs1_prev_0, rs1_prev_1, rs1_prev_2, rs1_prev_3);
        emit memory_access(constant(0), rs1_addr, clock, rs1_next_0, rs1_next_1, rs1_next_2, rs1_next_3);
        consume range_check_20(rs1_clock_diff);
        consume range_check_8_8(bit_multiplier - row_enabler - bit_shift_carry_0, bit_multiplier - row_enabler - bit_shift_carry_1);
        consume range_check_8_8(bit_multiplier - row_enabler - bit_shift_carry_2, bit_multiplier - row_enabler - bit_shift_carry_3);
        consume range_check_8_8(rd_next_0, rd_next_1);
        consume range_check_8_8(rd_next_2, rd_next_3);
        consume memory_access(constant(0), rd_addr, rd_clock_prev, rd_prev_0, rd_prev_1, rd_prev_2, rd_prev_3);
        emit memory_access(constant(0), rd_addr, clock, rd_next_0, rd_next_1, rd_next_2, rd_next_3);
        consume range_check_20(rd_clock_diff);
        return pc;
    }
}
