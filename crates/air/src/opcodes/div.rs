//! Divide/remainder opcodes (div/divu/rem/remu) as a felt function (airs.md
//! Section 16). Witnesses the quotient and remainder of rs1 = rs2 * q + r via
//! a sign-extended schoolbook carry chain, with special cases for a zero
//! divisor and signed overflow, and a |r| < |c| comparison scan. The flag sum
//! is the row activity indicator `enabler()`.

stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [],
    embedded_component: true,

    relation program_access(5);
    relation registers_state(2);
    relation memory_access(7);
    relation range_check_20(1);
    relation range_check_8_11(2);
    relation range_check_8_8(2);

    fn div(
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
        rs2_addr,
        rs2_prev_0,
        rs2_prev_1,
        rs2_prev_2,
        rs2_prev_3,
        rs2_clock_prev,
        rs2_next_0,
        rs2_next_1,
        rs2_next_2,
        rs2_next_3,
        zero_divisor,
        r_zero,
        q_0,
        q_1,
        q_2,
        q_3,
        r_0,
        r_1,
        r_2,
        r_3,
        b_sign,
        c_sign,
        q_sign,
        sign_xor,
        c_sum_inv,
        r_sum_inv,
        r_abs_0,
        r_abs_1,
        r_abs_2,
        r_abs_3,
        r_inv_0,
        r_inv_1,
        r_inv_2,
        r_inv_3,
        lt_marker_0,
        lt_marker_1,
        lt_marker_2,
        lt_marker_3,
        lt_diff,
        opcode_div_flag,
        opcode_divu_flag,
        opcode_rem_flag,
        opcode_remu_flag
    ) {
        let row_enabler = opcode_div_flag + opcode_divu_flag + opcode_rem_flag + opcode_remu_flag;
        let expected_opcode_id = opcode_div_flag * constant(crate::instructions::Opcode::Div as u32)
                    + opcode_divu_flag * constant(crate::instructions::Opcode::Divu as u32)
                    + opcode_rem_flag * constant(crate::instructions::Opcode::Rem as u32)
                    + opcode_remu_flag * constant(crate::instructions::Opcode::Remu as u32);
        let is_div = opcode_div_flag + opcode_divu_flag;
        let is_signed = opcode_div_flag + opcode_rem_flag;
        let special_case = zero_divisor + r_zero;
        let valid_not_zero_divisor = row_enabler - zero_divisor;
        let valid_not_special = row_enabler - special_case;
        let q_sum = q_0 + q_1 + q_2 + q_3;
        let c_sum = rs2_next_0 + rs2_next_1 + rs2_next_2 + rs2_next_3;
        let r_sum = r_0 + r_1 + r_2 + r_3;
        let c_sign_factor = 1 - 2 * c_sign;
        let diff_0 = c_sign_factor * (rs2_next_0 - r_abs_0);
        let diff_1 = c_sign_factor * (rs2_next_1 - r_abs_1);
        let diff_2 = c_sign_factor * (rs2_next_2 - r_abs_2);
        let diff_3 = c_sign_factor * (rs2_next_3 - r_abs_3);
        let a_0 = is_div * q_0 + (1 - is_div) * r_0;
        let a_1 = is_div * q_1 + (1 - is_div) * r_1;
        let a_2 = is_div * q_2 + (1 - is_div) * r_2;
        let a_3 = is_div * q_3 + (1 - is_div) * r_3;
        let carry_lt_0 = (r_0 + r_abs_0) * inv(pow2(8));
        let carry_lt_1 = (carry_lt_0 + r_1 + r_abs_1) * inv(pow2(8));
        let carry_lt_2 = (carry_lt_1 + r_2 + r_abs_2) * inv(pow2(8));
        let carry_lt_3 = (carry_lt_2 + r_3 + r_abs_3) * inv(pow2(8));
        let prefix_3 = special_case + lt_marker_3;
        let prefix_2 = prefix_3 + lt_marker_2;
        let prefix_1 = prefix_2 + lt_marker_1;
        let prefix_0 = prefix_1 + lt_marker_0;
        let lt_diff_minus_1 = lt_diff - 1;
        let c_hi = 255 * c_sign;
        let q_hi = 255 * q_sign;
        let b_hi = 255 * b_sign;
        let r_hi = 255 * b_sign * (1 - r_zero);
        let carry_0 = (rs2_next_0 * q_0 + r_0 - rs1_next_0) * inv(pow2(8));
        let carry_1 = (carry_0 + rs2_next_0 * q_1 + rs2_next_1 * q_0 + r_1 - rs1_next_1)
                        * inv(pow2(8));
        let carry_2 = (carry_1 + rs2_next_0 * q_2 + rs2_next_1 * q_1 + rs2_next_2 * q_0 + r_2
                        - rs1_next_2) * inv(pow2(8));
        let carry_3 = (carry_2 + rs2_next_0 * q_3 + rs2_next_1 * q_2 + rs2_next_2 * q_1
                        + rs2_next_3 * q_0 + r_3 - rs1_next_3) * inv(pow2(8));
        let carry_4 = (carry_3 + rs2_next_0 * q_hi + rs2_next_1 * q_3 + rs2_next_2 * q_2
                        + rs2_next_3 * q_1 + c_hi * q_0 + r_hi - b_hi) * inv(pow2(8));
        let carry_5 = (carry_4 + (rs2_next_0 + rs2_next_1) * q_hi + rs2_next_2 * q_3
                        + rs2_next_3 * q_2 + c_hi * (q_0 + q_1) + r_hi - b_hi)
                        * inv(pow2(8));
        let carry_6 = (carry_5 + (c_sum - rs2_next_3) * q_hi + rs2_next_3 * q_3
                        + c_hi * (q_sum - q_3) + r_hi - b_hi) * inv(pow2(8));
        let carry_7 = (carry_6 + c_sum * q_hi + c_hi * q_sum + r_hi - b_hi) * inv(pow2(8));
        let b_sign_check = 2 * is_signed * (rs1_next_3 - b_sign * pow2(7));
        let c_sign_check = 2 * is_signed * (rs2_next_3 - c_sign * pow2(7));
        let pc_next = pc + 4;
        let clock_next = clock + 1;
        let rs1_clock_diff = clock - rs1_clock_prev;
        let rs2_clock_diff = clock - rs2_clock_prev;
        let rd_clock_diff = clock - rd_clock_prev;

        constrain zero_divisor * (1 - zero_divisor);
        constrain r_zero * (1 - r_zero);
        constrain b_sign * (1 - b_sign);
        constrain c_sign * (1 - c_sign);
        constrain q_sign * (1 - q_sign);
        constrain sign_xor * (1 - sign_xor);
        constrain lt_marker_0 * (1 - lt_marker_0);
        constrain lt_marker_1 * (1 - lt_marker_1);
        constrain lt_marker_2 * (1 - lt_marker_2);
        constrain lt_marker_3 * (1 - lt_marker_3);
        constrain special_case * (1 - special_case);
        constrain valid_not_zero_divisor * (1 - valid_not_zero_divisor);
        constrain valid_not_special * (1 - valid_not_special);
        constrain zero_divisor * rs2_next_0;
        constrain zero_divisor * rs2_next_1;
        constrain zero_divisor * rs2_next_2;
        constrain zero_divisor * rs2_next_3;
        constrain zero_divisor * (q_0 - (pow2(8) - 1));
        constrain zero_divisor * (q_1 - (pow2(8) - 1));
        constrain zero_divisor * (q_2 - (pow2(8) - 1));
        constrain zero_divisor * (q_3 - (pow2(8) - 1));
        constrain valid_not_zero_divisor * (c_sum * c_sum_inv - 1);
        constrain r_zero * r_0;
        constrain r_zero * r_1;
        constrain r_zero * r_2;
        constrain r_zero * r_3;
        constrain valid_not_special * (r_sum * r_sum_inv - 1);
        constrain (1 - is_signed) * b_sign;
        constrain (1 - is_signed) * c_sign;
        constrain row_enabler * (sign_xor - b_sign - c_sign + 2 * b_sign * c_sign);
        constrain (1 - zero_divisor) * q_sum * (q_sign - sign_xor);
        constrain (1 - zero_divisor) * (q_sign - sign_xor) * q_sign;
        constrain (1 - sign_xor) * (r_abs_0 - r_0);
        constrain sign_xor * carry_lt_0 * (carry_lt_0 - 1);
        constrain sign_xor * (1 - carry_lt_0) * r_abs_0;
        constrain sign_xor * ((r_abs_0 - pow2(8)) * r_inv_0 - 1);
        constrain (1 - sign_xor) * (r_abs_1 - r_1);
        constrain sign_xor * (carry_lt_1 - carry_lt_0) * (carry_lt_1 - 1);
        constrain sign_xor * (1 - carry_lt_1) * r_abs_1;
        constrain sign_xor * ((r_abs_1 - pow2(8)) * r_inv_1 - 1);
        constrain (1 - sign_xor) * (r_abs_2 - r_2);
        constrain sign_xor * (carry_lt_2 - carry_lt_1) * (carry_lt_2 - 1);
        constrain sign_xor * (1 - carry_lt_2) * r_abs_2;
        constrain sign_xor * ((r_abs_2 - pow2(8)) * r_inv_2 - 1);
        constrain (1 - sign_xor) * (r_abs_3 - r_3);
        constrain sign_xor * (carry_lt_3 - carry_lt_2) * (carry_lt_3 - 1);
        constrain sign_xor * (1 - carry_lt_3) * r_abs_3;
        constrain sign_xor * ((r_abs_3 - pow2(8)) * r_inv_3 - 1);
        constrain (1 - prefix_3) * diff_3;
        constrain lt_marker_3 * (lt_diff - diff_3);
        constrain (1 - prefix_2) * diff_2;
        constrain lt_marker_2 * (lt_diff - diff_2);
        constrain (1 - prefix_1) * diff_1;
        constrain lt_marker_1 * (lt_diff - diff_1);
        constrain (1 - prefix_0) * diff_0;
        constrain lt_marker_0 * (lt_diff - diff_0);
        constrain row_enabler * (1 - prefix_0);

        consume program_access(pc, expected_opcode_id, rd_addr, rs1_addr, rs2_addr);
        consume registers_state(pc, clock);
        emit registers_state(pc_next, clock_next);
        consume memory_access(constant(0), rs1_addr, rs1_clock_prev, rs1_prev_0, rs1_prev_1, rs1_prev_2, rs1_prev_3);
        emit memory_access(constant(0), rs1_addr, clock, rs1_next_0, rs1_next_1, rs1_next_2, rs1_next_3);
        consume range_check_20(rs1_clock_diff);
        consume memory_access(constant(0), rs2_addr, rs2_clock_prev, rs2_prev_0, rs2_prev_1, rs2_prev_2, rs2_prev_3);
        emit memory_access(constant(0), rs2_addr, clock, rs2_next_0, rs2_next_1, rs2_next_2, rs2_next_3);
        consume range_check_20(rs2_clock_diff);
        consume range_check_8_11(q_0, carry_0);
        consume range_check_8_11(q_1, carry_1);
        consume range_check_8_11(q_2, carry_2);
        consume range_check_8_11(q_3, carry_3);
        consume range_check_8_11(r_0, carry_4);
        consume range_check_8_11(r_1, carry_5);
        consume range_check_8_11(r_2, carry_6);
        consume range_check_8_11(r_3, carry_7);
        consume range_check_8_8(b_sign_check, c_sign_check);
        consume(valid_not_special) range_check_20(lt_diff_minus_1);
        consume memory_access(constant(0), rd_addr, rd_clock_prev, rd_prev_0, rd_prev_1, rd_prev_2, rd_prev_3);
        emit memory_access(constant(0), rd_addr, clock, a_0, a_1, a_2, a_3);
        consume range_check_20(rd_clock_diff);
        return pc;
    }
}
