//! Division and remainder execution with generated witnesses and AIR.

stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [],
    embedded_component: true,
    logup_batch: 1,
    embedded_dynamic_component: true,
    vm_access: {
        state: crate::vm::MachineState,
        tracer: crate::trace::Tracer,
    },

    relation bitwise(4);
    relation memory_access(7);
    relation program_access(5);
    relation registers_state(2);
    relation range_check_8_8(2);
    relation range_check_m31(2);
    relation range_check_20(1);

    inline fn wide_product(
        lhs: [felt; 4],
        rhs: [felt; 4],
        lhs_fill,
        rhs_fill,
    ) {
        let step_0 = split_m31(lhs[0] * rhs[0]);
        assert step_0[3] == 0;
        let carry_0 = step_0[1] + 256 * step_0[2];

        let step_1 = split_m31(carry_0 + lhs[0] * rhs[1] + lhs[1] * rhs[0]);
        assert step_1[3] == 0;
        let carry_1 = step_1[1] + 256 * step_1[2];

        let step_2 = split_m31(
            carry_1 + lhs[0] * rhs[2] + lhs[1] * rhs[1] + lhs[2] * rhs[0],
        );
        assert step_2[3] == 0;
        let carry_2 = step_2[1] + 256 * step_2[2];

        let step_3 = split_m31(
            carry_2 + lhs[0] * rhs[3] + lhs[1] * rhs[2]
                + lhs[2] * rhs[1] + lhs[3] * rhs[0],
        );
        assert step_3[3] == 0;
        let carry_3 = step_3[1] + 256 * step_3[2];

        let step_4 = split_m31(
            carry_3 + lhs[0] * rhs_fill + lhs[1] * rhs[3]
                + lhs[2] * rhs[2] + lhs[3] * rhs[1] + lhs_fill * rhs[0],
        );
        assert step_4[3] == 0;
        let carry_4 = step_4[1] + 256 * step_4[2];

        let step_5 = split_m31(
            carry_4 + (lhs[0] + lhs[1]) * rhs_fill + lhs[2] * rhs[3]
                + lhs[3] * rhs[2] + lhs_fill * (rhs[0] + rhs[1]),
        );
        assert step_5[3] == 0;
        let carry_5 = step_5[1] + 256 * step_5[2];

        let step_6 = split_m31(
            carry_5 + (lhs[0] + lhs[1] + lhs[2]) * rhs_fill
                + lhs[3] * rhs[3]
                + lhs_fill * (rhs[0] + rhs[1] + rhs[2]),
        );
        assert step_6[3] == 0;
        let carry_6 = step_6[1] + 256 * step_6[2];

        let step_7 = split_m31(
            carry_6 + (lhs[0] + lhs[1] + lhs[2] + lhs[3]) * rhs_fill
                + lhs_fill * (rhs[0] + rhs[1] + rhs[2] + rhs[3]),
        );
        assert step_7[3] == 0;

        let low = [step_0[0], step_1[0], step_2[0], step_3[0]];
        let high = [step_4[0], step_5[0], step_6[0], step_7[0]];
        return (low, high);
    }

    fn div(
        clock,
        pc,
        rd_addr,
        rs1_addr,
        rs2_addr,
        opcode_div_flag,
        opcode_divu_flag,
        opcode_rem_flag,
        opcode_remu_flag,
    ) {
        let opcode = opcode_div_flag * constant(crate::instructions::Opcode::Div as u32)
            + opcode_divu_flag * constant(crate::instructions::Opcode::Divu as u32)
            + opcode_rem_flag * constant(crate::instructions::Opcode::Rem as u32)
            + opcode_remu_flag * constant(crate::instructions::Opcode::Remu as u32);
        let active = opcode_div_flag + opcode_divu_flag
            + opcode_rem_flag + opcode_remu_flag;
        let is_div = opcode_div_flag + opcode_divu_flag;
        let is_rem = opcode_rem_flag + opcode_remu_flag;
        let is_signed = opcode_div_flag + opcode_rem_flag;
        consume program_access(pc, opcode, rd_addr, rs1_addr, rs2_addr);
        read_reg rs1(clock, rs1_addr);
        read_reg rs2(clock, rs2_addr);

        let (
            quotient,
            remainder,
            zero_divisor,
            zero_remainder,
            overflow,
            divisor_sum_inverse,
            remainder_sum_inverse,
        ) = divrem_u32(rs1_next, rs2_next, is_signed);
        consume range_check_8_8(quotient[0], quotient[1]);
        consume range_check_8_8(quotient[2], quotient[3]);
        consume range_check_8_8(remainder[0], remainder[1]);
        consume range_check_8_8(remainder[2], remainder[3]);

        assert zero_divisor * (1 - zero_divisor) == 0;
        assert zero_divisor * rs2_next[0] == 0;
        assert zero_divisor * rs2_next[1] == 0;
        assert zero_divisor * rs2_next[2] == 0;
        assert zero_divisor * rs2_next[3] == 0;
        assert zero_divisor * (quotient[0] - 255) == 0;
        assert zero_divisor * (quotient[1] - 255) == 0;
        assert zero_divisor * (quotient[2] - 255) == 0;
        assert zero_divisor * (quotient[3] - 255) == 0;
        let divisor_sum = rs2_next[0] + rs2_next[1] + rs2_next[2] + rs2_next[3];
        constrain (active - zero_divisor) * (divisor_sum * divisor_sum_inverse - 1);

        assert zero_remainder * (1 - zero_remainder) == 0;
        assert zero_remainder * remainder[0] == 0;
        assert zero_remainder * remainder[1] == 0;
        assert zero_remainder * remainder[2] == 0;
        assert zero_remainder * remainder[3] == 0;
        let special_case = zero_divisor + zero_remainder;
        assert special_case * (1 - special_case) == 0;
        let regular = active - special_case;
        let remainder_sum = remainder[0] + remainder[1] + remainder[2] + remainder[3];
        constrain regular * (remainder_sum * remainder_sum_inverse - 1);

        assert overflow * (1 - overflow) == 0;
        assert (1 - is_signed) * overflow == 0;
        assert overflow * rs1_next[0] == 0;
        assert overflow * rs1_next[1] == 0;
        assert overflow * rs1_next[2] == 0;
        assert overflow * (rs1_next[3] - 128) == 0;
        assert overflow * (rs2_next[0] - 255) == 0;
        assert overflow * (rs2_next[1] - 255) == 0;
        assert overflow * (rs2_next[2] - 255) == 0;
        assert overflow * (rs2_next[3] - 255) == 0;

        let b_sign_mask = bitand(rs1_next[3], 128, is_signed);
        let c_sign_mask = bitand(rs2_next[3], 128, is_signed);
        let q_sign_mask = bitand(quotient[3], 128, is_signed);
        let b_sign = is_signed * b_sign_mask * inv(128);
        let c_sign = is_signed * c_sign_mask * inv(128);
        let q_sign = is_signed * q_sign_mask * inv(128);
        let b_fill = 255 * b_sign;
        let c_fill = 255 * c_sign;
        hint q_fill = 255 * q_sign * (1 - overflow);
        assert q_fill == 255 * q_sign * (1 - overflow);
        let r_fill = 255 * b_sign * (1 - zero_remainder);

        let zero_word = [0, 0, 0, 0];
        let (negated_divisor, _divisor_negation_borrow) = sub_u32(zero_word, rs2_next);
        let absolute_divisor = [
            rs2_next[0] + c_sign * (negated_divisor[0] - rs2_next[0]),
            rs2_next[1] + c_sign * (negated_divisor[1] - rs2_next[1]),
            rs2_next[2] + c_sign * (negated_divisor[2] - rs2_next[2]),
            rs2_next[3] + c_sign * (negated_divisor[3] - rs2_next[3]),
        ];
        let (negated_remainder, _remainder_negation_borrow) = sub_u32(zero_word, remainder);
        let absolute_remainder = [
            remainder[0] + b_sign * (negated_remainder[0] - remainder[0]),
            remainder[1] + b_sign * (negated_remainder[1] - remainder[1]),
            remainder[2] + b_sign * (negated_remainder[2] - remainder[2]),
            remainder[3] + b_sign * (negated_remainder[3] - remainder[3]),
        ];
        let (_comparison, remainder_is_less) = sub_u32(absolute_remainder, absolute_divisor);
        assert regular * (1 - remainder_is_less) == 0;

        let (product_low, product_high) = wide_product(
            rs2_next,
            quotient,
            c_fill,
            q_fill,
        );
        let (sum_low, carry_low) = add_u32(product_low, remainder);
        let remainder_high = [r_fill, r_fill, r_fill, r_fill];
        let (sum_high_base, _carry_high_base) = add_u32(product_high, remainder_high);
        let carry_word = [carry_low, 0, 0, 0];
        let (sum_high, _carry_high) = add_u32(sum_high_base, carry_word);
        assert sum_low[0] == rs1_next[0];
        assert sum_low[1] == rs1_next[1];
        assert sum_low[2] == rs1_next[2];
        assert sum_low[3] == rs1_next[3];
        assert sum_high[0] == b_fill;
        assert sum_high[1] == b_fill;
        assert sum_high[2] == b_fill;
        assert sum_high[3] == b_fill;

        let rd_value = [
            is_div * quotient[0] + is_rem * remainder[0],
            is_div * quotient[1] + is_rem * remainder[1],
            is_div * quotient[2] + is_rem * remainder[2],
            is_div * quotient[3] + is_rem * remainder[3],
        ];
        consume registers_state(pc, clock);
        emit registers_state(pc + 4, clock + 1);
        write_reg rd(clock, rd_addr, rd_value);
        return pc + 4;
    }
}
