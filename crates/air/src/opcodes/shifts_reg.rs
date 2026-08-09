//! Register-register shift execution with generated witnesses.

stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [],
    embedded_component: true,
    logup_batch: 2,
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
    relation range_check_20(1);

    inline fn shift_word(value: [felt; 4], shift_amount, left, sign, active) {
        let shift_mask_0 = bitand(shift_amount, 1, active);
        let shift_mask_1 = bitand(shift_amount, 2, active);
        let shift_mask_2 = bitand(shift_amount, 4, active);
        let shift_mask_3 = bitand(shift_amount, 8, active);
        let shift_mask_4 = bitand(shift_amount, 16, active);
        assert shift_amount
            == shift_mask_0 + shift_mask_1 + shift_mask_2 + shift_mask_3 + shift_mask_4;
        let shift_bit_0 = shift_mask_0;
        let shift_bit_1 = shift_mask_1 * inv(2);
        let shift_bit_2 = shift_mask_2 * inv(4);
        let shift_bit_3 = shift_mask_3 * inv(8);
        let shift_bit_4 = shift_mask_4 * inv(16);

        let bit_marker_0 = (1 - shift_bit_0) * (1 - shift_bit_1) * (1 - shift_bit_2);
        let bit_marker_1 = shift_bit_0 * (1 - shift_bit_1) * (1 - shift_bit_2);
        let bit_marker_2 = (1 - shift_bit_0) * shift_bit_1 * (1 - shift_bit_2);
        let bit_marker_3 = shift_bit_0 * shift_bit_1 * (1 - shift_bit_2);
        let bit_marker_4 = (1 - shift_bit_0) * (1 - shift_bit_1) * shift_bit_2;
        let bit_marker_5 = shift_bit_0 * (1 - shift_bit_1) * shift_bit_2;
        let bit_marker_6 = (1 - shift_bit_0) * shift_bit_1 * shift_bit_2;
        let bit_marker_7 = shift_bit_0 * shift_bit_1 * shift_bit_2;
        let limb_marker_0 = (1 - shift_bit_3) * (1 - shift_bit_4);
        let limb_marker_1 = shift_bit_3 * (1 - shift_bit_4);
        let limb_marker_2 = (1 - shift_bit_3) * shift_bit_4;
        let limb_marker_3 = shift_bit_3 * shift_bit_4;

        let multiplier = bit_marker_0 + 2 * bit_marker_1 + 4 * bit_marker_2
            + 8 * bit_marker_3 + 16 * bit_marker_4 + 32 * bit_marker_5
            + 64 * bit_marker_6 + 128 * bit_marker_7;
        let inverse_multiplier = bit_marker_0 + bit_marker_1 * inv(2)
            + bit_marker_2 * inv(4) + bit_marker_3 * inv(8)
            + bit_marker_4 * inv(16) + bit_marker_5 * inv(32)
            + bit_marker_6 * inv(64) + bit_marker_7 * inv(128);
        let low_mask = multiplier - 1;
        let high_mask = 128 * bit_marker_1 + 192 * bit_marker_2
            + 224 * bit_marker_3 + 240 * bit_marker_4 + 248 * bit_marker_5
            + 252 * bit_marker_6 + 254 * bit_marker_7;
        let right = active - left;

        let left_high_0 = bitand(value[0], high_mask, left);
        let left_high_1 = bitand(value[1], high_mask, left);
        let left_high_2 = bitand(value[2], high_mask, left);
        let left_high_3 = bitand(value[3], high_mask, left);
        let carry_scale = bit_marker_1 * inv(128) + bit_marker_2 * inv(64)
            + bit_marker_3 * inv(32) + bit_marker_4 * inv(16)
            + bit_marker_5 * inv(8) + bit_marker_6 * inv(4)
            + bit_marker_7 * inv(2);
        let left_carry_0 = left_high_0 * carry_scale;
        let left_carry_1 = left_high_1 * carry_scale;
        let left_carry_2 = left_high_2 * carry_scale;
        let left_carry_3 = left_high_3 * carry_scale;
        let left_low_0 = value[0] * multiplier - 256 * left_carry_0;
        let left_low_1 = value[1] * multiplier - 256 * left_carry_1;
        let left_low_2 = value[2] * multiplier - 256 * left_carry_2;
        let left_low_3 = value[3] * multiplier - 256 * left_carry_3;
        let left_base_0 = left_low_0;
        let left_base_1 = left_low_1 + left_carry_0;
        let left_base_2 = left_low_2 + left_carry_1;
        let left_base_3 = left_low_3 + left_carry_2;
        let left_result_0 = limb_marker_0 * left_base_0;
        let left_result_1 = limb_marker_0 * left_base_1 + limb_marker_1 * left_base_0;
        let left_result_2 = limb_marker_0 * left_base_2 + limb_marker_1 * left_base_1
            + limb_marker_2 * left_base_0;
        let left_result_3 = limb_marker_0 * left_base_3 + limb_marker_1 * left_base_2
            + limb_marker_2 * left_base_1 + limb_marker_3 * left_base_0;

        let right_carry_0 = bitand(value[0], low_mask, right);
        let right_carry_1 = bitand(value[1], low_mask, right);
        let right_carry_2 = bitand(value[2], low_mask, right);
        let right_carry_3 = bitand(value[3], low_mask, right);
        let right_base_0 = (value[0] - right_carry_0 + 256 * right_carry_1)
            * inverse_multiplier;
        let right_base_1 = (value[1] - right_carry_1 + 256 * right_carry_2)
            * inverse_multiplier;
        let right_base_2 = (value[2] - right_carry_2 + 256 * right_carry_3)
            * inverse_multiplier;
        let right_base_3 = (value[3] - right_carry_3) * inverse_multiplier
            + sign * (256 - 256 * inverse_multiplier);
        let sign_fill = 255 * sign;
        let right_result_0 = limb_marker_0 * right_base_0 + limb_marker_1 * right_base_1
            + limb_marker_2 * right_base_2 + limb_marker_3 * right_base_3;
        let right_result_1 = limb_marker_0 * right_base_1 + limb_marker_1 * right_base_2
            + limb_marker_2 * right_base_3 + limb_marker_3 * sign_fill;
        let right_result_2 = limb_marker_0 * right_base_2 + limb_marker_1 * right_base_3
            + (limb_marker_2 + limb_marker_3) * sign_fill;
        let right_result_3 = limb_marker_0 * right_base_3
            + (limb_marker_1 + limb_marker_2 + limb_marker_3) * sign_fill;

        let result = [
            left * left_result_0 + right * right_result_0,
            left * left_result_1 + right * right_result_1,
            left * left_result_2 + right * right_result_2,
            left * left_result_3 + right * right_result_3,
        ];
        return result;
    }

    fn shifts_reg(
        clock,
        pc,
        rd_addr,
        rs1_addr,
        rs2_addr,
        opcode_sll_flag,
        opcode_srl_flag,
        opcode_sra_flag,
    ) {
        let opcode = opcode_sll_flag * constant(crate::instructions::Opcode::Sll as u32)
            + opcode_srl_flag * constant(crate::instructions::Opcode::Srl as u32)
            + opcode_sra_flag * constant(crate::instructions::Opcode::Sra as u32);
        let active = opcode_sll_flag + opcode_srl_flag + opcode_sra_flag;
        consume program_access(pc, opcode, rd_addr, rs1_addr, rs2_addr);
        read_reg rs1(clock, rs1_addr);
        read_reg rs2(clock, rs2_addr);
        let shift_amount = bitand(rs2_next[0], 31);
        let sign_mask = bitand(rs1_next[3], 128, opcode_sra_flag);
        let sign = opcode_sra_flag * sign_mask * inv(128);
        let result = shift_word(rs1_next, shift_amount, opcode_sll_flag, sign, active);
        consume range_check_8_8(result[0], result[1]);
        consume range_check_8_8(result[2], result[3]);

        consume registers_state(pc, clock);
        emit registers_state(pc + 4, clock + 1);
        write_reg rd(clock, rd_addr, result);
        return pc + 4;
    }
}
