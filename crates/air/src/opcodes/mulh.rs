//! MULH/MULHSU/MULHU opcode AIR as a felt function (airs.md Section 15): the
//! high 32 bits of the 64-bit product, with sign extension selected by the
//! opcode flags. Quadratic schoolbook carries (carry_0..7) stay singleton
//! (batch-1) fractions.

stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [],
    embedded_component: true,

    relation program_access(5);
    relation registers_state(2);
    relation memory_access(7);
    relation range_check_8_11(2);
    relation range_check_20(1);

    fn mulh(
        clock, pc, rd_addr,
        rd_prev_0, rd_prev_1, rd_prev_2, rd_prev_3, rd_clock_prev,
        rd_next_0, rd_next_1, rd_next_2, rd_next_3,
        rs1_addr,
        rs1_prev_0, rs1_prev_1, rs1_prev_2, rs1_prev_3, rs1_clock_prev,
        rs1_next_0, rs1_next_1, rs1_next_2, rs1_next_3,
        rs2_addr,
        rs2_prev_0, rs2_prev_1, rs2_prev_2, rs2_prev_3, rs2_clock_prev,
        rs2_next_0, rs2_next_1, rs2_next_2, rs2_next_3,
        rd_high_0, rd_high_1, rd_high_2, rd_high_3,
        rs1_sign, rs2_sign,
        opcode_mulh_flag, opcode_mulhsu_flag, opcode_mulhu_flag
    ) {
        let expected_opcode_id = opcode_mulh_flag * constant(crate::instructions::Opcode::Mulh as u32)
            + opcode_mulhsu_flag * constant(crate::instructions::Opcode::Mulhsu as u32)
            + opcode_mulhu_flag * constant(crate::instructions::Opcode::Mulhu as u32);
        let rs1_top = rs1_next_3 + rs1_sign * pow2(7);
        let rs2_top = rs2_next_3 + rs2_sign * pow2(7);
        let rs1_fill = rs1_sign * (pow2(8) - 1);
        let rs2_fill = rs2_sign * (pow2(8) - 1);
        let carry_0 = (rs1_next_0 * rs2_next_0 - rd_high_0) * inv(pow2(8));
        let carry_1 = (carry_0 + rs1_next_0 * rs2_next_1 + rs1_next_1 * rs2_next_0 - rd_high_1) * inv(pow2(8));
        let carry_2 = (carry_1 + rs1_next_0 * rs2_next_2 + rs1_next_1 * rs2_next_1 + rs1_next_2 * rs2_next_0 - rd_high_2) * inv(pow2(8));
        let carry_3 = (carry_2 + rs1_next_0 * rs2_top + rs1_next_1 * rs2_next_2 + rs1_next_2 * rs2_next_1 + rs1_top * rs2_next_0 - rd_high_3) * inv(pow2(8));
        let carry_4 = (carry_3 + rs1_next_0 * rs2_fill + rs1_next_1 * rs2_top + rs1_next_2 * rs2_next_2 + rs1_top * rs2_next_1 + rs1_fill * rs2_next_0 - rd_next_0) * inv(pow2(8));
        let carry_5 = (carry_4 + rs1_next_0 * rs2_fill + rs1_next_1 * rs2_fill + rs1_next_2 * rs2_top + rs1_top * rs2_next_2 + rs1_fill * rs2_next_1 + rs1_fill * rs2_next_0 - rd_next_1) * inv(pow2(8));
        let carry_6 = (carry_5 + rs1_next_0 * rs2_fill + rs1_next_1 * rs2_fill + rs1_next_2 * rs2_fill + rs1_top * rs2_top + rs1_fill * rs2_next_2 + rs1_fill * rs2_next_1 + rs1_fill * rs2_next_0 - rd_next_2) * inv(pow2(8));
        let carry_7 = (carry_6 + rs1_next_0 * rs2_fill + rs1_next_1 * rs2_fill + rs1_next_2 * rs2_fill + rs1_top * rs2_fill + rs1_fill * rs2_top + rs1_fill * rs2_next_2 + rs1_fill * rs2_next_1 + rs1_fill * rs2_next_0 - rd_next_3) * inv(pow2(8));

        constrain rs1_sign * (1 - rs1_sign);
        constrain rs2_sign * (1 - rs2_sign);
        constrain (opcode_mulhsu_flag + opcode_mulhu_flag) * rs2_sign;
        constrain opcode_mulhu_flag * rs1_sign;

        consume program_access(pc, expected_opcode_id, rd_addr, rs1_addr, rs2_addr);
        consume registers_state(pc, clock);
        emit registers_state(pc + 4, clock + 1);
        consume memory_access(constant(0), rs1_addr, rs1_clock_prev, rs1_prev_0, rs1_prev_1, rs1_prev_2, rs1_prev_3);
        emit memory_access(constant(0), rs1_addr, clock, rs1_next_0, rs1_next_1, rs1_next_2, rs1_next_3);
        consume range_check_20(clock - rs1_clock_prev);
        consume memory_access(constant(0), rs2_addr, rs2_clock_prev, rs2_prev_0, rs2_prev_1, rs2_prev_2, rs2_prev_3);
        emit memory_access(constant(0), rs2_addr, clock, rs2_next_0, rs2_next_1, rs2_next_2, rs2_next_3);
        consume range_check_20(clock - rs2_clock_prev);
        consume range_check_8_11(rd_next_0, carry_0);
        consume range_check_8_11(rd_next_1, carry_1);
        consume range_check_8_11(rd_next_2, carry_2);
        consume range_check_8_11(rd_next_3, carry_3);
        consume range_check_8_11(rd_high_0, carry_4);
        consume range_check_8_11(rd_high_1, carry_5);
        consume range_check_8_11(rd_high_2, carry_6);
        consume range_check_8_11(rd_high_3, carry_7);
        consume memory_access(constant(0), rd_addr, rd_clock_prev, rd_prev_0, rd_prev_1, rd_prev_2, rd_prev_3);
        emit memory_access(constant(0), rd_addr, clock, rd_next_0, rd_next_1, rd_next_2, rd_next_3);
        consume range_check_20(clock - rd_clock_prev);
        return pc;
    }
}
