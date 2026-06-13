//! R-type ALU opcodes (add/sub/xor/or/and) as a felt function (airs.md
//! Section 1). Active opcode flag selects add/sub (carry chains) vs bitwise
//! (lookup); the flag sum is the row activity indicator `enabler()`.

stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [],
    embedded_component: true,

    relation program_access(5);
    relation registers_state(2);
    relation memory_access(7);
    relation range_check_8_8(2);
    relation range_check_20(1);
    relation bitwise(4);

    fn base_alu_reg(
        clock, pc, rd_addr,
        rd_prev_0, rd_prev_1, rd_prev_2, rd_prev_3, rd_clock_prev,
        rd_next_0, rd_next_1, rd_next_2, rd_next_3,
        rs1_addr,
        rs1_prev_0, rs1_prev_1, rs1_prev_2, rs1_prev_3, rs1_clock_prev,
        rs1_next_0, rs1_next_1, rs1_next_2, rs1_next_3,
        rs2_addr,
        rs2_prev_0, rs2_prev_1, rs2_prev_2, rs2_prev_3, rs2_clock_prev,
        rs2_next_0, rs2_next_1, rs2_next_2, rs2_next_3,
        opcode_add_flag, opcode_sub_flag, opcode_xor_flag, opcode_or_flag, opcode_and_flag
    ) {
        let expected_opcode_id = opcode_add_flag * constant(crate::instructions::Opcode::Add as u32)
            + opcode_sub_flag * constant(crate::instructions::Opcode::Sub as u32)
            + opcode_xor_flag * constant(crate::instructions::Opcode::Xor as u32)
            + opcode_or_flag * constant(crate::instructions::Opcode::Or as u32)
            + opcode_and_flag * constant(crate::instructions::Opcode::And as u32);
        let is_bitwise = opcode_xor_flag + opcode_or_flag + opcode_and_flag;
        let bitwise_id = 2 * opcode_xor_flag + opcode_or_flag;
        let carry_add_0 = (rs1_next_0 + rs2_next_0 - rd_next_0) * inv(pow2(8));
        let carry_add_1 = (rs1_next_1 + rs2_next_1 + carry_add_0 - rd_next_1) * inv(pow2(8));
        let carry_add_2 = (rs1_next_2 + rs2_next_2 + carry_add_1 - rd_next_2) * inv(pow2(8));
        let carry_add_3 = (rs1_next_3 + rs2_next_3 + carry_add_2 - rd_next_3) * inv(pow2(8));
        let carry_sub_0 = (rd_next_0 + rs2_next_0 - rs1_next_0) * inv(pow2(8));
        let carry_sub_1 = (rd_next_1 + rs2_next_1 - rs1_next_1 + carry_sub_0) * inv(pow2(8));
        let carry_sub_2 = (rd_next_2 + rs2_next_2 - rs1_next_2 + carry_sub_1) * inv(pow2(8));
        let carry_sub_3 = (rd_next_3 + rs2_next_3 - rs1_next_3 + carry_sub_2) * inv(pow2(8));

        constrain opcode_add_flag * carry_add_0 * (1 - carry_add_0);
        constrain opcode_add_flag * carry_add_1 * (1 - carry_add_1);
        constrain opcode_add_flag * carry_add_2 * (1 - carry_add_2);
        constrain opcode_add_flag * carry_add_3 * (1 - carry_add_3);
        constrain opcode_sub_flag * carry_sub_0 * (1 - carry_sub_0);
        constrain opcode_sub_flag * carry_sub_1 * (1 - carry_sub_1);
        constrain opcode_sub_flag * carry_sub_2 * (1 - carry_sub_2);
        constrain opcode_sub_flag * carry_sub_3 * (1 - carry_sub_3);

        consume program_access(pc, expected_opcode_id, rd_addr, rs1_addr, rs2_addr);
        consume registers_state(pc, clock);
        emit registers_state(pc + 4, clock + 1);
        // Read rs1.
        consume memory_access(constant(0), rs1_addr, rs1_clock_prev, rs1_prev_0, rs1_prev_1, rs1_prev_2, rs1_prev_3);
        emit memory_access(constant(0), rs1_addr, clock, rs1_next_0, rs1_next_1, rs1_next_2, rs1_next_3);
        consume range_check_20(clock - rs1_clock_prev);
        // Read rs2.
        consume memory_access(constant(0), rs2_addr, rs2_clock_prev, rs2_prev_0, rs2_prev_1, rs2_prev_2, rs2_prev_3);
        emit memory_access(constant(0), rs2_addr, clock, rs2_next_0, rs2_next_1, rs2_next_2, rs2_next_3);
        consume range_check_20(clock - rs2_clock_prev);
        // Bitwise limbs (xor/or/and).
        consume(is_bitwise) bitwise(rs1_next_0, rs2_next_0, rd_next_0, bitwise_id);
        consume(is_bitwise) bitwise(rs1_next_1, rs2_next_1, rd_next_1, bitwise_id);
        consume(is_bitwise) bitwise(rs1_next_2, rs2_next_2, rd_next_2, bitwise_id);
        consume(is_bitwise) bitwise(rs1_next_3, rs2_next_3, rd_next_3, bitwise_id);
        // rd byte ranges.
        consume range_check_8_8(rd_next_0, rd_next_1);
        consume range_check_8_8(rd_next_2, rd_next_3);
        // Write rd.
        consume memory_access(constant(0), rd_addr, rd_clock_prev, rd_prev_0, rd_prev_1, rd_prev_2, rd_prev_3);
        emit memory_access(constant(0), rd_addr, clock, rd_next_0, rd_next_1, rd_next_2, rd_next_3);
        consume range_check_20(clock - rd_clock_prev);
        return pc;
    }
}
