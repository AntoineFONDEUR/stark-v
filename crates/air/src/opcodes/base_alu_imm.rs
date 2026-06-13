//! I-type ALU opcodes (addi/xori/ori/andi) as a felt function (airs.md
//! Section 2). One row per instruction; the active opcode flag selects add
//! (carry chain) vs bitwise (lookup), and gates the shared accesses through
//! `active = sum(flags)`.

stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [],
    embedded_component: true,

    relation program_access(5);
    relation registers_state(2);
    relation memory_access(7);
    relation range_check_8_11(2);
    relation range_check_8_8(2);
    relation range_check_20(1);
    relation bitwise(4);

    fn base_alu_imm(
        clock, pc, rd_addr,
        rd_prev_0, rd_prev_1, rd_prev_2, rd_prev_3, rd_clock_prev,
        rd_next_0, rd_next_1, rd_next_2, rd_next_3,
        rs1_addr,
        rs1_prev_0, rs1_prev_1, rs1_prev_2, rs1_prev_3, rs1_clock_prev,
        rs1_next_0, rs1_next_1, rs1_next_2, rs1_next_3,
        imm_0, imm_1, imm_msb,
        opcode_add_flag, opcode_xor_flag, opcode_or_flag, opcode_and_flag
    ) {
        let active = opcode_add_flag + opcode_xor_flag + opcode_or_flag + opcode_and_flag;
        let expected_opcode_id = opcode_add_flag * constant(crate::instructions::Opcode::Addi as u32)
            + opcode_xor_flag * constant(crate::instructions::Opcode::Xori as u32)
            + opcode_or_flag * constant(crate::instructions::Opcode::Ori as u32)
            + opcode_and_flag * constant(crate::instructions::Opcode::Andi as u32);
        let imm = imm_0 + pow2(8) * imm_1 + pow2(11) * imm_msb;
        // Sign-extended immediate limbs (limb 0 is imm_0; limb 3 = limb 2).
        let sext_imm_1 = imm_1 + 248 * imm_msb;
        let sext_imm_2 = 255 * imm_msb;
        let is_bitwise = opcode_xor_flag + opcode_or_flag + opcode_and_flag;
        let bitwise_id = 2 * opcode_xor_flag + opcode_or_flag;
        let imm_1_shifted = pow2(8) * imm_1;
        // Carry chain of rd = rs1 + sext_imm over 8-bit limbs.
        let carry_0 = (rs1_next_0 + imm_0 - rd_next_0) * inv(pow2(8));
        let carry_1 = (rs1_next_1 + sext_imm_1 + carry_0 - rd_next_1) * inv(pow2(8));
        let carry_2 = (rs1_next_2 + sext_imm_2 + carry_1 - rd_next_2) * inv(pow2(8));
        let carry_3 = (rs1_next_3 + sext_imm_2 + carry_2 - rd_next_3) * inv(pow2(8));

        assert imm_msb * imm_msb == imm_msb;
        // Carry booleanity, gated by the add flag (so already degree 3 — must
        // not be enabler-gated again).
        constrain opcode_add_flag * carry_0 * (1 - carry_0);
        constrain opcode_add_flag * carry_1 * (1 - carry_1);
        constrain opcode_add_flag * carry_2 * (1 - carry_2);
        constrain opcode_add_flag * carry_3 * (1 - carry_3);

        consume(active) program_access(pc, expected_opcode_id, rd_addr, rs1_addr, imm);
        consume(active) range_check_8_11(imm_0, imm_1_shifted);
        consume(active) registers_state(pc, clock);
        emit(active) registers_state(pc + 4, clock + 1);
        // Read rs1.
        consume(active) memory_access(constant(0), rs1_addr, rs1_clock_prev, rs1_prev_0, rs1_prev_1, rs1_prev_2, rs1_prev_3);
        emit(active) memory_access(constant(0), rs1_addr, clock, rs1_next_0, rs1_next_1, rs1_next_2, rs1_next_3);
        consume(active) range_check_20(clock - rs1_clock_prev);
        // Bitwise limbs (xor/or/and).
        consume(is_bitwise) bitwise(rs1_next_0, imm_0, rd_next_0, bitwise_id);
        consume(is_bitwise) bitwise(rs1_next_1, sext_imm_1, rd_next_1, bitwise_id);
        consume(is_bitwise) bitwise(rs1_next_2, sext_imm_2, rd_next_2, bitwise_id);
        consume(is_bitwise) bitwise(rs1_next_3, sext_imm_2, rd_next_3, bitwise_id);
        // rd byte ranges.
        consume(active) range_check_8_8(rd_next_0, rd_next_1);
        consume(active) range_check_8_8(rd_next_2, rd_next_3);
        // Write rd.
        consume(active) memory_access(constant(0), rd_addr, rd_clock_prev, rd_prev_0, rd_prev_1, rd_prev_2, rd_prev_3);
        emit(active) memory_access(constant(0), rd_addr, clock, rd_next_0, rd_next_1, rd_next_2, rd_next_3);
        consume(active) range_check_20(clock - rd_clock_prev);
        return pc;
    }
}
