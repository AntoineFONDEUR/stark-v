//! Conditional equality-branch opcodes (beq/bne) as a felt function
//! (airs.md Section 7). Reads rs1/rs2, no register write; the branch target
//! is selected by `cmp_result`, and an inverse-witness sum proves inequality
//! when the operands must differ.

stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [],
    embedded_component: true,

    relation program_access(5);
    relation registers_state(2);
    relation memory_access(7);
    relation range_check_20(1);

    fn branch_eq(
        clock, pc,
        rs1_addr,
        rs1_prev_0, rs1_prev_1, rs1_prev_2, rs1_prev_3, rs1_clock_prev,
        rs1_next_0, rs1_next_1, rs1_next_2, rs1_next_3,
        rs2_addr,
        rs2_prev_0, rs2_prev_1, rs2_prev_2, rs2_prev_3, rs2_clock_prev,
        rs2_next_0, rs2_next_1, rs2_next_2, rs2_next_3,
        imm_felt, cmp_result,
        diff_inv_marker_0, diff_inv_marker_1, diff_inv_marker_2, diff_inv_marker_3,
        opcode_beq_flag, opcode_bne_flag
    ) {
        let expected_opcode_id = opcode_beq_flag * constant(crate::instructions::Opcode::Beq as u32)
            + opcode_bne_flag * constant(crate::instructions::Opcode::Bne as u32);
        // 1 when the operands must be equal under the active opcode.
        let cmp_eq = cmp_result * opcode_beq_flag + (1 - cmp_result) * opcode_bne_flag;
        let diff_inv_sum = cmp_eq
            + (rs1_next_0 - rs2_next_0) * diff_inv_marker_0
            + (rs1_next_1 - rs2_next_1) * diff_inv_marker_1
            + (rs1_next_2 - rs2_next_2) * diff_inv_marker_2
            + (rs1_next_3 - rs2_next_3) * diff_inv_marker_3;
        let to_pc = pc + imm_felt * cmp_result + 4 * (1 - cmp_result);

        assert cmp_result * cmp_result == cmp_result;
        // Equality forced limb-wise when cmp_eq fires (degree 3, flag-gated).
        constrain cmp_eq * (rs1_next_0 - rs2_next_0);
        constrain cmp_eq * (rs1_next_1 - rs2_next_1);
        constrain cmp_eq * (rs1_next_2 - rs2_next_2);
        constrain cmp_eq * (rs1_next_3 - rs2_next_3);
        // On enabled rows the inverse-witness sum is 1 (proves inequality).
        assert diff_inv_sum == 1;

        consume program_access(pc, expected_opcode_id, rs1_addr, rs2_addr, imm_felt);
        consume memory_access(constant(0), rs1_addr, rs1_clock_prev, rs1_prev_0, rs1_prev_1, rs1_prev_2, rs1_prev_3);
        emit memory_access(constant(0), rs1_addr, clock, rs1_next_0, rs1_next_1, rs1_next_2, rs1_next_3);
        consume range_check_20(clock - rs1_clock_prev);
        consume memory_access(constant(0), rs2_addr, rs2_clock_prev, rs2_prev_0, rs2_prev_1, rs2_prev_2, rs2_prev_3);
        emit memory_access(constant(0), rs2_addr, clock, rs2_next_0, rs2_next_1, rs2_next_2, rs2_next_3);
        consume range_check_20(clock - rs2_clock_prev);
        consume registers_state(pc, clock);
        emit registers_state(to_pc, clock + 1);
        return pc;
    }
}
