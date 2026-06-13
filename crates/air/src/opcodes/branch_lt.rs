//! Conditional ordering-branch opcodes (blt/bltu/bge/bgeu) as a felt function
//! (airs.md Section 8). Reads rs1/rs2, no register write; the
//! most-significant-first difference scan resolves the signed/unsigned
//! comparison and the branch target is selected by `cmp_result`. The flag sum
//! is the row activity indicator `enabler()`.

stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [],
    embedded_component: true,

    relation program_access(5);
    relation registers_state(2);
    relation memory_access(7);
    relation range_check_20(1);
    relation range_check_8_8(2);

    fn branch_lt(
        clock,
        pc,
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
        rs1_msl_felt,
        rs2_msl_felt,
        imm_felt,
        cmp_result,
        cmp_lt,
        diff_marker_0,
        diff_marker_1,
        diff_marker_2,
        diff_marker_3,
        diff_val,
        branch_target,
        opcode_blt_flag,
        opcode_bltu_flag,
        opcode_bge_flag,
        opcode_bgeu_flag
    ) {
        let row_enabler = opcode_blt_flag + opcode_bltu_flag + opcode_bge_flag + opcode_bgeu_flag;
        let expected_opcode_id = opcode_blt_flag * constant(crate::instructions::Opcode::Blt as u32)
                    + opcode_bltu_flag * constant(crate::instructions::Opcode::Bltu as u32)
                    + opcode_bge_flag * constant(crate::instructions::Opcode::Bge as u32)
                    + opcode_bgeu_flag * constant(crate::instructions::Opcode::Bgeu as u32);
        let lt = opcode_blt_flag + opcode_bltu_flag;
        let ge = opcode_bge_flag + opcode_bgeu_flag;
        let signed = opcode_blt_flag + opcode_bge_flag;
        let rs1_msl_gap = rs1_next_3 - rs1_msl_felt;
        let rs2_msl_gap = rs2_next_3 - rs2_msl_felt;
        let rs1_msl_shifted = rs1_msl_felt + signed * pow2(7);
        let rs2_msl_shifted = rs2_msl_felt + signed * pow2(7);
        let prefix_sum_final = diff_marker_0 + diff_marker_1 + diff_marker_2 + diff_marker_3;
        let lt_sign = 2 * cmp_lt - 1;
        let clock_next = clock + 1;
        let rs1_clock_diff = clock - rs1_clock_prev;
        let rs2_clock_diff = clock - rs2_clock_prev;

        constrain cmp_result * (1 - cmp_result);
        constrain diff_marker_0 * (1 - diff_marker_0);
        constrain diff_marker_1 * (1 - diff_marker_1);
        constrain diff_marker_2 * (1 - diff_marker_2);
        constrain diff_marker_3 * (1 - diff_marker_3);
        constrain row_enabler * (branch_target - (pc + imm_felt * cmp_result + 4 * (1 - cmp_result)));
        constrain rs1_msl_gap * (pow2(8) - rs1_msl_gap);
        constrain rs2_msl_gap * (pow2(8) - rs2_msl_gap);
        constrain (1 - diff_marker_3) * (lt_sign * (rs2_msl_felt - rs1_msl_felt));
        constrain diff_marker_3 * (diff_val - lt_sign * (rs2_msl_felt - rs1_msl_felt));
        constrain (1 - diff_marker_3 - diff_marker_2) * (lt_sign * (rs2_next_2 - rs1_next_2));
        constrain diff_marker_2 * (diff_val - lt_sign * (rs2_next_2 - rs1_next_2));
        constrain (1 - diff_marker_3 - diff_marker_2 - diff_marker_1)
                        * (lt_sign * (rs2_next_1 - rs1_next_1));
        constrain diff_marker_1 * (diff_val - lt_sign * (rs2_next_1 - rs1_next_1));
        constrain (1 - prefix_sum_final) * (lt_sign * (rs2_next_0 - rs1_next_0));
        constrain diff_marker_0 * (diff_val - lt_sign * (rs2_next_0 - rs1_next_0));
        constrain prefix_sum_final * (1 - prefix_sum_final);
        constrain (1 - prefix_sum_final) * cmp_lt;
        constrain cmp_lt - (cmp_result * lt + (1 - cmp_result) * ge);

        consume program_access(pc, expected_opcode_id, rs1_addr, rs2_addr, imm_felt);
        consume registers_state(pc, clock);
        emit registers_state(branch_target, clock_next);
        consume memory_access(constant(0), rs1_addr, rs1_clock_prev, rs1_prev_0, rs1_prev_1, rs1_prev_2, rs1_prev_3);
        emit memory_access(constant(0), rs1_addr, clock, rs1_next_0, rs1_next_1, rs1_next_2, rs1_next_3);
        consume range_check_20(rs1_clock_diff);
        consume memory_access(constant(0), rs2_addr, rs2_clock_prev, rs2_prev_0, rs2_prev_1, rs2_prev_2, rs2_prev_3);
        emit memory_access(constant(0), rs2_addr, clock, rs2_next_0, rs2_next_1, rs2_next_2, rs2_next_3);
        consume range_check_20(rs2_clock_diff);
        consume range_check_8_8(rs1_msl_shifted, rs2_msl_shifted);
        consume(prefix_sum_final) range_check_20(diff_val - 1);
        return pc;
    }
}
