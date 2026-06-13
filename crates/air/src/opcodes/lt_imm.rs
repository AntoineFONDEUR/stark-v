//! Immediate set-less-than opcodes (slti/sltiu) as a felt function (airs.md
//! Section 6). Reads rs1, compares against the sign-extended I-type immediate
//! and writes the comparison bit to rd. The most-significant-first difference
//! scan picks the first differing limb; the flag sum is the row activity
//! indicator `enabler()`.

stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [],
    embedded_component: true,

    relation program_access(5);
    relation registers_state(2);
    relation memory_access(7);
    relation range_check_20(1);
    relation range_check_8_8_4(3);

    fn lt_imm(
        clock, pc, rd_addr,
        rd_prev_0, rd_prev_1, rd_prev_2, rd_prev_3, rd_clock_prev,
        rd_next_0, rd_next_1, rd_next_2, rd_next_3,
        rs1_addr,
        rs1_prev_0, rs1_prev_1, rs1_prev_2, rs1_prev_3, rs1_clock_prev,
        rs1_next_0, rs1_next_1, rs1_next_2, rs1_next_3,
        cmp_result, rs1_msl_felt,
        imm_0, imm_1, imm_msb,
        opcode_slti_flag, opcode_sltiu_flag,
        diff_marker_0, diff_marker_1, diff_marker_2, diff_marker_3,
        diff_val
    ) {
        let expected_opcode_id = opcode_slti_flag * constant(crate::instructions::Opcode::Slti as u32)
            + opcode_sltiu_flag * constant(crate::instructions::Opcode::Sltiu as u32);
        // I-type immediate (airs.md 6.2).
        let imm = imm_0 + pow2(8) * imm_1 + pow2(11) * imm_msb;
        // Sign-extended immediate limbs; limb 0 is imm_0, limb 3 = limb 2.
        let sext_imm_1 = imm_1 + (pow2(8) - pow2(3)) * imm_msb;
        let sext_imm_2 = (pow2(8) - 1) * imm_msb;
        // Most significant limb of the comparison operand under the active
        // signedness.
        let sext_imm_msl_felt = opcode_sltiu_flag * sext_imm_2 - opcode_slti_flag * imm_msb;
        let rs1_msl_gap = rs1_next_3 - rs1_msl_felt;
        let rs1_msl_shifted = rs1_msl_felt + opcode_slti_flag * pow2(7);
        let imm_1_doubled = 2 * imm_1;
        let prefix_sum_final = diff_marker_0 + diff_marker_1 + diff_marker_2 + diff_marker_3;
        let cmp_sign = 2 * cmp_result - 1;

        constrain imm_msb * (1 - imm_msb);
        constrain rs1_msl_gap * (pow2(8) - rs1_msl_gap);
        constrain diff_marker_0 * (1 - diff_marker_0);
        constrain diff_marker_1 * (1 - diff_marker_1);
        constrain diff_marker_2 * (1 - diff_marker_2);
        constrain diff_marker_3 * (1 - diff_marker_3);
        // Comparison scan from the most significant limb down (airs.md 6.3).
        constrain (1 - diff_marker_3) * (cmp_sign * (sext_imm_msl_felt - rs1_msl_felt));
        constrain diff_marker_3 * (diff_val - cmp_sign * (sext_imm_msl_felt - rs1_msl_felt));
        constrain (1 - diff_marker_3 - diff_marker_2) * (cmp_sign * (sext_imm_2 - rs1_next_2));
        constrain diff_marker_2 * (diff_val - cmp_sign * (sext_imm_2 - rs1_next_2));
        constrain (1 - diff_marker_3 - diff_marker_2 - diff_marker_1)
            * (cmp_sign * (sext_imm_1 - rs1_next_1));
        constrain diff_marker_1 * (diff_val - cmp_sign * (sext_imm_1 - rs1_next_1));
        constrain (1 - prefix_sum_final) * (cmp_sign * (imm_0 - rs1_next_0));
        constrain diff_marker_0 * (diff_val - cmp_sign * (imm_0 - rs1_next_0));
        constrain prefix_sum_final * (1 - prefix_sum_final);
        constrain (1 - prefix_sum_final) * cmp_result;
        constrain cmp_result * (1 - cmp_result);

        consume program_access(pc, expected_opcode_id, rd_addr, rs1_addr, imm);
        // Immediate limb ranges and the sign-shifted most significant limb.
        consume range_check_8_8_4(rs1_msl_shifted, imm_0, imm_1_doubled);
        consume registers_state(pc, clock);
        emit registers_state(pc + 4, clock + 1);
        // Read rs1 (REG_AS = 0).
        consume memory_access(constant(0), rs1_addr, rs1_clock_prev, rs1_prev_0, rs1_prev_1, rs1_prev_2, rs1_prev_3);
        emit memory_access(constant(0), rs1_addr, clock, rs1_next_0, rs1_next_1, rs1_next_2, rs1_next_3);
        consume range_check_20(clock - rs1_clock_prev);
        // When the comparison scan fired, the limb difference is > 0.
        consume(prefix_sum_final) range_check_20(diff_val - 1);
        // Write rd := cmp_result (a single bit in limb 0).
        consume memory_access(constant(0), rd_addr, rd_clock_prev, rd_prev_0, rd_prev_1, rd_prev_2, rd_prev_3);
        emit memory_access(constant(0), rd_addr, clock, cmp_result, constant(0), constant(0), constant(0));
        consume range_check_20(clock - rd_clock_prev);
        return pc;
    }
}
