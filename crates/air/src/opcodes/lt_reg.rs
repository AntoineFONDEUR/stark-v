//! Register set-less-than opcodes (slt/sltu) as a felt function (airs.md
//! Section 5). Reads rs1/rs2, writes the single comparison bit to rd. A
//! most-significant-first difference scan picks the first differing limb; the
//! marker that fires range-checks its positive difference. The flag sum is the
//! row activity indicator `enabler()`.

stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [],
    embedded_component: true,

    relation program_access(5);
    relation registers_state(2);
    relation memory_access(7);
    relation range_check_20(1);
    relation range_check_8_8(2);

    fn lt_reg(
        clock, pc, rd_addr,
        rd_prev_0, rd_prev_1, rd_prev_2, rd_prev_3, rd_clock_prev,
        rd_next_0, rd_next_1, rd_next_2, rd_next_3,
        rs1_addr,
        rs1_prev_0, rs1_prev_1, rs1_prev_2, rs1_prev_3, rs1_clock_prev,
        rs1_next_0, rs1_next_1, rs1_next_2, rs1_next_3,
        rs2_addr,
        rs2_prev_0, rs2_prev_1, rs2_prev_2, rs2_prev_3, rs2_clock_prev,
        rs2_next_0, rs2_next_1, rs2_next_2, rs2_next_3,
        cmp_result, rs1_msl_felt, rs2_msl_felt,
        opcode_slt_flag, opcode_sltu_flag,
        diff_marker_0, diff_marker_1, diff_marker_2, diff_marker_3,
        diff_val
    ) {
        let expected_opcode_id = opcode_slt_flag * constant(crate::instructions::Opcode::Slt as u32)
            + opcode_sltu_flag * constant(crate::instructions::Opcode::Sltu as u32);
        // Most-significant-limb gaps: zero for unsigned interpretation, 2^8 when
        // the sign adjustment applies (airs.md 5.2).
        let rs1_msl_gap = rs1_next_3 - rs1_msl_felt;
        let rs2_msl_gap = rs2_next_3 - rs2_msl_felt;
        // Signed-shifted most significant limbs for the range check.
        let rs1_msl_shifted = rs1_msl_felt + opcode_slt_flag * pow2(7);
        let rs2_msl_shifted = rs2_msl_felt + opcode_slt_flag * pow2(7);
        // Sum of the difference markers: at most one fires.
        let prefix_sum_final = diff_marker_0 + diff_marker_1 + diff_marker_2 + diff_marker_3;
        // Sign of the comparison: +1 if cmp_result else -1.
        let cmp_sign = 2 * cmp_result - 1;

        constrain cmp_result * (1 - cmp_result);
        constrain diff_marker_0 * (1 - diff_marker_0);
        constrain diff_marker_1 * (1 - diff_marker_1);
        constrain diff_marker_2 * (1 - diff_marker_2);
        constrain diff_marker_3 * (1 - diff_marker_3);
        constrain rs1_msl_gap * (pow2(8) - rs1_msl_gap);
        constrain rs2_msl_gap * (pow2(8) - rs2_msl_gap);
        // Comparison scan from the most significant limb down: limbs above the
        // first difference are equal, and the marked limb's difference equals
        // diff_val (airs.md 5.3).
        constrain (1 - diff_marker_3) * (cmp_sign * (rs2_msl_felt - rs1_msl_felt));
        constrain diff_marker_3 * (diff_val - cmp_sign * (rs2_msl_felt - rs1_msl_felt));
        constrain (1 - diff_marker_3 - diff_marker_2) * (cmp_sign * (rs2_next_2 - rs1_next_2));
        constrain diff_marker_2 * (diff_val - cmp_sign * (rs2_next_2 - rs1_next_2));
        constrain (1 - diff_marker_3 - diff_marker_2 - diff_marker_1)
            * (cmp_sign * (rs2_next_1 - rs1_next_1));
        constrain diff_marker_1 * (diff_val - cmp_sign * (rs2_next_1 - rs1_next_1));
        constrain (1 - prefix_sum_final) * (cmp_sign * (rs2_next_0 - rs1_next_0));
        constrain diff_marker_0 * (diff_val - cmp_sign * (rs2_next_0 - rs1_next_0));
        constrain prefix_sum_final * (1 - prefix_sum_final);
        // Equal operands compare as not-less-than.
        constrain (1 - prefix_sum_final) * cmp_result;

        consume program_access(pc, expected_opcode_id, rd_addr, rs1_addr, rs2_addr);
        consume registers_state(pc, clock);
        emit registers_state(pc + 4, clock + 1);
        // Read rs1 (REG_AS = 0).
        consume memory_access(constant(0), rs1_addr, rs1_clock_prev, rs1_prev_0, rs1_prev_1, rs1_prev_2, rs1_prev_3);
        emit memory_access(constant(0), rs1_addr, clock, rs1_next_0, rs1_next_1, rs1_next_2, rs1_next_3);
        consume range_check_20(clock - rs1_clock_prev);
        // Read rs2.
        consume memory_access(constant(0), rs2_addr, rs2_clock_prev, rs2_prev_0, rs2_prev_1, rs2_prev_2, rs2_prev_3);
        emit memory_access(constant(0), rs2_addr, clock, rs2_next_0, rs2_next_1, rs2_next_2, rs2_next_3);
        consume range_check_20(clock - rs2_clock_prev);
        // Most significant limbs shifted into unsigned range under the signed
        // comparison convention.
        consume range_check_8_8(rs1_msl_shifted, rs2_msl_shifted);
        // When the comparison scan fired, the limb difference is > 0.
        consume(prefix_sum_final) range_check_20(diff_val - 1);
        // Write rd := cmp_result (a single bit in limb 0).
        consume memory_access(constant(0), rd_addr, rd_clock_prev, rd_prev_0, rd_prev_1, rd_prev_2, rd_prev_3);
        emit memory_access(constant(0), rd_addr, clock, cmp_result, constant(0), constant(0), constant(0));
        consume range_check_20(clock - rd_clock_prev);
        return pc;
    }
}
