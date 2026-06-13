//! JALR opcode AIR as a felt function (airs.md Section 11): jump to
//! `(rs1 + imm) & !1`, `rd = pc + 4`.

stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [],
    embedded_component: true,

    relation program_access(5);
    relation registers_state(2);
    relation memory_access(7);
    relation range_check_8_8(2);
    relation range_check_m31(2);
    relation range_check_20(1);

    fn jalr(
        clock, pc, rd_addr,
        rd_prev_0, rd_prev_1, rd_prev_2, rd_prev_3, rd_clock_prev,
        rd_next_0, rd_next_1, rd_next_2, rd_next_3,
        rs1_addr,
        rs1_prev_0, rs1_prev_1, rs1_prev_2, rs1_prev_3, rs1_clock_prev,
        rs1_next_0, rs1_next_1, rs1_next_2, rs1_next_3,
        to_pc_over_two, to_pc_lsb, imm_felt
    ) {
        let rs1_felt = rs1_next_0 + pow2(8) * rs1_next_1 + pow2(16) * rs1_next_2 + pow2(24) * rs1_next_3;
        let rd_felt = rd_next_0 + pow2(8) * rd_next_1 + pow2(16) * rd_next_2 + pow2(24) * rd_next_3;
        let jump_target = 2 * to_pc_over_two;

        assert to_pc_lsb * to_pc_lsb == to_pc_lsb;
        assert 2 * to_pc_over_two + to_pc_lsb == rs1_felt + imm_felt;
        assert rd_addr * rd_felt == rd_addr * (pc + 4);

        consume program_access(pc, constant(crate::instructions::Opcode::Jalr as u32), rd_addr, rs1_addr, imm_felt);
        // Read rs1.
        consume memory_access(constant(0), rs1_addr, rs1_clock_prev, rs1_prev_0, rs1_prev_1, rs1_prev_2, rs1_prev_3);
        emit memory_access(constant(0), rs1_addr, clock, rs1_next_0, rs1_next_1, rs1_next_2, rs1_next_3);
        consume range_check_20(clock - rs1_clock_prev);
        consume range_check_m31(rs1_next_0, rs1_next_3);
        // Jump.
        consume registers_state(pc, clock);
        emit registers_state(jump_target, clock + 1);
        // rd = pc + 4.
        consume range_check_8_8(rd_next_1, rd_next_2);
        consume range_check_m31(rd_next_0, rd_next_3);
        consume memory_access(constant(0), rd_addr, rd_clock_prev, rd_prev_0, rd_prev_1, rd_prev_2, rd_prev_3);
        emit memory_access(constant(0), rd_addr, clock, rd_next_0, rd_next_1, rd_next_2, rd_next_3);
        consume range_check_20(clock - rd_clock_prev);
        return pc;
    }
}
