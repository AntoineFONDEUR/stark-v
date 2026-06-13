//! AUIPC opcode AIR as a felt function (airs.md Section 10): `rd = pc + imm`.

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

    fn auipc(
        clock, pc, rd_addr,
        rd_prev_0, rd_prev_1, rd_prev_2, rd_prev_3, rd_clock_prev,
        rd_next_0, rd_next_1, rd_next_2, rd_next_3,
        imm_felt
    ) {
        let rd_felt = rd_next_0 + pow2(8) * rd_next_1 + pow2(16) * rd_next_2 + pow2(24) * rd_next_3;
        // rd = pc + imm.
        assert rd_felt == pc + imm_felt;

        consume program_access(pc, constant(crate::instructions::Opcode::Auipc as u32), rd_addr, imm_felt, constant(0));
        consume registers_state(pc, clock);
        emit registers_state(pc + 4, clock + 1);
        consume range_check_8_8(rd_next_1, rd_next_2);
        consume range_check_m31(rd_next_0, rd_next_3);
        consume memory_access(constant(0), rd_addr, rd_clock_prev, rd_prev_0, rd_prev_1, rd_prev_2, rd_prev_3);
        emit memory_access(constant(0), rd_addr, clock, rd_next_0, rd_next_1, rd_next_2, rd_next_3);
        consume range_check_20(clock - rd_clock_prev);
        return pc;
    }
}
