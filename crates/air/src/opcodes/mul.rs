//! MUL opcode AIR as a felt function (airs.md Section 14): rd = (rs1 * rs2)
//! mod 2^32 via a schoolbook 8-bit-limb carry chain. The carries are
//! quadratic, so every lookup stays a singleton (batch-1) fraction.

stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [],
    embedded_component: true,

    relation program_access(5);
    relation registers_state(2);
    relation memory_access(7);
    relation range_check_8_11(2);
    relation range_check_20(1);

    fn mul(
        clock, pc, rd_addr,
        rd_prev_0, rd_prev_1, rd_prev_2, rd_prev_3, rd_clock_prev,
        rd_next_0, rd_next_1, rd_next_2, rd_next_3,
        rs1_addr,
        rs1_prev_0, rs1_prev_1, rs1_prev_2, rs1_prev_3, rs1_clock_prev,
        rs1_next_0, rs1_next_1, rs1_next_2, rs1_next_3,
        rs2_addr,
        rs2_prev_0, rs2_prev_1, rs2_prev_2, rs2_prev_3, rs2_clock_prev,
        rs2_next_0, rs2_next_1, rs2_next_2, rs2_next_3
    ) {
        let carry_0 = (rs1_next_0 * rs2_next_0 - rd_next_0) * inv(pow2(8));
        let carry_1 = (carry_0 + rs1_next_1 * rs2_next_0 + rs1_next_0 * rs2_next_1 - rd_next_1)
            * inv(pow2(8));
        let carry_2 = (carry_1 + rs1_next_2 * rs2_next_0 + rs1_next_1 * rs2_next_1
            + rs1_next_0 * rs2_next_2 - rd_next_2) * inv(pow2(8));
        let carry_3 = (carry_2 + rs1_next_3 * rs2_next_0 + rs1_next_2 * rs2_next_1
            + rs1_next_1 * rs2_next_2 + rs1_next_0 * rs2_next_3 - rd_next_3) * inv(pow2(8));

        consume program_access(pc, constant(crate::instructions::Opcode::Mul as u32), rd_addr, rs1_addr, rs2_addr);
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
        consume memory_access(constant(0), rd_addr, rd_clock_prev, rd_prev_0, rd_prev_1, rd_prev_2, rd_prev_3);
        emit memory_access(constant(0), rd_addr, clock, rd_next_0, rd_next_1, rd_next_2, rd_next_3);
        consume range_check_20(clock - rd_clock_prev);
        return pc;
    }
}
