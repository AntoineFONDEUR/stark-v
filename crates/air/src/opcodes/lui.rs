//! LUI opcode AIR, expressed as a felt function (airs.md Section 9).
//!
//! `rd := imm << 12`. The register/program/memory accesses are the host
//! `crate::relations::Relations`, emitted/consumed directly; the runner fills
//! this table via [`lui_fill`] with the access values it computed from the
//! `Tracer`. This is the fn-DSL form of the former `define_air!` schema entry
//! — same relations, fewer columns (no unused `rd_next`).

stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [],
    embedded_component: true,

    relation program_access(5);
    relation registers_state(2);
    relation memory_access(7);
    relation range_check_8_8_4(3);
    relation range_check_20(1);

    fn lui(
        clock, pc, rd_addr,
        rd_prev_0, rd_prev_1, rd_prev_2, rd_prev_3, rd_clock_prev,
        imm_0, imm_1, imm_2
    ) {
        // U-type immediate: imm = imm_0 + 2^4 imm_1 + 2^12 imm_2.
        let imm = imm_0 + pow2(4) * imm_1 + pow2(12) * imm_2;
        // rd := imm << 12 has limbs (0, imm_0 * 2^4, imm_1, imm_2).
        let rd_val_1 = imm_0 * pow2(4);

        consume program_access(pc, constant(crate::instructions::Opcode::Lui as u32), rd_addr, imm, constant(0));
        consume registers_state(pc, clock);
        emit registers_state(pc + 4, clock + 1);
        consume range_check_8_8_4(imm_1, imm_2, imm_0);
        consume memory_access(constant(0), rd_addr, rd_clock_prev, rd_prev_0, rd_prev_1, rd_prev_2, rd_prev_3);
        emit memory_access(constant(0), rd_addr, clock, constant(0), rd_val_1, imm_1, imm_2);
        consume range_check_20(clock - rd_clock_prev);
        return pc;
    }
}
