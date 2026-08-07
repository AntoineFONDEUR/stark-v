//! Load-upper-immediate execution, witness generation, and AIR constraints.

stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [],
    embedded_component: true,
    logup_batch: 2,
    embedded_dynamic_component: true,
    vm_access: {
        state: crate::vm::MachineState,
        tracer: crate::trace::Tracer,
    },

    relation memory_access(7);
    relation program_access(5);
    relation registers_state(2);
    relation range_check_8_8_4(3);
    relation range_check_20(1);

    fn lui(clock, pc, rd_addr, imm_0, imm_1, imm_2) {
        let imm = imm_0 + 16 * imm_1 + 4096 * imm_2;
        consume program_access(
            pc,
            constant(crate::instructions::Opcode::Lui as u32),
            rd_addr,
            imm,
            0,
        );
        consume registers_state(pc, clock);
        emit registers_state(pc + 4, clock + 1);
        consume range_check_8_8_4(imm_1, imm_2, imm_0);
        write_reg rd(clock, rd_addr, [0, 16 * imm_0, imm_1, imm_2]);
        return pc + 4;
    }
}
