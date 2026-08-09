//! Jump-and-link execution, witness generation, and AIR constraints.

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
    relation range_check_8_8(2);
    relation range_check_m31(2);
    relation range_check_20(1);

    fn jal(clock, pc, rd_addr, imm_felt) {
        let link = split_m31(pc + 4);
        consume program_access(
            pc,
            constant(crate::instructions::Opcode::Jal as u32),
            rd_addr,
            imm_felt,
            0,
        );
        consume registers_state(pc, clock);
        emit registers_state(pc + imm_felt, clock + 1);
        write_reg rd(clock, rd_addr, link);
        return pc + imm_felt;
    }
}
