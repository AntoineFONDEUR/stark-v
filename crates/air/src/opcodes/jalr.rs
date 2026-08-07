//! Register-indirect jump-and-link execution, witness generation, and AIR constraints.

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

    relation bitwise(4);
    relation memory_access(7);
    relation program_access(5);
    relation registers_state(2);
    relation range_check_8_8(2);
    relation range_check_m31(2);
    relation range_check_20(1);

    fn jalr(clock, pc, rd_addr, rs1_addr, imm_felt) {
        consume program_access(
            pc,
            constant(crate::instructions::Opcode::Jalr as u32),
            rd_addr,
            rs1_addr,
            imm_felt,
        );
        read_reg rs1(clock, rs1_addr);
        consume range_check_m31(rs1_next[0], rs1_next[3]);
        let rs1_felt = rs1_next[0] + 256 * rs1_next[1]
            + 65536 * rs1_next[2] + 16777216 * rs1_next[3];
        let target = split_m31(rs1_felt + imm_felt);
        let target_lsb = bitand(target[0], 1);
        let aligned_target = rs1_felt + imm_felt - target_lsb;
        let link = split_m31(pc + 4);
        consume registers_state(pc, clock);
        emit registers_state(aligned_target, clock + 1);
        write_reg rd(clock, rd_addr, link);
        return aligned_target;
    }
}
