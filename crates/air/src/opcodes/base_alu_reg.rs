//! Register-register arithmetic and bitwise execution with generated witnesses.

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
    relation range_check_20(1);

    fn base_alu_reg(
        clock,
        pc,
        rd_addr,
        rs1_addr,
        rs2_addr,
        opcode_add_flag,
        opcode_sub_flag,
        opcode_xor_flag,
        opcode_or_flag,
        opcode_and_flag,
    ) {
        let opcode = opcode_add_flag * constant(crate::instructions::Opcode::Add as u32)
            + opcode_sub_flag * constant(crate::instructions::Opcode::Sub as u32)
            + opcode_xor_flag * constant(crate::instructions::Opcode::Xor as u32)
            + opcode_or_flag * constant(crate::instructions::Opcode::Or as u32)
            + opcode_and_flag * constant(crate::instructions::Opcode::And as u32);
        consume program_access(pc, opcode, rd_addr, rs1_addr, rs2_addr);
        read_reg rs1(clock, rs1_addr);
        read_reg rs2(clock, rs2_addr);

        let rd_value = binary_u32(
            rs1_next,
            rs2_next,
            enabler,
            opcode_add_flag,
            opcode_sub_flag,
            opcode_and_flag,
            opcode_or_flag,
            opcode_xor_flag,
        );

        consume registers_state(pc, clock);
        emit registers_state(pc + 4, clock + 1);
        write_reg rd(clock, rd_addr, rd_value);
        return pc + 4;
    }
}
