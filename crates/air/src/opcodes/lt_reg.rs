//! Register-register comparison execution with generated witnesses.

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

    fn lt_reg(
        clock,
        pc,
        rd_addr,
        rs1_addr,
        rs2_addr,
        opcode_slt_flag,
        opcode_sltu_flag,
    ) {
        let opcode = opcode_slt_flag * constant(crate::instructions::Opcode::Slt as u32)
            + opcode_sltu_flag * constant(crate::instructions::Opcode::Sltu as u32);
        consume program_access(pc, opcode, rd_addr, rs1_addr, rs2_addr);
        read_reg rs1(clock, rs1_addr);
        read_reg rs2(clock, rs2_addr);

        let rs1_flipped = bitxor(rs1_next[3], 128, opcode_slt_flag);
        let rs2_flipped = bitxor(rs2_next[3], 128, opcode_slt_flag);
        let rs1_msb = rs1_next[3]
            + opcode_slt_flag * (rs1_flipped - rs1_next[3]);
        let rs2_msb = rs2_next[3]
            + opcode_slt_flag * (rs2_flipped - rs2_next[3]);
        let lhs = [rs1_next[0], rs1_next[1], rs1_next[2], rs1_msb];
        let rhs = [rs2_next[0], rs2_next[1], rs2_next[2], rs2_msb];
        let (difference, less_than) = sub_u32(lhs, rhs);
        let rd_value = [less_than, 0, 0, 0];

        consume registers_state(pc, clock);
        emit registers_state(pc + 4, clock + 1);
        write_reg rd(clock, rd_addr, rd_value);
        return pc + 4;
    }
}
