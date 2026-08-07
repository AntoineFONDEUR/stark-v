//! Ordered-branch execution with generated witnesses.

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

    fn branch_lt(
        clock,
        pc,
        rs1_addr,
        rs2_addr,
        imm_felt,
        opcode_blt_flag,
        opcode_bltu_flag,
        opcode_bge_flag,
        opcode_bgeu_flag,
    ) {
        let opcode = opcode_blt_flag * constant(crate::instructions::Opcode::Blt as u32)
            + opcode_bltu_flag * constant(crate::instructions::Opcode::Bltu as u32)
            + opcode_bge_flag * constant(crate::instructions::Opcode::Bge as u32)
            + opcode_bgeu_flag * constant(crate::instructions::Opcode::Bgeu as u32);
        let signed = opcode_blt_flag + opcode_bge_flag;
        let branch_on_lt = opcode_blt_flag + opcode_bltu_flag;
        let branch_on_ge = opcode_bge_flag + opcode_bgeu_flag;
        consume program_access(pc, opcode, rs1_addr, rs2_addr, imm_felt);
        read_reg rs1(clock, rs1_addr);
        read_reg rs2(clock, rs2_addr);

        let rs1_flipped = bitxor(rs1_next[3], 128, signed);
        let rs2_flipped = bitxor(rs2_next[3], 128, signed);
        let rs1_msb = rs1_next[3] + signed * (rs1_flipped - rs1_next[3]);
        let rs2_msb = rs2_next[3] + signed * (rs2_flipped - rs2_next[3]);
        let lhs = [rs1_next[0], rs1_next[1], rs1_next[2], rs1_msb];
        let rhs = [rs2_next[0], rs2_next[1], rs2_next[2], rs2_msb];
        let (difference, less_than) = sub_u32(lhs, rhs);
        let take_branch = branch_on_lt * less_than
            + branch_on_ge * (1 - less_than);
        let next_pc = pc + imm_felt * take_branch + 4 * (1 - take_branch);

        consume registers_state(pc, clock);
        emit registers_state(next_pc, clock + 1);
        return next_pc;
    }
}
