//! Equality-branch execution with generated witnesses.

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
    relation range_check_20(1);

    fn branch_eq(
        clock,
        pc,
        rs1_addr,
        rs2_addr,
        imm_felt,
        opcode_beq_flag,
        opcode_bne_flag,
    ) {
        let opcode = opcode_beq_flag * constant(crate::instructions::Opcode::Beq as u32)
            + opcode_bne_flag * constant(crate::instructions::Opcode::Bne as u32);
        consume program_access(pc, opcode, rs1_addr, rs2_addr, imm_felt);
        read_reg rs1(clock, rs1_addr);
        read_reg rs2(clock, rs2_addr);

        let (forward_difference, forward_borrow) = sub_u32(rs1_next, rs2_next);
        let (reverse_difference, reverse_borrow) = sub_u32(rs2_next, rs1_next);
        let equal = 1 - forward_borrow - reverse_borrow;
        let take_branch = opcode_beq_flag * equal
            + opcode_bne_flag * (1 - equal);
        assert equal * (1 - equal) == 0;
        let next_pc = pc + imm_felt * take_branch + 4 * (1 - take_branch);

        consume registers_state(pc, clock);
        emit registers_state(next_pc, clock + 1);
        return next_pc;
    }
}
