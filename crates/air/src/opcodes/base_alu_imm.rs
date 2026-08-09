//! Register-immediate arithmetic and bitwise execution with generated witnesses.

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
    relation range_check_8_11(2);
    relation range_check_8_8(2);
    relation range_check_20(1);

    fn base_alu_imm(
        clock,
        pc,
        rd_addr,
        rs1_addr,
        imm_0,
        imm_1,
        imm_msb,
        opcode_add_flag,
        opcode_xor_flag,
        opcode_or_flag,
        opcode_and_flag,
    ) {
        let opcode = opcode_add_flag * constant(crate::instructions::Opcode::Addi as u32)
            + opcode_xor_flag * constant(crate::instructions::Opcode::Xori as u32)
            + opcode_or_flag * constant(crate::instructions::Opcode::Ori as u32)
            + opcode_and_flag * constant(crate::instructions::Opcode::Andi as u32);
        let imm = imm_0 + 256 * imm_1 + 2048 * imm_msb;
        let imm_upper = imm_1 + 248 * imm_msb;
        let imm_sign = 255 * imm_msb;
        let immediate = [imm_0, imm_upper, imm_sign, imm_sign];
        assert imm_msb * (1 - imm_msb) == 0;
        consume program_access(pc, opcode, rd_addr, rs1_addr, imm);
        consume range_check_8_11(imm_0, 256 * imm_1);
        read_reg rs1(clock, rs1_addr);

        let rd_value = binary_u32(
            rs1_next,
            immediate,
            enabler,
            opcode_add_flag,
            0,
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
