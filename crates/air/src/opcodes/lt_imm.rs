//! Register-immediate comparison execution with generated witnesses.

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

    fn lt_imm(
        clock,
        pc,
        rd_addr,
        rs1_addr,
        imm_0,
        imm_1,
        imm_msb,
        opcode_slti_flag,
        opcode_sltiu_flag,
    ) {
        let opcode = opcode_slti_flag * constant(crate::instructions::Opcode::Slti as u32)
            + opcode_sltiu_flag * constant(crate::instructions::Opcode::Sltiu as u32);
        let imm = imm_0 + 256 * imm_1 + 2048 * imm_msb;
        let imm_upper = imm_1 + 248 * imm_msb;
        let imm_sign = 255 * imm_msb;
        let immediate = [imm_0, imm_upper, imm_sign, imm_sign];
        assert imm_msb * (1 - imm_msb) == 0;
        consume program_access(pc, opcode, rd_addr, rs1_addr, imm);
        consume range_check_8_11(imm_0, 256 * imm_1);
        read_reg rs1(clock, rs1_addr);

        let rs1_flipped = bitxor(rs1_next[3], 128, opcode_slti_flag);
        let imm_flipped = bitxor(immediate[3], 128, opcode_slti_flag);
        let rs1_msb = rs1_next[3]
            + opcode_slti_flag * (rs1_flipped - rs1_next[3]);
        let imm_msb_ordered = immediate[3]
            + opcode_slti_flag * (imm_flipped - immediate[3]);
        let lhs = [rs1_next[0], rs1_next[1], rs1_next[2], rs1_msb];
        let rhs = [immediate[0], immediate[1], immediate[2], imm_msb_ordered];
        let (difference, less_than) = sub_u32(lhs, rhs);
        let rd_value = [less_than, 0, 0, 0];

        consume registers_state(pc, clock);
        emit registers_state(pc + 4, clock + 1);
        write_reg rd(clock, rd_addr, rd_value);
        return pc + 4;
    }
}
