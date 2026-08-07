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

        let (add_result, add_carry) = add_u32(
            rs1_next,
            rs2_next,
            opcode_add_flag,
        );
        let (sub_result, sub_borrow) = sub_u32(
            rs1_next,
            rs2_next,
            opcode_sub_flag,
        );
        let xor_0 = bitxor(rs1_next[0], rs2_next[0], opcode_xor_flag);
        let xor_1 = bitxor(rs1_next[1], rs2_next[1], opcode_xor_flag);
        let xor_2 = bitxor(rs1_next[2], rs2_next[2], opcode_xor_flag);
        let xor_3 = bitxor(rs1_next[3], rs2_next[3], opcode_xor_flag);
        let xor_result = [xor_0, xor_1, xor_2, xor_3];
        let or_0 = bitor(rs1_next[0], rs2_next[0], opcode_or_flag);
        let or_1 = bitor(rs1_next[1], rs2_next[1], opcode_or_flag);
        let or_2 = bitor(rs1_next[2], rs2_next[2], opcode_or_flag);
        let or_3 = bitor(rs1_next[3], rs2_next[3], opcode_or_flag);
        let or_result = [or_0, or_1, or_2, or_3];
        let and_0 = bitand(rs1_next[0], rs2_next[0], opcode_and_flag);
        let and_1 = bitand(rs1_next[1], rs2_next[1], opcode_and_flag);
        let and_2 = bitand(rs1_next[2], rs2_next[2], opcode_and_flag);
        let and_3 = bitand(rs1_next[3], rs2_next[3], opcode_and_flag);
        let and_result = [and_0, and_1, and_2, and_3];
        let rd_value = map(
            i,
            0..4,
            opcode_add_flag * add_result[i]
                + opcode_sub_flag * sub_result[i]
                + opcode_xor_flag * xor_result[i]
                + opcode_or_flag * or_result[i]
                + opcode_and_flag * and_result[i],
        );

        consume registers_state(pc, clock);
        emit registers_state(pc + 4, clock + 1);
        write_reg rd(clock, rd_addr, rd_value);
        return pc + 4;
    }
}
