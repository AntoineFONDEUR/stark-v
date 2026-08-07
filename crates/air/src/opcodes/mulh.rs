//! High-word multiplication variants with generated execution and AIR.

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

    inline fn wide_product(
        lhs: [felt; 4],
        rhs: [felt; 4],
        lhs_fill,
        rhs_fill,
    ) {
        let step_0 = split_m31(lhs[0] * rhs[0]);
        assert step_0[3] == 0;
        let carry_0 = step_0[1] + 256 * step_0[2];

        let step_1 = split_m31(carry_0 + lhs[0] * rhs[1] + lhs[1] * rhs[0]);
        assert step_1[3] == 0;
        let carry_1 = step_1[1] + 256 * step_1[2];

        let step_2 = split_m31(
            carry_1 + lhs[0] * rhs[2] + lhs[1] * rhs[1] + lhs[2] * rhs[0],
        );
        assert step_2[3] == 0;
        let carry_2 = step_2[1] + 256 * step_2[2];

        let step_3 = split_m31(
            carry_2 + lhs[0] * rhs[3] + lhs[1] * rhs[2]
                + lhs[2] * rhs[1] + lhs[3] * rhs[0],
        );
        assert step_3[3] == 0;
        let carry_3 = step_3[1] + 256 * step_3[2];

        let step_4 = split_m31(
            carry_3 + lhs[0] * rhs_fill + lhs[1] * rhs[3]
                + lhs[2] * rhs[2] + lhs[3] * rhs[1] + lhs_fill * rhs[0],
        );
        assert step_4[3] == 0;
        let carry_4 = step_4[1] + 256 * step_4[2];

        let step_5 = split_m31(
            carry_4 + lhs[0] * rhs_fill + lhs[1] * rhs_fill
                + lhs[2] * rhs[3] + lhs[3] * rhs[2]
                + lhs_fill * rhs[1] + lhs_fill * rhs[0],
        );
        assert step_5[3] == 0;
        let carry_5 = step_5[1] + 256 * step_5[2];

        let step_6 = split_m31(
            carry_5 + lhs[0] * rhs_fill + lhs[1] * rhs_fill
                + lhs[2] * rhs_fill + lhs[3] * rhs[3]
                + lhs_fill * rhs[2] + lhs_fill * rhs[1] + lhs_fill * rhs[0],
        );
        assert step_6[3] == 0;
        let carry_6 = step_6[1] + 256 * step_6[2];

        let step_7 = split_m31(
            carry_6 + lhs[0] * rhs_fill + lhs[1] * rhs_fill
                + lhs[2] * rhs_fill + lhs[3] * rhs_fill
                + lhs_fill * rhs[3] + lhs_fill * rhs[2]
                + lhs_fill * rhs[1] + lhs_fill * rhs[0],
        );
        assert step_7[3] == 0;

        let low = [step_0[0], step_1[0], step_2[0], step_3[0]];
        let high = [step_4[0], step_5[0], step_6[0], step_7[0]];
        return (low, high);
    }

    fn mulh(
        clock,
        pc,
        rd_addr,
        rs1_addr,
        rs2_addr,
        opcode_mulh_flag,
        opcode_mulhsu_flag,
        opcode_mulhu_flag,
    ) {
        let opcode = opcode_mulh_flag * constant(crate::instructions::Opcode::Mulh as u32)
            + opcode_mulhsu_flag * constant(crate::instructions::Opcode::Mulhsu as u32)
            + opcode_mulhu_flag * constant(crate::instructions::Opcode::Mulhu as u32);
        consume program_access(pc, opcode, rd_addr, rs1_addr, rs2_addr);
        read_reg rs1(clock, rs1_addr);
        read_reg rs2(clock, rs2_addr);

        let rs1_sign_mask = bitand(
            rs1_next[3],
            128 * (opcode_mulh_flag + opcode_mulhsu_flag),
        );
        let rs2_sign_mask = bitand(rs2_next[3], 128 * opcode_mulh_flag);
        let rs1_fill = 255 * rs1_sign_mask * inv(128);
        let rs2_fill = 255 * rs2_sign_mask * inv(128);
        let (low, high) = wide_product(rs1_next, rs2_next, rs1_fill, rs2_fill);

        consume registers_state(pc, clock);
        emit registers_state(pc + 4, clock + 1);
        write_reg rd(clock, rd_addr, high);
        return pc + 4;
    }
}
