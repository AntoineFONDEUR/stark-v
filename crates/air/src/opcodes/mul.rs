//! Low-word multiplication with generated execution and AIR.

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

    inline fn low_product(lhs: [felt; 4], rhs: [felt; 4]) {
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

        let result = [step_0[0], step_1[0], step_2[0], step_3[0]];
        return result;
    }

    fn mul(clock, pc, rd_addr, rs1_addr, rs2_addr) {
        consume program_access(
            pc,
            constant(crate::instructions::Opcode::Mul as u32),
            rd_addr,
            rs1_addr,
            rs2_addr,
        );
        read_reg rs1(clock, rs1_addr);
        read_reg rs2(clock, rs2_addr);
        let rd_value = low_product(rs1_next, rs2_next);

        consume registers_state(pc, clock);
        emit registers_state(pc + 4, clock + 1);
        write_reg rd(clock, rd_addr, rd_value);
        return pc + 4;
    }
}
