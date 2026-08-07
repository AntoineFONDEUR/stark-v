//! Load and store execution with generated witnesses and dynamic word accesses.

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

    fn load_store(
        clock,
        pc,
        r2_addr,
        rs1_addr,
        imm_felt,
        opcode_lb_flag,
        opcode_lh_flag,
        opcode_lbu_flag,
        opcode_lhu_flag,
        opcode_lw_flag,
        opcode_sb_flag,
        opcode_sh_flag,
        opcode_sw_flag,
    ) {
        let opcode = opcode_lb_flag * constant(crate::instructions::Opcode::Lb as u32)
            + opcode_lh_flag * constant(crate::instructions::Opcode::Lh as u32)
            + opcode_lbu_flag * constant(crate::instructions::Opcode::Lbu as u32)
            + opcode_lhu_flag * constant(crate::instructions::Opcode::Lhu as u32)
            + opcode_lw_flag * constant(crate::instructions::Opcode::Lw as u32)
            + opcode_sb_flag * constant(crate::instructions::Opcode::Sb as u32)
            + opcode_sh_flag * constant(crate::instructions::Opcode::Sh as u32)
            + opcode_sw_flag * constant(crate::instructions::Opcode::Sw as u32);
        let load_byte = opcode_lb_flag + opcode_lbu_flag;
        let load_half = opcode_lh_flag + opcode_lhu_flag;
        let store_byte = opcode_sb_flag;
        let store_half = opcode_sh_flag;
        let byte = load_byte + store_byte;
        let half = load_half + store_half;
        let word = opcode_lw_flag + opcode_sw_flag;
        let is_store = store_byte + store_half + opcode_sw_flag;
        let active = byte + half + word;
        let is_load = active - is_store;

        consume program_access(pc, opcode, rs1_addr, r2_addr, imm_felt);
        read_reg rs1(clock, rs1_addr);
        consume range_check_m31(rs1_next[0], rs1_next[3]);
        let rs1_value = rs1_next[0] + 256 * rs1_next[1]
            + 65536 * rs1_next[2] + 16777216 * rs1_next[3];
        let base_offset = bitand(rs1_next[0], 3);
        consume range_check_20((rs1_value - base_offset) * inv(4));
        let effective_addr = rs1_value + imm_felt;
        let effective_limbs = split_m31(effective_addr);
        let byte_offset = bitand(effective_limbs[0], 3);
        let offset_low = bitand(byte_offset, 1);
        let offset_high_mask = bitand(byte_offset, 2);
        let offset_high = offset_high_mask * inv(2);
        let aligned_addr = effective_addr - byte_offset;
        consume range_check_20(aligned_addr * inv(4));
        assert 0 == (half + word) * offset_low;
        assert 0 == word * offset_high;

        let marker_0 = (1 - offset_low) * (1 - offset_high);
        let marker_1 = offset_low * (1 - offset_high);
        let marker_2 = (1 - offset_low) * offset_high;
        let marker_3 = offset_low * offset_high;
        let source_addr_space = is_load;
        let destination_addr_space = is_store;
        let source_addr = is_load * aligned_addr + is_store * r2_addr;
        let destination_addr = is_load * r2_addr + is_store * aligned_addr;
        read_word source(clock, source_addr_space, source_addr);

        let selected_byte = marker_0 * source_next[0] + marker_1 * source_next[1]
            + marker_2 * source_next[2] + marker_3 * source_next[3];
        let selected_half_0 = (1 - offset_high) * source_next[0]
            + offset_high * source_next[2];
        let selected_half_1 = (1 - offset_high) * source_next[1]
            + offset_high * source_next[3];
        let byte_sign_mask = bitand(selected_byte, 128, opcode_lb_flag);
        let half_sign_mask = bitand(selected_half_1, 128, opcode_lh_flag);
        let sign_fill = 255 * (
            opcode_lb_flag * byte_sign_mask + opcode_lh_flag * half_sign_mask
        ) * inv(128);
        let loaded = [
            load_byte * selected_byte + load_half * selected_half_0
                + opcode_lw_flag * source_next[0],
            load_byte * sign_fill + load_half * selected_half_1
                + opcode_lw_flag * source_next[1],
            (load_byte + load_half) * sign_fill + opcode_lw_flag * source_next[2],
            (load_byte + load_half) * sign_fill + opcode_lw_flag * source_next[3],
        ];

        write_word destination(
            clock,
            destination_addr_space,
            destination_addr,
            [
                loaded[0]
                    + store_byte * (
                        destination_prev[0]
                            + marker_0 * (source_next[0] - destination_prev[0])
                    )
                    + store_half * (
                        (1 - offset_high) * source_next[0]
                            + offset_high * destination_prev[0]
                    )
                    + opcode_sw_flag * source_next[0],
                loaded[1]
                    + store_byte * (
                        destination_prev[1]
                            + marker_1 * (source_next[0] - destination_prev[1])
                    )
                    + store_half * (
                        (1 - offset_high) * source_next[1]
                            + offset_high * destination_prev[1]
                    )
                    + opcode_sw_flag * source_next[1],
                loaded[2]
                    + store_byte * (
                        destination_prev[2]
                            + marker_2 * (source_next[0] - destination_prev[2])
                    )
                    + store_half * (
                        (1 - offset_high) * destination_prev[2]
                            + offset_high * source_next[0]
                    )
                    + opcode_sw_flag * source_next[2],
                loaded[3]
                    + store_byte * (
                        destination_prev[3]
                            + marker_3 * (source_next[0] - destination_prev[3])
                    )
                    + store_half * (
                        (1 - offset_high) * destination_prev[3]
                            + offset_high * source_next[1]
                    )
                    + opcode_sw_flag * source_next[3],
            ],
        );

        consume registers_state(pc, clock);
        emit registers_state(pc + 4, clock + 1);
        return pc + 4;
    }
}
