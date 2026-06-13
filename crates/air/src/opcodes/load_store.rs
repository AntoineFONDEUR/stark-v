//! Load/store opcodes (lb/lh/lbu/lhu/lw/sb/sh/sw) as a felt function (airs.md
//! Section 13). A one-hot byte/half marker selects the accessed sub-word, the
//! source and destination alternate between register and RW-memory address
//! spaces by load/store, and signed loads sign-extend the high bytes. The flag
//! sum is the row activity indicator `enabler()`.

stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [],
    embedded_component: true,

    relation program_access(5);
    relation registers_state(2);
    relation memory_access(7);
    relation range_check_20(1);
    relation range_check_m31(2);

    fn load_store(
        clock,
        pc,
        dst_addr,
        dst_prev_0,
        dst_prev_1,
        dst_prev_2,
        dst_prev_3,
        dst_clock_prev,
        dst_next_0,
        dst_next_1,
        dst_next_2,
        dst_next_3,
        rs1_addr,
        rs1_prev_0,
        rs1_prev_1,
        rs1_prev_2,
        rs1_prev_3,
        rs1_clock_prev,
        rs1_next_0,
        rs1_next_1,
        rs1_next_2,
        rs1_next_3,
        src_addr,
        src_prev_0,
        src_prev_1,
        src_prev_2,
        src_prev_3,
        src_clock_prev,
        src_next_0,
        src_next_1,
        src_next_2,
        src_next_3,
        r2_idx,
        imm_felt,
        src_msb,
        shift_amount,
        src_addr_selector,
        dst_addr_selector,
        marker_0,
        marker_1,
        marker_2,
        marker_3,
        opcode_lb_flag,
        opcode_lh_flag,
        opcode_lbu_flag,
        opcode_lhu_flag,
        opcode_lw_flag,
        opcode_sb_flag,
        opcode_sh_flag,
        opcode_sw_flag
    ) {
        let row_enabler = opcode_lb_flag + opcode_lh_flag + opcode_lbu_flag + opcode_lhu_flag + opcode_lw_flag + opcode_sb_flag + opcode_sh_flag + opcode_sw_flag;
        let expected_opcode_id = opcode_lb_flag * constant(crate::instructions::Opcode::Lb as u32)
                    + opcode_lh_flag * constant(crate::instructions::Opcode::Lh as u32)
                    + opcode_lbu_flag * constant(crate::instructions::Opcode::Lbu as u32)
                    + opcode_lhu_flag * constant(crate::instructions::Opcode::Lhu as u32)
                    + opcode_lw_flag * constant(crate::instructions::Opcode::Lw as u32)
                    + opcode_sb_flag * constant(crate::instructions::Opcode::Sb as u32)
                    + opcode_sh_flag * constant(crate::instructions::Opcode::Sh as u32)
                    + opcode_sw_flag * constant(crate::instructions::Opcode::Sw as u32);
        let opcode_b_flag = opcode_lbu_flag + opcode_lb_flag + opcode_sb_flag;
        let opcode_h_flag = opcode_lhu_flag + opcode_lh_flag + opcode_sh_flag;
        let opcode_w_flag = opcode_lw_flag + opcode_sw_flag;
        let is_signed = opcode_lb_flag + opcode_lh_flag;
        let load_b_flag = opcode_lb_flag + opcode_lbu_flag;
        let load_h_flag = opcode_lh_flag + opcode_lhu_flag;
        let is_store = opcode_sb_flag + opcode_sh_flag + opcode_sw_flag;
        let is_load = row_enabler - is_store;
        let src_as = is_load;
        let dst_as = is_store;
        let mem_addr = rs1_next_0 + pow2(8) * rs1_next_1 + pow2(16) * rs1_next_2
                    + pow2(24) * rs1_next_3 + imm_felt;
        let sum_markers = marker_0 + marker_1 + marker_2 + marker_3;
        let shift_id = marker_1 + 2 * marker_2 + 3 * marker_3;
        let signed_mask = is_signed * src_msb * (pow2(8) - 1);
        let aligned_addr_quarter = (src_addr_selector + dst_addr_selector - r2_idx) * inv(4);
        let pc_next = pc + 4;
        let clock_next = clock + 1;
        let rs1_clock_diff = clock - rs1_clock_prev;
        let src_clock_diff = clock - src_clock_prev;
        let dst_clock_diff = clock - dst_clock_prev;

        constrain marker_0 * (1 - marker_0);
        constrain marker_1 * (1 - marker_1);
        constrain marker_2 * (1 - marker_2);
        constrain marker_3 * (1 - marker_3);
        constrain shift_amount - (opcode_b_flag * shift_id
                    + opcode_h_flag * (shift_id - 1) * inv(2));
        constrain src_addr_selector
                    - (is_load * (mem_addr - shift_amount) + is_store * r2_idx);
        constrain dst_addr_selector
                    - (is_load * r2_idx + is_store * (mem_addr - shift_amount));
        constrain opcode_b_flag * (1 - sum_markers);
        constrain opcode_h_flag * (2 - sum_markers);
        constrain opcode_h_flag * (1 - shift_id) * (5 - shift_id);
        constrain load_b_flag * (signed_mask - dst_next_1);
        constrain load_b_flag * (signed_mask - dst_next_2);
        constrain load_b_flag * (signed_mask - dst_next_3);
        constrain load_b_flag * (dst_next_0 - src_next_0) * marker_0;
        constrain opcode_sb_flag * (dst_next_0 - src_next_0) * marker_0;
        constrain load_b_flag * (dst_next_0 - src_next_1) * marker_1;
        constrain opcode_sb_flag * (dst_next_1 - src_next_0) * marker_1;
        constrain load_b_flag * (dst_next_0 - src_next_2) * marker_2;
        constrain opcode_sb_flag * (dst_next_2 - src_next_0) * marker_2;
        constrain load_b_flag * (dst_next_0 - src_next_3) * marker_3;
        constrain opcode_sb_flag * (dst_next_3 - src_next_0) * marker_3;
        constrain load_h_flag * (signed_mask - dst_next_2);
        constrain load_h_flag * (signed_mask - dst_next_3);
        constrain load_h_flag * (5 - shift_id) * inv(4) * (dst_next_0 - src_next_0);
        constrain load_h_flag * (5 - shift_id) * inv(4) * (dst_next_1 - src_next_1);
        constrain load_h_flag * (shift_id - 1) * inv(4) * (dst_next_0 - src_next_2);
        constrain load_h_flag * (shift_id - 1) * inv(4) * (dst_next_1 - src_next_3);
        constrain opcode_sh_flag * (5 - shift_id) * inv(4) * (dst_next_0 - src_next_0);
        constrain opcode_sh_flag * (5 - shift_id) * inv(4) * (dst_next_1 - src_next_1);
        constrain opcode_sh_flag * (shift_id - 1) * inv(4) * (dst_next_2 - src_next_0);
        constrain opcode_sh_flag * (shift_id - 1) * inv(4) * (dst_next_3 - src_next_1);
        constrain opcode_w_flag * (dst_next_0 - src_next_0);
        constrain opcode_w_flag * (dst_next_1 - src_next_1);
        constrain opcode_w_flag * (dst_next_2 - src_next_2);
        constrain opcode_w_flag * (dst_next_3 - src_next_3);

        consume program_access(pc, expected_opcode_id, rs1_addr, r2_idx, imm_felt);
        consume registers_state(pc, clock);
        emit registers_state(pc_next, clock_next);
        consume memory_access(constant(0), rs1_addr, rs1_clock_prev, rs1_prev_0, rs1_prev_1, rs1_prev_2, rs1_prev_3);
        emit memory_access(constant(0), rs1_addr, clock, rs1_next_0, rs1_next_1, rs1_next_2, rs1_next_3);
        consume range_check_20(rs1_clock_diff);
        consume range_check_20(aligned_addr_quarter);
        consume range_check_m31(rs1_next_0, rs1_next_3);
        consume memory_access(src_as, src_addr_selector, src_clock_prev, src_prev_0, src_prev_1, src_prev_2, src_prev_3);
        emit memory_access(src_as, src_addr_selector, clock, src_next_0, src_next_1, src_next_2, src_next_3);
        consume range_check_20(src_clock_diff);
        consume memory_access(dst_as, dst_addr_selector, dst_clock_prev, dst_prev_0, dst_prev_1, dst_prev_2, dst_prev_3);
        emit memory_access(dst_as, dst_addr_selector, clock, dst_next_0, dst_next_1, dst_next_2, dst_next_3);
        consume range_check_20(dst_clock_diff);
        return pc;
    }
}
