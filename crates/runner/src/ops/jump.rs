//! Jump operations.
//!
//! This file contains:
//! - jal family: jal (airs.md Section 12)
//! - jalr family: jalr (airs.md Section 11)

use super::utils::imm_to_felt;
use crate::trace::Tracer;
use crate::{Cpu, DecodedInst};

// =============================================================================
// JAL - airs.md Section 12
// =============================================================================

pub fn jal(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    use stwo::core::fields::m31::BaseField;
    let f = BaseField::from_u32_unchecked;

    let old_pc = cpu.pc;
    let return_addr = cpu.pc.wrapping_add(4);
    let rd = cpu.write_reg(inst.rd, return_addr, tracer);
    let clock = tracer.clock;
    cpu.pc = cpu.pc.wrapping_add(inst.imm as u32);

    let imm_felt = imm_to_felt(inst.imm);
    air::opcodes::jal::jal_fill(
        &mut tracer.jal,
        [
            f(clock),
            f(old_pc),
            f(rd.addr),
            f(rd.prev & 0xFF),
            f((rd.prev >> 8) & 0xFF),
            f((rd.prev >> 16) & 0xFF),
            f((rd.prev >> 24) & 0xFF),
            f(rd.clock_prev),
            f(rd.next & 0xFF),
            f((rd.next >> 8) & 0xFF),
            f((rd.next >> 16) & 0xFF),
            f((rd.next >> 24) & 0xFF),
            f(imm_felt),
        ],
        [],
    );
}

// =============================================================================
// JALR - airs.md Section 11
// =============================================================================

pub fn jalr(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    use stwo::core::fields::m31::BaseField;
    let f = BaseField::from_u32_unchecked;

    let old_pc = cpu.pc;
    let return_addr = cpu.pc.wrapping_add(4);
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let target = rs1.next.wrapping_add(inst.imm as u32);
    let target_aligned = target & !1; // Clear LSB
    let rd = cpu.write_reg(inst.rd, return_addr, tracer);
    let clock = tracer.clock;
    cpu.pc = target_aligned;

    let to_pc_over_two = target_aligned / 2;
    let to_pc_lsb = target & 1;
    let imm_felt = imm_to_felt(inst.imm);

    air::opcodes::jalr::jalr_fill(
        &mut tracer.jalr,
        [
            f(clock),
            f(old_pc),
            f(rd.addr),
            f(rd.prev & 0xFF),
            f((rd.prev >> 8) & 0xFF),
            f((rd.prev >> 16) & 0xFF),
            f((rd.prev >> 24) & 0xFF),
            f(rd.clock_prev),
            f(rd.next & 0xFF),
            f((rd.next >> 8) & 0xFF),
            f((rd.next >> 16) & 0xFF),
            f((rd.next >> 24) & 0xFF),
            f(rs1.addr),
            f(rs1.prev & 0xFF),
            f((rs1.prev >> 8) & 0xFF),
            f((rs1.prev >> 16) & 0xFF),
            f((rs1.prev >> 24) & 0xFF),
            f(rs1.clock_prev),
            f(rs1.next & 0xFF),
            f((rs1.next >> 8) & 0xFF),
            f((rs1.next >> 16) & 0xFF),
            f((rs1.next >> 24) & 0xFF),
            f(to_pc_over_two),
            f(to_pc_lsb),
            f(imm_felt),
        ],
        [],
    );
}
