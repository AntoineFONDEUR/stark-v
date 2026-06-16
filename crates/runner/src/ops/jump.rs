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
    let old_pc = cpu.pc;
    let return_addr = cpu.pc.wrapping_add(4);
    let rd = cpu.write_reg(inst.rd, return_addr, tracer);
    cpu.pc = cpu.pc.wrapping_add(inst.imm as u32);

    let imm_felt = imm_to_felt(inst.imm);
    trace_op!(jal: tracer, old_pc, rd, imm_felt);
}

// =============================================================================
// JALR - airs.md Section 11
// =============================================================================

pub fn jalr(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let return_addr = cpu.pc.wrapping_add(4);
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let target = rs1.next.wrapping_add(inst.imm as u32);
    let target_aligned = target & !1; // Clear LSB
    let rd = cpu.write_reg(inst.rd, return_addr, tracer);
    cpu.pc = target_aligned;

    // Witness columns for JALR
    let to_pc_over_two = target_aligned / 2;
    let to_pc_lsb = target & 1;
    let imm_felt = imm_to_felt(inst.imm);

    trace_op!(jalr: tracer, old_pc, rd, rs1,
        to_pc_over_two, to_pc_lsb,
        imm_felt
    );
}
