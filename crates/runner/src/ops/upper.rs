//! Upper immediate operations.
//!
//! This file contains:
//! - lui family: lui (airs.md Section 9)
//! - auipc family: auipc (airs.md Section 10)

use super::utils::imm_to_felt;
use crate::trace::Tracer;
use crate::{Cpu, DecodedInst};

// =============================================================================
// LUI - airs.md Section 9
// =============================================================================

pub fn lui(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    // LUI: rd = imm << 12 (imm is already shifted in decode)
    let rd = cpu.write_reg(inst.rd, inst.imm as u32, tracer);
    let old_pc = cpu.pc;
    cpu.advance_pc();

    // The immediate for LUI is a 20-bit value in the upper bits
    // imm as stored has already been shifted, so we need to extract the upper 20 bits
    let imm_val = (inst.imm as u32) >> 12; // Get the actual 20-bit immediate
    let imm_0 = imm_val & 0xF; // bits [0:3]
    let imm_1 = (imm_val >> 4) & 0xFF; // bits [4:11]
    let imm_2 = (imm_val >> 12) & 0xFF; // bits [12:19] (only 4 bits)

    trace_op!(lui: tracer, old_pc, rd,
        imm_0, imm_1, imm_2
    );
}

// =============================================================================
// AUIPC - airs.md Section 10
// =============================================================================

pub fn auipc(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let result = cpu.pc.wrapping_add(inst.imm as u32);
    let rd = cpu.write_reg(inst.rd, result, tracer);
    cpu.advance_pc();

    let imm_felt = imm_to_felt(inst.imm);
    trace_op!(auipc: tracer, old_pc, rd, imm_felt);
}
