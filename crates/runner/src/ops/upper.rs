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
    use stwo::core::fields::m31::BaseField;
    let f = BaseField::from_u32_unchecked;

    // LUI: rd = imm << 12 (imm is already shifted in decode)
    let rd = cpu.write_reg(inst.rd, inst.imm as u32, tracer);
    let old_pc = cpu.pc;
    let clock = tracer.clock;
    cpu.advance_pc();

    // The immediate for LUI is a 20-bit value in the upper bits; the stored
    // imm is already shifted, so extract the upper 20 bits.
    let imm_val = (inst.imm as u32) >> 12;
    let imm_0 = imm_val & 0xF; // bits [0:3]
    let imm_1 = (imm_val >> 4) & 0xFF; // bits [4:11]
    let imm_2 = (imm_val >> 12) & 0xFF; // bits [12:19] (only 4 bits)

    // Fill the felt-function lui table with the access values the AIR reads:
    // (clock, pc, rd_addr, rd_prev limbs, rd_clock_prev, imm limbs).
    air::opcodes::lui::lui_fill(
        &mut tracer.lui,
        [
            f(clock),
            f(old_pc),
            f(rd.addr),
            f(rd.prev & 0xFF),
            f((rd.prev >> 8) & 0xFF),
            f((rd.prev >> 16) & 0xFF),
            f((rd.prev >> 24) & 0xFF),
            f(rd.clock_prev),
            f(imm_0),
            f(imm_1),
            f(imm_2),
        ],
        [],
    );
}

// =============================================================================
// AUIPC - airs.md Section 10
// =============================================================================

pub fn auipc(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    use stwo::core::fields::m31::BaseField;
    let f = BaseField::from_u32_unchecked;

    let old_pc = cpu.pc;
    let result = cpu.pc.wrapping_add(inst.imm as u32);
    let rd = cpu.write_reg(inst.rd, result, tracer);
    let clock = tracer.clock;
    cpu.advance_pc();

    let imm_felt = imm_to_felt(inst.imm);
    air::opcodes::auipc::auipc_fill(
        &mut tracer.auipc,
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
