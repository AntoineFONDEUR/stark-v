//! I-type ALU operations.
//!
//! This file contains:
//! - base_alu_imm family: addi, xori, ori, andi (airs.md Section 2)
//! - shifts_imm family: slli, srli, srai (airs.md Section 4)
//! - lt_imm family: slti, sltiu (airs.md Section 6)

use super::utils::{compute_lt_imm_witness, compute_shift_witness};
use crate::trace::Tracer;
use crate::{Cpu, DecodedInst};

// =============================================================================
// Helper functions for immediate decoding
// =============================================================================

/// Decode a 12-bit signed immediate into its limbs for AIR columns
pub(crate) fn decode_imm_limbs(imm: i32) -> (u32, u32, u32) {
    // imm is a 12-bit signed value (-2048 to 2047)
    let imm_unsigned = (imm as u32) & 0xFFF; // 12 bits
    let imm_0 = imm_unsigned & 0xFF; // bits [0:7]
    let imm_1 = (imm_unsigned >> 8) & 0x7; // bits [8:10]
    let imm_msb = (imm_unsigned >> 11) & 1; // bit [11] (sign bit)
    (imm_0, imm_1, imm_msb)
}

// =============================================================================
// Base ALU Imm (addi/xori/ori/andi) - airs.md Section 2
// =============================================================================

pub fn addi(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let result = rs1.next.wrapping_add(inst.imm as u32);
    let rd = cpu.write_reg(inst.rd, result, tracer);
    cpu.advance_pc();

    let (imm_0, imm_1, imm_msb) = decode_imm_limbs(inst.imm);
    // opcode flags: add=1, xor=0, or=0, and=0
    trace_op!(base_alu_imm: tracer, old_pc, rd, rs1,
        imm_0, imm_1, imm_msb,
        1, 0, 0, 0
    );
}

pub fn xori(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let result = rs1.next ^ (inst.imm as u32);
    let rd = cpu.write_reg(inst.rd, result, tracer);
    cpu.advance_pc();

    let (imm_0, imm_1, imm_msb) = decode_imm_limbs(inst.imm);
    // opcode flags: add=0, xor=1, or=0, and=0
    trace_op!(base_alu_imm: tracer, old_pc, rd, rs1,
        imm_0, imm_1, imm_msb,
        0, 1, 0, 0
    );
}

pub fn ori(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let result = rs1.next | (inst.imm as u32);
    let rd = cpu.write_reg(inst.rd, result, tracer);
    cpu.advance_pc();

    let (imm_0, imm_1, imm_msb) = decode_imm_limbs(inst.imm);
    // opcode flags: add=0, xor=0, or=1, and=0
    trace_op!(base_alu_imm: tracer, old_pc, rd, rs1,
        imm_0, imm_1, imm_msb,
        0, 0, 1, 0
    );
}

pub fn andi(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let result = rs1.next & (inst.imm as u32);
    let rd = cpu.write_reg(inst.rd, result, tracer);
    cpu.advance_pc();

    let (imm_0, imm_1, imm_msb) = decode_imm_limbs(inst.imm);
    // opcode flags: add=0, xor=0, or=0, and=1
    trace_op!(base_alu_imm: tracer, old_pc, rd, rs1,
        imm_0, imm_1, imm_msb,
        0, 0, 0, 1
    );
}

// =============================================================================
// Shifts Imm (slli/srli/srai) - airs.md Section 4
// =============================================================================

pub fn slli(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let shamt = inst.imm as u32 & 0x1F;
    let result = rs1.next << shamt;
    let rd = cpu.write_reg(inst.rd, result, tracer);
    cpu.advance_pc();

    let w = compute_shift_witness(rs1.next, shamt, true, false);
    let bit_multiplier = 1u32 << (shamt % 8);

    // opcode flags: sll=1, srl=0, sra=0
    trace_op!(shifts_imm: tracer, old_pc, rd, rs1,
        w.rs1_sign, shamt,
        1, 0, 0,  // opcode flags
        bit_multiplier, 0,  // bit_multiplier_left, bit_multiplier_right
        w.bit_shift_marker[0], w.bit_shift_marker[1], w.bit_shift_marker[2], w.bit_shift_marker[3],
        w.bit_shift_marker[4], w.bit_shift_marker[5], w.bit_shift_marker[6], w.bit_shift_marker[7],
        w.limb_shift_marker[0], w.limb_shift_marker[1], w.limb_shift_marker[2], w.limb_shift_marker[3],
        w.bit_shift_carry[0], w.bit_shift_carry[1], w.bit_shift_carry[2], w.bit_shift_carry[3]
    );
}

pub fn srli(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let shamt = inst.imm as u32 & 0x1F;
    let result = rs1.next >> shamt;
    let rd = cpu.write_reg(inst.rd, result, tracer);
    cpu.advance_pc();

    let w = compute_shift_witness(rs1.next, shamt, false, false);
    let bit_multiplier = 1u32 << (shamt % 8);

    // opcode flags: sll=0, srl=1, sra=0
    trace_op!(shifts_imm: tracer, old_pc, rd, rs1,
        w.rs1_sign, shamt,
        0, 1, 0,  // opcode flags
        0, bit_multiplier,  // bit_multiplier_left, bit_multiplier_right
        w.bit_shift_marker[0], w.bit_shift_marker[1], w.bit_shift_marker[2], w.bit_shift_marker[3],
        w.bit_shift_marker[4], w.bit_shift_marker[5], w.bit_shift_marker[6], w.bit_shift_marker[7],
        w.limb_shift_marker[0], w.limb_shift_marker[1], w.limb_shift_marker[2], w.limb_shift_marker[3],
        w.bit_shift_carry[0], w.bit_shift_carry[1], w.bit_shift_carry[2], w.bit_shift_carry[3]
    );
}

pub fn srai(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let shamt = inst.imm as u32 & 0x1F;
    let result = ((rs1.next as i32) >> shamt) as u32;
    let rd = cpu.write_reg(inst.rd, result, tracer);
    cpu.advance_pc();

    let w = compute_shift_witness(rs1.next, shamt, false, true);
    let bit_multiplier = 1u32 << (shamt % 8);

    // opcode flags: sll=0, srl=0, sra=1
    trace_op!(shifts_imm: tracer, old_pc, rd, rs1,
        w.rs1_sign, shamt,
        0, 0, 1,  // opcode flags
        0, bit_multiplier,  // bit_multiplier_left, bit_multiplier_right
        w.bit_shift_marker[0], w.bit_shift_marker[1], w.bit_shift_marker[2], w.bit_shift_marker[3],
        w.bit_shift_marker[4], w.bit_shift_marker[5], w.bit_shift_marker[6], w.bit_shift_marker[7],
        w.limb_shift_marker[0], w.limb_shift_marker[1], w.limb_shift_marker[2], w.limb_shift_marker[3],
        w.bit_shift_carry[0], w.bit_shift_carry[1], w.bit_shift_carry[2], w.bit_shift_carry[3]
    );
}

// =============================================================================
// Less Than Imm (slti/sltiu) - airs.md Section 6
// =============================================================================

pub fn slti(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let cmp_result = if (rs1.next as i32) < inst.imm { 1 } else { 0 };
    let rd = cpu.write_reg(inst.rd, cmp_result, tracer);
    cpu.advance_pc();

    let (imm_0, imm_1, imm_msb) = decode_imm_limbs(inst.imm);
    let w = compute_lt_imm_witness(rs1.next, inst.imm, true);

    // opcode flags: slti=1, sltiu=0
    trace_op!(lt_imm: tracer, old_pc, rd, rs1,
        cmp_result, w.rs1_msl_felt,
        imm_0, imm_1, imm_msb,
        1, 0,  // opcode flags
        w.diff_marker[0], w.diff_marker[1], w.diff_marker[2], w.diff_marker[3],
        w.diff_val
    );
}

pub fn sltiu(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let cmp_result = if rs1.next < (inst.imm as u32) { 1 } else { 0 };
    let rd = cpu.write_reg(inst.rd, cmp_result, tracer);
    cpu.advance_pc();

    let (imm_0, imm_1, imm_msb) = decode_imm_limbs(inst.imm);
    let w = compute_lt_imm_witness(rs1.next, inst.imm, false);

    // opcode flags: slti=0, sltiu=1
    trace_op!(lt_imm: tracer, old_pc, rd, rs1,
        cmp_result, w.rs1_msl_felt,
        imm_0, imm_1, imm_msb,
        0, 1,  // opcode flags
        w.diff_marker[0], w.diff_marker[1], w.diff_marker[2], w.diff_marker[3],
        w.diff_val
    );
}
