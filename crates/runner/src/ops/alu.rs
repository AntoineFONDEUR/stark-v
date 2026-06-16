//! R-type ALU operations.
//!
//! This file contains:
//! - base_alu_reg family: add, sub, xor, or, and (airs.md Section 1)
//! - shifts_reg family: sll, srl, sra (airs.md Section 3)
//! - lt_reg family: slt, sltu (airs.md Section 5)

use super::utils::{compute_lt_reg_witness, compute_shift_witness};
use crate::trace::Tracer;
use crate::{Cpu, DecodedInst};

// =============================================================================
// Base ALU Reg (add/sub/xor/or/and) - airs.md Section 1
// =============================================================================

pub fn add(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let rs2 = cpu.read_reg(inst.rs2, tracer);
    let result = rs1.next.wrapping_add(rs2.next);
    let rd = cpu.write_reg(inst.rd, result, tracer);
    cpu.advance_pc();
    // opcode flags: add=1, sub=0, xor=0, or=0, and=0
    trace_op!(base_alu_reg: tracer, old_pc, rd, rs1, rs2, 1, 0, 0, 0, 0);
}

pub fn sub(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let rs2 = cpu.read_reg(inst.rs2, tracer);
    let result = rs1.next.wrapping_sub(rs2.next);
    let rd = cpu.write_reg(inst.rd, result, tracer);
    cpu.advance_pc();
    // opcode flags: add=0, sub=1, xor=0, or=0, and=0
    trace_op!(base_alu_reg: tracer, old_pc, rd, rs1, rs2, 0, 1, 0, 0, 0);
}

pub fn xor(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let rs2 = cpu.read_reg(inst.rs2, tracer);
    let result = rs1.next ^ rs2.next;
    let rd = cpu.write_reg(inst.rd, result, tracer);
    cpu.advance_pc();
    // opcode flags: add=0, sub=0, xor=1, or=0, and=0
    trace_op!(base_alu_reg: tracer, old_pc, rd, rs1, rs2, 0, 0, 1, 0, 0);
}

pub fn or(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let rs2 = cpu.read_reg(inst.rs2, tracer);
    let result = rs1.next | rs2.next;
    let rd = cpu.write_reg(inst.rd, result, tracer);
    cpu.advance_pc();
    // opcode flags: add=0, sub=0, xor=0, or=1, and=0
    trace_op!(base_alu_reg: tracer, old_pc, rd, rs1, rs2, 0, 0, 0, 1, 0);
}

pub fn and(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let rs2 = cpu.read_reg(inst.rs2, tracer);
    let result = rs1.next & rs2.next;
    let rd = cpu.write_reg(inst.rd, result, tracer);
    cpu.advance_pc();
    // opcode flags: add=0, sub=0, xor=0, or=0, and=1
    trace_op!(base_alu_reg: tracer, old_pc, rd, rs1, rs2, 0, 0, 0, 0, 1);
}

// =============================================================================
// Shifts Reg (sll/srl/sra) - airs.md Section 3
// =============================================================================

pub fn sll(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let rs2 = cpu.read_reg(inst.rs2, tracer);
    let shamt = rs2.next & 0x1F;
    let result = rs1.next << shamt;
    let rd = cpu.write_reg(inst.rd, result, tracer);
    cpu.advance_pc();

    let w = compute_shift_witness(rs1.next, shamt, true, false);
    let bit_multiplier = 1u32 << (shamt % 8);

    // opcode flags: sll=1, srl=0, sra=0
    trace_op!(shifts_reg: tracer, old_pc, rd, rs1, rs2,
        w.rs1_sign,
        1, 0, 0,  // opcode flags
        bit_multiplier, 0,  // bit_multiplier_left, bit_multiplier_right
        w.bit_shift_marker[0], w.bit_shift_marker[1], w.bit_shift_marker[2], w.bit_shift_marker[3],
        w.bit_shift_marker[4], w.bit_shift_marker[5], w.bit_shift_marker[6], w.bit_shift_marker[7],
        w.limb_shift_marker[0], w.limb_shift_marker[1], w.limb_shift_marker[2], w.limb_shift_marker[3],
        w.bit_shift_carry[0], w.bit_shift_carry[1], w.bit_shift_carry[2], w.bit_shift_carry[3]
    );
}

pub fn srl(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let rs2 = cpu.read_reg(inst.rs2, tracer);
    let shamt = rs2.next & 0x1F;
    let result = rs1.next >> shamt;
    let rd = cpu.write_reg(inst.rd, result, tracer);
    cpu.advance_pc();

    let w = compute_shift_witness(rs1.next, shamt, false, false);
    let bit_multiplier = 1u32 << (shamt % 8);

    // opcode flags: sll=0, srl=1, sra=0
    trace_op!(shifts_reg: tracer, old_pc, rd, rs1, rs2,
        w.rs1_sign,
        0, 1, 0,  // opcode flags
        0, bit_multiplier,  // bit_multiplier_left, bit_multiplier_right
        w.bit_shift_marker[0], w.bit_shift_marker[1], w.bit_shift_marker[2], w.bit_shift_marker[3],
        w.bit_shift_marker[4], w.bit_shift_marker[5], w.bit_shift_marker[6], w.bit_shift_marker[7],
        w.limb_shift_marker[0], w.limb_shift_marker[1], w.limb_shift_marker[2], w.limb_shift_marker[3],
        w.bit_shift_carry[0], w.bit_shift_carry[1], w.bit_shift_carry[2], w.bit_shift_carry[3]
    );
}

pub fn sra(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let rs2 = cpu.read_reg(inst.rs2, tracer);
    let shamt = rs2.next & 0x1F;
    let result = ((rs1.next as i32) >> shamt) as u32;
    let rd = cpu.write_reg(inst.rd, result, tracer);
    cpu.advance_pc();

    let w = compute_shift_witness(rs1.next, shamt, false, true);
    let bit_multiplier = 1u32 << (shamt % 8);

    // opcode flags: sll=0, srl=0, sra=1
    trace_op!(shifts_reg: tracer, old_pc, rd, rs1, rs2,
        w.rs1_sign,
        0, 0, 1,  // opcode flags
        0, bit_multiplier,  // bit_multiplier_left, bit_multiplier_right
        w.bit_shift_marker[0], w.bit_shift_marker[1], w.bit_shift_marker[2], w.bit_shift_marker[3],
        w.bit_shift_marker[4], w.bit_shift_marker[5], w.bit_shift_marker[6], w.bit_shift_marker[7],
        w.limb_shift_marker[0], w.limb_shift_marker[1], w.limb_shift_marker[2], w.limb_shift_marker[3],
        w.bit_shift_carry[0], w.bit_shift_carry[1], w.bit_shift_carry[2], w.bit_shift_carry[3]
    );
}

// =============================================================================
// Less Than Reg (slt/sltu) - airs.md Section 5
// =============================================================================

pub fn slt(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let rs2 = cpu.read_reg(inst.rs2, tracer);
    let cmp_result = if (rs1.next as i32) < (rs2.next as i32) {
        1
    } else {
        0
    };
    let rd = cpu.write_reg(inst.rd, cmp_result, tracer);
    cpu.advance_pc();

    let w = compute_lt_reg_witness(rs1.next, rs2.next, true);

    // opcode flags: slt=1, sltu=0
    trace_op!(lt_reg: tracer, old_pc, rd, rs1, rs2,
        cmp_result, w.rs1_msl_felt, w.rs2_msl_felt,
        1, 0,  // opcode flags
        w.diff_marker[0], w.diff_marker[1], w.diff_marker[2], w.diff_marker[3],
        w.diff_val
    );
}

pub fn sltu(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let rs2 = cpu.read_reg(inst.rs2, tracer);
    let cmp_result = if rs1.next < rs2.next { 1 } else { 0 };
    let rd = cpu.write_reg(inst.rd, cmp_result, tracer);
    cpu.advance_pc();

    let w = compute_lt_reg_witness(rs1.next, rs2.next, false);

    // opcode flags: slt=0, sltu=1
    trace_op!(lt_reg: tracer, old_pc, rd, rs1, rs2,
        cmp_result, w.rs1_msl_felt, w.rs2_msl_felt,
        0, 1,  // opcode flags
        w.diff_marker[0], w.diff_marker[1], w.diff_marker[2], w.diff_marker[3],
        w.diff_val
    );
}
