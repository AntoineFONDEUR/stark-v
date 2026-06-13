//! R-type ALU operations.
//!
//! This file contains:
//! - base_alu_reg family: add, sub, xor, or, and (airs.md Section 1)
//! - shifts_reg family: sll, srl, sra (airs.md Section 3)
//! - lt_reg family: slt, sltu (airs.md Section 5)

use super::utils::{compute_lt_reg_witness, compute_shift_witness};
use crate::trace::Tracer;
use crate::{Cpu, DecodedInst};

/// Fill one base_alu_reg row in the felt-function table from the rs1/rs2 reads
/// and rd write accesses and the one-hot opcode flags.
#[allow(clippy::too_many_arguments)]
pub(crate) fn fill_base_alu_reg(
    tracer: &mut Tracer,
    pc: u32,
    rd: &crate::trace::Access,
    rs1: &crate::trace::Access,
    rs2: &crate::trace::Access,
    flags: [u32; 5],
) {
    use stwo::core::fields::m31::BaseField;
    let f = BaseField::from_u32_unchecked;
    let clock = tracer.clock;
    let limbs = |a: &crate::trace::Access| {
        [
            f(a.addr),
            f(a.prev & 0xFF),
            f((a.prev >> 8) & 0xFF),
            f((a.prev >> 16) & 0xFF),
            f((a.prev >> 24) & 0xFF),
            f(a.clock_prev),
            f(a.next & 0xFF),
            f((a.next >> 8) & 0xFF),
            f((a.next >> 16) & 0xFF),
            f((a.next >> 24) & 0xFF),
        ]
    };
    let rd = limbs(rd);
    let rs1 = limbs(rs1);
    let rs2 = limbs(rs2);
    air::opcodes::base_alu_reg::base_alu_reg_fill(
        &mut tracer.base_alu_reg,
        [
            f(clock),
            f(pc),
            rd[0],
            rd[1],
            rd[2],
            rd[3],
            rd[4],
            rd[5],
            rd[6],
            rd[7],
            rd[8],
            rd[9],
            rs1[0],
            rs1[1],
            rs1[2],
            rs1[3],
            rs1[4],
            rs1[5],
            rs1[6],
            rs1[7],
            rs1[8],
            rs1[9],
            rs2[0],
            rs2[1],
            rs2[2],
            rs2[3],
            rs2[4],
            rs2[5],
            rs2[6],
            rs2[7],
            rs2[8],
            rs2[9],
            f(flags[0]),
            f(flags[1]),
            f(flags[2]),
            f(flags[3]),
            f(flags[4]),
        ],
        [],
    );
}

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
    fill_base_alu_reg(tracer, old_pc, &rd, &rs1, &rs2, [1, 0, 0, 0, 0]);
}

pub fn sub(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let rs2 = cpu.read_reg(inst.rs2, tracer);
    let result = rs1.next.wrapping_sub(rs2.next);
    let rd = cpu.write_reg(inst.rd, result, tracer);
    cpu.advance_pc();
    // opcode flags: add=0, sub=1, xor=0, or=0, and=0
    fill_base_alu_reg(tracer, old_pc, &rd, &rs1, &rs2, [0, 1, 0, 0, 0]);
}

pub fn xor(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let rs2 = cpu.read_reg(inst.rs2, tracer);
    let result = rs1.next ^ rs2.next;
    let rd = cpu.write_reg(inst.rd, result, tracer);
    cpu.advance_pc();
    // opcode flags: add=0, sub=0, xor=1, or=0, and=0
    fill_base_alu_reg(tracer, old_pc, &rd, &rs1, &rs2, [0, 0, 1, 0, 0]);
}

pub fn or(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let rs2 = cpu.read_reg(inst.rs2, tracer);
    let result = rs1.next | rs2.next;
    let rd = cpu.write_reg(inst.rd, result, tracer);
    cpu.advance_pc();
    // opcode flags: add=0, sub=0, xor=0, or=1, and=0
    fill_base_alu_reg(tracer, old_pc, &rd, &rs1, &rs2, [0, 0, 0, 1, 0]);
}

pub fn and(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let rs2 = cpu.read_reg(inst.rs2, tracer);
    let result = rs1.next & rs2.next;
    let rd = cpu.write_reg(inst.rd, result, tracer);
    cpu.advance_pc();
    // opcode flags: add=0, sub=0, xor=0, or=0, and=1
    fill_base_alu_reg(tracer, old_pc, &rd, &rs1, &rs2, [0, 0, 0, 0, 1]);
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

/// Fill one lt_reg row from the rs1/rs2 reads, rd write, the comparison bit,
/// the most-significant-limb witnesses, difference markers and the slt/sltu
/// flags.
#[allow(clippy::too_many_arguments)]
pub(crate) fn fill_lt_reg(
    tracer: &mut Tracer,
    pc: u32,
    rd: &crate::trace::Access,
    rs1: &crate::trace::Access,
    rs2: &crate::trace::Access,
    cmp_result: u32,
    rs1_msl_felt: u32,
    rs2_msl_felt: u32,
    flags: [u32; 2],
    diff_marker: [u32; 4],
    diff_val: u32,
) {
    use stwo::core::fields::m31::BaseField;
    let f = BaseField::from_u32_unchecked;
    let clock = tracer.clock;
    let limbs = |a: &crate::trace::Access| {
        [
            a.addr,
            a.prev & 0xFF,
            (a.prev >> 8) & 0xFF,
            (a.prev >> 16) & 0xFF,
            (a.prev >> 24) & 0xFF,
            a.clock_prev,
            a.next & 0xFF,
            (a.next >> 8) & 0xFF,
            (a.next >> 16) & 0xFF,
            (a.next >> 24) & 0xFF,
        ]
    };
    let rd = limbs(rd);
    let rs1 = limbs(rs1);
    let rs2 = limbs(rs2);
    let mut args = Vec::with_capacity(42);
    args.extend([clock, pc]);
    args.extend(rd);
    args.extend(rs1);
    args.extend(rs2);
    args.extend([cmp_result, rs1_msl_felt, rs2_msl_felt, flags[0], flags[1]]);
    args.extend(diff_marker);
    args.push(diff_val);
    air::opcodes::lt_reg::lt_reg_fill(
        &mut tracer.lt_reg,
        args.into_iter()
            .map(f)
            .collect::<Vec<_>>()
            .try_into()
            .expect("lt_reg fill takes 42 felts"),
        [],
    );
}

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
    fill_lt_reg(
        tracer,
        old_pc,
        &rd,
        &rs1,
        &rs2,
        cmp_result,
        w.rs1_msl_felt,
        w.rs2_msl_felt,
        [1, 0],
        w.diff_marker,
        w.diff_val,
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
    fill_lt_reg(
        tracer,
        old_pc,
        &rd,
        &rs1,
        &rs2,
        cmp_result,
        w.rs1_msl_felt,
        w.rs2_msl_felt,
        [0, 1],
        w.diff_marker,
        w.diff_val,
    );
}
