//! I-type ALU operations.
//!
//! This file contains:
//! - base_alu_imm family: addi, xori, ori, andi
//! - shifts_imm family: slli, srli, srai
//! - lt_imm family: slti, sltiu

use air::opcodes::base_alu_imm::base_alu_imm_fill;
use air::opcodes::lt_imm::lt_imm_fill;
use stwo::core::fields::m31::BaseField;

use super::utils::compute_shift_witness;
use crate::trace::Tracer;
use crate::{Cpu, DecodedInst, MachineState, Memory};

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
// Base ALU Imm (addi/xori/ori/andi)
// =============================================================================

fn execute_base_alu_imm(
    cpu: &mut Cpu,
    memory: &mut Memory,
    inst: &DecodedInst,
    tracer: &mut Tracer,
    flags: [u32; 4],
) {
    // Decoding selects the row; generated execution owns state mutation and tracing.
    let (imm_0, imm_1, imm_msb) = decode_imm_limbs(inst.imm);
    let args = [
        tracer.clock,
        cpu.pc,
        u32::from(inst.rd),
        u32::from(inst.rs1),
        imm_0,
        imm_1,
        imm_msb,
        flags[0],
        flags[1],
        flags[2],
        flags[3],
    ]
    .map(BaseField::from_u32_unchecked);
    let [next_pc] = {
        let mut state = MachineState::new(cpu, memory);
        base_alu_imm_fill(&mut state, tracer, args, [])
    };
    cpu.pc = next_pc.0;
}

pub fn addi(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_base_alu_imm(cpu, memory, inst, tracer, [1, 0, 0, 0]);
}

pub fn xori(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_base_alu_imm(cpu, memory, inst, tracer, [0, 1, 0, 0]);
}

pub fn ori(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_base_alu_imm(cpu, memory, inst, tracer, [0, 0, 1, 0]);
}

pub fn andi(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_base_alu_imm(cpu, memory, inst, tracer, [0, 0, 0, 1]);
}

// =============================================================================
// Shifts Imm (slli/srli/srai)
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
// Less Than Imm (slti/sltiu)
// =============================================================================

fn execute_lt_imm(
    cpu: &mut Cpu,
    memory: &mut Memory,
    inst: &DecodedInst,
    tracer: &mut Tracer,
    flags: [u32; 2],
) {
    // Decoding selects signedness; generated execution owns comparison semantics.
    let (imm_0, imm_1, imm_msb) = decode_imm_limbs(inst.imm);
    let args = [
        tracer.clock,
        cpu.pc,
        u32::from(inst.rd),
        u32::from(inst.rs1),
        imm_0,
        imm_1,
        imm_msb,
        flags[0],
        flags[1],
    ]
    .map(BaseField::from_u32_unchecked);
    let [next_pc] = {
        let mut state = MachineState::new(cpu, memory);
        lt_imm_fill(&mut state, tracer, args, [])
    };
    cpu.pc = next_pc.0;
}

pub fn slti(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_lt_imm(cpu, memory, inst, tracer, [1, 0]);
}

pub fn sltiu(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_lt_imm(cpu, memory, inst, tracer, [0, 1]);
}
