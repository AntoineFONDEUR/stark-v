//! I-type ALU operations.
//!
//! This file contains:
//! - base_alu_imm family: addi, xori, ori, andi
//! - shifts_imm family: slli, srli, srai
//! - lt_imm family: slti, sltiu

use air::opcodes::base_alu_imm::base_alu_imm_fill;
use air::opcodes::lt_imm::lt_imm_fill;
use air::opcodes::shifts_imm::shifts_imm_fill;
use stwo::core::fields::m31::BaseField;

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

fn execute_shifts_imm(
    cpu: &mut Cpu,
    memory: &mut Memory,
    inst: &DecodedInst,
    tracer: &mut Tracer,
    flags: [u32; 3],
) {
    // Decoding selects direction and fill; generated execution owns the shift.
    let args = [
        tracer.clock,
        cpu.pc,
        u32::from(inst.rd),
        u32::from(inst.rs1),
        inst.imm as u32 & 0x1f,
        flags[0],
        flags[1],
        flags[2],
    ]
    .map(BaseField::from_u32_unchecked);
    let [next_pc] = {
        let mut state = MachineState::new(cpu, memory);
        shifts_imm_fill(&mut state, tracer, args, [])
    };
    cpu.pc = next_pc.0;
}

pub fn slli(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_shifts_imm(cpu, memory, inst, tracer, [1, 0, 0]);
}

pub fn srli(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_shifts_imm(cpu, memory, inst, tracer, [0, 1, 0]);
}

pub fn srai(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_shifts_imm(cpu, memory, inst, tracer, [0, 0, 1]);
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
