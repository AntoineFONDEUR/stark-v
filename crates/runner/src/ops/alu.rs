//! R-type ALU operations.
//!
//! This file contains:
//! - base_alu_reg family: add, sub, xor, or, and
//! - shifts_reg family: sll, srl, sra
//! - lt_reg family: slt, sltu

use air::opcodes::base_alu_reg::base_alu_reg_fill;
use air::opcodes::lt_reg::lt_reg_fill;
use air::opcodes::shifts_reg::shifts_reg_fill;
use stwo::core::fields::m31::BaseField;

use crate::trace::Tracer;
use crate::{Cpu, DecodedInst, MachineState, Memory};

// =============================================================================
// Base ALU Reg (add/sub/xor/or/and)
// =============================================================================

fn execute_base_alu_reg(
    cpu: &mut Cpu,
    memory: &mut Memory,
    inst: &DecodedInst,
    tracer: &mut Tracer,
    flags: [u32; 5],
) {
    // Decoding selects the row; generated execution owns state mutation and tracing.
    let args = [
        tracer.clock,
        cpu.pc,
        u32::from(inst.rd),
        u32::from(inst.rs1),
        u32::from(inst.rs2),
        flags[0],
        flags[1],
        flags[2],
        flags[3],
        flags[4],
    ]
    .map(BaseField::from_u32_unchecked);
    let [next_pc] = {
        let mut state = MachineState::new(cpu, memory);
        base_alu_reg_fill(&mut state, tracer, args, [])
    };
    cpu.pc = next_pc.0;
}

pub fn add(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_base_alu_reg(cpu, memory, inst, tracer, [1, 0, 0, 0, 0]);
}

pub fn sub(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_base_alu_reg(cpu, memory, inst, tracer, [0, 1, 0, 0, 0]);
}

pub fn xor(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_base_alu_reg(cpu, memory, inst, tracer, [0, 0, 1, 0, 0]);
}

pub fn or(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_base_alu_reg(cpu, memory, inst, tracer, [0, 0, 0, 1, 0]);
}

pub fn and(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_base_alu_reg(cpu, memory, inst, tracer, [0, 0, 0, 0, 1]);
}

// =============================================================================
// Shifts Reg (sll/srl/sra)
// =============================================================================

fn execute_shifts_reg(
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
        u32::from(inst.rs2),
        flags[0],
        flags[1],
        flags[2],
    ]
    .map(BaseField::from_u32_unchecked);
    let [next_pc] = {
        let mut state = MachineState::new(cpu, memory);
        shifts_reg_fill(&mut state, tracer, args, [])
    };
    cpu.pc = next_pc.0;
}

pub fn sll(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_shifts_reg(cpu, memory, inst, tracer, [1, 0, 0]);
}

pub fn srl(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_shifts_reg(cpu, memory, inst, tracer, [0, 1, 0]);
}

pub fn sra(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_shifts_reg(cpu, memory, inst, tracer, [0, 0, 1]);
}

// =============================================================================
// Less Than Reg (slt/sltu)
// =============================================================================

fn execute_lt_reg(
    cpu: &mut Cpu,
    memory: &mut Memory,
    inst: &DecodedInst,
    tracer: &mut Tracer,
    flags: [u32; 2],
) {
    // Decoding selects signedness; generated execution owns comparison semantics.
    let args = [
        tracer.clock,
        cpu.pc,
        u32::from(inst.rd),
        u32::from(inst.rs1),
        u32::from(inst.rs2),
        flags[0],
        flags[1],
    ]
    .map(BaseField::from_u32_unchecked);
    let [next_pc] = {
        let mut state = MachineState::new(cpu, memory);
        lt_reg_fill(&mut state, tracer, args, [])
    };
    cpu.pc = next_pc.0;
}

pub fn slt(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_lt_reg(cpu, memory, inst, tracer, [1, 0]);
}

pub fn sltu(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_lt_reg(cpu, memory, inst, tracer, [0, 1]);
}
