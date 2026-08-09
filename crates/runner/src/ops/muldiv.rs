//! Multiply/Divide operations (M extension).
//!
//! This file contains:
//! - mul family: mul
//! - mulh family: mulh, mulhsu, mulhu
//! - div family: div, divu, rem, remu

use air::opcodes::div::div_fill;
use air::opcodes::mul::mul_fill;
use air::opcodes::mulh::mulh_fill;
use stwo::core::fields::m31::BaseField;

use crate::trace::Tracer;
use crate::{Cpu, DecodedInst, MachineState, Memory};

// =============================================================================
// MUL
// =============================================================================

pub fn mul(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    // Generated execution binds the wrapping product to the traced accesses.
    let args = [
        tracer.clock,
        cpu.pc,
        u32::from(inst.rd),
        u32::from(inst.rs1),
        u32::from(inst.rs2),
    ]
    .map(BaseField::from_u32_unchecked);
    let [next_pc] = {
        let mut state = MachineState::new(cpu, memory);
        mul_fill(&mut state, tracer, args, [])
    };
    cpu.pc = next_pc.0;
}

// =============================================================================
// MULH (mulh/mulhsu/mulhu)
// =============================================================================

fn execute_mulh(
    cpu: &mut Cpu,
    memory: &mut Memory,
    inst: &DecodedInst,
    tracer: &mut Tracer,
    flags: [u32; 3],
) {
    // Decoding selects signedness; generated execution owns the wide product.
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
        mulh_fill(&mut state, tracer, args, [])
    };
    cpu.pc = next_pc.0;
}

pub fn mulh(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_mulh(cpu, memory, inst, tracer, [1, 0, 0]);
}

pub fn mulhsu(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_mulh(cpu, memory, inst, tracer, [0, 1, 0]);
}

pub fn mulhu(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_mulh(cpu, memory, inst, tracer, [0, 0, 1]);
}

// =============================================================================
// DIV (div/divu/rem/remu)
// =============================================================================

fn execute_div(
    cpu: &mut Cpu,
    memory: &mut Memory,
    inst: &DecodedInst,
    tracer: &mut Tracer,
    flags: [u32; 4],
) {
    // Decoding selects signedness and result kind; generated execution owns division.
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
    ]
    .map(BaseField::from_u32_unchecked);
    let [next_pc] = {
        let mut state = MachineState::new(cpu, memory);
        div_fill(&mut state, tracer, args, [])
    };
    cpu.pc = next_pc.0;
}

pub fn div(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_div(cpu, memory, inst, tracer, [1, 0, 0, 0]);
}

pub fn divu(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_div(cpu, memory, inst, tracer, [0, 1, 0, 0]);
}

pub fn rem(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_div(cpu, memory, inst, tracer, [0, 0, 1, 0]);
}

pub fn remu(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_div(cpu, memory, inst, tracer, [0, 0, 0, 1]);
}
