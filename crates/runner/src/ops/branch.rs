//! Branch decode adapters for felt-generated execution.

use air::opcodes::branch_eq::branch_eq_fill;
use air::opcodes::branch_lt::branch_lt_fill;
use stwo::core::fields::m31::BaseField;

use super::utils::imm_to_felt;
use crate::trace::Tracer;
use crate::{Cpu, DecodedInst, MachineState, Memory};

fn execute_branch_eq(
    cpu: &mut Cpu,
    memory: &mut Memory,
    inst: &DecodedInst,
    tracer: &mut Tracer,
    flags: [u32; 2],
) {
    // Decoding selects equality polarity; generated execution owns the branch.
    let args = [
        tracer.clock,
        cpu.pc,
        u32::from(inst.rs1),
        u32::from(inst.rs2),
        imm_to_felt(inst.imm),
        flags[0],
        flags[1],
    ]
    .map(BaseField::from_u32_unchecked);
    let [next_pc] = {
        let mut state = MachineState::new(cpu, memory);
        branch_eq_fill(&mut state, tracer, args, [])
    };
    cpu.pc = next_pc.0;
}

pub fn beq(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_branch_eq(cpu, memory, inst, tracer, [1, 0]);
}

pub fn bne(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_branch_eq(cpu, memory, inst, tracer, [0, 1]);
}

fn execute_branch_lt(
    cpu: &mut Cpu,
    memory: &mut Memory,
    inst: &DecodedInst,
    tracer: &mut Tracer,
    flags: [u32; 4],
) {
    // Decoding selects signedness and polarity; generated execution owns the branch.
    let args = [
        tracer.clock,
        cpu.pc,
        u32::from(inst.rs1),
        u32::from(inst.rs2),
        imm_to_felt(inst.imm),
        flags[0],
        flags[1],
        flags[2],
        flags[3],
    ]
    .map(BaseField::from_u32_unchecked);
    let [next_pc] = {
        let mut state = MachineState::new(cpu, memory);
        branch_lt_fill(&mut state, tracer, args, [])
    };
    cpu.pc = next_pc.0;
}

pub fn blt(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_branch_lt(cpu, memory, inst, tracer, [1, 0, 0, 0]);
}

pub fn bltu(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_branch_lt(cpu, memory, inst, tracer, [0, 1, 0, 0]);
}

pub fn bge(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_branch_lt(cpu, memory, inst, tracer, [0, 0, 1, 0]);
}

pub fn bgeu(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_branch_lt(cpu, memory, inst, tracer, [0, 0, 0, 1]);
}
