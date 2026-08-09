//! Load decode adapters for felt-generated load/store execution.

use super::utils::imm_to_felt;
use air::opcodes::load_store::load_store_fill;
use stwo::core::fields::m31::BaseField;

use crate::trace::Tracer;
use crate::{Cpu, DecodedInst, MachineState, Memory};

pub(super) fn execute_load_store(
    cpu: &mut Cpu,
    memory: &mut Memory,
    inst: &DecodedInst,
    tracer: &mut Tracer,
    r2_addr: u8,
    flags: [u32; 8],
) {
    // Decoding selects the lane operation; generated execution owns state and tracing.
    let args = [
        BaseField::from_u32_unchecked(tracer.clock),
        BaseField::from_u32_unchecked(cpu.pc),
        BaseField::from_u32_unchecked(u32::from(r2_addr)),
        BaseField::from_u32_unchecked(u32::from(inst.rs1)),
        BaseField::from_u32_unchecked(imm_to_felt(inst.imm)),
        BaseField::from_u32_unchecked(flags[0]),
        BaseField::from_u32_unchecked(flags[1]),
        BaseField::from_u32_unchecked(flags[2]),
        BaseField::from_u32_unchecked(flags[3]),
        BaseField::from_u32_unchecked(flags[4]),
        BaseField::from_u32_unchecked(flags[5]),
        BaseField::from_u32_unchecked(flags[6]),
        BaseField::from_u32_unchecked(flags[7]),
    ];
    let [next_pc] = {
        let mut state = MachineState::new(cpu, memory);
        load_store_fill(&mut state, tracer, args, [])
    };
    cpu.pc = next_pc.0;
}

pub fn lb(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_load_store(cpu, memory, inst, tracer, inst.rd, [1, 0, 0, 0, 0, 0, 0, 0]);
}

pub fn lh(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_load_store(cpu, memory, inst, tracer, inst.rd, [0, 1, 0, 0, 0, 0, 0, 0]);
}

pub fn lbu(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_load_store(cpu, memory, inst, tracer, inst.rd, [0, 0, 1, 0, 0, 0, 0, 0]);
}

pub fn lhu(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_load_store(cpu, memory, inst, tracer, inst.rd, [0, 0, 0, 1, 0, 0, 0, 0]);
}

pub fn lw(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_load_store(cpu, memory, inst, tracer, inst.rd, [0, 0, 0, 0, 1, 0, 0, 0]);
}
