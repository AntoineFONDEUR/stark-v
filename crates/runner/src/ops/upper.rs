//! Upper immediate operations.
//!
//! This file contains:
//! - decode adapters for felt-defined LUI and AUIPC

use air::opcodes::auipc::auipc_fill;
use air::opcodes::lui::lui_fill;
use stwo::core::fields::m31::BaseField;

use super::utils::imm_to_felt;
use crate::trace::Tracer;
use crate::{Cpu, DecodedInst, MachineState, Memory};

// =============================================================================
// LUI
// =============================================================================

pub fn lui(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    // Decoding stays host-side; the generated function owns state mutation and tracing.
    let immediate = (inst.imm as u32) >> 12;
    let args = [
        BaseField::from_u32_unchecked(tracer.clock),
        BaseField::from_u32_unchecked(cpu.pc),
        BaseField::from_u32_unchecked(u32::from(inst.rd)),
        BaseField::from_u32_unchecked(immediate & 0x0f),
        BaseField::from_u32_unchecked((immediate >> 4) & 0xff),
        BaseField::from_u32_unchecked((immediate >> 12) & 0xff),
    ];
    let [next_pc] = {
        let mut state = MachineState::new(cpu, memory);
        lui_fill(&mut state, tracer, args, [])
    };
    cpu.pc = next_pc.0;
}

// =============================================================================
// AUIPC
// =============================================================================

pub fn auipc(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    // Decoding stays host-side; the generated function owns state mutation and tracing.
    let args = [
        BaseField::from_u32_unchecked(tracer.clock),
        BaseField::from_u32_unchecked(cpu.pc),
        BaseField::from_u32_unchecked(u32::from(inst.rd)),
        BaseField::from_u32_unchecked(imm_to_felt(inst.imm)),
    ];
    let [next_pc] = {
        let mut state = MachineState::new(cpu, memory);
        auipc_fill(&mut state, tracer, args, [])
    };
    cpu.pc = next_pc.0;
}

#[cfg(test)]
mod tests {
    use air::instructions::Opcode;

    use super::*;

    #[test]
    fn lui_generated_execution_writes_the_upper_immediate() {
        let mut cpu = Cpu::new(0x1000, 0, 0);
        let mut memory = Memory::new();
        let inst = DecodedInst {
            opcode: Opcode::Lui,
            rd: 5,
            rs1: 0,
            rs2: 0,
            imm: 0x1234_5000,
        };
        let mut tracer = Tracer {
            clock: 1,
            ..Default::default()
        };

        lui(&mut cpu, &mut memory, &inst, &mut tracer);

        assert_eq!(cpu.reg(5), 0x1234_5000);
    }

    #[test]
    fn lui_generated_execution_returns_the_next_pc() {
        let mut cpu = Cpu::new(0x1000, 0, 0);
        let mut memory = Memory::new();
        let inst = DecodedInst {
            opcode: Opcode::Lui,
            rd: 5,
            rs1: 0,
            rs2: 0,
            imm: 0x1234_5000,
        };
        let mut tracer = Tracer {
            clock: 1,
            ..Default::default()
        };

        lui(&mut cpu, &mut memory, &inst, &mut tracer);

        assert_eq!(cpu.pc, 0x1004);
    }

    #[test]
    fn lui_generated_execution_preserves_x0() {
        let mut cpu = Cpu::new(0x1000, 0, 0);
        let mut memory = Memory::new();
        let inst = DecodedInst {
            opcode: Opcode::Lui,
            rd: 0,
            rs1: 0,
            rs2: 0,
            imm: 0x1234_5000,
        };
        let mut tracer = Tracer {
            clock: 1,
            ..Default::default()
        };

        lui(&mut cpu, &mut memory, &inst, &mut tracer);

        assert_eq!(cpu.reg(0), 0);
    }

    #[test]
    fn lui_generated_execution_records_one_row() {
        let mut cpu = Cpu::new(0x1000, 0, 0);
        let mut memory = Memory::new();
        let inst = DecodedInst {
            opcode: Opcode::Lui,
            rd: 5,
            rs1: 0,
            rs2: 0,
            imm: 0x1234_5000,
        };
        let mut tracer = Tracer {
            clock: 1,
            ..Default::default()
        };

        lui(&mut cpu, &mut memory, &inst, &mut tracer);

        assert_eq!(tracer.lui.len(), 1);
    }

    #[test]
    fn auipc_generated_execution_writes_the_pc_relative_value() {
        let mut cpu = Cpu::new(0x1000, 0, 0);
        let mut memory = Memory::new();
        let inst = DecodedInst {
            opcode: Opcode::Auipc,
            rd: 5,
            rs1: 0,
            rs2: 0,
            imm: 0x2000,
        };
        let mut tracer = Tracer {
            clock: 1,
            ..Default::default()
        };

        auipc(&mut cpu, &mut memory, &inst, &mut tracer);

        assert_eq!(cpu.reg(5), 0x3000);
    }

    #[test]
    fn auipc_generated_execution_returns_the_next_pc() {
        let mut cpu = Cpu::new(0x1000, 0, 0);
        let mut memory = Memory::new();
        let inst = DecodedInst {
            opcode: Opcode::Auipc,
            rd: 5,
            rs1: 0,
            rs2: 0,
            imm: 0x2000,
        };
        let mut tracer = Tracer {
            clock: 1,
            ..Default::default()
        };

        auipc(&mut cpu, &mut memory, &inst, &mut tracer);

        assert_eq!(cpu.pc, 0x1004);
    }

    #[test]
    fn auipc_generated_execution_records_one_row() {
        let mut cpu = Cpu::new(0x1000, 0, 0);
        let mut memory = Memory::new();
        let inst = DecodedInst {
            opcode: Opcode::Auipc,
            rd: 5,
            rs1: 0,
            rs2: 0,
            imm: 0x2000,
        };
        let mut tracer = Tracer {
            clock: 1,
            ..Default::default()
        };

        auipc(&mut cpu, &mut memory, &inst, &mut tracer);

        assert_eq!(tracer.auipc.len(), 1);
    }
}
