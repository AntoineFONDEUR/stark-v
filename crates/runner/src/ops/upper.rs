//! Upper immediate operations.
//!
//! This file contains:
//! - a decode adapter for felt-defined LUI
//! - the AUIPC handler

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

pub fn auipc(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let result = cpu.pc.wrapping_add(inst.imm as u32);
    let rd = cpu.write_reg(inst.rd, result, tracer);
    cpu.advance_pc();

    let imm_felt = imm_to_felt(inst.imm);
    trace_op!(auipc: tracer, old_pc, rd, imm_felt);
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
}
