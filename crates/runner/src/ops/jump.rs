//! Jump operations.
//!
//! This file contains:
//! - decode adapters for felt-defined JAL and JALR

use air::opcodes::jal::jal_fill;
use air::opcodes::jalr::jalr_fill;
use stwo::core::fields::m31::BaseField;

use super::utils::imm_to_felt;
use crate::trace::Tracer;
use crate::{Cpu, DecodedInst, MachineState, Memory};

// =============================================================================
// JAL
// =============================================================================

pub fn jal(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    // Decoding stays host-side; the generated function owns state mutation and tracing.
    let args = [
        BaseField::from_u32_unchecked(tracer.clock),
        BaseField::from_u32_unchecked(cpu.pc),
        BaseField::from_u32_unchecked(u32::from(inst.rd)),
        BaseField::from_u32_unchecked(imm_to_felt(inst.imm)),
    ];
    let [next_pc] = {
        let mut state = MachineState::new(cpu, memory);
        jal_fill(&mut state, tracer, args, [])
    };
    cpu.pc = next_pc.0;
}

// =============================================================================
// JALR
// =============================================================================

pub fn jalr(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    // Decoding stays host-side; the generated function owns state mutation and tracing.
    let args = [
        BaseField::from_u32_unchecked(tracer.clock),
        BaseField::from_u32_unchecked(cpu.pc),
        BaseField::from_u32_unchecked(u32::from(inst.rd)),
        BaseField::from_u32_unchecked(u32::from(inst.rs1)),
        BaseField::from_u32_unchecked(imm_to_felt(inst.imm)),
    ];
    let [next_pc] = {
        let mut state = MachineState::new(cpu, memory);
        jalr_fill(&mut state, tracer, args, [])
    };
    cpu.pc = next_pc.0;
}

#[cfg(test)]
mod tests {
    use air::instructions::Opcode;

    use super::*;

    #[test]
    fn jal_generated_execution_writes_the_link() {
        let mut cpu = Cpu::new(0x1000, 0, 0);
        let mut memory = Memory::new();
        let inst = DecodedInst {
            opcode: Opcode::Jal,
            rd: 5,
            rs1: 0,
            rs2: 0,
            imm: 0x20,
        };
        let mut tracer = Tracer {
            clock: 1,
            ..Default::default()
        };

        jal(&mut cpu, &mut memory, &inst, &mut tracer);

        assert_eq!(cpu.reg(5), 0x1004);
    }

    #[test]
    fn jal_generated_execution_returns_the_target() {
        let mut cpu = Cpu::new(0x1000, 0, 0);
        let mut memory = Memory::new();
        let inst = DecodedInst {
            opcode: Opcode::Jal,
            rd: 5,
            rs1: 0,
            rs2: 0,
            imm: 0x20,
        };
        let mut tracer = Tracer {
            clock: 1,
            ..Default::default()
        };

        jal(&mut cpu, &mut memory, &inst, &mut tracer);

        assert_eq!(cpu.pc, 0x1020);
    }

    #[test]
    fn jalr_generated_execution_clears_the_target_lsb() {
        let mut cpu = Cpu::new(0x1000, 0, 0);
        cpu.set_reg(6, 0x2001);
        let mut memory = Memory::new();
        let inst = DecodedInst {
            opcode: Opcode::Jalr,
            rd: 5,
            rs1: 6,
            rs2: 0,
            imm: 2,
        };
        let mut tracer = Tracer {
            clock: 1,
            ..Default::default()
        };

        jalr(&mut cpu, &mut memory, &inst, &mut tracer);

        assert_eq!(cpu.pc, 0x2002);
    }

    #[test]
    fn jalr_generated_execution_writes_the_link() {
        let mut cpu = Cpu::new(0x1000, 0, 0);
        cpu.set_reg(6, 0x2000);
        let mut memory = Memory::new();
        let inst = DecodedInst {
            opcode: Opcode::Jalr,
            rd: 5,
            rs1: 6,
            rs2: 0,
            imm: 0,
        };
        let mut tracer = Tracer {
            clock: 1,
            ..Default::default()
        };

        jalr(&mut cpu, &mut memory, &inst, &mut tracer);

        assert_eq!(cpu.reg(5), 0x1004);
    }

    #[test]
    fn jalr_generated_execution_reads_before_an_aliasing_link_write() {
        let mut cpu = Cpu::new(0x1000, 0, 0);
        cpu.set_reg(5, 0x2001);
        let mut memory = Memory::new();
        let inst = DecodedInst {
            opcode: Opcode::Jalr,
            rd: 5,
            rs1: 5,
            rs2: 0,
            imm: 0,
        };
        let mut tracer = Tracer {
            clock: 1,
            ..Default::default()
        };

        jalr(&mut cpu, &mut memory, &inst, &mut tracer);

        assert_eq!(cpu.pc, 0x2000);
    }
}
