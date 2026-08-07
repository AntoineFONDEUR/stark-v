//! Instruction execution routed to opcode and syscall handlers.

use crate::ops::{alu, alu_imm, branch, jump, load, muldiv, store, upper};
use crate::{Cpu, DecodedInst, Memory, Opcode, RunError, Tracer, syscalls};

/// Execute a decoded instruction. Each opcode handles PC advancement internally.
pub fn execute(
    cpu: &mut Cpu,
    mem: &mut Memory,
    inst: &DecodedInst,
    tracer: &mut Tracer,
) -> Result<(), RunError> {
    match inst.opcode {
        // R-type ALU
        Opcode::Add => alu::add(cpu, mem, inst, tracer),
        Opcode::Sub => alu::sub(cpu, mem, inst, tracer),
        Opcode::Sll => alu::sll(cpu, mem, inst, tracer),
        Opcode::Slt => alu::slt(cpu, mem, inst, tracer),
        Opcode::Sltu => alu::sltu(cpu, mem, inst, tracer),
        Opcode::Xor => alu::xor(cpu, mem, inst, tracer),
        Opcode::Srl => alu::srl(cpu, mem, inst, tracer),
        Opcode::Sra => alu::sra(cpu, mem, inst, tracer),
        Opcode::Or => alu::or(cpu, mem, inst, tracer),
        Opcode::And => alu::and(cpu, mem, inst, tracer),

        // I-type ALU
        Opcode::Addi => alu_imm::addi(cpu, mem, inst, tracer),
        Opcode::Slti => alu_imm::slti(cpu, mem, inst, tracer),
        Opcode::Sltiu => alu_imm::sltiu(cpu, mem, inst, tracer),
        Opcode::Xori => alu_imm::xori(cpu, mem, inst, tracer),
        Opcode::Ori => alu_imm::ori(cpu, mem, inst, tracer),
        Opcode::Andi => alu_imm::andi(cpu, mem, inst, tracer),
        Opcode::Slli => alu_imm::slli(cpu, mem, inst, tracer),
        Opcode::Srli => alu_imm::srli(cpu, mem, inst, tracer),
        Opcode::Srai => alu_imm::srai(cpu, mem, inst, tracer),

        // Loads
        Opcode::Lb => load::lb(cpu, mem, inst, tracer),
        Opcode::Lh => load::lh(cpu, mem, inst, tracer),
        Opcode::Lw => load::lw(cpu, mem, inst, tracer),
        Opcode::Lbu => load::lbu(cpu, mem, inst, tracer),
        Opcode::Lhu => load::lhu(cpu, mem, inst, tracer),

        // Stores
        Opcode::Sb => store::sb(cpu, mem, inst, tracer),
        Opcode::Sh => store::sh(cpu, mem, inst, tracer),
        Opcode::Sw => store::sw(cpu, mem, inst, tracer),

        // Branches
        Opcode::Beq => branch::beq(cpu, mem, inst, tracer),
        Opcode::Bne => branch::bne(cpu, mem, inst, tracer),
        Opcode::Blt => branch::blt(cpu, mem, inst, tracer),
        Opcode::Bge => branch::bge(cpu, mem, inst, tracer),
        Opcode::Bltu => branch::bltu(cpu, mem, inst, tracer),
        Opcode::Bgeu => branch::bgeu(cpu, mem, inst, tracer),

        // Jumps
        Opcode::Jal => jump::jal(cpu, mem, inst, tracer),
        Opcode::Jalr => jump::jalr(cpu, mem, inst, tracer),

        // Upper immediates
        Opcode::Lui => upper::lui(cpu, mem, inst, tracer),
        Opcode::Auipc => upper::auipc(cpu, mem, inst, tracer),

        // M-extension
        Opcode::Mul => muldiv::mul(cpu, mem, inst, tracer),
        Opcode::Mulh => muldiv::mulh(cpu, mem, inst, tracer),
        Opcode::Mulhsu => muldiv::mulhsu(cpu, mem, inst, tracer),
        Opcode::Mulhu => muldiv::mulhu(cpu, mem, inst, tracer),
        Opcode::Div => muldiv::div(cpu, inst, tracer),
        Opcode::Divu => muldiv::divu(cpu, inst, tracer),
        Opcode::Rem => muldiv::rem(cpu, inst, tracer),
        Opcode::Remu => muldiv::remu(cpu, inst, tracer),

        // Dispatch before advancing so rejected calls cannot mutate execution state.
        Opcode::Ecall => {
            syscalls::dispatch(cpu, tracer)?;
            cpu.advance_pc();
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[rstest::rstest]
    #[case(Opcode::Add, 0xffff_fffe, 5, 3)]
    #[case(Opcode::Sub, 2, 5, 0xffff_fffd)]
    #[case(Opcode::Xor, 0xf0f0_00ff, 0x0ff0_ff00, 0xff00_ffff)]
    #[case(Opcode::Or, 0xf0f0_00ff, 0x0ff0_ff00, 0xfff0_ffff)]
    #[case(Opcode::And, 0xf0f0_00ff, 0x0ff0_ff00, 0x00f0_0000)]
    fn generated_register_alu_honors_word_boundaries(
        #[case] opcode: Opcode,
        #[case] lhs: u32,
        #[case] rhs: u32,
        #[case] expected: u32,
    ) {
        let mut cpu = Cpu::new(0x1000, 0, 0);
        cpu.set_reg(1, lhs);
        cpu.set_reg(2, rhs);
        let mut memory = Memory::new();
        let inst = DecodedInst {
            opcode,
            rd: 3,
            rs1: 1,
            rs2: 2,
            imm: 0,
        };
        let mut tracer = Tracer {
            clock: 1,
            ..Default::default()
        };

        execute(&mut cpu, &mut memory, &inst, &mut tracer).expect("execution must succeed");

        assert_eq!(cpu.reg(3), expected);
    }

    #[rstest::rstest]
    #[case(Opcode::Addi, 0, -1, 0xffff_ffff)]
    #[case(Opcode::Xori, 0x1234_5678, -1, 0xedcb_a987)]
    #[case(Opcode::Ori, 0x1234_5678, -1, 0xffff_ffff)]
    #[case(Opcode::Andi, 0x1234_5678, -1, 0x1234_5678)]
    fn generated_immediate_alu_sign_extends_the_twelve_bit_operand(
        #[case] opcode: Opcode,
        #[case] lhs: u32,
        #[case] immediate: i32,
        #[case] expected: u32,
    ) {
        let mut cpu = Cpu::new(0x1000, 0, 0);
        cpu.set_reg(1, lhs);
        let mut memory = Memory::new();
        let inst = DecodedInst {
            opcode,
            rd: 3,
            rs1: 1,
            rs2: 0,
            imm: immediate,
        };
        let mut tracer = Tracer {
            clock: 1,
            ..Default::default()
        };

        execute(&mut cpu, &mut memory, &inst, &mut tracer).expect("execution must succeed");

        assert_eq!(cpu.reg(3), expected);
    }

    #[rstest::rstest]
    #[case(Opcode::Slt, u32::MAX, 1, 1)]
    #[case(Opcode::Slt, i32::MAX as u32, i32::MIN as u32, 0)]
    #[case(Opcode::Sltu, u32::MAX, 1, 0)]
    #[case(Opcode::Sltu, 1, u32::MAX, 1)]
    fn generated_register_comparison_honors_signed_and_unsigned_order(
        #[case] opcode: Opcode,
        #[case] lhs: u32,
        #[case] rhs: u32,
        #[case] expected: u32,
    ) {
        let mut cpu = Cpu::new(0x1000, 0, 0);
        cpu.set_reg(1, lhs);
        cpu.set_reg(2, rhs);
        let mut memory = Memory::new();
        let inst = DecodedInst {
            opcode,
            rd: 3,
            rs1: 1,
            rs2: 2,
            imm: 0,
        };
        let mut tracer = Tracer {
            clock: 1,
            ..Default::default()
        };

        execute(&mut cpu, &mut memory, &inst, &mut tracer).expect("execution must succeed");

        assert_eq!(cpu.reg(3), expected);
    }

    #[rstest::rstest]
    #[case(Opcode::Slti, i32::MIN as u32, -2048, 1)]
    #[case(Opcode::Slti, u32::MAX, -1, 0)]
    #[case(Opcode::Sltiu, 0, -1, 1)]
    #[case(Opcode::Sltiu, u32::MAX, -2048, 0)]
    fn generated_immediate_comparison_honors_sign_extension_and_order(
        #[case] opcode: Opcode,
        #[case] lhs: u32,
        #[case] immediate: i32,
        #[case] expected: u32,
    ) {
        let mut cpu = Cpu::new(0x1000, 0, 0);
        cpu.set_reg(1, lhs);
        let mut memory = Memory::new();
        let inst = DecodedInst {
            opcode,
            rd: 3,
            rs1: 1,
            rs2: 0,
            imm: immediate,
        };
        let mut tracer = Tracer {
            clock: 1,
            ..Default::default()
        };

        execute(&mut cpu, &mut memory, &inst, &mut tracer).expect("execution must succeed");

        assert_eq!(cpu.reg(3), expected);
    }

    #[rstest::rstest]
    #[case(Opcode::Beq, 7, 7, 8, 0x1008)]
    #[case(Opcode::Beq, 7, 8, 8, 0x1004)]
    #[case(Opcode::Bne, 7, 8, 8, 0x1008)]
    #[case(Opcode::Bne, 7, 7, 8, 0x1004)]
    #[case(Opcode::Blt, u32::MAX, 1, -8, 0x0ff8)]
    #[case(Opcode::Bltu, u32::MAX, 1, 8, 0x1004)]
    #[case(Opcode::Bge, 1, u32::MAX, 8, 0x1008)]
    #[case(Opcode::Bgeu, u32::MAX, 1, 8, 0x1008)]
    fn generated_branch_selects_the_authenticated_next_pc(
        #[case] opcode: Opcode,
        #[case] lhs: u32,
        #[case] rhs: u32,
        #[case] immediate: i32,
        #[case] expected_pc: u32,
    ) {
        let mut cpu = Cpu::new(0x1000, 0, 0);
        cpu.set_reg(1, lhs);
        cpu.set_reg(2, rhs);
        let mut memory = Memory::new();
        let inst = DecodedInst {
            opcode,
            rd: 0,
            rs1: 1,
            rs2: 2,
            imm: immediate,
        };
        let mut tracer = Tracer {
            clock: 1,
            ..Default::default()
        };

        execute(&mut cpu, &mut memory, &inst, &mut tracer).expect("execution must succeed");

        assert_eq!(cpu.pc, expected_pc);
    }

    #[rstest::rstest]
    #[case(Opcode::Sll, 0x1234_5678, 8, 0x3456_7800)]
    #[case(Opcode::Sll, 1, 32, 1)]
    #[case(Opcode::Srl, 0x8000_0001, 31, 1)]
    #[case(Opcode::Sra, 0x8000_0000, 31, u32::MAX)]
    #[case(Opcode::Sra, i32::MAX as u32, 31, 0)]
    fn generated_register_shift_masks_the_amount_and_selects_the_fill(
        #[case] opcode: Opcode,
        #[case] value: u32,
        #[case] shift: u32,
        #[case] expected: u32,
    ) {
        let mut cpu = Cpu::new(0x1000, 0, 0);
        cpu.set_reg(1, value);
        cpu.set_reg(2, shift);
        let mut memory = Memory::new();
        let inst = DecodedInst {
            opcode,
            rd: 3,
            rs1: 1,
            rs2: 2,
            imm: 0,
        };
        let mut tracer = Tracer {
            clock: 1,
            ..Default::default()
        };

        execute(&mut cpu, &mut memory, &inst, &mut tracer).expect("execution must succeed");

        assert_eq!(cpu.reg(3), expected);
    }

    #[rstest::rstest]
    #[case(Opcode::Slli, 1, 31, 0x8000_0000)]
    #[case(Opcode::Srli, 0x8000_0000, 31, 1)]
    #[case(Opcode::Srai, 0x8000_0000, 31, u32::MAX)]
    #[case(Opcode::Srai, 0x8000_0000, 0, 0x8000_0000)]
    fn generated_immediate_shift_honors_extreme_amounts(
        #[case] opcode: Opcode,
        #[case] value: u32,
        #[case] shift: i32,
        #[case] expected: u32,
    ) {
        let mut cpu = Cpu::new(0x1000, 0, 0);
        cpu.set_reg(1, value);
        let mut memory = Memory::new();
        let inst = DecodedInst {
            opcode,
            rd: 3,
            rs1: 1,
            rs2: 0,
            imm: shift,
        };
        let mut tracer = Tracer {
            clock: 1,
            ..Default::default()
        };

        execute(&mut cpu, &mut memory, &inst, &mut tracer).expect("execution must succeed");

        assert_eq!(cpu.reg(3), expected);
    }

    #[rstest::rstest]
    #[case(Opcode::Mul, u32::MAX, 2, 3, 0xffff_fffe)]
    #[case(Opcode::Mulh, u32::MAX, 2, 3, u32::MAX)]
    #[case(Opcode::Mulh, i32::MIN as u32, u32::MAX, 3, 0)]
    #[case(Opcode::Mulhsu, u32::MAX, u32::MAX, 3, u32::MAX)]
    #[case(Opcode::Mulhu, u32::MAX, u32::MAX, 3, 0xffff_fffe)]
    #[case(Opcode::Mulhu, u32::MAX, 2, 1, 1)]
    #[case(Opcode::Mul, 3, 7, 2, 21)]
    fn generated_multiply_honors_signedness_wrapping_and_aliasing(
        #[case] opcode: Opcode,
        #[case] lhs: u32,
        #[case] rhs: u32,
        #[case] rd: u8,
        #[case] expected: u32,
    ) {
        let mut cpu = Cpu::new(0x1000, 0, 0);
        cpu.set_reg(1, lhs);
        cpu.set_reg(2, rhs);
        let mut memory = Memory::new();
        let inst = DecodedInst {
            opcode,
            rd,
            rs1: 1,
            rs2: 2,
            imm: 0,
        };
        let mut tracer = Tracer {
            clock: 1,
            ..Default::default()
        };

        execute(&mut cpu, &mut memory, &inst, &mut tracer).expect("execution must succeed");

        assert_eq!(cpu.reg(rd), expected);
    }
}
