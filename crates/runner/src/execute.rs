use crate::ops::{alu, alu_imm, branch, jump, load, muldiv, store, upper};
use crate::{Cpu, DecodedInst, Memory, Opcode, Tracer};

/// Execute a decoded instruction. Each opcode handles PC advancement internally.
pub fn execute(cpu: &mut Cpu, mem: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    match inst.opcode {
        // R-type ALU
        Opcode::Add => alu::add(cpu, inst, tracer),
        Opcode::Sub => alu::sub(cpu, inst, tracer),
        Opcode::Sll => alu::sll(cpu, inst, tracer),
        Opcode::Slt => alu::slt(cpu, inst, tracer),
        Opcode::Sltu => alu::sltu(cpu, inst, tracer),
        Opcode::Xor => alu::xor(cpu, inst, tracer),
        Opcode::Srl => alu::srl(cpu, inst, tracer),
        Opcode::Sra => alu::sra(cpu, inst, tracer),
        Opcode::Or => alu::or(cpu, inst, tracer),
        Opcode::And => alu::and(cpu, inst, tracer),

        // I-type ALU
        Opcode::Addi => alu_imm::addi(cpu, inst, tracer),
        Opcode::Slti => alu_imm::slti(cpu, inst, tracer),
        Opcode::Sltiu => alu_imm::sltiu(cpu, inst, tracer),
        Opcode::Xori => alu_imm::xori(cpu, inst, tracer),
        Opcode::Ori => alu_imm::ori(cpu, inst, tracer),
        Opcode::Andi => alu_imm::andi(cpu, inst, tracer),
        Opcode::Slli => alu_imm::slli(cpu, inst, tracer),
        Opcode::Srli => alu_imm::srli(cpu, inst, tracer),
        Opcode::Srai => alu_imm::srai(cpu, inst, tracer),

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
        Opcode::Beq => branch::beq(cpu, inst, tracer),
        Opcode::Bne => branch::bne(cpu, inst, tracer),
        Opcode::Blt => branch::blt(cpu, inst, tracer),
        Opcode::Bge => branch::bge(cpu, inst, tracer),
        Opcode::Bltu => branch::bltu(cpu, inst, tracer),
        Opcode::Bgeu => branch::bgeu(cpu, inst, tracer),

        // Jumps
        Opcode::Jal => jump::jal(cpu, inst, tracer),
        Opcode::Jalr => jump::jalr(cpu, inst, tracer),

        // Upper immediates
        Opcode::Lui => upper::lui(cpu, inst, tracer),
        Opcode::Auipc => upper::auipc(cpu, inst, tracer),

        // M-extension
        Opcode::Mul => muldiv::mul(cpu, inst, tracer),
        Opcode::Mulh => muldiv::mulh(cpu, inst, tracer),
        Opcode::Mulhsu => muldiv::mulhsu(cpu, inst, tracer),
        Opcode::Mulhu => muldiv::mulhu(cpu, inst, tracer),
        Opcode::Div => muldiv::div(cpu, inst, tracer),
        Opcode::Divu => muldiv::divu(cpu, inst, tracer),
        Opcode::Rem => muldiv::rem(cpu, inst, tracer),
        Opcode::Remu => muldiv::remu(cpu, inst, tracer),
    }
}
