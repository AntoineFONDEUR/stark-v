use rustc_hash::FxHashMap;

/// Instruction cache: maps PC address to decoded instruction.
pub type InstCache = FxHashMap<u32, DecodedInst>;

/// All RV32IM opcodes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Opcode {
    // R-type ALU
    Add,
    Sub,
    Sll,
    Slt,
    Sltu,
    Xor,
    Srl,
    Sra,
    Or,
    And,

    // I-type ALU
    Addi,
    Slti,
    Sltiu,
    Xori,
    Ori,
    Andi,
    Slli,
    Srli,
    Srai,

    // Loads
    Lb,
    Lh,
    Lw,
    Lbu,
    Lhu,

    // Stores
    Sb,
    Sh,
    Sw,

    // Branches
    Beq,
    Bne,
    Blt,
    Bge,
    Bltu,
    Bgeu,

    // Jumps
    Jal,
    Jalr,

    // Upper immediates
    Lui,
    Auipc,

    // M-extension (multiply/divide)
    Mul,
    Mulh,
    Mulhsu,
    Mulhu,
    Div,
    Divu,
    Rem,
    Remu,
}

/// Decoded instruction with all fields extracted.
#[derive(Debug, Clone, Copy)]
pub struct DecodedInst {
    pub opcode: Opcode,
    pub rd: u8,
    pub rs1: u8,
    pub rs2: u8,
    pub imm: i32,
}

impl DecodedInst {
    /// Decode a 32-bit instruction word.
    pub fn decode(inst: u32) -> Option<Self> {
        let opcode_bits = inst & 0x7F;
        let rd = ((inst >> 7) & 0x1F) as u8;
        let funct3 = (inst >> 12) & 0x7;
        let rs1 = ((inst >> 15) & 0x1F) as u8;
        let rs2 = ((inst >> 20) & 0x1F) as u8;
        let funct7 = (inst >> 25) & 0x7F;

        let (opcode, imm) = match opcode_bits {
            // R-type: ADD, SUB, SLL, SLT, SLTU, XOR, SRL, SRA, OR, AND
            // Also M-extension: MUL, MULH, MULHSU, MULHU, DIV, DIVU, REM, REMU
            0b0110011 => {
                let op = match (funct3, funct7) {
                    (0b000, 0b0000000) => Opcode::Add,
                    (0b000, 0b0100000) => Opcode::Sub,
                    (0b001, 0b0000000) => Opcode::Sll,
                    (0b010, 0b0000000) => Opcode::Slt,
                    (0b011, 0b0000000) => Opcode::Sltu,
                    (0b100, 0b0000000) => Opcode::Xor,
                    (0b101, 0b0000000) => Opcode::Srl,
                    (0b101, 0b0100000) => Opcode::Sra,
                    (0b110, 0b0000000) => Opcode::Or,
                    (0b111, 0b0000000) => Opcode::And,
                    // M-extension
                    (0b000, 0b0000001) => Opcode::Mul,
                    (0b001, 0b0000001) => Opcode::Mulh,
                    (0b010, 0b0000001) => Opcode::Mulhsu,
                    (0b011, 0b0000001) => Opcode::Mulhu,
                    (0b100, 0b0000001) => Opcode::Div,
                    (0b101, 0b0000001) => Opcode::Divu,
                    (0b110, 0b0000001) => Opcode::Rem,
                    (0b111, 0b0000001) => Opcode::Remu,
                    _ => return None,
                };
                (op, 0)
            }

            // I-type ALU: ADDI, SLTI, SLTIU, XORI, ORI, ANDI, SLLI, SRLI, SRAI
            0b0010011 => {
                let imm_i = (inst as i32) >> 20;
                let shamt = (inst >> 20) & 0x1F;
                let op = match funct3 {
                    0b000 => Opcode::Addi,
                    0b010 => Opcode::Slti,
                    0b011 => Opcode::Sltiu,
                    0b100 => Opcode::Xori,
                    0b110 => Opcode::Ori,
                    0b111 => Opcode::Andi,
                    0b001 => Opcode::Slli,
                    0b101 => {
                        if funct7 == 0b0100000 {
                            Opcode::Srai
                        } else {
                            Opcode::Srli
                        }
                    }
                    _ => return None,
                };
                let imm = if matches!(op, Opcode::Slli | Opcode::Srli | Opcode::Srai) {
                    shamt as i32
                } else {
                    imm_i
                };
                (op, imm)
            }

            // Load: LB, LH, LW, LBU, LHU
            0b0000011 => {
                let imm_i = (inst as i32) >> 20;
                let op = match funct3 {
                    0b000 => Opcode::Lb,
                    0b001 => Opcode::Lh,
                    0b010 => Opcode::Lw,
                    0b100 => Opcode::Lbu,
                    0b101 => Opcode::Lhu,
                    _ => return None,
                };
                (op, imm_i)
            }

            // Store: SB, SH, SW
            0b0100011 => {
                let imm_s = (((inst >> 25) & 0x7F) << 5) | ((inst >> 7) & 0x1F);
                let imm_s = ((imm_s as i32) << 20) >> 20; // Sign extend from 12 bits
                let op = match funct3 {
                    0b000 => Opcode::Sb,
                    0b001 => Opcode::Sh,
                    0b010 => Opcode::Sw,
                    _ => return None,
                };
                (op, imm_s)
            }

            // Branch: BEQ, BNE, BLT, BGE, BLTU, BGEU
            0b1100011 => {
                // B-type immediate
                let imm12 = (inst >> 31) & 1;
                let imm10_5 = (inst >> 25) & 0x3F;
                let imm4_1 = (inst >> 8) & 0xF;
                let imm11 = (inst >> 7) & 1;
                let imm_b = (imm12 << 12) | (imm11 << 11) | (imm10_5 << 5) | (imm4_1 << 1);
                let imm_b = ((imm_b as i32) << 19) >> 19; // Sign extend from 13 bits
                let op = match funct3 {
                    0b000 => Opcode::Beq,
                    0b001 => Opcode::Bne,
                    0b100 => Opcode::Blt,
                    0b101 => Opcode::Bge,
                    0b110 => Opcode::Bltu,
                    0b111 => Opcode::Bgeu,
                    _ => return None,
                };
                (op, imm_b)
            }

            // JAL
            0b1101111 => {
                // J-type immediate
                let imm20 = (inst >> 31) & 1;
                let imm10_1 = (inst >> 21) & 0x3FF;
                let imm11 = (inst >> 20) & 1;
                let imm19_12 = (inst >> 12) & 0xFF;
                let imm_j = (imm20 << 20) | (imm19_12 << 12) | (imm11 << 11) | (imm10_1 << 1);
                let imm_j = ((imm_j as i32) << 11) >> 11; // Sign extend from 21 bits
                (Opcode::Jal, imm_j)
            }

            // JALR
            0b1100111 => {
                let imm_i = (inst as i32) >> 20;
                (Opcode::Jalr, imm_i)
            }

            // LUI
            0b0110111 => {
                let imm_u = (inst & 0xFFFFF000) as i32;
                (Opcode::Lui, imm_u)
            }

            // AUIPC
            0b0010111 => {
                let imm_u = (inst & 0xFFFFF000) as i32;
                (Opcode::Auipc, imm_u)
            }

            _ => return None,
        };

        Some(DecodedInst {
            opcode,
            rd,
            rs1,
            rs2,
            imm,
        })
    }
}
