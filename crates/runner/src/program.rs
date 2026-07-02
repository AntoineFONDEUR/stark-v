use crate::commitment::{CommitmentError, MemoryLayout};
use crate::instructions::{DecodedInst, Opcode};
use crate::memory::Memory;
use crate::ops::utils::imm_to_felt;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProgramRow {
    pub addr: u32,
    pub values: [u32; 4],
}

pub fn decode_program_word(addr: u32, word: u32) -> Result<[u32; 4], CommitmentError> {
    let inst =
        DecodedInst::decode(word).ok_or(CommitmentError::DecodeFailure { pc: addr, word })?;
    let opcode_id = inst.opcode as u32;

    let values = match inst.opcode {
        Opcode::Add
        | Opcode::Sub
        | Opcode::Sll
        | Opcode::Slt
        | Opcode::Sltu
        | Opcode::Xor
        | Opcode::Srl
        | Opcode::Sra
        | Opcode::Or
        | Opcode::And
        | Opcode::Mul
        | Opcode::Mulh
        | Opcode::Mulhsu
        | Opcode::Mulhu
        | Opcode::Div
        | Opcode::Divu
        | Opcode::Rem
        | Opcode::Remu => [opcode_id, inst.rd as u32, inst.rs1 as u32, inst.rs2 as u32],
        Opcode::Sb | Opcode::Sh | Opcode::Sw => [
            opcode_id,
            inst.rs1 as u32,
            inst.rs2 as u32,
            imm_to_felt(inst.imm),
        ],
        Opcode::Lb | Opcode::Lh | Opcode::Lw | Opcode::Lbu | Opcode::Lhu => [
            opcode_id,
            inst.rs1 as u32,
            inst.rd as u32,
            imm_to_felt(inst.imm),
        ],
        Opcode::Slli | Opcode::Srli | Opcode::Srai => [
            opcode_id,
            inst.rd as u32,
            inst.rs1 as u32,
            (inst.imm as u32) & 0x1F,
        ],
        Opcode::Addi | Opcode::Slti | Opcode::Sltiu | Opcode::Xori | Opcode::Ori | Opcode::Andi => {
            [
                opcode_id,
                inst.rd as u32,
                inst.rs1 as u32,
                (inst.imm as u32) & 0xFFF,
            ]
        }
        Opcode::Jalr => [
            opcode_id,
            inst.rd as u32,
            inst.rs1 as u32,
            imm_to_felt(inst.imm),
        ],
        Opcode::Lui => {
            let decoded_imm = (word >> 12) & 0xFFFFF;
            [opcode_id, inst.rd as u32, decoded_imm, 0]
        }
        Opcode::Auipc => [opcode_id, inst.rd as u32, imm_to_felt(inst.imm), 0],
        Opcode::Jal => [opcode_id, inst.rd as u32, imm_to_felt(inst.imm), 0],
        Opcode::Beq | Opcode::Bne | Opcode::Blt | Opcode::Bge | Opcode::Bltu | Opcode::Bgeu => [
            opcode_id,
            inst.rs1 as u32,
            inst.rs2 as u32,
            imm_to_felt(inst.imm),
        ],
    };

    Ok(values)
}

pub fn decode_program(
    memory: &Memory,
    layout: &MemoryLayout,
) -> Result<Vec<ProgramRow>, CommitmentError> {
    let program_range = layout.program_base..layout.program_end;
    let range_len = layout.program_end.saturating_sub(layout.program_base) as usize;
    let mut rows = Vec::with_capacity(range_len / 4);

    for addr in program_range.step_by(4) {
        let word = memory.read_u32(addr);
        if word != 0 {
            let values = decode_program_word(addr, word)?;
            rows.push(ProgramRow { addr, values });
        }
    }

    Ok(rows)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn encode_r_type(funct7: u32, rs2: u32, rs1: u32, funct3: u32, rd: u32, opcode: u32) -> u32 {
        (funct7 << 25) | (rs2 << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | opcode
    }

    fn encode_i_type(imm: i32, rs1: u32, funct3: u32, rd: u32, opcode: u32) -> u32 {
        let imm_u = (imm as u32) & 0xFFF;
        (imm_u << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | opcode
    }

    fn encode_shift_i_type(shamt: u32, rs1: u32, funct3: u32, rd: u32, opcode: u32) -> u32 {
        (shamt << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | opcode
    }

    fn encode_s_type(imm: i32, rs2: u32, rs1: u32, funct3: u32, opcode: u32) -> u32 {
        let imm_u = (imm as u32) & 0xFFF;
        let imm_11_5 = (imm_u >> 5) & 0x7F;
        let imm_4_0 = imm_u & 0x1F;
        (imm_11_5 << 25) | (rs2 << 20) | (rs1 << 15) | (funct3 << 12) | (imm_4_0 << 7) | opcode
    }

    fn encode_b_type(imm: i32, rs2: u32, rs1: u32, funct3: u32, opcode: u32) -> u32 {
        let imm_u = (imm as u32) & 0x1FFF;
        let imm_12 = (imm_u >> 12) & 0x1;
        let imm_10_5 = (imm_u >> 5) & 0x3F;
        let imm_4_1 = (imm_u >> 1) & 0xF;
        let imm_11 = (imm_u >> 11) & 0x1;
        (imm_12 << 31)
            | (imm_10_5 << 25)
            | (rs2 << 20)
            | (rs1 << 15)
            | (funct3 << 12)
            | (imm_4_1 << 8)
            | (imm_11 << 7)
            | opcode
    }

    fn encode_u_type(imm: u32, rd: u32, opcode: u32) -> u32 {
        (imm << 12) | (rd << 7) | opcode
    }

    fn encode_j_type(imm: i32, rd: u32, opcode: u32) -> u32 {
        let imm_u = (imm as u32) & 0x1FFFFF;
        let imm_20 = (imm_u >> 20) & 0x1;
        let imm_10_1 = (imm_u >> 1) & 0x3FF;
        let imm_11 = (imm_u >> 11) & 0x1;
        let imm_19_12 = (imm_u >> 12) & 0xFF;
        (imm_20 << 31) | (imm_10_1 << 21) | (imm_11 << 20) | (imm_19_12 << 12) | (rd << 7) | opcode
    }

    #[test]
    fn test_decode_program_word_tuples() {
        let base = 0u32;
        let add = encode_r_type(0, 2, 1, 0, 3, 0x33);
        let addi = encode_i_type(-1, 6, 0, 5, 0x13);
        let slli = encode_shift_i_type(3, 2, 0b001, 1, 0x13);
        let lw = encode_i_type(8, 5, 0b010, 4, 0x03);
        let sw = encode_s_type(12, 4, 5, 0b010, 0x23);
        let lui = encode_u_type(0xABCDE, 7, 0x37);
        let auipc = encode_u_type(0x10000, 8, 0x17);
        let jal = encode_j_type(16, 1, 0x6F);
        let beq = encode_b_type(8, 2, 1, 0b000, 0x63);

        let add_vals = decode_program_word(base, add).unwrap();
        assert_eq!(add_vals, [Opcode::Add as u32, 3, 1, 2,]);

        let addi_vals = decode_program_word(base + 4, addi).unwrap();
        assert_eq!(addi_vals, [Opcode::Addi as u32, 5, 6, 4095,]);

        let slli_vals = decode_program_word(base + 8, slli).unwrap();
        assert_eq!(slli_vals, [Opcode::Slli as u32, 1, 2, 3,]);

        let lw_vals = decode_program_word(base + 12, lw).unwrap();
        assert_eq!(lw_vals, [Opcode::Lw as u32, 5, 4, 8,]);

        let sw_vals = decode_program_word(base + 16, sw).unwrap();
        assert_eq!(sw_vals, [Opcode::Sw as u32, 5, 4, 12,]);

        let lui_vals = decode_program_word(base + 20, lui).unwrap();
        assert_eq!(lui_vals, [Opcode::Lui as u32, 7, 0xABCDE, 0,]);

        let auipc_vals = decode_program_word(base + 24, auipc).unwrap();
        assert_eq!(
            auipc_vals,
            [
                Opcode::Auipc as u32,
                8,
                imm_to_felt((auipc & 0xFFFFF000) as i32),
                0,
            ]
        );

        let jal_vals = decode_program_word(base + 28, jal).unwrap();
        assert_eq!(jal_vals, [Opcode::Jal as u32, 1, imm_to_felt(16), 0,]);

        let beq_vals = decode_program_word(base + 32, beq).unwrap();
        assert_eq!(beq_vals, [Opcode::Beq as u32, 1, 2, imm_to_felt(8),]);
    }
}
