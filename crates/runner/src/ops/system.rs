//! SYSTEM instructions: ECALL.
//!
//! The zkVM exposes one syscall, COMMIT: absorb register `a0` into the output
//! journal — a running Poseidon2 sponge whose final digest is the program's
//! committed output. Unlike the fixed output region, the journal accepts an
//! unbounded number of words spread across any continuation segments; the
//! sponge state chains from one segment to the next and the final digest is
//! carried on the aggregate boundary.
//!
//! Additional syscalls (guest-callable precompiles) will dispatch on `a7`;
//! today every ECALL commits `a0`.

use crate::trace::Tracer;
use crate::{Cpu, DecodedInst};

/// RISC-V ABI register holding the COMMIT argument (`a0` = x10).
pub const A0: u8 = 10;

/// The M31 prime; journal lanes are field elements.
const P: u32 = 0x7fff_ffff;

/// The output journal: a Poseidon2 sponge state carried across the whole
/// execution. Genesis is all-zero; each COMMIT absorbs one word.
pub type Journal = [u32; 16];

/// Absorb one 32-bit word into the sponge and return the new state.
///
/// The word is split into two 16-bit lanes (each a valid M31 element, so the
/// absorption is injective) added into the rate, then one permutation is
/// applied — the same construction the in-AIR `ecall` component proves.
pub fn absorb(state: &Journal, word: u32) -> Journal {
    let lo = word & 0xffff;
    let hi = word >> 16;
    let mut next = *state;
    next[0] = (next[0] + lo) % P;
    next[1] = (next[1] + hi) % P;
    air::poseidon2::poseidon2_permutation(&mut next);
    next
}

/// Execute ECALL (COMMIT): read `a0`, absorb it into `journal`, advance PC.
pub fn ecall(cpu: &mut Cpu, journal: &mut Journal, inst: &DecodedInst, tracer: &mut Tracer) {
    debug_assert!(matches!(inst.opcode, crate::Opcode::Ecall));
    let a0 = cpu.read_reg(A0, tracer);
    *journal = absorb(journal, a0.next);
    cpu.advance_pc();
}
