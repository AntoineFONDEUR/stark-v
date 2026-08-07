//! Internal syscall request decoding and dispatch policy.

use crate::instructions::{COMMIT_HASH_DOMAIN, COMMIT_SYSCALL_ID};
use crate::poseidon2::{DIGEST_WORDS, T, poseidon2_traced_state};
use crate::trace::Tracer;
use crate::{Cpu, RunError};

const ARGUMENT_REGISTER: u8 = 10;
const SYSCALL_ID_REGISTER: u8 = 17;

/// Dispatches one `ecall` without exposing any unproved output state.
pub(crate) fn dispatch(cpu: &mut Cpu, tracer: &mut Tracer) -> Result<(), RunError> {
    let id = cpu.reg(SYSCALL_ID_REGISTER);
    if id != COMMIT_SYSCALL_ID {
        return Err(RunError::UnsupportedSyscall { pc: cpu.pc, id });
    }

    // The generated AIR consumes these reads before journal state becomes observable.
    let selector = cpu.read_reg(SYSCALL_ID_REGISTER, tracer);
    let argument = cpu.read_reg(ARGUMENT_REGISTER, tracer);
    let journal_step = u32::try_from(tracer.commit.len()).expect("COMMIT trace length exceeds u32");
    let journal_prev_clock = tracer.commit.clock.last().copied().unwrap_or(0);
    let journal_prev = cpu.public_io_state();
    let mut input = [0_u32; T];
    input[..DIGEST_WORDS].copy_from_slice(&journal_prev);
    let argument_limbs = argument.next.to_le_bytes();
    input[DIGEST_WORDS..DIGEST_WORDS + 4].copy_from_slice(&argument_limbs.map(u32::from));
    input[DIGEST_WORDS + 4] = COMMIT_HASH_DOMAIN;
    let journal_next = poseidon2_traced_state(&mut tracer.poseidon2, input, false, true);
    cpu.set_public_io_state(
        journal_next[..DIGEST_WORDS]
            .try_into()
            .expect("journal digest width is fixed"),
    );
    trace_op!(commit: tracer, cpu.pc, selector, argument, journal_step, journal_prev_clock,
        journal_prev[0], journal_prev[1], journal_prev[2], journal_prev[3],
        journal_prev[4], journal_prev[5], journal_prev[6], journal_prev[7],
        journal_next[0], journal_next[1], journal_next[2], journal_next[3],
        journal_next[4], journal_next[5], journal_next[6], journal_next[7],
        journal_next[8], journal_next[9], journal_next[10], journal_next[11],
        journal_next[12], journal_next[13], journal_next[14], journal_next[15]
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dispatch_reports_the_selected_syscall() {
        let mut cpu = Cpu::new(0x400, 0, 0);
        cpu.set_reg(SYSCALL_ID_REGISTER, 7);
        cpu.set_reg(ARGUMENT_REGISTER, 0x1234_5678);

        assert!(matches!(
            dispatch(&mut cpu, &mut Tracer::default()),
            Err(RunError::UnsupportedSyscall { pc: 0x400, id: 7 })
        ));
    }
}
