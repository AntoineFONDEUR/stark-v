//! Internal syscall request decoding and dispatch policy.

use crate::instructions::COMMIT_SYSCALL_ID;
use crate::trace::Tracer;
use crate::{Cpu, RunError};

const ARGUMENT_REGISTER: u8 = 10;
const SYSCALL_ID_REGISTER: u8 = 17;

/// Dispatches one `ecall` without exposing any unproved output state.
pub(crate) fn dispatch(cpu: &Cpu, tracer: &mut Tracer) -> Result<(), RunError> {
    let id = cpu.reg(SYSCALL_ID_REGISTER);
    if id != COMMIT_SYSCALL_ID {
        return Err(RunError::UnsupportedSyscall { pc: cpu.pc, id });
    }

    // The generated AIR consumes these reads before journal state becomes observable.
    let selector = cpu.read_reg(SYSCALL_ID_REGISTER, tracer);
    let argument = cpu.read_reg(ARGUMENT_REGISTER, tracer);
    trace_op!(commit: tracer, cpu.pc, selector, argument);
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
            dispatch(&cpu, &mut Tracer::default()),
            Err(RunError::UnsupportedSyscall { pc: 0x400, id: 7 })
        ));
    }
}
