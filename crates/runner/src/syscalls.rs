//! Internal syscall request decoding and dispatch policy.

use crate::{Cpu, RunError};

const ARGUMENT_REGISTER: u8 = 10;
const SYSCALL_ID_REGISTER: u8 = 17;

/// Dispatches one `ecall` without exposing any unproved output state.
pub(crate) fn dispatch(cpu: &Cpu) -> Result<(), RunError> {
    let id = cpu.reg(SYSCALL_ID_REGISTER);
    let _argument = cpu.reg(ARGUMENT_REGISTER);

    // Calls remain disabled until their AIR authenticates every observable effect.
    Err(RunError::UnsupportedSyscall { pc: cpu.pc, id })
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
            dispatch(&cpu),
            Err(RunError::UnsupportedSyscall { pc: 0x400, id: 7 })
        ));
    }
}
