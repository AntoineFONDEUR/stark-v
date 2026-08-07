//! Proof-bound guest syscall interfaces.

/// Syscall selector for one journal COMMIT transition.
pub const COMMIT_SYSCALL_ID: u32 = 1;

/// Commits one word to the proof-bound application journal.
#[cfg(target_arch = "riscv32")]
#[inline(always)]
pub fn commit(word: u32) {
    unsafe {
        // Fixed registers keep the guest ABI identical to the authenticated AIR reads.
        core::arch::asm!(
            "ecall",
            in("a7") COMMIT_SYSCALL_ID,
            in("a0") word,
            options(nostack, nomem)
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn commit_selector_matches_the_proved_abi() {
        assert_eq!(COMMIT_SYSCALL_ID, 1);
    }
}
