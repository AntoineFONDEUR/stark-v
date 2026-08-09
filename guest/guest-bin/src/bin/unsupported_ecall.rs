//! Guest fixture for the runner's proof-first syscall rejection boundary.

#![no_std]
#![no_main]

use core::arch::asm;

#[unsafe(no_mangle)]
pub extern "C" fn __zkvm_start() -> ! {
    unsafe {
        // The runner reads the standard RISC-V syscall id and first argument registers.
        asm!(
            "li a7, 7",
            "li a0, 0x12345678",
            "ecall",
            options(nostack, nomem)
        );
    }
    guest_bin::halt()
}
