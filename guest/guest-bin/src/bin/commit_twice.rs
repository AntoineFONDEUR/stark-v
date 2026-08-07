//! Guest fixture for two execution-ordered proof-bound COMMIT calls.

#![no_std]
#![no_main]

use core::arch::asm;

#[unsafe(no_mangle)]
pub extern "C" fn __zkvm_start() -> ! {
    unsafe {
        // Distinct words make any change in the authenticated order observable.
        asm!(
            "li a7, 1",
            "li a0, 0x11223344",
            "ecall",
            "li a0, 0x55667788",
            "ecall",
            options(nostack, nomem)
        );
    }
    guest_bin::glue::output_raw(&[])
}
