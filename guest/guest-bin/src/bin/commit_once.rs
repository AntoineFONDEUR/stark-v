//! Guest fixture for one proof-bound COMMIT syscall row.

#![no_std]
#![no_main]

use core::arch::asm;

#[unsafe(no_mangle)]
pub extern "C" fn __zkvm_start() -> ! {
    unsafe {
        // The internal ABI uses a7 as selector and a0 as the committed word.
        asm!(
            "li a7, 1",
            "li a0, 0x12345678",
            "ecall",
            options(nostack, nomem)
        );
    }
    // Every provable segment authenticates the public output-length word.
    guest_bin::glue::output_raw(&[])
}
