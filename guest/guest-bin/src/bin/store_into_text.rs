//! Deliberately stores a word into the read-only code region (address
//! 0x400, the TEXT origin) to exercise the runner's StoreIntoText fault.
#![no_std]
#![no_main]
use core::arch::asm;

#[unsafe(no_mangle)]
pub extern "C" fn __zkvm_start() -> ! {
    unsafe {
        asm!(
            "li t0, 0x00000400", // TEXT origin (_start lives here)
            "li t1, 0xDEADBEEF",
            "sw t1, 0(t0)",
            options(nostack)
        );
    }
    guest_bin::halt()
}
