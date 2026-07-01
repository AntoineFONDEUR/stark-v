//! Commits a sequence of words to the output journal via ECALL, then halts.
//! Exercises the SYS_COMMIT syscall and the cross-segment journal sponge.

#![no_std]
#![no_main]

#[unsafe(no_mangle)]
pub extern "C" fn __zkvm_start() -> ! {
    // SAFETY: running inside the zkVM guest environment.
    unsafe {
        for i in 0..8u32 {
            guest_lib::io::commit_word(i.wrapping_mul(0x9e37_79b9).wrapping_add(1));
        }
    }
    guest_bin::halt()
}
