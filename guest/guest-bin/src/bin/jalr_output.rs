//! Minimal proof-capable JALR guest.

#![no_std]
#![no_main]

use core::arch::asm;

guest_bin::guest_main!({
    let link: u32;
    unsafe {
        asm!(
            "la {target}, 1f",
            "addi {target}, {target}, 1",
            "jalr {link}, {target}, 0",
            "nop",
            "1:",
            target = out(reg) _,
            link = out(reg) link,
            options(nostack, nomem),
        );
    }
    link
});
