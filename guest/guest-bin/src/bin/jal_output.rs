//! Minimal proof-capable JAL guest.

#![no_std]
#![no_main]

use core::arch::asm;

guest_bin::guest_main!({
    let link: u32;
    unsafe {
        asm!(
            "jal {link}, 1f",
            "nop",
            "1:",
            link = out(reg) link,
            options(nostack, nomem),
        );
    }
    link
});
