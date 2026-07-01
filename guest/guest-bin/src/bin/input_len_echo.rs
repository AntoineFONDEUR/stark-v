//! Echoes the host-provided input length as its output — exercises the
//! `__input_len` word the host publishes at setup.

#![no_std]
#![no_main]

guest_bin::guest_main!({
    // SAFETY: running inside the zkVM guest environment.
    let len = unsafe { guest_lib::io::read_input_len() };
    guest_lib::programs::ConstantResult { value: len as u32 }
});
