//! Guest fixture for one proof-bound COMMIT syscall row.

#![no_std]
#![no_main]

#[unsafe(no_mangle)]
pub extern "C" fn __zkvm_start() -> ! {
    guest_lib::commit(0x1234_5678);
    // Every provable segment authenticates the public output-length word.
    guest_bin::glue::output_raw(&[])
}
