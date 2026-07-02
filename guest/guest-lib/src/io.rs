//! I/O helpers for guest programs.
//!
//! These functions use extern linker symbols from guest-bin/linker.ld
//! to access the zkVM's I/O memory regions.
//!
//! This module is only available when compiling for riscv32.

unsafe extern "C" {
    static __input_len: u8;
    static __input_start: u8;
    static __input_end: u8;
    static __halt_flag: u8;
    static __output_len: u8;
    static __output_data: u8;
    static __output_end: u8;
}

/// Read the actual number of input bytes the host provided.
///
/// The host writes this at `__input_len` before execution; it is at most the
/// input buffer capacity (`__input_end - __input_start`).
///
/// # Safety
/// Only call from within a zkVM guest program.
pub unsafe fn read_input_len() -> usize {
    unsafe {
        let len_addr = core::ptr::addr_of!(__input_len) as *const u32;
        core::ptr::read_volatile(len_addr) as usize
    }
}

/// Read input bytes from the input buffer.
///
/// # Safety
/// Only call from within a zkVM guest program.
pub unsafe fn read_input_bytes(buf: &mut [u8]) -> usize {
    unsafe {
        let start = core::ptr::addr_of!(__input_start) as usize;
        let end = core::ptr::addr_of!(__input_end) as usize;
        let input_size = end.saturating_sub(start);
        let len = buf.len().min(input_size);
        for (i, byte) in buf.iter_mut().take(len).enumerate() {
            let addr = start + i;
            *byte = core::ptr::read_volatile(addr as *const u8);
        }
        len
    }
}

/// Read a u32 from the start of the input buffer.
///
/// # Safety
/// Only call from within a zkVM guest program.
/// Caller must ensure input contains at least 4 bytes.
pub unsafe fn read_input_u32() -> u32 {
    unsafe {
        let start = core::ptr::addr_of!(__input_start) as *const u32;
        core::ptr::read_volatile(start)
    }
}

/// Read input bytes from the input buffer starting at a given offset.
///
/// # Safety
/// Only call from within a zkVM guest program.
pub unsafe fn read_input_bytes_at(offset: usize, buf: &mut [u8]) -> usize {
    unsafe {
        let start = core::ptr::addr_of!(__input_start) as usize;
        let end = core::ptr::addr_of!(__input_end) as usize;
        let input_size = end.saturating_sub(start);
        if offset >= input_size {
            return 0;
        }
        let available = input_size - offset;
        let len = buf.len().min(available);
        for (i, byte) in buf.iter_mut().take(len).enumerate() {
            let addr = start + offset + i;
            *byte = core::ptr::read_volatile(addr as *const u8);
        }
        len
    }
}

/// Write output bytes to the output buffer and set the length.
///
/// # Safety
/// Only call from within a zkVM guest program.
pub unsafe fn write_output_bytes(data: &[u8]) {
    unsafe {
        let data_start = core::ptr::addr_of!(__output_data) as usize;
        let data_end = core::ptr::addr_of!(__output_end) as usize;
        let max_size = data_end.saturating_sub(data_start);
        let len = data.len().min(max_size);
        // Write length
        let len_addr = core::ptr::addr_of!(__output_len) as *mut u32;
        core::ptr::write_volatile(len_addr, len as u32);
        // Write data
        for (i, byte) in data.iter().take(len).enumerate() {
            let addr = data_start + i;
            core::ptr::write_volatile(addr as *mut u8, *byte);
        }
    }
}

/// Signal halt to the zkVM runtime.
///
/// # Safety
/// Only call from within a zkVM guest program.
pub unsafe fn halt() {
    unsafe {
        let halt_addr = core::ptr::addr_of!(__halt_flag) as *mut u32;
        core::ptr::write_volatile(halt_addr, 1);
    }
}
