use crate::Memory;
use goblin::elf::Elf;
use goblin::elf::program_header::PT_LOAD;
use thiserror::Error;
use tracing::debug;

#[derive(Error, Debug)]
pub enum ElfError {
    #[error("Failed to parse ELF: {0}")]
    Parse(#[from] goblin::error::Error),
    #[error("Not a 32-bit ELF")]
    Not32Bit,
    #[error("Not a RISC-V ELF")]
    NotRiscV,
}

/// Loaded ELF with entry point and memory initialization.
pub struct LoadedElf {
    /// Entry point PC.
    pub entry: u32,
    /// Initial stack pointer.
    pub sp: u32,
    /// Global pointer.
    pub gp: u32,
    /// Memory initialized with loadable segments.
    pub memory: Memory,
    /// Text segment base address.
    pub text_base: u32,
    /// Text segment end address (exclusive).
    pub text_end: u32,
    /// Data segment base address.
    pub data_base: u32,
    /// Data segment end address (exclusive).
    pub data_end: u32,
    /// Stack bottom address.
    pub stack_bottom: u32,
    /// Address of halt flag (from __halt_flag linker symbol).
    pub halt_flag_addr: u32,
    /// Address of output length (from __output_len linker symbol).
    pub output_len_addr: u32,
    /// Address of output data start (from __output_data linker symbol).
    pub output_data_addr: u32,
    /// Address of output data end (from __output_end linker symbol).
    pub output_end_addr: u32,
    /// Address of input data start (from __input_start linker symbol).
    pub input_start_addr: u32,
    /// Address of input data end (from __input_end linker symbol).
    pub input_end_addr: u32,
    /// Address of the input length word (from __input_len linker symbol), if
    /// the program exposes one. The host writes the actual input byte count
    /// here so the guest need not treat the whole buffer as live.
    pub input_len_addr: Option<u32>,
}

/// Load an ELF file and return the entry point, initial registers, and memory.
pub fn load_elf(bytes: &[u8]) -> Result<LoadedElf, ElfError> {
    let elf = Elf::parse(bytes)?;

    // Verify it's a 32-bit RISC-V ELF
    if !elf.is_lib && elf.header.e_machine != goblin::elf::header::EM_RISCV {
        return Err(ElfError::NotRiscV);
    }

    let entry = elf.entry as u32;
    debug!(entry = format_args!("0x{:08x}", entry), "ELF entry point");

    // Helper to find a symbol by name
    let find_symbol = |name: &str| -> Option<u32> {
        elf.syms
            .iter()
            .find(|s| elf.strtab.get_at(s.st_name).is_some_and(|n| n == name))
            .map(|s| s.st_value as u32)
    };

    // Find __global_pointer$ symbol
    let gp = find_symbol("__global_pointer$").unwrap_or(0x0020_0800);
    debug!(gp = format_args!("0x{:08x}", gp), "Global pointer");

    // Find __stack_top symbol
    let sp = find_symbol("__stack_top").unwrap_or(0x0020_0000);
    debug!(sp = format_args!("0x{:08x}", sp), "Stack pointer");
    let stack_bottom = find_symbol("__stack_bottom")
        .or_else(|| find_symbol("__stack_size").map(|size| sp.wrapping_sub(size)))
        .unwrap_or(sp);
    debug!(
        stack_bottom = format_args!("0x{:08x}", stack_bottom),
        "Stack bottom"
    );
    let text_base = find_symbol("__text_start").unwrap_or(entry);
    let text_len = find_symbol("__text_len").unwrap_or(0);
    let text_end = text_base.wrapping_add(text_len);

    let data_base = find_symbol("__data_start").unwrap_or(stack_bottom);
    let data_len = find_symbol("__data_len").unwrap_or(0);
    let data_end = data_base.wrapping_add(data_len);

    // Find I/O region symbols
    let halt_flag_addr = find_symbol("__halt_flag").unwrap_or(0x0010_0000);
    let output_len_addr = find_symbol("__output_len").unwrap_or(0x0010_0004);
    let output_data_addr = find_symbol("__output_data").unwrap_or(0x0010_0008);
    let output_end_addr = find_symbol("__output_end").unwrap_or(0x001F_FC00);
    let input_start_addr = find_symbol("__input_start").unwrap_or(output_len_addr);
    let input_end_addr = find_symbol("__input_end").unwrap_or(input_start_addr);
    let input_len_addr = find_symbol("__input_len");
    debug!(
        halt_flag = format_args!("0x{:08x}", halt_flag_addr),
        output_len = format_args!("0x{:08x}", output_len_addr),
        output_data = format_args!("0x{:08x}", output_data_addr),
        output_end = format_args!("0x{:08x}", output_end_addr),
        input_start = format_args!("0x{:08x}", input_start_addr),
        input_end = format_args!("0x{:08x}", input_end_addr),
        "I/O region"
    );

    // Load all PT_LOAD segments into memory
    let mut mem_data = Vec::new();
    for ph in &elf.program_headers {
        if ph.p_type == PT_LOAD {
            let vaddr = ph.p_vaddr as u32;
            let file_offset = ph.p_offset as usize;
            let file_size = ph.p_filesz as usize;
            let mem_size = ph.p_memsz as usize;

            debug!(
                vaddr = format_args!("0x{:08x}", vaddr),
                file_offset,
                file_size,
                mem_size,
                bss_size = mem_size.saturating_sub(file_size),
                "Loading PT_LOAD segment"
            );

            // Copy file contents
            if file_size > 0 && file_offset + file_size <= bytes.len() {
                for (i, &byte) in bytes[file_offset..file_offset + file_size]
                    .iter()
                    .enumerate()
                {
                    mem_data.push((vaddr.wrapping_add(i as u32), byte));
                }
            }

            // Zero-fill BSS (memsz > filesz)
            for i in file_size..mem_size {
                mem_data.push((vaddr.wrapping_add(i as u32), 0));
            }
        }
    }

    debug!(total_bytes = mem_data.len(), "Total memory bytes loaded");

    let memory: Memory = mem_data.into_iter().collect();

    Ok(LoadedElf {
        entry,
        sp,
        gp,
        memory,
        text_base,
        text_end,
        data_base,
        data_end,
        stack_bottom,
        halt_flag_addr,
        output_len_addr,
        output_data_addr,
        output_end_addr,
        input_start_addr,
        input_end_addr,
        input_len_addr,
    })
}
