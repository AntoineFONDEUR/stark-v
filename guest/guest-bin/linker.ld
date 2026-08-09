OUTPUT_ARCH(riscv)
ENTRY(_start)

MEMORY {
    TEXT (rx)  : ORIGIN = 0x00000400, LENGTH = 0x000FFC00
    DATA (rw) : ORIGIN = 0x00200000, LENGTH = 0x00100000
}

/* Stack grows down from __stack_top toward __stack_bottom. A guard gap of
 * unmapped addresses sits below it so an overflow lands on memory nothing
 * else uses (a contained fault) instead of corrupting the output region. */
__stack_size = 0x00010000; /* 64 KiB */
__stack_top = 0x00200000;
__stack_bottom = __stack_top - __stack_size;
__stack_guard = 0x00001000; /* 4 KiB unmapped below the stack */

/* I/O region between TEXT end and the stack guard.
 *
 * Layout, low to high:
 *   [__input_len : u32] actual input byte count (host-written)
 *   [__input_start .. __input_end] input buffer
 *   [__halt_flag : u32]
 *   [__output_len : u32]
 *   [__output_data .. __output_end] output buffer
 * followed by the stack guard, then the stack.
 */
__io_start = 0x00100000;
__input_len = __io_start;
__input_start = __input_len + 4;
__input_capacity = 0x00010000; /* 64 KiB input buffer */
__input_end = __input_start + __input_capacity;
__halt_flag = __input_end;
__output_len = __halt_flag + 4;
__output_data = __halt_flag + 8;
__output_end = __stack_bottom - __stack_guard;

SECTIONS {
    .text : ALIGN(4) {
        __text_start = .;
        KEEP(*(.text._start))
        *(.text .text.*)
        *(.gnu.linkonce.t.*)
        __text_end = .;
    } > TEXT

    .rodata : ALIGN(4) {
        __data_start = .;
        *(.rodata .rodata.*)
        *(.srodata .srodata.*)
        *(.eh_frame*)
    } > DATA

    .bss (NOLOAD) : ALIGN(4) {
        __bss_start = .;
        *(.sbss .sbss.*)
        *(.bss .bss.*)
        *(COMMON)
        __bss_end = .;
    } > DATA

    .data : ALIGN(4) {
        *(.data .data.*)
        *(.sdata .sdata.*)
    } > DATA

    __text_len = __text_end - __text_start;
    __data_end = .;
    __data_len = __data_end - __data_start;

    /* Heap occupies remaining DATA region after static data */
    __heap_start = ALIGN(__data_end, 16);
    __heap_end = ORIGIN(DATA) + LENGTH(DATA);

    PROVIDE(__global_pointer$ = ORIGIN(DATA) + 0x800);

    /DISCARD/ : {
        *(.comment)
        *(.note.GNU-stack)
    }
}
