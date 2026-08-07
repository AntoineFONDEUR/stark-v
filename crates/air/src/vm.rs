//! Architectural state interface used by felt-generated witness execution.

/// Raw register and aligned-memory operations needed by generated AIR functions.
///
/// The generated function owns trace access and constraint semantics; an
/// implementation only exposes the underlying architectural state.
pub trait MachineState {
    /// Read one general-purpose register.
    fn read_register(&self, index: u8) -> u32;

    /// Write one general-purpose register, preserving x0 semantics.
    fn write_register(&mut self, index: u8, value: u32);

    /// Read one aligned little-endian memory word.
    fn read_memory_word(&self, address: u32) -> u32;

    /// Write one aligned little-endian memory word.
    fn write_memory_word(&mut self, address: u32, value: u32);
}
