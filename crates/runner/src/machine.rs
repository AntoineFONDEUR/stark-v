//! Borrowed architectural state for felt-generated opcode execution.

use air::vm::MachineState as MachineStateTrait;

use crate::{Cpu, Memory};

/// Mutable CPU and memory view exposed to generated witness functions.
pub struct MachineState<'a> {
    cpu: &'a mut Cpu,
    memory: &'a mut Memory,
}

impl<'a> MachineState<'a> {
    /// Borrow the architectural state for one generated opcode call.
    pub fn new(cpu: &'a mut Cpu, memory: &'a mut Memory) -> Self {
        Self { cpu, memory }
    }
}

impl MachineStateTrait for MachineState<'_> {
    fn read_register(&self, index: u8) -> u32 {
        self.cpu.reg(index)
    }

    fn write_register(&mut self, index: u8, value: u32) {
        self.cpu.set_reg(index, value);
    }

    fn read_memory_word(&self, address: u32) -> u32 {
        self.memory.read_u32(address)
    }

    fn write_memory_word(&mut self, address: u32, value: u32) {
        self.memory.write_u32(address, value);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn register_write_preserves_x0() {
        let mut cpu = Cpu::new(0, 0, 0);
        let mut memory = Memory::new();
        let mut state = MachineState::new(&mut cpu, &mut memory);
        state.write_register(0, 7);
        assert_eq!(state.read_register(0), 0);
    }

    #[test]
    fn register_write_updates_general_register() {
        let mut cpu = Cpu::new(0, 0, 0);
        let mut memory = Memory::new();
        let mut state = MachineState::new(&mut cpu, &mut memory);
        state.write_register(5, 7);
        assert_eq!(state.read_register(5), 7);
    }

    #[test]
    fn memory_write_updates_aligned_word() {
        let mut cpu = Cpu::new(0, 0, 0);
        let mut memory = Memory::new();
        let mut state = MachineState::new(&mut cpu, &mut memory);
        state.write_memory_word(0x1000, 0x1234_5678);
        assert_eq!(state.read_memory_word(0x1000), 0x1234_5678);
    }
}
