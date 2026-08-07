//! Mutable architectural state for one RV32IM execution.

use air::poseidon2::Poseidon2Digest;

use crate::trace::{Access, Tracer};

/// CPU state: 32 general-purpose registers and program counter.
pub struct Cpu {
    /// General-purpose registers x0-x31. x0 is hardwired to 0.
    regs: [u32; 32],
    /// Program counter.
    pub pc: u32,
    /// Proof-bound journal digest carried across segment boundaries.
    public_io_state: Poseidon2Digest,
}

impl Cpu {
    /// Create a new CPU with all registers zeroed apart from sp and gp, and pc at entry point.
    pub fn new(entry_pc: u32, sp: u32, gp: u32) -> Self {
        let mut regs = [0u32; 32];
        regs[2] = sp; // x2 = sp
        regs[3] = gp; // x3 = gp
        Self {
            regs,
            pc: entry_pc,
            public_io_state: Poseidon2Digest::default(),
        }
    }

    /// Read register value. x0 always returns 0.
    #[inline]
    pub fn reg(&self, idx: u8) -> u32 {
        if idx == 0 { 0 } else { self.regs[idx as usize] }
    }

    /// Write register value. Writes to x0 are ignored.
    #[inline]
    pub fn set_reg(&mut self, idx: u8, val: u32) {
        if idx != 0 {
            self.regs[idx as usize] = val;
        }
    }

    /// Advance PC by 4 bytes (one instruction).
    #[inline]
    pub fn advance_pc(&mut self) {
        self.pc = self.pc.wrapping_add(4);
    }

    /// Snapshot all general-purpose registers.
    #[inline]
    pub fn regs(&self) -> [u32; 32] {
        self.regs
    }

    /// Return the current proof-bound journal digest.
    #[inline]
    pub fn public_io_state(&self) -> Poseidon2Digest {
        self.public_io_state
    }

    /// Replace the journal digest after an authenticated permutation.
    #[inline]
    pub(crate) fn set_public_io_state(&mut self, state: Poseidon2Digest) {
        self.public_io_state = state;
    }

    // =========================================================================
    // Traced access methods
    // =========================================================================

    /// Read register with trace tracking.
    /// Intermediate catch-ups are stored in `tracer.clock_update`.
    /// Returns the final access record.
    #[inline]
    pub fn read_reg(&self, idx: u8, tracer: &mut Tracer) -> Access {
        let value = self.reg(idx);
        tracer.trace_reg_access(idx, value, value)
    }

    /// Write register with trace tracking.
    /// Intermediate catch-ups are stored in `tracer.clock_update`.
    /// Returns the final access record.
    #[inline]
    pub fn write_reg(&mut self, idx: u8, val: u32, tracer: &mut Tracer) -> Access {
        let prev = self.reg(idx);
        self.set_reg(idx, val);
        let next = if idx == 0 { 0 } else { val };
        tracer.trace_reg_access(idx, prev, next)
    }
}

#[cfg(test)]
#[allow(clippy::field_reassign_with_default)]
mod tests {
    use super::*;

    // =========================================================================
    // Basic CPU Operations
    // =========================================================================

    #[test]
    fn test_cpu_new() {
        let cpu = Cpu::new(0x1000, 0x2000, 0x3000);
        assert_eq!(cpu.pc, 0x1000);
        assert_eq!(cpu.reg(2), 0x2000); // sp
        assert_eq!(cpu.reg(3), 0x3000); // gp
        assert_eq!(cpu.reg(0), 0); // x0 always 0
        assert_eq!(cpu.reg(1), 0); // other regs start at 0
    }

    #[test]
    fn test_x0_always_zero() {
        let mut cpu = Cpu::new(0, 0, 0);
        cpu.set_reg(0, 0xDEADBEEF);
        assert_eq!(cpu.reg(0), 0); // Still 0
    }

    #[test]
    fn test_public_io_state_starts_zero() {
        assert_eq!(Cpu::new(0, 0, 0).public_io_state(), [0; 8]);
    }

    #[test]
    fn test_advance_pc() {
        let mut cpu = Cpu::new(0x1000, 0, 0);
        cpu.advance_pc();
        assert_eq!(cpu.pc, 0x1004);
    }

    // =========================================================================
    // Traced Read Access
    // =========================================================================

    #[test]
    fn test_read_reg_traced_first_access() {
        let mut cpu = Cpu::new(0, 0, 0);
        cpu.set_reg(5, 0x42);
        let mut tracer = Tracer::default();
        tracer.clock = 10;

        let access = cpu.read_reg(5, &mut tracer);

        assert_eq!(access.addr, 5);
        assert_eq!(access.prev, 0x42);
        assert_eq!(access.next, 0x42);
        assert_eq!(access.clock_prev, 0);
        // Note: access.clock is no longer stored; use tracer.clock at call site
        assert!(tracer.clock_update.is_empty());
    }

    #[test]
    fn test_read_reg_traced_with_gap() {
        let mut cpu = Cpu::new(0, 0, 0);
        cpu.set_reg(5, 0x42);
        let mut tracer = Tracer::with_max_clock_diff(100);

        tracer.clock = 0;
        cpu.read_reg(5, &mut tracer);

        tracer.clock = 350;
        let access = cpu.read_reg(5, &mut tracer);

        // Gap of 350 with max_diff 100 needs 3 intermediates
        assert_eq!(tracer.clock_update.len(), 3);

        // Verify intermediates have correct clock_prev progression: 0, 100, 200
        assert_eq!(tracer.clock_update.clock_prev[0], 0);
        assert_eq!(tracer.clock_update.clock_prev[1], 100);
        assert_eq!(tracer.clock_update.clock_prev[2], 200);

        // Final access's clock_prev is 300, and tracer.clock=350, so diff is 50 which is <= 100
        assert_eq!(access.clock_prev, 300);
    }

    #[test]
    fn test_read_x0_traced() {
        let cpu = Cpu::new(0, 0, 0);
        let mut tracer = Tracer::default();
        tracer.clock = 5;

        let access = cpu.read_reg(0, &mut tracer);

        assert_eq!(access.addr, 0);
        assert_eq!(access.prev, 0);
        assert_eq!(access.next, 0);
        assert!(tracer.clock_update.is_empty());
    }

    // =========================================================================
    // Traced Write Access
    // =========================================================================

    #[test]
    fn test_write_reg_traced_records_change() {
        let mut cpu = Cpu::new(0, 0, 0);
        cpu.set_reg(5, 0x11);
        let mut tracer = Tracer::default();
        tracer.clock = 5;

        let access = cpu.write_reg(5, 0x22, &mut tracer);

        assert_eq!(access.addr, 5);
        assert_eq!(access.prev, 0x11);
        assert_eq!(access.next, 0x22);
        assert_eq!(access.clock_prev, 0);
        // Note: access.clock is no longer stored; use tracer.clock at call site
        assert!(tracer.clock_update.is_empty());

        // Verify register was updated
        assert_eq!(cpu.reg(5), 0x22);
    }

    #[test]
    fn test_write_reg_traced_with_gap() {
        let mut cpu = Cpu::new(0, 0, 0);
        let mut tracer = Tracer::with_max_clock_diff(100);

        tracer.clock = 0;
        cpu.write_reg(5, 0x11, &mut tracer);

        tracer.clock = 350;
        let access = cpu.write_reg(5, 0x22, &mut tracer);

        // Gap of 350 with max_diff 100 needs 3 intermediates
        assert_eq!(tracer.clock_update.len(), 3);

        // Verify intermediates have correct clock_prev progression: 0, 100, 200
        assert_eq!(tracer.clock_update.clock_prev[0], 0);
        assert_eq!(tracer.clock_update.clock_prev[1], 100);
        assert_eq!(tracer.clock_update.clock_prev[2], 200);

        // Final access's clock_prev is 300, and tracer.clock=350, so diff is 50 which is <= 100
        assert_eq!(access.clock_prev, 300);
    }

    #[test]
    fn test_write_x0_traced() {
        let mut cpu = Cpu::new(0, 0, 0);
        let mut tracer = Tracer::default();
        tracer.clock = 5;

        let access = cpu.write_reg(0, 0xDEADBEEF, &mut tracer);

        // Still traces the access
        assert_eq!(access.addr, 0);
        assert_eq!(access.prev, 0);
        assert_eq!(access.next, 0); // x0 stays 0
        assert!(tracer.clock_update.is_empty());

        // Verify x0 is still 0
        assert_eq!(cpu.reg(0), 0);
    }

    #[test]
    fn test_consecutive_traced_accesses() {
        let mut cpu = Cpu::new(0, 0, 0);
        let mut tracer = Tracer::default();

        tracer.clock = 1;
        cpu.write_reg(5, 0x11, &mut tracer);

        tracer.clock = 2;
        let access = cpu.write_reg(5, 0x22, &mut tracer);

        assert_eq!(access.clock_prev, 1);
        // Note: access.clock is no longer stored; current clock is tracer.clock=2
        assert_eq!(access.prev, 0x11);
        assert_eq!(access.next, 0x22);
        assert!(tracer.clock_update.is_empty());
    }
}
