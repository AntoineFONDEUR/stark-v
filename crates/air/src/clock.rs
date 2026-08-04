//! Read-write memory clock updates.
//!
//! Every register/memory access is constrained to advance that location's
//! clock by at most `max_clock_diff`. When an execution touches a location
//! after a longer pause, the gap is bridged with synthetic catch-up rows
//! that re-write the same value at intermediate clocks: [`ClockGapTable`]
//! stores those rows in columnar form and the [`Tracer`] gap-filling methods
//! generate them transparently while tracing real accesses.

use simd::AlignedVec;

use crate::trace::{Access, Tracer};

/// Columnar storage for synthetic clock catch-up rows.
///
/// The AIR fixes each row to advance the access clock by
/// [`crate::schema::trace::DEFAULT_MAX_CLOCK_DIFF`] without changing the
/// value.
#[derive(Clone)]
pub struct ClockGapTable {
    pub addr_space: AlignedVec<u32>,
    pub addr: AlignedVec<u32>,
    pub value: AlignedVec<u32>,
    pub clock_prev: AlignedVec<u32>,
    pub max_clock_diff: u32,
}

impl Default for ClockGapTable {
    fn default() -> Self {
        Self {
            addr_space: AlignedVec::new(),
            addr: AlignedVec::new(),
            value: AlignedVec::new(),
            clock_prev: AlignedVec::new(),
            max_clock_diff: crate::schema::trace::DEFAULT_MAX_CLOCK_DIFF,
        }
    }
}

impl std::fmt::Debug for ClockGapTable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut list = f.debug_list();
        for i in 0..self.len() {
            list.entry(&ClockGapAccess {
                addr_space: self.addr_space[i],
                access: Access {
                    addr: self.addr[i],
                    prev: self.value[i],
                    clock_prev: self.clock_prev[i],
                    next: self.value[i],
                },
            });
        }
        list.finish()
    }
}

impl ClockGapTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_capacity(cap: usize) -> Self {
        Self {
            addr_space: AlignedVec::with_capacity(cap),
            addr: AlignedVec::with_capacity(cap),
            value: AlignedVec::with_capacity(cap),
            clock_prev: AlignedVec::with_capacity(cap),
            max_clock_diff: crate::schema::trace::DEFAULT_MAX_CLOCK_DIFF,
        }
    }

    pub fn with_max_clock_diff(max_clock_diff: u32) -> Self {
        Self {
            max_clock_diff,
            ..Default::default()
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.addr.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.addr.is_empty()
    }

    #[inline]
    pub fn push(&mut self, addr_space: u32, access: Access) {
        debug_assert_eq!(
            access.prev, access.next,
            "clock catch-up must not change value"
        );
        self.addr_space.push(addr_space);
        self.addr.push(access.addr);
        self.value.push(access.prev);
        self.clock_prev.push(access.clock_prev);
    }

    /// Consumes the table and returns columns in canonical order.
    /// Order matches the generated `ClockUpdateColumns` layout, pinned by
    /// `tests/clock_layout.rs`.
    pub fn into_columns(self) -> Vec<AlignedVec<u32>> {
        let len = self.len();
        let mut enabler = AlignedVec::with_capacity(len);
        for _ in 0..len {
            enabler.push(1);
        }

        let mut value_0 = AlignedVec::with_capacity(len);
        let mut value_1 = AlignedVec::with_capacity(len);
        let mut value_2 = AlignedVec::with_capacity(len);
        let mut value_3 = AlignedVec::with_capacity(len);
        for val in self.value.iter() {
            let val = *val;
            value_0.push(val & 0xFF);
            value_1.push((val >> 8) & 0xFF);
            value_2.push((val >> 16) & 0xFF);
            value_3.push((val >> 24) & 0xFF);
        }

        vec![
            enabler,
            self.addr_space,
            self.addr,
            self.clock_prev,
            value_0,
            value_1,
            value_2,
            value_3,
        ]
    }

    /// Convert table to trace columns, padding to power of 2.
    /// Always produces columns with minimum log_size of 4 (16 rows),
    /// even for empty tables.
    pub fn into_witness(
        self,
    ) -> Vec<
        stwo::prover::poly::circle::CircleEvaluation<
            stwo::prover::backend::simd::SimdBackend,
            stwo::core::fields::m31::BaseField,
            stwo::prover::poly::BitReversedOrder,
        >,
    > {
        let len = self.len() as u32;
        let log_size = len.next_power_of_two().ilog2().max(4);
        self.into_witness_with_log_size(log_size)
            .expect("the natural clock trace log size contains every row")
    }

    /// Converts the clock table to a verifier-selected fixed trace size.
    ///
    /// Returning `None` lets the fixed-profile prover reject an oversized
    /// segment before committing execution-dependent column geometry.
    pub fn into_witness_with_log_size(
        self,
        log_size: u32,
    ) -> Option<
        Vec<
            stwo::prover::poly::circle::CircleEvaluation<
                stwo::prover::backend::simd::SimdBackend,
                stwo::core::fields::m31::BaseField,
                stwo::prover::poly::BitReversedOrder,
            >,
        >,
    > {
        use stwo::core::poly::circle::CanonicCoset;
        use stwo::prover::backend::simd::column::BaseColumn;
        use stwo::prover::poly::circle::CircleEvaluation;

        let padded_len = 1_u32.checked_shl(log_size)?;
        if log_size < 4 || self.len() > padded_len as usize {
            return None;
        }
        let columns = self.into_columns();
        let domain = CanonicCoset::new(log_size).circle_domain();

        Some(
            columns
                .into_iter()
                .map(|mut col| {
                    col.resize(padded_len as usize, 0);
                    let base_col: BaseColumn = col.into();
                    CircleEvaluation::new(domain, base_col)
                })
                .collect(),
        )
    }

    pub fn to_witness(
        &self,
    ) -> Vec<
        stwo::prover::poly::circle::CircleEvaluation<
            stwo::prover::backend::simd::SimdBackend,
            stwo::core::fields::m31::BaseField,
            stwo::prover::poly::BitReversedOrder,
        >,
    > {
        self.clone().into_witness()
    }

    /// Returns an iterator over Access values stored in columnar form.
    pub fn iter(&self) -> ClockGapTableIter<'_> {
        ClockGapTableIter {
            table: self,
            idx: 0,
        }
    }
}

/// One synthetic clock catch-up row.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ClockGapAccess {
    pub addr_space: u32,
    pub access: Access,
}

/// Iterator over [`ClockGapTable`] that yields [`ClockGapAccess`] values.
pub struct ClockGapTableIter<'a> {
    table: &'a ClockGapTable,
    idx: usize,
}

impl Iterator for ClockGapTableIter<'_> {
    type Item = ClockGapAccess;

    fn next(&mut self) -> Option<Self::Item> {
        if self.idx >= self.table.len() {
            None
        } else {
            let clock_prev = self.table.clock_prev[self.idx];
            let value = self.table.value[self.idx];
            let access = ClockGapAccess {
                addr_space: self.table.addr_space[self.idx],
                access: Access {
                    addr: self.table.addr[self.idx],
                    prev: value,
                    clock_prev,
                    next: value,
                },
            };
            self.idx += 1;
            Some(access)
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.table.len() - self.idx;
        (remaining, Some(remaining))
    }
}

impl ExactSizeIterator for ClockGapTableIter<'_> {}

impl<'a> IntoIterator for &'a ClockGapTable {
    type Item = ClockGapAccess;
    type IntoIter = ClockGapTableIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl Tracer {
    /// Generate and store intermediate accesses for clock catch-up.
    fn fill_gap(
        &mut self,
        table: GapTable,
        addr: u32,
        value: u32,
        clock_prev: u32,
        target_clock: u32,
    ) -> u32 {
        let mut current_clock = clock_prev;

        while target_clock.saturating_sub(current_clock) > self.max_clock_diff {
            let next_clock = current_clock.saturating_add(self.max_clock_diff);
            let access = Access {
                addr,
                prev: value,
                clock_prev: current_clock,
                next: value,
            };
            self.clock_update.push(table.addr_space(), access);
            current_clock = next_clock;
        }

        current_clock
    }

    /// Trace a register access with gap-filling.
    /// Intermediate accesses are pushed to `clock_update`.
    /// Returns only the final access.
    pub fn trace_reg_access(&mut self, idx: u8, prev: u32, next: u32) -> Access {
        let clock_prev = self.reg_clock[idx as usize];
        let addr = idx as u32;

        // Generate intermediate catch-up accesses and get final clock_prev
        let final_clock_prev = self.fill_gap(GapTable::Reg, addr, prev, clock_prev, self.clock);

        // Update the register's clock after gap-filling
        if final_clock_prev != clock_prev {
            self.reg_clock[idx as usize] = final_clock_prev;
        }

        // Create the final access (clock is available from tracer.clock at call site)
        let final_access = Access {
            addr,
            prev,
            clock_prev: final_clock_prev,
            next,
        };

        // Update the register's clock
        self.reg_clock[idx as usize] = self.clock;

        final_access
    }

    /// Trace a memory access with gap-filling.
    /// All memory accesses are traced at 4-byte aligned addresses.
    /// Intermediate accesses are pushed to `clock_update`.
    /// Returns only the final access.
    pub fn trace_mem_access(&mut self, addr: u32, prev: u32, next: u32) -> Access {
        // Always use 4-byte aligned address
        let aligned_addr = addr & !3;

        self.mem_initial.entry(aligned_addr).or_insert(prev);

        let clock_prev = self.mem_clock.get(&aligned_addr).copied().unwrap_or(0);

        // Generate intermediate catch-up accesses and get final clock_prev
        let final_clock_prev =
            self.fill_gap(GapTable::Mem, aligned_addr, prev, clock_prev, self.clock);

        // Update mem_clock after gap-filling
        if final_clock_prev != clock_prev {
            self.mem_clock.insert(aligned_addr, final_clock_prev);
        }

        // Create the final access (clock is available from tracer.clock at call site)
        let final_access = Access {
            addr: aligned_addr,
            prev,
            clock_prev: final_clock_prev,
            next,
        };

        // Update the memory word's clock
        self.mem_clock.insert(aligned_addr, self.clock);

        final_access
    }

    pub fn trace_instr_access(&mut self, pc: u32) {
        *self.program_reads.entry(pc).or_insert(0) += 1;
    }
}

/// Helper enum for gap-filling table selection.
#[derive(Clone, Copy)]
enum GapTable {
    Reg,
    Mem,
}

impl GapTable {
    fn addr_space(self) -> u32 {
        match self {
            GapTable::Reg => 0,
            GapTable::Mem => 1,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::trace::DEFAULT_MAX_CLOCK_DIFF;

    const MEM_ADDR: u32 = 0x2000;

    // =========================================================================
    // Tracer Construction
    // =========================================================================

    #[test]
    fn test_default_tracer() {
        let tracer = Tracer::default();
        assert_eq!(tracer.clock, 0);
        assert_eq!(tracer.max_clock_diff, DEFAULT_MAX_CLOCK_DIFF);
        assert_eq!(tracer.reg_clock, [0; 32]);
        assert!(tracer.mem_clock.is_empty());
        assert!(tracer.mem_initial.is_empty());
        assert!(tracer.program_reads.is_empty());
    }

    #[test]
    fn test_with_max_clock_diff() {
        let tracer = Tracer::with_max_clock_diff(100);
        assert_eq!(tracer.max_clock_diff, 100);
        assert_eq!(tracer.clock, 0);
    }

    // =========================================================================
    // Memory Access Tracing
    // =========================================================================

    #[test]
    fn test_trace_mem_access_first_access() {
        let mut tracer = Tracer {
            clock: 10,
            ..Default::default()
        };

        let access = tracer.trace_mem_access(MEM_ADDR, 0x42, 0x42);

        assert_eq!(access.addr, MEM_ADDR);
        assert_eq!(access.prev, 0x42);
        assert_eq!(access.next, 0x42);
        assert_eq!(access.clock_prev, 0);
        // Note: access.clock is no longer stored; use tracer.clock at call site
        assert!(tracer.clock_update.is_empty());
    }

    #[test]
    fn test_trace_mem_access_consecutive() {
        let mut tracer = Tracer {
            clock: 1,
            ..Default::default()
        };
        tracer.trace_mem_access(MEM_ADDR, 0x11, 0x11);

        tracer.clock = 2;
        let access = tracer.trace_mem_access(MEM_ADDR, 0x11, 0x22);

        assert_eq!(access.clock_prev, 1);
        // Note: access.clock is no longer stored; current clock is tracer.clock=2
        assert_eq!(access.prev, 0x11);
        assert_eq!(access.next, 0x22);
        assert!(tracer.clock_update.is_empty());
    }

    #[test]
    fn test_trace_mem_access_gap_filling() {
        let mut tracer = Tracer::with_max_clock_diff(100);

        tracer.clock = 0;
        tracer.trace_mem_access(MEM_ADDR, 0x42, 0x42);

        tracer.clock = 350;
        let access = tracer.trace_mem_access(MEM_ADDR, 0x42, 0x42);

        // Gap of 350 with max_diff 100 needs 3 intermediates
        assert_eq!(
            tracer.clock_update.len(),
            3,
            "Expected 3 intermediates, got {}",
            tracer.clock_update.len()
        );

        // Verify intermediates have correct clock_prev progression
        // Each intermediate's clock was clock_prev + max_clock_diff (now implicit)
        // Sequence: 0 -> 100 -> 200 -> 300 -> 350 (final)
        assert_eq!(tracer.clock_update.clock_prev[0], 0);
        assert_eq!(tracer.clock_update.clock_prev[1], 100);
        assert_eq!(tracer.clock_update.clock_prev[2], 200);

        // Final access's clock_prev should be 300 (after 3 intermediates)
        assert_eq!(access.clock_prev, 300);
        // Final access's clock is tracer.clock=350, diff is 50 which is <= 100
    }

    #[test]
    fn test_trace_mem_access_exact_max_diff() {
        let mut tracer = Tracer::with_max_clock_diff(100);

        tracer.clock = 0;
        tracer.trace_mem_access(MEM_ADDR, 0, 0);

        tracer.clock = 100;
        let access = tracer.trace_mem_access(MEM_ADDR, 0, 0);

        // Exactly at max_clock_diff - no intermediate needed
        assert!(tracer.clock_update.is_empty());
        assert_eq!(access.clock_prev, 0);
        // Note: access.clock is no longer stored; current clock is tracer.clock=100
    }

    #[test]
    fn test_trace_mem_access_preserves_value() {
        let mut tracer = Tracer::with_max_clock_diff(50);

        tracer.clock = 0;
        tracer.trace_mem_access(MEM_ADDR, 0xAB, 0xAB);

        tracer.clock = 200;
        let access = tracer.trace_mem_access(MEM_ADDR, 0xAB, 0xAB);

        // All intermediate accesses should preserve the value
        for intermediate in &tracer.clock_update {
            assert_eq!(intermediate.access.prev, 0xAB);
            assert_eq!(intermediate.access.next, 0xAB);
        }
        // Final access should also preserve value
        assert_eq!(access.prev, 0xAB);
        assert_eq!(access.next, 0xAB);
    }

    #[test]
    fn test_trace_mem_access_updates_mem_clock() {
        let mut tracer = Tracer {
            clock: 10,
            ..Default::default()
        };

        tracer.trace_mem_access(MEM_ADDR, 0, 0);

        assert_eq!(tracer.mem_clock.get(&MEM_ADDR), Some(&10));
    }

    // =========================================================================
    // Register Access Tracing
    // =========================================================================

    #[test]
    fn test_trace_reg_access_first_access() {
        let mut tracer = Tracer {
            clock: 10,
            ..Default::default()
        };

        let access = tracer.trace_reg_access(5, 0x42, 0x42);

        assert_eq!(access.addr, 5);
        assert_eq!(access.prev, 0x42);
        assert_eq!(access.next, 0x42);
        assert_eq!(access.clock_prev, 0);
        // Note: access.clock is no longer stored; use tracer.clock at call site
        assert!(tracer.clock_update.is_empty());
    }

    #[test]
    fn test_trace_reg_access_consecutive() {
        let mut tracer = Tracer {
            clock: 1,
            ..Default::default()
        };
        tracer.trace_reg_access(5, 0x11, 0x11);

        tracer.clock = 2;
        let access = tracer.trace_reg_access(5, 0x11, 0x22);

        assert_eq!(access.clock_prev, 1);
        // Note: access.clock is no longer stored; current clock is tracer.clock=2
        assert_eq!(access.prev, 0x11);
        assert_eq!(access.next, 0x22);
        assert!(tracer.clock_update.is_empty());
    }

    #[test]
    fn test_trace_reg_access_gap_filling() {
        let mut tracer = Tracer::with_max_clock_diff(100);

        tracer.clock = 0;
        tracer.trace_reg_access(5, 0x42, 0x42);

        tracer.clock = 350;
        let access = tracer.trace_reg_access(5, 0x42, 0x42);

        // Gap of 350 with max_diff 100 needs 3 intermediates
        assert_eq!(
            tracer.clock_update.len(),
            3,
            "Expected 3 intermediates, got {}",
            tracer.clock_update.len()
        );

        // Verify intermediates have correct clock_prev progression
        // Each intermediate's clock was clock_prev + max_clock_diff (now implicit)
        // Sequence: 0 -> 100 -> 200 -> 300 -> 350 (final)
        assert_eq!(tracer.clock_update.clock_prev[0], 0);
        assert_eq!(tracer.clock_update.clock_prev[1], 100);
        assert_eq!(tracer.clock_update.clock_prev[2], 200);

        // Final access's clock_prev should be 300 (after 3 intermediates)
        assert_eq!(access.clock_prev, 300);
        // Final access's clock is tracer.clock=350, diff is 50 which is <= 100
    }

    #[test]
    fn test_trace_reg_access_x0() {
        let mut tracer = Tracer {
            clock: 10,
            ..Default::default()
        };

        // x0 can still be traced - the caller handles x0 semantics
        let access = tracer.trace_reg_access(0, 0, 0);

        assert_eq!(access.addr, 0);
        assert_eq!(access.prev, 0);
        assert_eq!(access.next, 0);
        assert!(tracer.clock_update.is_empty());
    }

    #[test]
    fn test_trace_reg_access_updates_reg_clock() {
        let mut tracer = Tracer {
            clock: 10,
            ..Default::default()
        };

        tracer.trace_reg_access(5, 0, 0);

        assert_eq!(tracer.reg_clock[5], 10);
    }

    // =========================================================================
    // Edge Cases
    // =========================================================================

    #[test]
    fn test_max_clock_diff_one() {
        let mut tracer = Tracer::with_max_clock_diff(1);

        tracer.clock = 0;
        tracer.trace_mem_access(MEM_ADDR, 0, 0);

        tracer.clock = 5;
        let access = tracer.trace_mem_access(MEM_ADDR, 0, 0);

        // With max_clock_diff=1, gap of 5 needs 4 intermediates + 1 final
        assert_eq!(tracer.clock_update.len(), 4);

        // Verify intermediates have correct clock_prev progression: 0, 1, 2, 3
        // Each intermediate's clock was clock_prev + 1 (now implicit)
        assert_eq!(tracer.clock_update.clock_prev[0], 0);
        assert_eq!(tracer.clock_update.clock_prev[1], 1);
        assert_eq!(tracer.clock_update.clock_prev[2], 2);
        assert_eq!(tracer.clock_update.clock_prev[3], 3);

        // Final access's clock_prev is 4, and tracer.clock=5, so diff is 1
        assert_eq!(access.clock_prev, 4);
    }

    #[test]
    fn test_max_clock_diff_max() {
        let mut tracer = Tracer::with_max_clock_diff(u32::MAX);

        tracer.clock = 0;
        tracer.trace_mem_access(MEM_ADDR, 0, 0);

        tracer.clock = u32::MAX - 1;
        tracer.trace_mem_access(MEM_ADDR, 0, 0);

        // No intermediate ever needed
        assert!(tracer.clock_update.is_empty());
    }

    #[test]
    fn test_clock_gap_table_push() {
        let mut table = ClockGapTable::with_max_clock_diff(100);

        // ClockGapTable is for gap-filling: prev == next
        let value = 42u32;
        let access = Access {
            addr: 100,
            prev: value,
            clock_prev: 0,
            next: value,
        };
        table.push(1, access);

        assert_eq!(table.len(), 1);
        assert_eq!(table.addr_space[0], 1);
        assert_eq!(table.addr[0], 100);
        assert_eq!(table.value[0], value);
    }
}
