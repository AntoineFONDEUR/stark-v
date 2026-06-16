//! Trace tables and the runtime tracer.
//!
//! Table definitions and the `Tracer` struct are generated in
//! [`crate::schema::trace`] by `define_air!` and re-exported here; the
//! clock catch-up machinery lives in [`crate::clock`] and is re-exported
//! because macro-generated code resolves it through `crate::trace`.

/// Unified access record for both registers and memory.
///
/// - For registers: `addr` is the register index (0-31)
/// - For memory: `addr` is the byte address
/// - Values stored as `[u8; 4]` little-endian limbs (1-4 bytes meaningful)
///
/// Note: The current clock (`clock`) is not stored here because it's redundant
/// with the VM's `tracer.clock` at the time of the access.
#[derive(Clone, Copy, Default, PartialEq, Eq)]
pub struct Access {
    pub addr: u32,
    pub prev: u32,
    pub clock_prev: u32,
    pub next: u32,
}

impl std::fmt::Debug for Access {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Access")
            .field("addr", &format_args!("{:#x}", self.addr))
            .field("prev", &format_args!("{:#x}", self.prev))
            .field("clock_prev", &self.clock_prev)
            .field("next", &format_args!("{:#x}", self.next))
            .finish()
    }
}

pub use crate::clock::{ClockGapAccess, ClockGapTable, ClockGapTableIter};
pub use crate::schema::trace::*;

#[cfg(test)]
#[allow(clippy::field_reassign_with_default)]
mod tests {
    use super::*;

    // =========================================================================
    // Columnar Table Tests
    // =========================================================================

    #[test]
    fn test_base_alu_reg_table_push() {
        let mut table = BaseAluRegTable::new();

        let rd = Access {
            addr: 1,
            prev: 0,
            clock_prev: 0,
            next: 10,
        };
        let rs1 = Access {
            addr: 2,
            prev: 5,
            clock_prev: 0,
            next: 5,
        };
        let rs2 = Access {
            addr: 3,
            prev: 5,
            clock_prev: 0,
            next: 5,
        };

        // Push with opcode flags: add=1, sub=0, xor=0, or=0, and=0
        table.push(1, 0x1000, rd, rs1, rs2, 1, 0, 0, 0, 0);

        assert_eq!(table.len(), 1);
        assert_eq!(table.clock[0], 1);
        assert_eq!(table.pc[0], 0x1000);
        assert_eq!(table.rd_addr[0], 1);
        assert_eq!(table.rd_next[0], 10);
        assert_eq!(table.rs1_addr[0], 2);
        assert_eq!(table.rs2_addr[0], 3);
        assert_eq!(table.opcode_add_flag[0], 1);
        assert_eq!(table.opcode_sub_flag[0], 0);
    }

    #[test]
    fn test_total_traces() {
        let mut tracer = Tracer::default();

        // Push some traces
        let rd = Access::default();
        let rs1 = Access::default();
        let rs2 = Access::default();

        // base_alu_reg with add flag
        tracer.base_alu_reg.push(0, 0, rd, rs1, rs2, 1, 0, 0, 0, 0);
        tracer.base_alu_reg.push(1, 4, rd, rs1, rs2, 1, 0, 0, 0, 0);
        // base_alu_reg with sub flag
        tracer.base_alu_reg.push(2, 8, rd, rs1, rs2, 0, 1, 0, 0, 0);

        assert_eq!(tracer.total_traces(), 3);
    }

    #[test]
    fn test_trace_op_macro() {
        let mut tracer = Tracer::default();
        tracer.clock = 1;

        let rd = Access::default();
        let rs1 = Access::default();
        let rs2 = Access::default();

        trace_op!(base_alu_reg: tracer, 0x1000, rd, rs1, rs2, 1, 0, 0, 0, 0);

        assert_eq!(tracer.base_alu_reg.len(), 1);
        assert_eq!(tracer.base_alu_reg.clock[0], 1);
        assert_eq!(tracer.base_alu_reg.pc[0], 0x1000);
    }

    // Test prover column generation for new family tables
    mod prover_column_tests {
        use super::prover_columns::*;

        #[test]
        fn test_base_alu_reg_columns_size() {
            // base_alu_reg: clock, pc, rd (10), rs1 (10), rs2 (10),
            // + 5 opcode flags = 37 total (no enabler - has flags)
            assert_eq!(BaseAluRegColumns::<()>::SIZE, 37);
        }

        #[test]
        fn test_base_alu_imm_columns_size() {
            // base_alu_imm: clock, pc, rd (10), rs1 (10),
            // + imm_0, imm_1, imm_msb (3) + 4 opcode flags = 29 total (no enabler - has flags)
            assert_eq!(BaseAluImmColumns::<()>::SIZE, 29);
        }

        #[test]
        fn test_lui_columns_size() {
            // LUI: enabler (1), clock, pc, rd (10), imm_0, imm_1, imm_2 = 16 total
            assert_eq!(LuiColumns::<()>::SIZE, 16);
        }

        #[test]
        fn test_load_store_columns_size() {
            // load_store: clock (1), pc (1), dst (10), rs1 (10), src (10),
            // + r2_idx, imm_felt, src_msb, shift_amount (4)
            // + src_addr_selector, dst_addr_selector (2)
            // + marker_0..3 (4) + 8 opcode flags = 50 total (no enabler - has flags)
            assert_eq!(LoadStoreColumns::<()>::SIZE, 50);
        }

        #[test]
        fn test_branch_eq_columns_size() {
            // branch_eq: clock (1), pc (1), rs1 (10), rs2 (10),
            // + imm_felt (1), cmp_result (1) + diff_inv_marker_0..3 (4) + 2 opcode flags = 30 total (no enabler - has flags)
            assert_eq!(BranchEqColumns::<()>::SIZE, 30);
        }

        #[test]
        fn test_jal_columns_size() {
            // JAL: enabler (1), clock, pc, rd (10), imm_felt = 14 total
            assert_eq!(JalColumns::<()>::SIZE, 14);
        }

        #[test]
        fn test_mul_columns_size() {
            // MUL: enabler (1), clock, pc, rd (10), rs1 (10), rs2 (10) = 33 total
            assert_eq!(MulColumns::<()>::SIZE, 33);
        }
    }

    // Test derived columns and constraints declared in define_trace_tables!
    mod derived_column_tests {
        use super::prover_columns::*;
        use stwo::core::fields::m31::BaseField;

        fn f(v: u32) -> BaseField {
            BaseField::from_u32_unchecked(v)
        }

        /// All-zero LUI columns, mutated per test.
        fn zero_lui_cols() -> LuiColumns<BaseField> {
            LuiColumns::from_iter(std::iter::repeat_n(f(0), LuiColumns::<()>::SIZE))
        }

        /// All-zero Base ALU Imm columns, mutated per test.
        fn zero_base_alu_imm_cols() -> BaseAluImmColumns<BaseField> {
            BaseAluImmColumns::from_iter(std::iter::repeat_n(f(0), BaseAluImmColumns::<()>::SIZE))
        }

        #[test]
        fn test_lui_imm_combines_limbs() {
            let mut cols = zero_lui_cols();
            cols.imm_0 = f(3);
            cols.imm_1 = f(5);
            cols.imm_2 = f(7);
            assert_eq!(cols.imm(), f(3 + 5 * (1 << 4) + 7 * (1 << 12)));
        }

        #[test]
        fn test_lui_pc_next_adds_four() {
            let mut cols = zero_lui_cols();
            cols.pc = f(0x1000);
            assert_eq!(cols.pc_next(), f(0x1004));
        }

        #[test]
        fn test_lui_rd_clock_diff() {
            let mut cols = zero_lui_cols();
            cols.clock = f(10);
            cols.rd_clock_prev = f(4);
            assert_eq!(cols.rd_clock_diff(), f(6));
        }

        #[test]
        fn test_lui_enabler_booleanity_holds_for_one() {
            let mut cols = zero_lui_cols();
            cols.enabler = f(1);
            assert_eq!(cols.constraints()[0], f(0));
        }

        #[test]
        fn test_lui_enabler_booleanity_fails_for_two() {
            let mut cols = zero_lui_cols();
            cols.enabler = f(2);
            assert_ne!(cols.constraints()[0], f(0));
        }

        #[test]
        fn test_base_alu_imm_enabler_sums_flags() {
            let mut cols = zero_base_alu_imm_cols();
            cols.opcode_add_flag = f(1);
            cols.opcode_or_flag = f(1);
            assert_eq!(cols.enabler(), f(2));
        }

        #[test]
        fn test_base_alu_imm_expected_opcode_id_selects_active_flag() {
            let mut cols = zero_base_alu_imm_cols();
            cols.opcode_xor_flag = f(1);
            assert_eq!(
                cols.expected_opcode_id(),
                f(crate::instructions::Opcode::Xori as u32)
            );
        }

        #[test]
        fn test_base_alu_imm_carry_0_detects_limb_overflow() {
            let mut cols = zero_base_alu_imm_cols();
            // 255 + 1 = 256 = 0 with carry 1 over an 8-bit limb
            cols.rs1_next_0 = f(255);
            cols.imm_0 = f(1);
            cols.rd_next_0 = f(0);
            assert_eq!(cols.carry_0(), f(1));
        }

        #[test]
        fn test_base_alu_imm_carry_1_chains_carry_0() {
            let mut cols = zero_base_alu_imm_cols();
            // Limb 0 overflows; limb 1 receives the carry and overflows too
            cols.rs1_next_0 = f(255);
            cols.imm_0 = f(1);
            cols.rd_next_0 = f(0);
            cols.rs1_next_1 = f(255);
            cols.rd_next_1 = f(0);
            assert_eq!(cols.carry_1(), f(1));
        }

        #[test]
        fn test_base_alu_imm_carry_booleanity_holds_for_valid_add() {
            let mut cols = zero_base_alu_imm_cols();
            cols.opcode_add_flag = f(1);
            // rs1 = 255, imm = 1: rd = 256, i.e. limb 0 wraps to 0 and limb 1 is 1
            cols.rs1_next_0 = f(255);
            cols.imm_0 = f(1);
            cols.rd_next_0 = f(0);
            cols.rd_next_1 = f(1);
            assert!(cols.constraints().iter().all(|c| *c == f(0)));
        }

        #[test]
        fn test_at_extracts_row_values() {
            // Column c holds [c, c + 100]; pc is the third column (index 2)
            let data: Vec<Vec<BaseField>> = (0..LuiColumns::<()>::SIZE as u32)
                .map(|c| vec![f(c), f(c + 100)])
                .collect();
            let cols = LuiColumns::from_iter(data.iter());
            assert_eq!(cols.at(1).pc, f(102));
        }
    }

    // =========================================================================
    // Table Debug Tests
    // =========================================================================

    mod debug_table_tests {
        use super::*;

        #[test]
        fn test_base_alu_reg_table_to_table() {
            let mut table = BaseAluRegTable::new();

            let rd = Access {
                addr: 1,
                prev: 0,
                clock_prev: 0,
                next: 10,
            };
            let rs1 = Access {
                addr: 2,
                prev: 5,
                clock_prev: 1,
                next: 5,
            };
            let rs2 = Access {
                addr: 3,
                prev: 7,
                clock_prev: 2,
                next: 7,
            };

            // Push two rows
            table.push(1, 0x1000, rd, rs1, rs2, 1, 0, 0, 0, 0);
            table.push(2, 0x1004, rd, rs1, rs2, 0, 1, 0, 0, 0);

            table.to_table().to_string();
        }

        #[test]
        fn test_lui_table_to_table_with_enabler() {
            // LUI has an enabler column (no opcode flags)
            let mut table = LuiTable::new();

            let rd = Access {
                addr: 10,
                prev: 0,
                clock_prev: 0,
                next: 0x12345000,
            };

            table.push(1, 0x1000, rd, 0x12, 0x34, 0x50);

            // Inspect header cells, not the rendered string: the dynamic
            // arrangement truncates wide headers to the terminal width.
            let headers: Vec<String> = table
                .to_table()
                .header()
                .expect("headers are always set")
                .cell_iter()
                .map(|cell| cell.content())
                .collect();
            assert!(headers.contains(&"enabler".to_string()));
        }

        #[test]
        fn test_empty_table_to_table() {
            let table = BaseAluRegTable::new();

            // An empty table still carries its headers; inspect the cells,
            // not the rendered string, which truncates to the terminal width.
            let headers: Vec<String> = table
                .to_table()
                .header()
                .expect("headers are always set")
                .cell_iter()
                .map(|cell| cell.content())
                .collect();
            assert!(headers.contains(&"clock".to_string()));
        }

        #[test]
        fn test_tracer_print_tables() {
            let mut tracer = Tracer::default();

            // Add some traces
            let rd = Access::default();
            let rs1 = Access::default();
            let rs2 = Access::default();

            tracer.base_alu_reg.push(0, 0, rd, rs1, rs2, 1, 0, 0, 0, 0);
            tracer.base_alu_reg.push(1, 4, rd, rs1, rs2, 1, 0, 0, 0, 0);

            // This should not panic
            tracer.print_tables(Some(10), Some(10));
        }

        #[test]
        fn test_tracer_print_tables_empty() {
            let tracer = Tracer::default();

            // Empty tracer should not panic
            tracer.print_tables(None, None);
        }

        #[test]
        fn test_multiple_tables_to_table() {
            let mut tracer = Tracer::default();

            // Add traces to different tables
            let rd = Access::default();
            let rs1 = Access::default();
            let rs2 = Access::default();

            tracer.base_alu_reg.push(0, 0, rd, rs1, rs2, 1, 0, 0, 0, 0);
            tracer.lui.push(1, 4, rd, 0, 0, 0);
            tracer.jal.push(2, 8, rd, 100);

            // Each table should produce valid output
            let base_alu_output = tracer.base_alu_reg.to_table().to_string();
            let lui_output = tracer.lui.to_table().to_string();
            let jal_output = tracer.jal.to_table().to_string();

            // LUI and JAL have enabler columns, BaseAluReg doesn't
            assert!(lui_output.contains("enabler"));
            assert!(jal_output.contains("enabler"));
            assert!(!base_alu_output.contains("enabler"));
        }
    }
}
