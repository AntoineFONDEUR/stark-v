//! Trace tables and the runtime tracer.
//!
//! Manual schema tables and felt-DSL tables are assembled into one `Tracer`
//! by [`crate::schema::trace`] and re-exported here. The clock catch-up
//! machinery lives in [`crate::clock`] and is re-exported because generated
//! code resolves it through `crate::trace`.

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

    #[test]
    fn total_traces_counts_generated_component_rows() {
        use crate::opcodes::base_alu_imm::prover_columns::BaseAluImmColumns;
        use crate::opcodes::base_alu_reg::prover_columns::BaseAluRegColumns;

        let mut tracer = Tracer::default();
        tracer
            .base_alu_reg
            .push_row(&vec![0; BaseAluRegColumns::<()>::SIZE]);
        tracer
            .base_alu_reg
            .push_row(&vec![0; BaseAluRegColumns::<()>::SIZE]);
        tracer
            .base_alu_imm
            .push_row(&vec![0; BaseAluImmColumns::<()>::SIZE]);

        assert_eq!(tracer.total_traces(), 3);
    }

    // Component column layouts remain explicit protocol geometry.
    mod prover_column_tests {
        use super::prover_columns::*;

        #[test]
        fn test_load_store_columns_size() {
            // Inputs, dynamic accesses, lane selectors, and materialized products.
            assert_eq!(LoadStoreColumns::<()>::SIZE, 75);
        }

        #[test]
        fn test_jal_columns_size() {
            // The generated layout includes the link split, register access,
            // and materialized next-PC return in addition to the inputs.
            assert_eq!(JalColumns::<()>::SIZE, 20);
        }

        #[test]
        fn test_mul_columns_size() {
            // Inputs, authenticated accesses, product splits, and next PC.
            assert_eq!(MulColumns::<()>::SIZE, 51);
        }
    }

    // Manual schema constraints are testable directly on their generated columns.
    mod derived_column_tests {
        use super::prover_columns::*;
        use stwo::core::fields::m31::BaseField;

        fn f(v: u32) -> BaseField {
            BaseField::from_u32_unchecked(v)
        }

        /// A valid COMMIT row starts from a zeroed generated column layout.
        fn valid_commit_cols() -> CommitColumns<BaseField> {
            let mut cols =
                CommitColumns::from_iter(std::iter::repeat_n(f(0), CommitColumns::<()>::SIZE));
            cols.enabler = f(1);
            cols.clock = f(1);
            cols.selector_addr = f(17);
            cols.selector_prev_0 = f(crate::instructions::COMMIT_SYSCALL_ID);
            cols.selector_next_0 = f(crate::instructions::COMMIT_SYSCALL_ID);
            cols.argument_addr = f(10);
            cols.argument_prev_0 = f(0x78);
            cols.argument_prev_1 = f(0x56);
            cols.argument_prev_2 = f(0x34);
            cols.argument_prev_3 = f(0x12);
            cols.argument_next_0 = f(0x78);
            cols.argument_next_1 = f(0x56);
            cols.argument_next_2 = f(0x34);
            cols.argument_next_3 = f(0x12);
            cols
        }

        #[test]
        fn commit_accepts_the_authenticated_selector_and_argument_reads() {
            assert!(
                valid_commit_cols()
                    .constraints()
                    .iter()
                    .all(|constraint| *constraint == f(0))
            );
        }

        #[test]
        fn commit_rejects_a_non_commit_selector() {
            let mut cols = valid_commit_cols();
            cols.selector_prev_0 = f(crate::instructions::COMMIT_SYSCALL_ID + 1);
            cols.selector_next_0 = f(crate::instructions::COMMIT_SYSCALL_ID + 1);

            assert!(
                cols.constraints()
                    .iter()
                    .any(|constraint| *constraint != f(0))
            );
        }

        #[test]
        fn commit_rejects_a_hidden_argument_write() {
            let mut cols = valid_commit_cols();
            cols.argument_next_0 = f(0x79);

            assert!(
                cols.constraints()
                    .iter()
                    .any(|constraint| *constraint != f(0))
            );
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
        fn test_tracer_print_tables_empty() {
            let tracer = Tracer::default();

            // Empty tracer should not panic
            tracer.print_tables(None, None);
        }

        #[test]
        fn test_jal_table_to_table_with_enabler() {
            let table = JalTable::new();

            // Header cells retain the full schema when terminal rendering truncates wide tables.
            let headers: Vec<String> = table
                .to_table()
                .header()
                .expect("headers are always set")
                .cell_iter()
                .map(|cell| cell.content())
                .collect();
            assert!(headers.contains(&"enabler".to_string()));
        }
    }
}
