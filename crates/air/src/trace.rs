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
mod tests {
    use super::*;

    // Column counts of the trace tables (schema- or fn-DSL-generated); a
    // change here means the table layout changed.
    mod prover_column_tests {
        use super::prover_columns::*;

        #[test]
        fn test_base_alu_reg_columns_size() {
            // clock, pc, rd (10), rs1 (10), rs2 (10) + 5 opcode flags = 37.
            assert_eq!(BaseAluRegColumns::<()>::SIZE, 37);
        }

        #[test]
        fn test_base_alu_imm_columns_size() {
            // clock, pc, rd (10), rs1 (10), imm_0/1/msb (3) + 4 flags = 29.
            assert_eq!(BaseAluImmColumns::<()>::SIZE, 29);
        }

        #[test]
        fn test_load_store_columns_size() {
            assert_eq!(LoadStoreColumns::<()>::SIZE, 50);
        }

        #[test]
        fn test_branch_eq_columns_size() {
            assert_eq!(BranchEqColumns::<()>::SIZE, 30);
        }

        #[test]
        fn test_jal_columns_size() {
            // enabler (1), clock, pc, rd (10), imm_felt = 14.
            assert_eq!(JalColumns::<()>::SIZE, 14);
        }

        #[test]
        fn test_mul_columns_size() {
            assert_eq!(MulColumns::<()>::SIZE, 33);
        }
    }

    mod row_extract_tests {
        use super::prover_columns::*;
        use stwo::core::fields::m31::BaseField;

        fn f(v: u32) -> BaseField {
            BaseField::from_u32_unchecked(v)
        }

        #[test]
        fn test_at_extracts_row_values() {
            // Column c holds [c, c + 100]; pc is the third column (index 2,
            // after enabler and clock).
            let data: Vec<Vec<BaseField>> = (0..JalColumns::<()>::SIZE as u32)
                .map(|c| vec![f(c), f(c + 100)])
                .collect();
            let cols = JalColumns::from_iter(data.iter());
            assert_eq!(cols.at(1).pc, f(102));
        }
    }

    #[test]
    fn test_tracer_print_tables_empty() {
        // An empty tracer must not panic when printing.
        let tracer = Tracer::default();
        tracer.print_tables(None, None);
    }
}
