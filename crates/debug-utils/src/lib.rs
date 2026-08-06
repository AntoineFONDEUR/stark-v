//! Debug utilities for printing trace data as formatted tables.
//!
//! Provides functions for converting trace data to readable table output using comfy-table.
//!
//! # Display Configuration
//!
//! Use [`set_display_options`] to configure max rows shown:
//! ```ignore
//! debug_utils::set_display_options(Some(100)); // Show max 100 rows
//! ```

pub use comfy_table::Table;
use comfy_table::{Cell, ContentArrangement};
use stwo::core::ColumnVec;
use stwo::core::fields::m31::{BaseField, M31, P};
use stwo::prover::backend::Column as StwoColumn;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::simd::m31::PackedM31;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;

use std::sync::atomic::{AtomicUsize, Ordering};

/// Global max rows setting (0 = unlimited)
static MAX_ROWS: AtomicUsize = AtomicUsize::new(0);

/// Half of the prime modulus, used for centering M31 values.
const HALF_P: i32 = (P / 2) as i32;

/// Set the maximum rows displayed when printing tables.
///
/// # Arguments
/// * `max_rows` - Maximum number of rows to display (None for unlimited)
/// * `_max_cols` - Ignored (kept for API compatibility, comfy-table handles column width automatically)
pub fn set_display_options(max_rows: Option<usize>, _max_cols: Option<usize>) {
    MAX_ROWS.store(max_rows.unwrap_or(0), Ordering::Relaxed);
}

/// Get the current max rows setting (0 = unlimited)
fn get_max_rows() -> usize {
    MAX_ROWS.load(Ordering::Relaxed)
}

/// Convert an M31 field element to a centered i32 in range (-P/2, P/2).
#[inline]
pub fn m31_to_centered_i32(m: M31) -> i32 {
    let v = m.0 as i32;
    if v > HALF_P { v - P as i32 } else { v }
}

/// Create a Table from parallel slices of u32 with column names.
///
/// This is a convenient helper for building tables from columnar trace data.
///
/// # Example
/// ```ignore
/// let table = slices_to_table(&[
///     ("clk", &clk_data[..]),
///     ("pc", &pc_data[..]),
/// ]);
/// println!("{table}");
/// ```
pub fn slices_to_table(columns: &[(&str, &[u32])]) -> Table {
    let mut table = Table::new();
    table.set_content_arrangement(ContentArrangement::Dynamic);

    if columns.is_empty() {
        return table;
    }

    // Set headers
    let headers: Vec<Cell> = columns.iter().map(|(name, _)| Cell::new(*name)).collect();
    table.set_header(headers);

    // Determine number of rows
    let num_rows = columns.first().map(|(_, data)| data.len()).unwrap_or(0);
    let max_rows = get_max_rows();
    let display_rows = if max_rows > 0 && num_rows > max_rows {
        max_rows
    } else {
        num_rows
    };

    // Add data rows
    for row_idx in 0..display_rows {
        let row: Vec<Cell> = columns
            .iter()
            .map(|(_, data)| Cell::new(data.get(row_idx).copied().unwrap_or(0)))
            .collect();
        table.add_row(row);
    }

    // Add truncation indicator if needed
    if max_rows > 0 && num_rows > max_rows {
        let truncated_row: Vec<Cell> = columns.iter().map(|_| Cell::new("...")).collect();
        table.add_row(truncated_row);
        // Add a footer row showing total
        let footer: Vec<Cell> = std::iter::once(Cell::new(format!("({num_rows} rows total)")))
            .chain(columns.iter().skip(1).map(|_| Cell::new("")))
            .collect();
        table.add_row(footer);
    }

    table
}

/// Trait for converting trace data to comfy-table Tables.
pub trait ToTable {
    /// Convert to a Table with auto-generated column names (col_0, col_1, ...).
    fn to_table(&self) -> Table;

    /// Convert to a Table with custom column names.
    /// If fewer names are provided than columns, remaining columns use auto-generated names.
    fn to_table_named(&self, names: &[&str]) -> Table;
}

// Helper to get column name
fn col_name(names: &[&str], idx: usize) -> String {
    names
        .get(idx)
        .map(|s| s.to_string())
        .unwrap_or_else(|| format!("col_{idx}"))
}

// =============================================================================
// Vec<Vec<u32>> - Multi-column Table
// =============================================================================

impl ToTable for Vec<Vec<u32>> {
    fn to_table(&self) -> Table {
        self.to_table_named(&[])
    }

    fn to_table_named(&self, names: &[&str]) -> Table {
        let mut table = Table::new();
        table.set_content_arrangement(ContentArrangement::Dynamic);

        if self.is_empty() {
            return table;
        }

        // Set headers
        let headers: Vec<Cell> = self
            .iter()
            .enumerate()
            .map(|(i, _)| Cell::new(col_name(names, i)))
            .collect();
        table.set_header(headers);

        // Determine number of rows
        let num_rows = self.first().map(|c| c.len()).unwrap_or(0);
        let max_rows = get_max_rows();
        let display_rows = if max_rows > 0 && num_rows > max_rows {
            max_rows
        } else {
            num_rows
        };

        // Add data rows
        for row_idx in 0..display_rows {
            let row: Vec<Cell> = self
                .iter()
                .map(|col| Cell::new(col.get(row_idx).copied().unwrap_or(0)))
                .collect();
            table.add_row(row);
        }

        // Add truncation indicator
        if max_rows > 0 && num_rows > max_rows {
            let truncated_row: Vec<Cell> = self.iter().map(|_| Cell::new("...")).collect();
            table.add_row(truncated_row);
        }

        table
    }
}

// =============================================================================
// Vec<Vec<M31>> - Multi-column Table with centered i32 values
// =============================================================================

impl ToTable for Vec<Vec<M31>> {
    fn to_table(&self) -> Table {
        self.to_table_named(&[])
    }

    fn to_table_named(&self, names: &[&str]) -> Table {
        let mut table = Table::new();
        table.set_content_arrangement(ContentArrangement::Dynamic);

        if self.is_empty() {
            return table;
        }

        // Set headers
        let headers: Vec<Cell> = self
            .iter()
            .enumerate()
            .map(|(i, _)| Cell::new(col_name(names, i)))
            .collect();
        table.set_header(headers);

        // Determine number of rows
        let num_rows = self.first().map(|c| c.len()).unwrap_or(0);
        let max_rows = get_max_rows();
        let display_rows = if max_rows > 0 && num_rows > max_rows {
            max_rows
        } else {
            num_rows
        };

        // Add data rows
        for row_idx in 0..display_rows {
            let row: Vec<Cell> = self
                .iter()
                .map(|col| {
                    let val = col
                        .get(row_idx)
                        .map(|&m| m31_to_centered_i32(m))
                        .unwrap_or(0);
                    Cell::new(val)
                })
                .collect();
            table.add_row(row);
        }

        // Add truncation indicator
        if max_rows > 0 && num_rows > max_rows {
            let truncated_row: Vec<Cell> = self.iter().map(|_| Cell::new("...")).collect();
            table.add_row(truncated_row);
        }

        table
    }
}

// =============================================================================
// Vec<u32> - Single column Table
// =============================================================================

impl ToTable for Vec<u32> {
    fn to_table(&self) -> Table {
        self.to_table_named(&[])
    }

    fn to_table_named(&self, names: &[&str]) -> Table {
        let mut table = Table::new();
        table.set_content_arrangement(ContentArrangement::Dynamic);

        let name = col_name(names, 0);
        table.set_header(vec![Cell::new(name)]);

        let max_rows = get_max_rows();
        let display_rows = if max_rows > 0 && self.len() > max_rows {
            max_rows
        } else {
            self.len()
        };

        for val in self.iter().take(display_rows) {
            table.add_row(vec![Cell::new(val)]);
        }

        if max_rows > 0 && self.len() > max_rows {
            table.add_row(vec![Cell::new("...")]);
        }

        table
    }
}

// =============================================================================
// Vec<M31> - Single column Table with centered i32 values
// =============================================================================

impl ToTable for Vec<M31> {
    fn to_table(&self) -> Table {
        self.to_table_named(&[])
    }

    fn to_table_named(&self, names: &[&str]) -> Table {
        let mut table = Table::new();
        table.set_content_arrangement(ContentArrangement::Dynamic);

        let name = col_name(names, 0);
        table.set_header(vec![Cell::new(name)]);

        let max_rows = get_max_rows();
        let display_rows = if max_rows > 0 && self.len() > max_rows {
            max_rows
        } else {
            self.len()
        };

        for m in self.iter().take(display_rows) {
            table.add_row(vec![Cell::new(m31_to_centered_i32(*m))]);
        }

        if max_rows > 0 && self.len() > max_rows {
            table.add_row(vec![Cell::new("...")]);
        }

        table
    }
}

// =============================================================================
// Vec<PackedM31> - Single column Table (flattened, centered i32)
// =============================================================================

impl ToTable for Vec<PackedM31> {
    fn to_table(&self) -> Table {
        self.to_table_named(&[])
    }

    fn to_table_named(&self, names: &[&str]) -> Table {
        let mut table = Table::new();
        table.set_content_arrangement(ContentArrangement::Dynamic);

        let name = col_name(names, 0);
        table.set_header(vec![Cell::new(name)]);

        let values: Vec<i32> = self
            .iter()
            .flat_map(|packed| packed.to_array())
            .map(m31_to_centered_i32)
            .collect();

        let max_rows = get_max_rows();
        let display_rows = if max_rows > 0 && values.len() > max_rows {
            max_rows
        } else {
            values.len()
        };

        for val in values.iter().take(display_rows) {
            table.add_row(vec![Cell::new(val)]);
        }

        if max_rows > 0 && values.len() > max_rows {
            table.add_row(vec![Cell::new("...")]);
        }

        table
    }
}

// =============================================================================
// Vec<Vec<PackedM31>> - Multi-column Table (each inner vec flattened)
// =============================================================================

impl ToTable for Vec<Vec<PackedM31>> {
    fn to_table(&self) -> Table {
        self.to_table_named(&[])
    }

    fn to_table_named(&self, names: &[&str]) -> Table {
        let mut table = Table::new();
        table.set_content_arrangement(ContentArrangement::Dynamic);

        if self.is_empty() {
            return table;
        }

        // Set headers
        let headers: Vec<Cell> = self
            .iter()
            .enumerate()
            .map(|(i, _)| Cell::new(col_name(names, i)))
            .collect();
        table.set_header(headers);

        // Flatten each column
        let flattened: Vec<Vec<i32>> = self
            .iter()
            .map(|col| {
                col.iter()
                    .flat_map(|packed| packed.to_array())
                    .map(m31_to_centered_i32)
                    .collect()
            })
            .collect();

        let num_rows = flattened.first().map(|c| c.len()).unwrap_or(0);
        let max_rows = get_max_rows();
        let display_rows = if max_rows > 0 && num_rows > max_rows {
            max_rows
        } else {
            num_rows
        };

        // Add data rows
        for row_idx in 0..display_rows {
            let row: Vec<Cell> = flattened
                .iter()
                .map(|col| Cell::new(col.get(row_idx).copied().unwrap_or(0)))
                .collect();
            table.add_row(row);
        }

        // Add truncation indicator
        if max_rows > 0 && num_rows > max_rows {
            let truncated_row: Vec<Cell> = flattened.iter().map(|_| Cell::new("...")).collect();
            table.add_row(truncated_row);
        }

        table
    }
}

// =============================================================================
// ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>
// =============================================================================

impl ToTable for ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    fn to_table(&self) -> Table {
        self.to_table_named(&[])
    }

    fn to_table_named(&self, names: &[&str]) -> Table {
        let mut table = Table::new();
        table.set_content_arrangement(ContentArrangement::Dynamic);

        if self.is_empty() {
            return table;
        }

        // Set headers
        let headers: Vec<Cell> = self
            .iter()
            .enumerate()
            .map(|(i, _)| Cell::new(col_name(names, i)))
            .collect();
        table.set_header(headers);

        // Convert to CPU and collect values
        let columns: Vec<Vec<i32>> = self
            .iter()
            .map(|eval| {
                eval.values
                    .to_cpu()
                    .iter()
                    .map(|&m| m31_to_centered_i32(m))
                    .collect()
            })
            .collect();

        let num_rows = columns.first().map(|c| c.len()).unwrap_or(0);
        let max_rows = get_max_rows();
        let display_rows = if max_rows > 0 && num_rows > max_rows {
            max_rows
        } else {
            num_rows
        };

        // Add data rows
        for row_idx in 0..display_rows {
            let row: Vec<Cell> = columns
                .iter()
                .map(|col| Cell::new(col.get(row_idx).copied().unwrap_or(0)))
                .collect();
            table.add_row(row);
        }

        // Add truncation indicator
        if max_rows > 0 && num_rows > max_rows {
            let truncated_row: Vec<Cell> = columns.iter().map(|_| Cell::new("...")).collect();
            table.add_row(truncated_row);
        }

        table
    }
}

// =============================================================================
// Vec<&[PackedM31]> - Multi-column Table from slices of PackedM31
// =============================================================================

impl ToTable for Vec<&[PackedM31]> {
    fn to_table(&self) -> Table {
        self.to_table_named(&[])
    }

    fn to_table_named(&self, names: &[&str]) -> Table {
        let mut table = Table::new();
        table.set_content_arrangement(ContentArrangement::Dynamic);

        if self.is_empty() {
            return table;
        }

        // Set headers
        let headers: Vec<Cell> = self
            .iter()
            .enumerate()
            .map(|(i, _)| Cell::new(col_name(names, i)))
            .collect();
        table.set_header(headers);

        // Flatten each column (each PackedM31 has 16 elements)
        let flattened: Vec<Vec<i32>> = self
            .iter()
            .map(|col| {
                col.iter()
                    .flat_map(|packed| packed.to_array())
                    .map(m31_to_centered_i32)
                    .collect()
            })
            .collect();

        let num_rows = flattened.first().map(|c| c.len()).unwrap_or(0);
        let max_rows = get_max_rows();
        let display_rows = if max_rows > 0 && num_rows > max_rows {
            max_rows
        } else {
            num_rows
        };

        // Add data rows
        for row_idx in 0..display_rows {
            let row: Vec<Cell> = flattened
                .iter()
                .map(|col| Cell::new(col.get(row_idx).copied().unwrap_or(0)))
                .collect();
            table.add_row(row);
        }

        // Add truncation indicator
        if max_rows > 0 && num_rows > max_rows {
            let truncated_row: Vec<Cell> = flattened.iter().map(|_| Cell::new("...")).collect();
            table.add_row(truncated_row);
        }

        table
    }
}

// =============================================================================
// Vec<PackedQM31> - 4 columns Table (one per QM31 limb), rows are flattened lanes
// =============================================================================

use stwo::prover::backend::simd::qm31::PackedQM31;

impl ToTable for Vec<PackedQM31> {
    fn to_table(&self) -> Table {
        self.to_table_named(&[])
    }

    fn to_table_named(&self, names: &[&str]) -> Table {
        let mut table = Table::new();
        table.set_content_arrangement(ContentArrangement::Dynamic);

        // QM31 has 4 limbs: (a, b, c, d) where QM31 = CM31(a,b) + CM31(c,d)*i
        let headers: Vec<Cell> = (0..4).map(|i| Cell::new(col_name(names, i))).collect();
        table.set_header(headers);

        // Flatten: each PackedQM31 has 16 lanes, each lane is a QM31 with 4 M31 components
        // Each row represents one QM31 value with its 4 limbs as columns
        let rows: Vec<[i32; 4]> = self
            .iter()
            .flat_map(|packed| {
                packed.to_array().map(|qm31| {
                    // QM31 = CM31(a, b) + CM31(c, d) * i
                    // qm31.0 = first CM31, qm31.1 = second CM31
                    // CM31.0 = first M31, CM31.1 = second M31
                    [
                        m31_to_centered_i32(qm31.0.0),
                        m31_to_centered_i32(qm31.0.1),
                        m31_to_centered_i32(qm31.1.0),
                        m31_to_centered_i32(qm31.1.1),
                    ]
                })
            })
            .collect();

        let max_rows = get_max_rows();
        let display_rows = if max_rows > 0 && rows.len() > max_rows {
            max_rows
        } else {
            rows.len()
        };

        for limbs in rows.iter().take(display_rows) {
            let row: Vec<Cell> = limbs.iter().map(Cell::new).collect();
            table.add_row(row);
        }

        if max_rows > 0 && rows.len() > max_rows {
            table.add_row(vec![
                Cell::new("..."),
                Cell::new("..."),
                Cell::new("..."),
                Cell::new("..."),
            ]);
        }

        table
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Mutex;

    // Mutex to serialize tests that modify global state
    static TEST_MUTEX: Mutex<()> = Mutex::new(());

    fn reset_display_options() {
        set_display_options(None, None);
    }

    #[test]
    fn test_vec_u32() {
        let _lock = TEST_MUTEX.lock().unwrap();
        reset_display_options();

        let data: Vec<u32> = vec![1, 2, 3, 4, 5];
        let table = data.to_table();
        let output = table.to_string();
        assert!(output.contains("col_0"));
        // Just verify the table is non-empty and contains data
        assert!(output.len() > 20);
    }

    #[test]
    fn test_vec_vec_u32() {
        let _lock = TEST_MUTEX.lock().unwrap();
        reset_display_options();

        let data: Vec<Vec<u32>> = vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]];
        let table = data.to_table_named(&["a", "b", "c"]);
        let output = table.to_string();
        assert!(output.contains("a"));
        assert!(output.contains("b"));
        assert!(output.contains("c"));
    }

    #[test]
    fn test_vec_m31_centered() {
        let _lock = TEST_MUTEX.lock().unwrap();
        reset_display_options();

        // Test that values > P/2 become negative
        let half_p_plus_1 = M31::from(HALF_P as u32 + 1);
        let data: Vec<M31> = vec![M31::from(0), M31::from(1), half_p_plus_1];
        let table = data.to_table_named(&["val"]);
        let output = table.to_string();
        assert!(output.contains("val"));
        // The third value should be negative (shown with minus sign)
        assert!(output.contains("-"));
    }

    #[test]
    fn test_vec_packed_m31() {
        let _lock = TEST_MUTEX.lock().unwrap();
        reset_display_options();

        // Create two PackedM31 (each with 16 lanes)
        let packed1 = PackedM31::from_array(std::array::from_fn(|i| M31::from(i as u32)));
        let packed2 = PackedM31::from_array(std::array::from_fn(|i| M31::from((i + 16) as u32)));
        let data: Vec<PackedM31> = vec![packed1, packed2];

        let table = data.to_table_named(&["vals"]);
        let output = table.to_string();

        // Should contain header
        assert!(output.contains("vals"));
        // Should have many rows (32 values)
        assert!(output.lines().count() > 30);
    }

    #[test]
    fn test_vec_vec_packed_m31() {
        let _lock = TEST_MUTEX.lock().unwrap();
        reset_display_options();

        // Create two columns, each with 2 PackedM31 (32 elements per column)
        let col1 = vec![
            PackedM31::from_array(std::array::from_fn(|i| M31::from(i as u32))),
            PackedM31::from_array(std::array::from_fn(|i| M31::from((i + 16) as u32))),
        ];
        let col2 = vec![
            PackedM31::from_array(std::array::from_fn(|i| M31::from((i + 100) as u32))),
            PackedM31::from_array(std::array::from_fn(|i| M31::from((i + 116) as u32))),
        ];
        let data: Vec<Vec<PackedM31>> = vec![col1, col2];

        let table = data.to_table_named(&["a", "b"]);
        let output = table.to_string();

        assert!(output.contains("a"));
        assert!(output.contains("b"));
        assert!(output.contains("100"));
    }

    #[test]
    fn test_column_vec_circle_evaluation() {
        let _lock = TEST_MUTEX.lock().unwrap();
        reset_display_options();

        use stwo::core::poly::circle::CanonicCoset;

        // Create a small domain (size 16 = 2^4)
        let log_size = 4u32;
        let domain = CanonicCoset::new(log_size).circle_domain();

        // Create two columns of evaluations
        let col1_values: Vec<M31> = (0..16).map(M31::from).collect();
        let col2_values: Vec<M31> = (100..116).map(M31::from).collect();

        let eval1 = CircleEvaluation::<SimdBackend, BaseField, BitReversedOrder>::new(
            domain,
            col1_values.into_iter().collect(),
        );
        let eval2 = CircleEvaluation::<SimdBackend, BaseField, BitReversedOrder>::new(
            domain,
            col2_values.into_iter().collect(),
        );

        let traces: ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> =
            vec![eval1, eval2];

        let table = traces.to_table_named(&["col_a", "col_b"]);
        let output = table.to_string();

        assert!(output.contains("col_a"));
        assert!(output.contains("col_b"));
    }

    #[test]
    fn test_slices_to_table() {
        let _lock = TEST_MUTEX.lock().unwrap();
        reset_display_options();

        let clk = [1u32, 2, 3];
        let pc = [0x1000u32, 0x1004, 0x1008];

        let table = slices_to_table(&[("clk", &clk[..]), ("pc", &pc[..])]);
        let output = table.to_string();

        assert!(output.contains("clk"));
        assert!(output.contains("pc"));
        assert!(output.contains("4096")); // 0x1000
    }

    #[test]
    fn test_max_rows_truncation() {
        let _lock = TEST_MUTEX.lock().unwrap();
        reset_display_options();

        // Set max rows to 3
        set_display_options(Some(3), None);

        let data: Vec<u32> = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        let table = data.to_table();
        let output = table.to_string();

        // Should show truncation indicator
        assert!(
            output.contains("..."),
            "Output should contain '...': {}",
            output
        );

        // Reset
        reset_display_options();
    }
}
