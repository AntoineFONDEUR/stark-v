//! Exact PCS column and query layout for recursion VM proofs.
//!
//! The VM AIR program determines every committed column, its commitment tree,
//! and its degree. This module checks the manifest's flat table list, tree
//! heights, sampled-value count, claimed-sum count, queried-value count, and
//! effective lifting bound against that generated program. The resulting
//! layout is the sole index map used by Merkle leaves and DEEP quotients, so a
//! proof cannot reinterpret one flat wire slot as a different tree or column.

use core::fmt;

use air::digest::M31Word;

use super::protocol::{
    FixedProofShape, ProofShapeError, ValidatedPcsParameters, ValidatedProofShape,
};
use super::vm_air_program::{VM_AIR_COMPONENT_COUNT, VmAirProgram};

/// Checked tree-major, column-major, query-major VM PCS geometry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VmPcsLayout {
    column_log_sizes: Vec<Vec<u32>>,
    tree_column_offsets: Vec<usize>,
    tree_heights: Vec<u32>,
    lifting_log_size: u32,
    n_queries: usize,
}

impl VmPcsLayout {
    pub fn new<const N_TABLES: usize, const N_TREES: usize, const N_FRI_LAYERS: usize>(
        program: &VmAirProgram,
        pcs: ValidatedPcsParameters,
        shape: &FixedProofShape<N_TABLES, N_TREES, N_FRI_LAYERS>,
    ) -> Result<Self, VmPcsLayoutError> {
        let validated_shape = shape.validate(pcs).map_err(VmPcsLayoutError::ProofShape)?;
        validate_program_counts(program, pcs, shape)?;

        let column_log_sizes = program.column_log_sizes().0.clone();
        if column_log_sizes.len() != N_TREES {
            return Err(VmPcsLayoutError::TreeCountMismatch {
                expected: column_log_sizes.len(),
                actual: N_TREES,
            });
        }
        let tree_column_offsets = tree_column_offsets(&column_log_sizes)?;
        let total_columns = *tree_column_offsets
            .last()
            .expect("tree offsets include the terminal column count");
        if total_columns != N_TABLES {
            return Err(VmPcsLayoutError::ColumnCountMismatch {
                expected: total_columns,
                actual: N_TABLES,
            });
        }
        for (table, (expected, actual)) in column_log_sizes
            .iter()
            .flatten()
            .copied()
            .zip(shape.table_log_sizes)
            .enumerate()
        {
            if expected != actual.as_u32() {
                return Err(VmPcsLayoutError::TableLogSizeMismatch {
                    table,
                    expected,
                    actual: actual.as_u32(),
                });
            }
        }

        let tree_heights = expected_tree_heights(&column_log_sizes, pcs)?;
        for (tree, (expected, actual)) in tree_heights
            .iter()
            .copied()
            .zip(shape.tree_heights)
            .enumerate()
        {
            if expected != actual.as_u32() {
                return Err(VmPcsLayoutError::TreeHeightMismatch {
                    tree,
                    expected,
                    actual: actual.as_u32(),
                });
            }
        }
        validate_effective_degree(program, pcs, validated_shape)?;

        Ok(Self {
            column_log_sizes,
            tree_column_offsets,
            tree_heights,
            lifting_log_size: validated_shape.lifting_log_size(),
            n_queries: pcs.config().fri_config.n_queries,
        })
    }

    pub fn column_log_sizes(&self) -> &[Vec<u32>] {
        &self.column_log_sizes
    }

    pub fn tree_heights(&self) -> &[u32] {
        &self.tree_heights
    }

    pub const fn lifting_log_size(&self) -> u32 {
        self.lifting_log_size
    }

    pub const fn n_queries(&self) -> usize {
        self.n_queries
    }

    pub fn total_column_count(&self) -> usize {
        *self
            .tree_column_offsets
            .last()
            .expect("tree offsets include the terminal column count")
    }

    pub fn queried_value_count(&self) -> Result<usize, VmPcsLayoutError> {
        self.total_column_count().checked_mul(self.n_queries).ok_or(
            VmPcsLayoutError::ArithmeticOverflow {
                field: "queried value count",
            },
        )
    }

    /// Returns the canonical flat wire index for one authenticated trace value.
    pub fn queried_value_index(
        &self,
        tree: usize,
        column: usize,
        query: usize,
    ) -> Result<usize, VmPcsLayoutError> {
        let columns = self
            .column_log_sizes
            .get(tree)
            .ok_or(VmPcsLayoutError::TreeIndexOutOfRange { tree })?;
        if column >= columns.len() {
            return Err(VmPcsLayoutError::ColumnIndexOutOfRange {
                tree,
                column,
                column_count: columns.len(),
            });
        }
        if query >= self.n_queries {
            return Err(VmPcsLayoutError::QueryIndexOutOfRange {
                query,
                query_count: self.n_queries,
            });
        }
        self.tree_column_offsets[tree]
            .checked_add(column)
            .and_then(|column| column.checked_mul(self.n_queries))
            .and_then(|base| base.checked_add(query))
            .ok_or(VmPcsLayoutError::ArithmeticOverflow {
                field: "queried value index",
            })
    }
}

fn validate_program_counts<
    const N_TABLES: usize,
    const N_TREES: usize,
    const N_FRI_LAYERS: usize,
>(
    program: &VmAirProgram,
    pcs: ValidatedPcsParameters,
    shape: &FixedProofShape<N_TABLES, N_TREES, N_FRI_LAYERS>,
) -> Result<(), VmPcsLayoutError> {
    validate_count(
        "claimed sums",
        VM_AIR_COMPONENT_COUNT,
        shape.claimed_sum_count,
    )?;
    validate_count(
        "sampled values",
        program.sample_coordinates().len(),
        shape.sampled_value_count,
    )?;
    let total_columns = program
        .column_log_sizes()
        .iter()
        .try_fold(0_usize, |total, columns| total.checked_add(columns.len()))
        .ok_or(VmPcsLayoutError::ArithmeticOverflow {
            field: "VM column count",
        })?;
    let expected_queried_values = total_columns
        .checked_mul(pcs.config().fri_config.n_queries)
        .ok_or(VmPcsLayoutError::ArithmeticOverflow {
            field: "queried value count",
        })?;
    validate_count(
        "queried values",
        expected_queried_values,
        shape.queried_value_count,
    )
}

fn validate_count(
    field: &'static str,
    expected: usize,
    actual: M31Word,
) -> Result<(), VmPcsLayoutError> {
    let actual =
        usize::try_from(actual.as_u32()).map_err(|_| VmPcsLayoutError::CountDoesNotFitUsize {
            field,
            actual: actual.as_u32(),
        })?;
    if expected == actual {
        Ok(())
    } else {
        Err(VmPcsLayoutError::CountMismatch {
            field,
            expected,
            actual,
        })
    }
}

fn tree_column_offsets(column_log_sizes: &[Vec<u32>]) -> Result<Vec<usize>, VmPcsLayoutError> {
    let mut offsets = Vec::with_capacity(column_log_sizes.len() + 1);
    offsets.push(0_usize);
    for columns in column_log_sizes {
        let next = offsets
            .last()
            .copied()
            .expect("offsets start at zero")
            .checked_add(columns.len())
            .ok_or(VmPcsLayoutError::ArithmeticOverflow {
                field: "tree column offsets",
            })?;
        offsets.push(next);
    }
    Ok(offsets)
}

fn expected_tree_heights(
    column_log_sizes: &[Vec<u32>],
    pcs: ValidatedPcsParameters,
) -> Result<Vec<u32>, VmPcsLayoutError> {
    let config = pcs.config();
    column_log_sizes
        .iter()
        .enumerate()
        .map(|(tree, columns)| {
            let largest = columns
                .iter()
                .copied()
                .max()
                .ok_or(VmPcsLayoutError::EmptyCommitmentTree { tree })?;
            let natural = largest
                .checked_add(config.fri_config.log_blowup_factor)
                .ok_or(VmPcsLayoutError::ArithmeticOverflow {
                    field: "extended column log size",
                })?;
            if let Some(lifting) = config.lifting_log_size {
                if natural > lifting {
                    return Err(VmPcsLayoutError::TreeExceedsLiftingDomain {
                        tree,
                        natural,
                        lifting,
                    });
                }
                Ok(lifting)
            } else {
                Ok(natural)
            }
        })
        .collect()
}

fn validate_effective_degree(
    program: &VmAirProgram,
    pcs: ValidatedPcsParameters,
    shape: ValidatedProofShape,
) -> Result<(), VmPcsLayoutError> {
    let expected = shape
        .lifting_log_size()
        .checked_sub(pcs.config().fri_config.log_blowup_factor)
        .ok_or(VmPcsLayoutError::ArithmeticOverflow {
            field: "effective maximum degree",
        })?;
    let actual = program.max_log_degree_bound();
    if expected == actual {
        Ok(())
    } else {
        Err(VmPcsLayoutError::MaxLogDegreeBoundMismatch { expected, actual })
    }
}

/// VM AIR program and manifest geometry disagree.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VmPcsLayoutError {
    ProofShape(ProofShapeError),
    TreeCountMismatch {
        expected: usize,
        actual: usize,
    },
    ColumnCountMismatch {
        expected: usize,
        actual: usize,
    },
    TableLogSizeMismatch {
        table: usize,
        expected: u32,
        actual: u32,
    },
    TreeHeightMismatch {
        tree: usize,
        expected: u32,
        actual: u32,
    },
    CountDoesNotFitUsize {
        field: &'static str,
        actual: u32,
    },
    CountMismatch {
        field: &'static str,
        expected: usize,
        actual: usize,
    },
    EmptyCommitmentTree {
        tree: usize,
    },
    TreeExceedsLiftingDomain {
        tree: usize,
        natural: u32,
        lifting: u32,
    },
    MaxLogDegreeBoundMismatch {
        expected: u32,
        actual: u32,
    },
    TreeIndexOutOfRange {
        tree: usize,
    },
    ColumnIndexOutOfRange {
        tree: usize,
        column: usize,
        column_count: usize,
    },
    QueryIndexOutOfRange {
        query: usize,
        query_count: usize,
    },
    ArithmeticOverflow {
        field: &'static str,
    },
}

impl fmt::Display for VmPcsLayoutError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for VmPcsLayoutError {}

#[cfg(test)]
mod tests {
    use prover::components::{COMPONENT_COUNT, COMPONENT_NAMES};

    use super::*;
    use crate::pcs_deep_circuit::{PcsDeepProfile, build_pcs_deep_reference};
    use crate::protocol::{OptionalM31Word, PcsParameters};

    const VM_COLUMN_COUNT: usize = 1_757;
    const TREE_COUNT: usize = 4;
    const FRI_LAYER_COUNT: usize = 5;
    const QUERY_COUNT: usize = 2;

    fn component_log_sizes() -> [u32; COMPONENT_COUNT] {
        core::array::from_fn(|index| match COMPONENT_NAMES[index] {
            "bitwise" => 18,
            "range_check_20" | "range_check_8_8_4" => 20,
            "range_check_8_11" => 19,
            "range_check_8_8" => 16,
            "range_check_m31" => 15,
            _ => 6,
        })
    }

    fn pcs() -> ValidatedPcsParameters {
        PcsParameters {
            interaction_pow_bits: M31Word::ZERO,
            pow_bits: M31Word::ZERO,
            fri_log_blowup_factor: M31Word::from(1_u16),
            fri_n_queries: M31Word::from(QUERY_COUNT as u16),
            fri_log_last_layer_degree_bound: M31Word::ZERO,
            fri_fold_step: M31Word::from(4_u16),
            lifting_log_size: OptionalM31Word::None,
        }
        .validate()
        .expect("fixture PCS parameters are valid")
    }

    fn shape(
        program: &VmAirProgram,
    ) -> FixedProofShape<VM_COLUMN_COUNT, TREE_COUNT, FRI_LAYER_COUNT> {
        let word = |value: usize| {
            M31Word::try_from(u32::try_from(value).expect("fixture count fits u32"))
                .expect("fixture count is canonical")
        };
        let table_log_sizes = program
            .column_log_sizes()
            .iter()
            .flatten()
            .copied()
            .map(M31Word::try_from)
            .collect::<Result<Vec<_>, _>>()
            .expect("fixture table log sizes are canonical");
        FixedProofShape {
            claimed_sum_count: word(VM_AIR_COMPONENT_COUNT),
            sampled_value_count: word(program.sample_coordinates().len()),
            queried_value_count: word(VM_COLUMN_COUNT * QUERY_COUNT),
            trace_path_count: word(TREE_COUNT * QUERY_COUNT),
            raw_query_count: word(QUERY_COUNT),
            last_layer_coefficient_count: M31Word::from(1_u16),
            table_log_sizes: table_log_sizes
                .try_into()
                .expect("fixture VM column count stays stable"),
            tree_heights: [M31Word::from(21_u16); TREE_COUNT],
            fri_layer_fold_widths: [M31Word::from(16_u16); FRI_LAYER_COUNT],
            fri_layer_tree_heights: [19_u16, 15, 11, 7, 3].map(M31Word::from),
        }
    }

    fn layout() -> VmPcsLayout {
        let program = VmAirProgram::new(component_log_sizes()).expect("fixture program is valid");
        VmPcsLayout::new(&program, pcs(), &shape(&program))
            .expect("generated program and manifest layout agree")
    }

    #[test]
    fn generated_vm_layout_matches_the_complete_manifest_geometry() {
        let layout = layout();
        assert_eq!(
            (
                layout.column_log_sizes().len(),
                layout.total_column_count(),
                layout.queried_value_count().unwrap(),
                layout.tree_heights(),
                layout.lifting_log_size(),
            ),
            (
                TREE_COUNT,
                VM_COLUMN_COUNT,
                VM_COLUMN_COUNT * QUERY_COUNT,
                &[21_u32; TREE_COUNT][..],
                21_u32,
            )
        );
    }

    #[test]
    fn queried_value_indices_are_tree_column_query_major() {
        let layout = layout();
        let last_tree = TREE_COUNT - 1;
        let last_column = layout.column_log_sizes()[last_tree].len() - 1;
        assert_eq!(
            layout.queried_value_index(last_tree, last_column, QUERY_COUNT - 1),
            Ok(VM_COLUMN_COUNT * QUERY_COUNT - 1)
        );
    }

    #[test]
    fn generated_vm_deep_profile_uses_the_complete_air_sample_layout() {
        let program = VmAirProgram::new(component_log_sizes()).expect("fixture program is valid");
        let layout = VmPcsLayout::new(&program, pcs(), &shape(&program))
            .expect("generated program and manifest layout agree");
        let profile = PcsDeepProfile::from_vm(&program, &layout)
            .expect("generated sample offsets define the DEEP profile");
        let reference = build_pcs_deep_reference(&profile)
            .expect("production VM DEEP reference has valid fixed denominators");
        assert_eq!(
            (
                profile.sample_count(),
                profile.column_count(),
                profile.lifting_log_size(),
                profile.query_count(),
                reference.nonzero_output_count(),
            ),
            (
                program.sample_coordinates().len(),
                VM_COLUMN_COUNT,
                layout.lifting_log_size(),
                QUERY_COUNT,
                0,
            )
        );
    }

    #[test]
    fn one_table_degree_substitution_is_rejected() {
        let program = VmAirProgram::new(component_log_sizes()).expect("fixture program is valid");
        let mut shape = shape(&program);
        shape.table_log_sizes[0] =
            M31Word::try_from(shape.table_log_sizes[0].as_u32() - 1).unwrap();
        assert!(matches!(
            VmPcsLayout::new(&program, pcs(), &shape),
            Err(VmPcsLayoutError::TableLogSizeMismatch { table: 0, .. })
        ));
    }

    #[test]
    fn unsplit_composition_degree_is_rejected_by_the_real_pcs_geometry() {
        let baseline = VmAirProgram::new(component_log_sizes()).expect("fixture program is valid");
        let unsplit = VmAirProgram::new_with_max_log_degree_bound(
            component_log_sizes(),
            baseline.max_log_degree_bound() + 1,
        )
        .expect("the explicit bound is internally representable");
        assert_eq!(
            VmPcsLayout::new(&unsplit, pcs(), &shape(&baseline)),
            Err(VmPcsLayoutError::TableLogSizeMismatch {
                table: VM_COLUMN_COUNT - 8,
                expected: baseline.max_log_degree_bound() + 1,
                actual: baseline.max_log_degree_bound(),
            })
        );
    }
}
