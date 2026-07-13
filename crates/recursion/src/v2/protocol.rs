//! Canonical protocol manifest for recursion version 2.
//!
//! The manifest contains every verifier-owned value that changes transcript
//! replay or fixed proof parsing. Its encoding uses canonical M31 words and
//! explicit field tags, so two roles cannot share an accidental byte layout.
//! This module defines the format only; it does not select production roots,
//! proof dimensions, or a verifier implementation.

use core::fmt;

use air::digest::{
    HashSuiteDigest, M31Word, ProtocolId, RecursionAirProgramDigest, RecursionPreprocessingDigest,
    VmAirProgramDigest, VmPreprocessingDigest,
};
use prover::poseidon2_channel::poseidon2_hash_m31_words;
use stwo::core::fri::FriConfig;
use stwo::core::pcs::PcsConfig;
use stwo::core::poly::circle::{MAX_CIRCLE_DOMAIN_LOG_SIZE, MIN_CIRCLE_DOMAIN_LOG_SIZE};
use stwo::core::vcs_lifted::verifier::LOG_PACKED_LEAF_SIZE;

const PROTOCOL_MANIFEST_HASH_DOMAIN: u16 = 0x5632;
const MAX_POW_BITS: u32 = 31;
const MIN_FRI_LOG_BLOWUP: u32 = 1;
const MAX_FRI_LOG_BLOWUP: u32 = 16;
const MAX_FRI_LAST_LAYER_LOG_DEGREE: u32 = 10;
const MAX_FRI_FOLD_STEP: u32 = 4;
const MAX_FRI_QUERIES: u32 = 256;

/// Version of the recursion protocol statement and manifest encoding.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
#[repr(transparent)]
pub struct ProtocolVersion(pub M31Word);

impl ProtocolVersion {
    /// Returns the canonical version word used by the wire and transcript.
    pub const fn word(self) -> M31Word {
        self.0
    }
}

/// An optional PCS parameter with one canonical two-word representation.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum OptionalM31Word {
    None,
    Some(M31Word),
}

/// All parameters read by STWO's commitment-scheme transcript.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct PcsParameters {
    pub interaction_pow_bits: M31Word,
    pub pow_bits: M31Word,
    pub fri_log_blowup_factor: M31Word,
    pub fri_n_queries: M31Word,
    pub fri_log_last_layer_degree_bound: M31Word,
    pub fri_fold_step: M31Word,
    pub lifting_log_size: OptionalM31Word,
}

impl PcsParameters {
    /// Checks every value before calling STWO constructors that otherwise panic.
    pub fn validate(self) -> Result<ValidatedPcsParameters, PcsParameterError> {
        let interaction_pow_bits = self.interaction_pow_bits.as_u32();
        if interaction_pow_bits > MAX_POW_BITS {
            return Err(PcsParameterError::InteractionPowBitsOutOfRange {
                value: interaction_pow_bits,
            });
        }
        let pow_bits = self.pow_bits.as_u32();
        if pow_bits > MAX_POW_BITS {
            return Err(PcsParameterError::PcsPowBitsOutOfRange { value: pow_bits });
        }
        let log_blowup_factor = self.fri_log_blowup_factor.as_u32();
        if !(MIN_FRI_LOG_BLOWUP..=MAX_FRI_LOG_BLOWUP).contains(&log_blowup_factor) {
            return Err(PcsParameterError::FriLogBlowupOutOfRange {
                value: log_blowup_factor,
            });
        }
        let n_queries_word = self.fri_n_queries.as_u32();
        if n_queries_word == 0 {
            return Err(PcsParameterError::ZeroFriQueries);
        }
        if n_queries_word > MAX_FRI_QUERIES {
            return Err(PcsParameterError::FriQueryCountOutOfRange {
                value: n_queries_word,
            });
        }
        let n_queries = usize::try_from(n_queries_word).map_err(|_| {
            PcsParameterError::FriQueryCountOutOfRange {
                value: n_queries_word,
            }
        })?;
        let log_last_layer_degree_bound = self.fri_log_last_layer_degree_bound.as_u32();
        if log_last_layer_degree_bound > MAX_FRI_LAST_LAYER_LOG_DEGREE {
            return Err(PcsParameterError::FriLastLayerLogDegreeOutOfRange {
                value: log_last_layer_degree_bound,
            });
        }
        let fold_step = self.fri_fold_step.as_u32();
        if !(1..=MAX_FRI_FOLD_STEP).contains(&fold_step) {
            return Err(PcsParameterError::FriFoldStepOutOfRange { value: fold_step });
        }
        let lifting_log_size = match self.lifting_log_size {
            OptionalM31Word::None => None,
            OptionalM31Word::Some(value) => {
                let value = value.as_u32();
                if !(MIN_CIRCLE_DOMAIN_LOG_SIZE..=MAX_CIRCLE_DOMAIN_LOG_SIZE).contains(&value) {
                    return Err(PcsParameterError::LiftingLogSizeOutOfRange { value });
                }
                Some(value)
            }
        };

        let fri_config = FriConfig::new(
            log_last_layer_degree_bound,
            log_blowup_factor,
            n_queries,
            fold_step,
        );
        Ok(ValidatedPcsParameters {
            interaction_pow_bits,
            config: PcsConfig {
                pow_bits,
                fri_config,
                lifting_log_size,
            },
        })
    }
}

/// PCS values safe to use in STWO and the fixed verifier plan.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ValidatedPcsParameters {
    interaction_pow_bits: u32,
    config: PcsConfig,
}

impl ValidatedPcsParameters {
    pub const fn interaction_pow_bits(self) -> u32 {
        self.interaction_pow_bits
    }

    pub const fn config(self) -> PcsConfig {
        self.config
    }
}

/// Counts and per-tree/per-layer sizes that make one proof wire shape fixed.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct FixedProofShape<const N_TABLES: usize, const N_TREES: usize, const N_FRI_LAYERS: usize> {
    pub claimed_sum_count: M31Word,
    pub sampled_value_count: M31Word,
    pub queried_value_count: M31Word,
    pub trace_path_count: M31Word,
    pub raw_query_count: M31Word,
    pub last_layer_coefficient_count: M31Word,
    pub table_log_sizes: [M31Word; N_TABLES],
    pub tree_heights: [M31Word; N_TREES],
    pub fri_layer_fold_widths: [M31Word; N_FRI_LAYERS],
    pub fri_layer_tree_heights: [M31Word; N_FRI_LAYERS],
}

impl<const N_TABLES: usize, const N_TREES: usize, const N_FRI_LAYERS: usize>
    FixedProofShape<N_TABLES, N_TREES, N_FRI_LAYERS>
{
    /// Validates the exact fixed wire geometry implied by one PCS profile.
    pub fn validate(
        &self,
        pcs: ValidatedPcsParameters,
    ) -> Result<ValidatedProofShape, ProofShapeError> {
        if N_TABLES == 0 {
            return Err(ProofShapeError::EmptyTableLayout);
        }
        if N_TREES == 0 {
            return Err(ProofShapeError::EmptyTreeLayout);
        }
        validate_nonzero_shape_count("claimed sums", self.claimed_sum_count)?;
        validate_nonzero_shape_count("sampled values", self.sampled_value_count)?;
        validate_nonzero_shape_count("queried values", self.queried_value_count)?;

        let config = pcs.config();
        let n_queries = config.fri_config.n_queries;
        validate_shape_count("raw queries", n_queries, self.raw_query_count)?;
        let expected_trace_paths =
            N_TREES
                .checked_mul(n_queries)
                .ok_or(ProofShapeError::ArithmeticOverflow {
                    field: "trace path count",
                })?;
        validate_shape_count("trace paths", expected_trace_paths, self.trace_path_count)?;

        let queried_value_count = shape_word_as_usize("queried values", self.queried_value_count)?;
        if !queried_value_count.is_multiple_of(n_queries) {
            return Err(ProofShapeError::QueriedValuesNotPerRawQuery {
                queried_values: queried_value_count,
                raw_queries: n_queries,
            });
        }

        for (table, log_size) in self.table_log_sizes.iter().enumerate() {
            validate_log_size("table", table, log_size.as_u32(), false)?;
        }
        for (tree, height) in self.tree_heights.iter().enumerate() {
            validate_log_size("tree", tree, height.as_u32(), true)?;
        }

        let described_lifting_log_size = self
            .tree_heights
            .iter()
            .map(|height| height.as_u32())
            .max()
            .ok_or(ProofShapeError::EmptyTreeLayout)?;
        let lifting_log_size = config
            .lifting_log_size
            .unwrap_or(described_lifting_log_size);
        validate_log_size("lifting", 0, lifting_log_size, false)?;
        if config.lifting_log_size.is_some() {
            for (tree, actual) in self.tree_heights.iter().enumerate() {
                if actual.as_u32() != lifting_log_size {
                    return Err(ProofShapeError::TreeHeightMismatch {
                        tree,
                        expected: lifting_log_size,
                        actual: actual.as_u32(),
                    });
                }
            }
        }

        let log_blowup_factor = config.fri_config.log_blowup_factor;
        for (table, log_size) in self.table_log_sizes.iter().enumerate() {
            let committed_log_size = log_size.as_u32().checked_add(log_blowup_factor).ok_or(
                ProofShapeError::ArithmeticOverflow {
                    field: "committed table log size",
                },
            )?;
            if committed_log_size > lifting_log_size {
                return Err(ProofShapeError::TableExceedsLiftingDomain {
                    table,
                    table_log_size: log_size.as_u32(),
                    log_blowup_factor,
                    lifting_log_size,
                });
            }
        }

        let last_layer_log_degree = config.fri_config.log_last_layer_degree_bound;
        let fold_step = config.fri_config.fold_step;
        let invalid_fri_range = |column_log_degree| ProofShapeError::InvalidFriDegreeRange {
            column_log_degree,
            last_layer_log_degree,
            fold_step,
        };
        let column_log_degree = lifting_log_size
            .checked_sub(log_blowup_factor)
            .ok_or_else(|| invalid_fri_range(0))?;
        let folds = column_log_degree
            .checked_sub(last_layer_log_degree)
            .ok_or_else(|| invalid_fri_range(column_log_degree))?;
        if folds < fold_step {
            return Err(invalid_fri_range(column_log_degree));
        }
        let expected_fri_layers = folds.div_ceil(fold_step) as usize;
        if N_FRI_LAYERS != expected_fri_layers {
            return Err(ProofShapeError::FriLayerCountMismatch {
                expected: expected_fri_layers,
                actual: N_FRI_LAYERS,
            });
        }

        let expected_last_layer_coefficients = 1_usize.checked_shl(last_layer_log_degree).ok_or(
            ProofShapeError::ArithmeticOverflow {
                field: "last-layer coefficient count",
            },
        )?;
        validate_shape_count(
            "last-layer coefficients",
            expected_last_layer_coefficients,
            self.last_layer_coefficient_count,
        )?;

        let mut remaining_folds = folds;
        let mut layer_domain_log_size = lifting_log_size;
        for layer in 0..N_FRI_LAYERS {
            let layer_fold_step = remaining_folds.min(fold_step);
            let expected_width =
                1_u32
                    .checked_shl(layer_fold_step)
                    .ok_or(ProofShapeError::ArithmeticOverflow {
                        field: "FRI fold width",
                    })?;
            let actual_width = self.fri_layer_fold_widths[layer].as_u32();
            if actual_width != expected_width {
                return Err(ProofShapeError::FriFoldWidthMismatch {
                    layer,
                    expected: expected_width,
                    actual: actual_width,
                });
            }

            let packed_leaf_log_size =
                if layer_fold_step > 1 && layer_domain_log_size >= LOG_PACKED_LEAF_SIZE {
                    LOG_PACKED_LEAF_SIZE
                } else {
                    0
                };
            let expected_tree_height = layer_domain_log_size - packed_leaf_log_size;
            let actual_tree_height = self.fri_layer_tree_heights[layer].as_u32();
            if actual_tree_height != expected_tree_height {
                return Err(ProofShapeError::FriTreeHeightMismatch {
                    layer,
                    expected: expected_tree_height,
                    actual: actual_tree_height,
                });
            }
            layer_domain_log_size -= layer_fold_step;
            remaining_folds -= layer_fold_step;
        }

        Ok(ValidatedProofShape {
            lifting_log_size,
            column_log_degree,
        })
    }
}

/// Domain facts derived only after a proof shape and PCS profile agree.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ValidatedProofShape {
    lifting_log_size: u32,
    column_log_degree: u32,
}

impl ValidatedProofShape {
    pub const fn lifting_log_size(self) -> u32 {
        self.lifting_log_size
    }

    pub const fn column_log_degree(self) -> u32 {
        self.column_log_degree
    }
}

/// Verifier-owned inputs that identify one VM and recursion proof protocol.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct ProtocolManifest<
    const VM_TABLES: usize,
    const VM_TREES: usize,
    const VM_FRI_LAYERS: usize,
    const RECURSION_TABLES: usize,
    const RECURSION_TREES: usize,
    const RECURSION_FRI_LAYERS: usize,
> {
    pub version: ProtocolVersion,
    pub hash_suite: HashSuiteDigest,
    pub vm_preprocessing: VmPreprocessingDigest,
    pub recursion_preprocessing: RecursionPreprocessingDigest,
    pub vm_air_program: VmAirProgramDigest,
    pub recursion_air_program: RecursionAirProgramDigest,
    pub vm_pcs: PcsParameters,
    pub recursion_pcs: PcsParameters,
    pub vm_proof_shape: FixedProofShape<VM_TABLES, VM_TREES, VM_FRI_LAYERS>,
    pub recursion_proof_shape:
        FixedProofShape<RECURSION_TABLES, RECURSION_TREES, RECURSION_FRI_LAYERS>,
}

impl<
    const VM_TABLES: usize,
    const VM_TREES: usize,
    const VM_FRI_LAYERS: usize,
    const RECURSION_TABLES: usize,
    const RECURSION_TREES: usize,
    const RECURSION_FRI_LAYERS: usize,
>
    ProtocolManifest<
        VM_TABLES,
        VM_TREES,
        VM_FRI_LAYERS,
        RECURSION_TABLES,
        RECURSION_TREES,
        RECURSION_FRI_LAYERS,
    >
{
    /// Commits the complete tagged manifest under the V2 identity domain.
    pub fn protocol_id(&self) -> ProtocolId {
        ProtocolId::from(poseidon2_hash_m31_words(
            &self.canonical_words(),
            M31Word::from(PROTOCOL_MANIFEST_HASH_DOMAIN),
        ))
    }

    /// Validates both proof systems before the manifest enters a verifier key.
    pub fn validate(
        self,
    ) -> Result<
        ValidatedProtocolManifest<
            VM_TABLES,
            VM_TREES,
            VM_FRI_LAYERS,
            RECURSION_TABLES,
            RECURSION_TREES,
            RECURSION_FRI_LAYERS,
        >,
        ProtocolManifestError,
    > {
        let vm_pcs = self
            .vm_pcs
            .validate()
            .map_err(ProtocolManifestError::VmPcs)?;
        let recursion_pcs = self
            .recursion_pcs
            .validate()
            .map_err(ProtocolManifestError::RecursionPcs)?;
        let vm_shape = self
            .vm_proof_shape
            .validate(vm_pcs)
            .map_err(ProtocolManifestError::VmShape)?;
        let recursion_shape = self
            .recursion_proof_shape
            .validate(recursion_pcs)
            .map_err(ProtocolManifestError::RecursionShape)?;
        let protocol_id = self.protocol_id();
        Ok(ValidatedProtocolManifest {
            manifest: self,
            protocol_id,
            vm_pcs,
            recursion_pcs,
            vm_shape,
            recursion_shape,
        })
    }
}

/// A manifest whose PCS constructors and fixed FRI layouts cannot panic.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ValidatedProtocolManifest<
    const VM_TABLES: usize,
    const VM_TREES: usize,
    const VM_FRI_LAYERS: usize,
    const RECURSION_TABLES: usize,
    const RECURSION_TREES: usize,
    const RECURSION_FRI_LAYERS: usize,
> {
    manifest: ProtocolManifest<
        VM_TABLES,
        VM_TREES,
        VM_FRI_LAYERS,
        RECURSION_TABLES,
        RECURSION_TREES,
        RECURSION_FRI_LAYERS,
    >,
    protocol_id: ProtocolId,
    vm_pcs: ValidatedPcsParameters,
    recursion_pcs: ValidatedPcsParameters,
    vm_shape: ValidatedProofShape,
    recursion_shape: ValidatedProofShape,
}

impl<
    const VM_TABLES: usize,
    const VM_TREES: usize,
    const VM_FRI_LAYERS: usize,
    const RECURSION_TABLES: usize,
    const RECURSION_TREES: usize,
    const RECURSION_FRI_LAYERS: usize,
>
    ValidatedProtocolManifest<
        VM_TABLES,
        VM_TREES,
        VM_FRI_LAYERS,
        RECURSION_TABLES,
        RECURSION_TREES,
        RECURSION_FRI_LAYERS,
    >
{
    pub const fn manifest(
        &self,
    ) -> &ProtocolManifest<
        VM_TABLES,
        VM_TREES,
        VM_FRI_LAYERS,
        RECURSION_TABLES,
        RECURSION_TREES,
        RECURSION_FRI_LAYERS,
    > {
        &self.manifest
    }

    pub const fn protocol_id(&self) -> ProtocolId {
        self.protocol_id
    }

    pub const fn vm_pcs(&self) -> ValidatedPcsParameters {
        self.vm_pcs
    }

    pub const fn recursion_pcs(&self) -> ValidatedPcsParameters {
        self.recursion_pcs
    }

    pub const fn vm_shape(&self) -> ValidatedProofShape {
        self.vm_shape
    }

    pub const fn recursion_shape(&self) -> ValidatedProofShape {
        self.recursion_shape
    }
}

/// Tags in the canonical word encoding.
///
/// Tags bind identical digest or numeric values to their semantic position.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
#[repr(u16)]
pub enum CanonicalTag {
    Manifest = 1,
    Version = 2,
    HashSuite = 3,
    VmPreprocessing = 4,
    RecursionPreprocessing = 5,
    VmAirProgram = 6,
    RecursionAirProgram = 7,
    VmPcs = 8,
    RecursionPcs = 9,
    VmProofShape = 10,
    RecursionProofShape = 11,
    Pcs = 20,
    InteractionPowBits = 21,
    PowBits = 22,
    FriLogBlowupFactor = 23,
    FriNQueries = 24,
    FriLogLastLayerDegreeBound = 25,
    FriFoldStep = 26,
    LiftingLogSize = 27,
    ProofShape = 40,
    CommitmentCount = 41,
    ClaimedSumCount = 42,
    SampledValueCount = 43,
    QueriedValueCount = 44,
    TracePathCount = 45,
    RawQueryCount = 46,
    FriLayerCount = 47,
    LastLayerCoefficientCount = 48,
    TableLogSizes = 49,
    TreeHeights = 50,
    FriLayerFoldWidths = 51,
    FriLayerTreeHeights = 52,
    SpanStatement = 60,
    JobContext = 61,
    CompleteExecution = 62,
    MachineState = 63,
    SlotSpan = 64,
    EmptyBody = 65,
    ExecutedBody = 66,
    ExecutedSpan = 67,
    AbsentEdge = 68,
    PresentEdge = 69,
}

impl CanonicalTag {
    /// Returns the tag as a canonical transcript word.
    pub fn word(self) -> M31Word {
        M31Word::from(self as u16)
    }
}

/// Deterministic canonical M31-word encoding for transcript-bound values.
pub trait CanonicalWords {
    /// Appends the value to an existing canonical word stream.
    fn append_canonical_words(&self, output: &mut Vec<M31Word>);

    /// Returns the complete canonical word stream for this value.
    fn canonical_words(&self) -> Vec<M31Word> {
        let mut output = Vec::new();
        self.append_canonical_words(&mut output);
        output
    }
}

impl CanonicalWords for PcsParameters {
    fn append_canonical_words(&self, output: &mut Vec<M31Word>) {
        output.extend([
            CanonicalTag::Pcs.word(),
            CanonicalTag::InteractionPowBits.word(),
            self.interaction_pow_bits,
            CanonicalTag::PowBits.word(),
            self.pow_bits,
            CanonicalTag::FriLogBlowupFactor.word(),
            self.fri_log_blowup_factor,
            CanonicalTag::FriNQueries.word(),
            self.fri_n_queries,
            CanonicalTag::FriLogLastLayerDegreeBound.word(),
            self.fri_log_last_layer_degree_bound,
            CanonicalTag::FriFoldStep.word(),
            self.fri_fold_step,
            CanonicalTag::LiftingLogSize.word(),
        ]);
        match self.lifting_log_size {
            OptionalM31Word::None => output.extend([M31Word::ZERO, M31Word::ZERO]),
            OptionalM31Word::Some(value) => {
                output.extend([M31Word::from(1_u16), value]);
            }
        }
    }
}

impl<const N_TABLES: usize, const N_TREES: usize, const N_FRI_LAYERS: usize> CanonicalWords
    for FixedProofShape<N_TABLES, N_TREES, N_FRI_LAYERS>
{
    fn append_canonical_words(&self, output: &mut Vec<M31Word>) {
        let table_count = array_len_word::<N_TABLES>();
        let tree_count = array_len_word::<N_TREES>();
        let fri_layer_count = array_len_word::<N_FRI_LAYERS>();
        output.extend([
            CanonicalTag::ProofShape.word(),
            CanonicalTag::CommitmentCount.word(),
            tree_count,
            CanonicalTag::ClaimedSumCount.word(),
            self.claimed_sum_count,
            CanonicalTag::SampledValueCount.word(),
            self.sampled_value_count,
            CanonicalTag::QueriedValueCount.word(),
            self.queried_value_count,
            CanonicalTag::TracePathCount.word(),
            self.trace_path_count,
            CanonicalTag::RawQueryCount.word(),
            self.raw_query_count,
            CanonicalTag::FriLayerCount.word(),
            fri_layer_count,
            CanonicalTag::LastLayerCoefficientCount.word(),
            self.last_layer_coefficient_count,
            CanonicalTag::TableLogSizes.word(),
            table_count,
        ]);
        output.extend(self.table_log_sizes);
        output.extend([CanonicalTag::TreeHeights.word(), tree_count]);
        output.extend(self.tree_heights);
        output.extend([CanonicalTag::FriLayerFoldWidths.word(), fri_layer_count]);
        output.extend(self.fri_layer_fold_widths);
        output.extend([CanonicalTag::FriLayerTreeHeights.word(), fri_layer_count]);
        output.extend(self.fri_layer_tree_heights);
    }
}

impl<
    const VM_TABLES: usize,
    const VM_TREES: usize,
    const VM_FRI_LAYERS: usize,
    const RECURSION_TABLES: usize,
    const RECURSION_TREES: usize,
    const RECURSION_FRI_LAYERS: usize,
> CanonicalWords
    for ProtocolManifest<
        VM_TABLES,
        VM_TREES,
        VM_FRI_LAYERS,
        RECURSION_TABLES,
        RECURSION_TREES,
        RECURSION_FRI_LAYERS,
    >
{
    fn append_canonical_words(&self, output: &mut Vec<M31Word>) {
        output.extend([
            CanonicalTag::Manifest.word(),
            CanonicalTag::Version.word(),
            self.version.0,
        ]);
        append_digest(
            output,
            CanonicalTag::HashSuite,
            self.hash_suite.digest().words(),
        );
        append_digest(
            output,
            CanonicalTag::VmPreprocessing,
            self.vm_preprocessing.digest().words(),
        );
        append_digest(
            output,
            CanonicalTag::RecursionPreprocessing,
            self.recursion_preprocessing.digest().words(),
        );
        append_digest(
            output,
            CanonicalTag::VmAirProgram,
            self.vm_air_program.digest().words(),
        );
        append_digest(
            output,
            CanonicalTag::RecursionAirProgram,
            self.recursion_air_program.digest().words(),
        );
        output.push(CanonicalTag::VmPcs.word());
        self.vm_pcs.append_canonical_words(output);
        output.push(CanonicalTag::RecursionPcs.word());
        self.recursion_pcs.append_canonical_words(output);
        output.push(CanonicalTag::VmProofShape.word());
        self.vm_proof_shape.append_canonical_words(output);
        output.push(CanonicalTag::RecursionProofShape.word());
        self.recursion_proof_shape.append_canonical_words(output);
    }
}

fn append_digest(output: &mut Vec<M31Word>, tag: CanonicalTag, digest: &[M31Word; 8]) {
    output.push(tag.word());
    output.extend_from_slice(digest);
}

fn array_len_word<const N: usize>() -> M31Word {
    u32::try_from(N)
        .ok()
        .and_then(|count| M31Word::try_from(count).ok())
        .expect("a Rust array length used by the protocol fits in M31")
}

fn validate_nonzero_shape_count(
    field: &'static str,
    value: M31Word,
) -> Result<(), ProofShapeError> {
    if value == M31Word::ZERO {
        Err(ProofShapeError::ZeroCount { field })
    } else {
        Ok(())
    }
}

fn validate_shape_count(
    field: &'static str,
    expected: usize,
    actual: M31Word,
) -> Result<(), ProofShapeError> {
    let actual = shape_word_as_usize(field, actual)?;
    if actual == expected {
        Ok(())
    } else {
        Err(ProofShapeError::CountMismatch {
            field,
            expected,
            actual,
        })
    }
}

fn shape_word_as_usize(field: &'static str, value: M31Word) -> Result<usize, ProofShapeError> {
    usize::try_from(value.as_u32()).map_err(|_| ProofShapeError::CountOutOfRange {
        field,
        value: value.as_u32(),
    })
}

fn validate_log_size(
    field: &'static str,
    index: usize,
    value: u32,
    allow_zero: bool,
) -> Result<(), ProofShapeError> {
    let minimum = if allow_zero {
        0
    } else {
        MIN_CIRCLE_DOMAIN_LOG_SIZE
    };
    if (minimum..=MAX_CIRCLE_DOMAIN_LOG_SIZE).contains(&value) {
        Ok(())
    } else {
        Err(ProofShapeError::LogSizeOutOfRange {
            field,
            index,
            value,
            minimum,
            maximum: MAX_CIRCLE_DOMAIN_LOG_SIZE,
        })
    }
}

/// A PCS manifest value that cannot define the supported V2 verifier.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PcsParameterError {
    InteractionPowBitsOutOfRange { value: u32 },
    PcsPowBitsOutOfRange { value: u32 },
    FriLogBlowupOutOfRange { value: u32 },
    ZeroFriQueries,
    FriQueryCountOutOfRange { value: u32 },
    FriLastLayerLogDegreeOutOfRange { value: u32 },
    FriFoldStepOutOfRange { value: u32 },
    LiftingLogSizeOutOfRange { value: u32 },
}

impl fmt::Display for PcsParameterError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InteractionPowBitsOutOfRange { value } => {
                write!(
                    formatter,
                    "interaction PoW bits {value} exceed {MAX_POW_BITS}"
                )
            }
            Self::PcsPowBitsOutOfRange { value } => {
                write!(formatter, "PCS PoW bits {value} exceed {MAX_POW_BITS}")
            }
            Self::FriLogBlowupOutOfRange { value } => write!(
                formatter,
                "FRI log blowup {value} is outside {MIN_FRI_LOG_BLOWUP}..={MAX_FRI_LOG_BLOWUP}"
            ),
            Self::ZeroFriQueries => write!(formatter, "FRI query count is zero"),
            Self::FriQueryCountOutOfRange { value } => {
                write!(
                    formatter,
                    "FRI query count {value} exceeds the V2 maximum {MAX_FRI_QUERIES}"
                )
            }
            Self::FriLastLayerLogDegreeOutOfRange { value } => write!(
                formatter,
                "FRI last-layer log degree {value} exceeds {MAX_FRI_LAST_LAYER_LOG_DEGREE}"
            ),
            Self::FriFoldStepOutOfRange { value } => write!(
                formatter,
                "FRI fold step {value} is outside 1..={MAX_FRI_FOLD_STEP}"
            ),
            Self::LiftingLogSizeOutOfRange { value } => write!(
                formatter,
                "lifting log size {value} is outside {MIN_CIRCLE_DOMAIN_LOG_SIZE}..={MAX_CIRCLE_DOMAIN_LOG_SIZE}"
            ),
        }
    }
}

impl std::error::Error for PcsParameterError {}

/// An inconsistency between fixed proof arrays and the validated PCS profile.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProofShapeError {
    EmptyTableLayout,
    EmptyTreeLayout,
    ZeroCount {
        field: &'static str,
    },
    CountOutOfRange {
        field: &'static str,
        value: u32,
    },
    CountMismatch {
        field: &'static str,
        expected: usize,
        actual: usize,
    },
    ArithmeticOverflow {
        field: &'static str,
    },
    QueriedValuesNotPerRawQuery {
        queried_values: usize,
        raw_queries: usize,
    },
    LogSizeOutOfRange {
        field: &'static str,
        index: usize,
        value: u32,
        minimum: u32,
        maximum: u32,
    },
    TreeHeightMismatch {
        tree: usize,
        expected: u32,
        actual: u32,
    },
    TableExceedsLiftingDomain {
        table: usize,
        table_log_size: u32,
        log_blowup_factor: u32,
        lifting_log_size: u32,
    },
    InvalidFriDegreeRange {
        column_log_degree: u32,
        last_layer_log_degree: u32,
        fold_step: u32,
    },
    FriLayerCountMismatch {
        expected: usize,
        actual: usize,
    },
    FriFoldWidthMismatch {
        layer: usize,
        expected: u32,
        actual: u32,
    },
    FriTreeHeightMismatch {
        layer: usize,
        expected: u32,
        actual: u32,
    },
}

impl fmt::Display for ProofShapeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyTableLayout => write!(formatter, "proof shape has no AIR tables"),
            Self::EmptyTreeLayout => write!(formatter, "proof shape has no commitment trees"),
            Self::ZeroCount { field } => write!(formatter, "proof-shape {field} count is zero"),
            Self::CountOutOfRange { field, value } => {
                write!(
                    formatter,
                    "proof-shape {field} count {value} does not fit usize"
                )
            }
            Self::CountMismatch {
                field,
                expected,
                actual,
            } => write!(
                formatter,
                "proof-shape {field} count is {actual}, expected {expected}"
            ),
            Self::ArithmeticOverflow { field } => {
                write!(formatter, "proof-shape {field} arithmetic overflowed")
            }
            Self::QueriedValuesNotPerRawQuery {
                queried_values,
                raw_queries,
            } => write!(
                formatter,
                "{queried_values} queried values do not split across {raw_queries} raw queries"
            ),
            Self::LogSizeOutOfRange {
                field,
                index,
                value,
                minimum,
                maximum,
            } => write!(
                formatter,
                "{field} log size {index} is {value}, expected {minimum}..={maximum}"
            ),
            Self::TreeHeightMismatch {
                tree,
                expected,
                actual,
            } => write!(
                formatter,
                "tree {tree} has height {actual}, lifting config requires {expected}"
            ),
            Self::TableExceedsLiftingDomain {
                table,
                table_log_size,
                log_blowup_factor,
                lifting_log_size,
            } => write!(
                formatter,
                "table {table} log size {table_log_size} plus blowup {log_blowup_factor} exceeds lifting size {lifting_log_size}"
            ),
            Self::InvalidFriDegreeRange {
                column_log_degree,
                last_layer_log_degree,
                fold_step,
            } => write!(
                formatter,
                "FRI cannot fold column degree {column_log_degree} to {last_layer_log_degree} with first step {fold_step}"
            ),
            Self::FriLayerCountMismatch { expected, actual } => write!(
                formatter,
                "proof shape has {actual} FRI layers, expected {expected}"
            ),
            Self::FriFoldWidthMismatch {
                layer,
                expected,
                actual,
            } => write!(
                formatter,
                "FRI layer {layer} has width {actual}, expected {expected}"
            ),
            Self::FriTreeHeightMismatch {
                layer,
                expected,
                actual,
            } => write!(
                formatter,
                "FRI layer {layer} has tree height {actual}, expected {expected}"
            ),
        }
    }
}

impl std::error::Error for ProofShapeError {}

/// Identifies which half of a dual VM/recursion manifest is invalid.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProtocolManifestError {
    VmPcs(PcsParameterError),
    RecursionPcs(PcsParameterError),
    VmShape(ProofShapeError),
    RecursionShape(ProofShapeError),
}

impl fmt::Display for ProtocolManifestError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::VmPcs(source) => write!(formatter, "invalid VM PCS profile: {source}"),
            Self::RecursionPcs(source) => {
                write!(formatter, "invalid recursion PCS profile: {source}")
            }
            Self::VmShape(source) => write!(formatter, "invalid VM proof shape: {source}"),
            Self::RecursionShape(source) => {
                write!(formatter, "invalid recursion proof shape: {source}")
            }
        }
    }
}

impl std::error::Error for ProtocolManifestError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::VmPcs(source) | Self::RecursionPcs(source) => Some(source),
            Self::VmShape(source) | Self::RecursionShape(source) => Some(source),
        }
    }
}

#[cfg(test)]
mod tests {
    use rstest::rstest;

    use air::digest::Digest8;

    use super::*;

    type TestManifest = ProtocolManifest<2, 2, 2, 2, 2, 2>;

    #[derive(Clone, Copy, Debug)]
    enum ManifestField {
        Version,
        HashSuite,
        VmPreprocessing,
        RecursionPreprocessing,
        VmAirProgram,
        RecursionAirProgram,
        VmInteractionPowBits,
        VmPowBits,
        VmFriLogBlowupFactor,
        VmFriNQueries,
        VmFriLogLastLayerDegreeBound,
        VmFriFoldStep,
        VmLiftingLogSize,
        RecursionInteractionPowBits,
        RecursionPowBits,
        RecursionFriLogBlowupFactor,
        RecursionFriNQueries,
        RecursionFriLogLastLayerDegreeBound,
        RecursionFriFoldStep,
        RecursionLiftingLogSize,
        VmClaimedSumCount,
        VmSampledValueCount,
        VmQueriedValueCount,
        VmTracePathCount,
        VmRawQueryCount,
        VmLastLayerCoefficientCount,
        VmTableLogSizes,
        VmTreeHeights,
        VmFriLayerFoldWidths,
        VmFriLayerTreeHeights,
        RecursionClaimedSumCount,
        RecursionSampledValueCount,
        RecursionQueriedValueCount,
        RecursionTracePathCount,
        RecursionRawQueryCount,
        RecursionLastLayerCoefficientCount,
        RecursionTableLogSizes,
        RecursionTreeHeights,
        RecursionFriLayerFoldWidths,
        RecursionFriLayerTreeHeights,
    }

    fn word(value: u16) -> M31Word {
        M31Word::from(value)
    }

    fn digest(seed: u16) -> Digest8 {
        Digest8::new([
            word(seed),
            word(seed + 1),
            word(seed + 2),
            word(seed + 3),
            word(seed + 4),
            word(seed + 5),
            word(seed + 6),
            word(seed + 7),
        ])
    }

    fn pcs(seed: u16) -> PcsParameters {
        PcsParameters {
            interaction_pow_bits: word(seed),
            pow_bits: word(seed + 1),
            fri_log_blowup_factor: word(seed + 2),
            fri_n_queries: word(seed + 3),
            fri_log_last_layer_degree_bound: word(seed + 4),
            fri_fold_step: word(seed + 5),
            lifting_log_size: OptionalM31Word::Some(word(seed + 6)),
        }
    }

    fn shape(seed: u16) -> FixedProofShape<2, 2, 2> {
        FixedProofShape {
            claimed_sum_count: word(seed),
            sampled_value_count: word(seed + 1),
            queried_value_count: word(seed + 2),
            trace_path_count: word(seed + 3),
            raw_query_count: word(seed + 4),
            last_layer_coefficient_count: word(seed + 5),
            table_log_sizes: [word(seed + 6), word(seed + 7)],
            tree_heights: [word(seed + 8), word(seed + 9)],
            fri_layer_fold_widths: [word(seed + 10), word(seed + 11)],
            fri_layer_tree_heights: [word(seed + 12), word(seed + 13)],
        }
    }

    fn manifest() -> TestManifest {
        ProtocolManifest {
            version: ProtocolVersion(word(1)),
            hash_suite: HashSuiteDigest::from(digest(10)),
            vm_preprocessing: VmPreprocessingDigest::from(digest(20)),
            recursion_preprocessing: RecursionPreprocessingDigest::from(digest(30)),
            vm_air_program: VmAirProgramDigest::from(digest(40)),
            recursion_air_program: RecursionAirProgramDigest::from(digest(50)),
            vm_pcs: pcs(60),
            recursion_pcs: pcs(70),
            vm_proof_shape: shape(80),
            recursion_proof_shape: shape(100),
        }
    }

    fn valid_pcs() -> PcsParameters {
        PcsParameters {
            interaction_pow_bits: word(8),
            pow_bits: word(10),
            fri_log_blowup_factor: word(1),
            fri_n_queries: word(3),
            fri_log_last_layer_degree_bound: M31Word::ZERO,
            fri_fold_step: word(2),
            lifting_log_size: OptionalM31Word::Some(word(8)),
        }
    }

    fn valid_shape() -> FixedProofShape<2, 2, 4> {
        FixedProofShape {
            claimed_sum_count: word(1),
            sampled_value_count: word(4),
            queried_value_count: word(6),
            trace_path_count: word(6),
            raw_query_count: word(3),
            last_layer_coefficient_count: word(1),
            table_log_sizes: [word(5), word(6)],
            tree_heights: [word(8), word(8)],
            fri_layer_fold_widths: [word(4), word(4), word(4), word(2)],
            fri_layer_tree_heights: [word(6), word(4), word(2), word(2)],
        }
    }

    fn valid_manifest() -> ProtocolManifest<2, 2, 4, 2, 2, 4> {
        ProtocolManifest {
            version: ProtocolVersion(word(2)),
            hash_suite: HashSuiteDigest::from(digest(10)),
            vm_preprocessing: VmPreprocessingDigest::from(digest(20)),
            recursion_preprocessing: RecursionPreprocessingDigest::from(digest(30)),
            vm_air_program: VmAirProgramDigest::from(digest(40)),
            recursion_air_program: RecursionAirProgramDigest::from(digest(50)),
            vm_pcs: valid_pcs(),
            recursion_pcs: valid_pcs(),
            vm_proof_shape: valid_shape(),
            recursion_proof_shape: valid_shape(),
        }
    }

    fn replace_first_word(value: Digest8) -> Digest8 {
        let mut words = value.into_words();
        words[0] = word(500);
        Digest8::new(words)
    }

    fn change_manifest_field(mut value: TestManifest, field: ManifestField) -> TestManifest {
        match field {
            ManifestField::Version => value.version = ProtocolVersion(word(500)),
            ManifestField::HashSuite => {
                value.hash_suite =
                    HashSuiteDigest::from(replace_first_word(value.hash_suite.into_digest()));
            }
            ManifestField::VmPreprocessing => {
                value.vm_preprocessing = VmPreprocessingDigest::from(replace_first_word(
                    value.vm_preprocessing.into_digest(),
                ));
            }
            ManifestField::RecursionPreprocessing => {
                value.recursion_preprocessing = RecursionPreprocessingDigest::from(
                    replace_first_word(value.recursion_preprocessing.into_digest()),
                );
            }
            ManifestField::VmAirProgram => {
                value.vm_air_program = VmAirProgramDigest::from(replace_first_word(
                    value.vm_air_program.into_digest(),
                ));
            }
            ManifestField::RecursionAirProgram => {
                value.recursion_air_program = RecursionAirProgramDigest::from(replace_first_word(
                    value.recursion_air_program.into_digest(),
                ));
            }
            ManifestField::VmInteractionPowBits => {
                value.vm_pcs.interaction_pow_bits = word(500);
            }
            ManifestField::VmPowBits => value.vm_pcs.pow_bits = word(500),
            ManifestField::VmFriLogBlowupFactor => {
                value.vm_pcs.fri_log_blowup_factor = word(500);
            }
            ManifestField::VmFriNQueries => value.vm_pcs.fri_n_queries = word(500),
            ManifestField::VmFriLogLastLayerDegreeBound => {
                value.vm_pcs.fri_log_last_layer_degree_bound = word(500);
            }
            ManifestField::VmFriFoldStep => value.vm_pcs.fri_fold_step = word(500),
            ManifestField::VmLiftingLogSize => {
                value.vm_pcs.lifting_log_size = OptionalM31Word::None;
            }
            ManifestField::RecursionInteractionPowBits => {
                value.recursion_pcs.interaction_pow_bits = word(500);
            }
            ManifestField::RecursionPowBits => value.recursion_pcs.pow_bits = word(500),
            ManifestField::RecursionFriLogBlowupFactor => {
                value.recursion_pcs.fri_log_blowup_factor = word(500);
            }
            ManifestField::RecursionFriNQueries => {
                value.recursion_pcs.fri_n_queries = word(500);
            }
            ManifestField::RecursionFriLogLastLayerDegreeBound => {
                value.recursion_pcs.fri_log_last_layer_degree_bound = word(500);
            }
            ManifestField::RecursionFriFoldStep => {
                value.recursion_pcs.fri_fold_step = word(500);
            }
            ManifestField::RecursionLiftingLogSize => {
                value.recursion_pcs.lifting_log_size = OptionalM31Word::None;
            }
            ManifestField::VmClaimedSumCount => {
                value.vm_proof_shape.claimed_sum_count = word(500);
            }
            ManifestField::VmSampledValueCount => {
                value.vm_proof_shape.sampled_value_count = word(500);
            }
            ManifestField::VmQueriedValueCount => {
                value.vm_proof_shape.queried_value_count = word(500);
            }
            ManifestField::VmTracePathCount => {
                value.vm_proof_shape.trace_path_count = word(500);
            }
            ManifestField::VmRawQueryCount => {
                value.vm_proof_shape.raw_query_count = word(500);
            }
            ManifestField::VmLastLayerCoefficientCount => {
                value.vm_proof_shape.last_layer_coefficient_count = word(500);
            }
            ManifestField::VmTableLogSizes => {
                value.vm_proof_shape.table_log_sizes[0] = word(500);
            }
            ManifestField::VmTreeHeights => {
                value.vm_proof_shape.tree_heights[0] = word(500);
            }
            ManifestField::VmFriLayerFoldWidths => {
                value.vm_proof_shape.fri_layer_fold_widths[0] = word(500);
            }
            ManifestField::VmFriLayerTreeHeights => {
                value.vm_proof_shape.fri_layer_tree_heights[0] = word(500);
            }
            ManifestField::RecursionClaimedSumCount => {
                value.recursion_proof_shape.claimed_sum_count = word(500);
            }
            ManifestField::RecursionSampledValueCount => {
                value.recursion_proof_shape.sampled_value_count = word(500);
            }
            ManifestField::RecursionQueriedValueCount => {
                value.recursion_proof_shape.queried_value_count = word(500);
            }
            ManifestField::RecursionTracePathCount => {
                value.recursion_proof_shape.trace_path_count = word(500);
            }
            ManifestField::RecursionRawQueryCount => {
                value.recursion_proof_shape.raw_query_count = word(500);
            }
            ManifestField::RecursionLastLayerCoefficientCount => {
                value.recursion_proof_shape.last_layer_coefficient_count = word(500);
            }
            ManifestField::RecursionTableLogSizes => {
                value.recursion_proof_shape.table_log_sizes[0] = word(500);
            }
            ManifestField::RecursionTreeHeights => {
                value.recursion_proof_shape.tree_heights[0] = word(500);
            }
            ManifestField::RecursionFriLayerFoldWidths => {
                value.recursion_proof_shape.fri_layer_fold_widths[0] = word(500);
            }
            ManifestField::RecursionFriLayerTreeHeights => {
                value.recursion_proof_shape.fri_layer_tree_heights[0] = word(500);
            }
        }
        value
    }

    #[test]
    fn vm_and_recursion_preprocessing_use_distinct_encoding_tags() {
        assert_ne!(
            CanonicalTag::VmPreprocessing.word(),
            CanonicalTag::RecursionPreprocessing.word()
        );
    }

    #[test]
    fn absent_and_zero_lifting_sizes_have_distinct_encodings() {
        let mut absent = pcs(1);
        absent.lifting_log_size = OptionalM31Word::None;
        let mut zero = pcs(1);
        zero.lifting_log_size = OptionalM31Word::Some(M31Word::ZERO);
        assert_ne!(absent.canonical_words(), zero.canonical_words());
    }

    #[test]
    fn manifest_encoding_is_deterministic() {
        assert_eq!(manifest().canonical_words(), manifest().canonical_words());
    }

    #[test]
    fn manifest_protocol_id_is_deterministic() {
        assert_eq!(manifest().protocol_id(), manifest().protocol_id());
    }

    #[test]
    fn manifest_protocol_id_matches_conformance_vector() {
        assert_eq!(
            manifest().protocol_id(),
            ProtocolId::from(
                Digest8::try_from([
                    478_045_862,
                    405_973_984,
                    209_742_061,
                    1_668_992_471,
                    1_869_861_411,
                    1_958_982_823,
                    1_848_617_412,
                    1_055_531_657,
                ])
                .expect("the protocol conformance digest words are canonical")
            )
        );
    }

    #[test]
    fn valid_manifest_constructs_checked_profiles() {
        let manifest = valid_manifest();
        assert_eq!(
            manifest.validate().map(|validated| (
                validated.protocol_id(),
                validated.vm_shape().lifting_log_size(),
                validated.recursion_shape().column_log_degree(),
            )),
            Ok((manifest.protocol_id(), 8, 7))
        );
    }

    #[test]
    fn pcs_validation_rejects_an_unsupported_fold_step() {
        let mut parameters = valid_pcs();
        parameters.fri_fold_step = word(5);
        assert_eq!(
            parameters.validate(),
            Err(PcsParameterError::FriFoldStepOutOfRange { value: 5 })
        );
    }

    #[test]
    fn manifest_validation_rejects_a_raw_query_count_mismatch() {
        let mut manifest = valid_manifest();
        manifest.vm_proof_shape.raw_query_count = word(2);
        assert_eq!(
            manifest.validate(),
            Err(ProtocolManifestError::VmShape(
                ProofShapeError::CountMismatch {
                    field: "raw queries",
                    expected: 3,
                    actual: 2,
                }
            ))
        );
    }

    #[test]
    fn manifest_validation_rejects_a_fri_tree_height_mismatch() {
        let mut manifest = valid_manifest();
        manifest.recursion_proof_shape.fri_layer_tree_heights[1] = word(5);
        assert_eq!(
            manifest.validate(),
            Err(ProtocolManifestError::RecursionShape(
                ProofShapeError::FriTreeHeightMismatch {
                    layer: 1,
                    expected: 4,
                    actual: 5,
                }
            ))
        );
    }

    #[rstest]
    #[case::version(ManifestField::Version)]
    #[case::hash_suite(ManifestField::HashSuite)]
    #[case::vm_preprocessing(ManifestField::VmPreprocessing)]
    #[case::recursion_preprocessing(ManifestField::RecursionPreprocessing)]
    #[case::vm_air_program(ManifestField::VmAirProgram)]
    #[case::recursion_air_program(ManifestField::RecursionAirProgram)]
    #[case::vm_interaction_pow_bits(ManifestField::VmInteractionPowBits)]
    #[case::vm_pow_bits(ManifestField::VmPowBits)]
    #[case::vm_fri_log_blowup_factor(ManifestField::VmFriLogBlowupFactor)]
    #[case::vm_fri_n_queries(ManifestField::VmFriNQueries)]
    #[case::vm_fri_log_last_layer_degree_bound(ManifestField::VmFriLogLastLayerDegreeBound)]
    #[case::vm_fri_fold_step(ManifestField::VmFriFoldStep)]
    #[case::vm_lifting_log_size(ManifestField::VmLiftingLogSize)]
    #[case::recursion_interaction_pow_bits(ManifestField::RecursionInteractionPowBits)]
    #[case::recursion_pow_bits(ManifestField::RecursionPowBits)]
    #[case::recursion_fri_log_blowup_factor(ManifestField::RecursionFriLogBlowupFactor)]
    #[case::recursion_fri_n_queries(ManifestField::RecursionFriNQueries)]
    #[case::recursion_fri_log_last_layer_degree_bound(
        ManifestField::RecursionFriLogLastLayerDegreeBound
    )]
    #[case::recursion_fri_fold_step(ManifestField::RecursionFriFoldStep)]
    #[case::recursion_lifting_log_size(ManifestField::RecursionLiftingLogSize)]
    #[case::vm_claimed_sum_count(ManifestField::VmClaimedSumCount)]
    #[case::vm_sampled_value_count(ManifestField::VmSampledValueCount)]
    #[case::vm_queried_value_count(ManifestField::VmQueriedValueCount)]
    #[case::vm_trace_path_count(ManifestField::VmTracePathCount)]
    #[case::vm_raw_query_count(ManifestField::VmRawQueryCount)]
    #[case::vm_last_layer_coefficient_count(ManifestField::VmLastLayerCoefficientCount)]
    #[case::vm_table_log_sizes(ManifestField::VmTableLogSizes)]
    #[case::vm_tree_heights(ManifestField::VmTreeHeights)]
    #[case::vm_fri_layer_fold_widths(ManifestField::VmFriLayerFoldWidths)]
    #[case::vm_fri_layer_tree_heights(ManifestField::VmFriLayerTreeHeights)]
    #[case::recursion_claimed_sum_count(ManifestField::RecursionClaimedSumCount)]
    #[case::recursion_sampled_value_count(ManifestField::RecursionSampledValueCount)]
    #[case::recursion_queried_value_count(ManifestField::RecursionQueriedValueCount)]
    #[case::recursion_trace_path_count(ManifestField::RecursionTracePathCount)]
    #[case::recursion_raw_query_count(ManifestField::RecursionRawQueryCount)]
    #[case::recursion_last_layer_coefficient_count(
        ManifestField::RecursionLastLayerCoefficientCount
    )]
    #[case::recursion_table_log_sizes(ManifestField::RecursionTableLogSizes)]
    #[case::recursion_tree_heights(ManifestField::RecursionTreeHeights)]
    #[case::recursion_fri_layer_fold_widths(ManifestField::RecursionFriLayerFoldWidths)]
    #[case::recursion_fri_layer_tree_heights(ManifestField::RecursionFriLayerTreeHeights)]
    fn every_manifest_field_changes_the_canonical_encoding(#[case] field: ManifestField) {
        let baseline = manifest();
        let changed = change_manifest_field(baseline, field);
        assert!(
            baseline.canonical_words() != changed.canonical_words()
                && baseline.protocol_id() != changed.protocol_id()
        );
    }
}
