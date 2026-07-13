//! Canonical protocol manifest for recursion version 2.
//!
//! The manifest contains every verifier-owned value that changes transcript
//! replay or fixed proof parsing. Its encoding uses canonical M31 words and
//! explicit field tags, so two roles cannot share an accidental byte layout.
//! This module defines the format only; it does not select production roots,
//! proof dimensions, or a verifier implementation.

use air::digest::{
    HashSuiteDigest, M31Word, RecursionAirProgramDigest, RecursionPreprocessingDigest,
    VmAirProgramDigest, VmPreprocessingDigest,
};

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
        assert_ne!(baseline.canonical_words(), changed.canonical_words());
    }
}
