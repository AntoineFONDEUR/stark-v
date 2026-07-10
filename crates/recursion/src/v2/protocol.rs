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

/// An optional PCS parameter with one canonical two-word representation.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum OptionalM31Word {
    None,
    Some(M31Word),
}

/// All parameters read by STWO's commitment-scheme transcript.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct PcsParameters {
    pub pow_bits: M31Word,
    pub fri_log_blowup_factor: M31Word,
    pub fri_n_queries: M31Word,
    pub fri_log_last_layer_degree_bound: M31Word,
    pub fri_fold_step: M31Word,
    pub lifting_log_size: OptionalM31Word,
}

/// Counts and table sizes that make one proof wire shape fixed.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct FixedProofShape<const N_TABLES: usize> {
    pub commitment_count: M31Word,
    pub sampled_value_count: M31Word,
    pub queried_value_count: M31Word,
    pub trace_opening_count: M31Word,
    pub fri_layer_count: M31Word,
    pub fri_fold_width: M31Word,
    pub fri_opening_count: M31Word,
    pub last_layer_coefficient_count: M31Word,
    pub max_merkle_depth: M31Word,
    pub table_log_sizes: [M31Word; N_TABLES],
}

/// Verifier-owned inputs that identify one VM and recursion proof protocol.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct ProtocolManifest<const VM_TABLES: usize, const RECURSION_TABLES: usize> {
    pub version: ProtocolVersion,
    pub hash_suite: HashSuiteDigest,
    pub vm_preprocessing: VmPreprocessingDigest,
    pub recursion_preprocessing: RecursionPreprocessingDigest,
    pub vm_air_program: VmAirProgramDigest,
    pub recursion_air_program: RecursionAirProgramDigest,
    pub vm_pcs: PcsParameters,
    pub recursion_pcs: PcsParameters,
    pub vm_proof_shape: FixedProofShape<VM_TABLES>,
    pub recursion_proof_shape: FixedProofShape<RECURSION_TABLES>,
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
    PowBits = 21,
    FriLogBlowupFactor = 22,
    FriNQueries = 23,
    FriLogLastLayerDegreeBound = 24,
    FriFoldStep = 25,
    LiftingLogSize = 26,
    ProofShape = 40,
    CommitmentCount = 41,
    SampledValueCount = 42,
    QueriedValueCount = 43,
    TraceOpeningCount = 44,
    FriLayerCount = 45,
    FriFoldWidth = 46,
    FriOpeningCount = 47,
    LastLayerCoefficientCount = 48,
    MaxMerkleDepth = 49,
    TableLogSizes = 50,
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

impl<const N_TABLES: usize> CanonicalWords for FixedProofShape<N_TABLES> {
    fn append_canonical_words(&self, output: &mut Vec<M31Word>) {
        let table_count = u32::try_from(N_TABLES)
            .ok()
            .and_then(|count| M31Word::try_from(count).ok())
            .expect("a Rust array length used by the protocol fits in M31");
        output.extend([
            CanonicalTag::ProofShape.word(),
            CanonicalTag::CommitmentCount.word(),
            self.commitment_count,
            CanonicalTag::SampledValueCount.word(),
            self.sampled_value_count,
            CanonicalTag::QueriedValueCount.word(),
            self.queried_value_count,
            CanonicalTag::TraceOpeningCount.word(),
            self.trace_opening_count,
            CanonicalTag::FriLayerCount.word(),
            self.fri_layer_count,
            CanonicalTag::FriFoldWidth.word(),
            self.fri_fold_width,
            CanonicalTag::FriOpeningCount.word(),
            self.fri_opening_count,
            CanonicalTag::LastLayerCoefficientCount.word(),
            self.last_layer_coefficient_count,
            CanonicalTag::MaxMerkleDepth.word(),
            self.max_merkle_depth,
            CanonicalTag::TableLogSizes.word(),
            table_count,
        ]);
        output.extend(self.table_log_sizes);
    }
}

impl<const VM_TABLES: usize, const RECURSION_TABLES: usize> CanonicalWords
    for ProtocolManifest<VM_TABLES, RECURSION_TABLES>
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

#[cfg(test)]
mod tests {
    use rstest::rstest;

    use air::digest::Digest8;

    use super::*;

    type TestManifest = ProtocolManifest<2, 2>;

    #[derive(Clone, Copy, Debug)]
    enum ManifestField {
        Version,
        HashSuite,
        VmPreprocessing,
        RecursionPreprocessing,
        VmAirProgram,
        RecursionAirProgram,
        VmPowBits,
        VmFriLogBlowupFactor,
        VmFriNQueries,
        VmFriLogLastLayerDegreeBound,
        VmFriFoldStep,
        VmLiftingLogSize,
        RecursionPowBits,
        RecursionFriLogBlowupFactor,
        RecursionFriNQueries,
        RecursionFriLogLastLayerDegreeBound,
        RecursionFriFoldStep,
        RecursionLiftingLogSize,
        VmCommitmentCount,
        VmSampledValueCount,
        VmQueriedValueCount,
        VmTraceOpeningCount,
        VmFriLayerCount,
        VmFriFoldWidth,
        VmFriOpeningCount,
        VmLastLayerCoefficientCount,
        VmMaxMerkleDepth,
        VmTableLogSizes,
        RecursionCommitmentCount,
        RecursionSampledValueCount,
        RecursionQueriedValueCount,
        RecursionTraceOpeningCount,
        RecursionFriLayerCount,
        RecursionFriFoldWidth,
        RecursionFriOpeningCount,
        RecursionLastLayerCoefficientCount,
        RecursionMaxMerkleDepth,
        RecursionTableLogSizes,
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
            pow_bits: word(seed),
            fri_log_blowup_factor: word(seed + 1),
            fri_n_queries: word(seed + 2),
            fri_log_last_layer_degree_bound: word(seed + 3),
            fri_fold_step: word(seed + 4),
            lifting_log_size: OptionalM31Word::Some(word(seed + 5)),
        }
    }

    fn shape(seed: u16) -> FixedProofShape<2> {
        FixedProofShape {
            commitment_count: word(seed),
            sampled_value_count: word(seed + 1),
            queried_value_count: word(seed + 2),
            trace_opening_count: word(seed + 3),
            fri_layer_count: word(seed + 4),
            fri_fold_width: word(seed + 5),
            fri_opening_count: word(seed + 6),
            last_layer_coefficient_count: word(seed + 7),
            max_merkle_depth: word(seed + 8),
            table_log_sizes: [word(seed + 9), word(seed + 10)],
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
            ManifestField::VmCommitmentCount => {
                value.vm_proof_shape.commitment_count = word(500);
            }
            ManifestField::VmSampledValueCount => {
                value.vm_proof_shape.sampled_value_count = word(500);
            }
            ManifestField::VmQueriedValueCount => {
                value.vm_proof_shape.queried_value_count = word(500);
            }
            ManifestField::VmTraceOpeningCount => {
                value.vm_proof_shape.trace_opening_count = word(500);
            }
            ManifestField::VmFriLayerCount => {
                value.vm_proof_shape.fri_layer_count = word(500);
            }
            ManifestField::VmFriFoldWidth => {
                value.vm_proof_shape.fri_fold_width = word(500);
            }
            ManifestField::VmFriOpeningCount => {
                value.vm_proof_shape.fri_opening_count = word(500);
            }
            ManifestField::VmLastLayerCoefficientCount => {
                value.vm_proof_shape.last_layer_coefficient_count = word(500);
            }
            ManifestField::VmMaxMerkleDepth => {
                value.vm_proof_shape.max_merkle_depth = word(500);
            }
            ManifestField::VmTableLogSizes => {
                value.vm_proof_shape.table_log_sizes[0] = word(500);
            }
            ManifestField::RecursionCommitmentCount => {
                value.recursion_proof_shape.commitment_count = word(500);
            }
            ManifestField::RecursionSampledValueCount => {
                value.recursion_proof_shape.sampled_value_count = word(500);
            }
            ManifestField::RecursionQueriedValueCount => {
                value.recursion_proof_shape.queried_value_count = word(500);
            }
            ManifestField::RecursionTraceOpeningCount => {
                value.recursion_proof_shape.trace_opening_count = word(500);
            }
            ManifestField::RecursionFriLayerCount => {
                value.recursion_proof_shape.fri_layer_count = word(500);
            }
            ManifestField::RecursionFriFoldWidth => {
                value.recursion_proof_shape.fri_fold_width = word(500);
            }
            ManifestField::RecursionFriOpeningCount => {
                value.recursion_proof_shape.fri_opening_count = word(500);
            }
            ManifestField::RecursionLastLayerCoefficientCount => {
                value.recursion_proof_shape.last_layer_coefficient_count = word(500);
            }
            ManifestField::RecursionMaxMerkleDepth => {
                value.recursion_proof_shape.max_merkle_depth = word(500);
            }
            ManifestField::RecursionTableLogSizes => {
                value.recursion_proof_shape.table_log_sizes[0] = word(500);
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
    #[case::vm_pow_bits(ManifestField::VmPowBits)]
    #[case::vm_fri_log_blowup_factor(ManifestField::VmFriLogBlowupFactor)]
    #[case::vm_fri_n_queries(ManifestField::VmFriNQueries)]
    #[case::vm_fri_log_last_layer_degree_bound(ManifestField::VmFriLogLastLayerDegreeBound)]
    #[case::vm_fri_fold_step(ManifestField::VmFriFoldStep)]
    #[case::vm_lifting_log_size(ManifestField::VmLiftingLogSize)]
    #[case::recursion_pow_bits(ManifestField::RecursionPowBits)]
    #[case::recursion_fri_log_blowup_factor(ManifestField::RecursionFriLogBlowupFactor)]
    #[case::recursion_fri_n_queries(ManifestField::RecursionFriNQueries)]
    #[case::recursion_fri_log_last_layer_degree_bound(
        ManifestField::RecursionFriLogLastLayerDegreeBound
    )]
    #[case::recursion_fri_fold_step(ManifestField::RecursionFriFoldStep)]
    #[case::recursion_lifting_log_size(ManifestField::RecursionLiftingLogSize)]
    #[case::vm_commitment_count(ManifestField::VmCommitmentCount)]
    #[case::vm_sampled_value_count(ManifestField::VmSampledValueCount)]
    #[case::vm_queried_value_count(ManifestField::VmQueriedValueCount)]
    #[case::vm_trace_opening_count(ManifestField::VmTraceOpeningCount)]
    #[case::vm_fri_layer_count(ManifestField::VmFriLayerCount)]
    #[case::vm_fri_fold_width(ManifestField::VmFriFoldWidth)]
    #[case::vm_fri_opening_count(ManifestField::VmFriOpeningCount)]
    #[case::vm_last_layer_coefficient_count(ManifestField::VmLastLayerCoefficientCount)]
    #[case::vm_max_merkle_depth(ManifestField::VmMaxMerkleDepth)]
    #[case::vm_table_log_sizes(ManifestField::VmTableLogSizes)]
    #[case::recursion_commitment_count(ManifestField::RecursionCommitmentCount)]
    #[case::recursion_sampled_value_count(ManifestField::RecursionSampledValueCount)]
    #[case::recursion_queried_value_count(ManifestField::RecursionQueriedValueCount)]
    #[case::recursion_trace_opening_count(ManifestField::RecursionTraceOpeningCount)]
    #[case::recursion_fri_layer_count(ManifestField::RecursionFriLayerCount)]
    #[case::recursion_fri_fold_width(ManifestField::RecursionFriFoldWidth)]
    #[case::recursion_fri_opening_count(ManifestField::RecursionFriOpeningCount)]
    #[case::recursion_last_layer_coefficient_count(
        ManifestField::RecursionLastLayerCoefficientCount
    )]
    #[case::recursion_max_merkle_depth(ManifestField::RecursionMaxMerkleDepth)]
    #[case::recursion_table_log_sizes(ManifestField::RecursionTableLogSizes)]
    fn every_manifest_field_changes_the_canonical_encoding(#[case] field: ManifestField) {
        let baseline = manifest();
        let changed = change_manifest_field(baseline, field);
        assert_ne!(baseline.canonical_words(), changed.canonical_words());
    }
}
