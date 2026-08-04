//! Canonical fixed-width proof wire for recursion.
//!
//! Wire types contain arrays only: no proof-selected configuration, length
//! prefix, platform-sized integer, or serde enum enters the recursive
//! protocol. Decoding reconstructs the checked statement types, rejects
//! non-canonical field limbs, and requires every inactive Merkle or FRI slot
//! to use its unique all-zero encoding.

use core::fmt;

use air::digest::{
    Digest8, IoDigest, M31Word, MemoryDigest, NonCanonicalM31Word, ProgramDigest, ProtocolId,
};
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::SecureField;

use super::protocol::{FixedProofShape, ProtocolVersion, fri_query_path_depth};
use super::statement::{
    CompleteExecutionStatement, EdgeClaim, ExecutedSpan, JobContext, MachineState, SlotSpan,
    SpanBody, SpanStatement, StatementError,
};

pub const U32_BYTES: usize = size_of::<u32>();
pub const U64_BYTES: usize = size_of::<u64>();
pub const M31_WORD_BYTES: usize = U32_BYTES;
pub const DIGEST_BYTES: usize = 8 * M31_WORD_BYTES;
pub const QM31_BYTES: usize = 4 * M31_WORD_BYTES;

/// RV32 machine words remain raw `u32` values so words at or above the M31
/// modulus cannot alias field elements during serialization.
pub const MACHINE_STATE_BYTES: usize = U32_BYTES + 32 * U32_BYTES + 2 * DIGEST_BYTES;
pub const COMPLETE_EXECUTION_BYTES: usize =
    2 * DIGEST_BYTES + 2 * MACHINE_STATE_BYTES + 2 * DIGEST_BYTES + U64_BYTES;
pub const JOB_CONTEXT_BYTES: usize = COMPLETE_EXECUTION_BYTES + U32_BYTES;
pub const SLOT_SPAN_BYTES: usize = U64_BYTES + U32_BYTES;
pub const EDGE_CLAIM_BYTES: usize = U32_BYTES + DIGEST_BYTES;
pub const EXECUTED_SPAN_BYTES: usize =
    2 * U32_BYTES + 2 * U64_BYTES + 2 * MACHINE_STATE_BYTES + 2 * EDGE_CLAIM_BYTES;
pub const SPAN_BODY_BYTES: usize = U32_BYTES + EXECUTED_SPAN_BYTES;
pub const SPAN_STATEMENT_BYTES: usize = JOB_CONTEXT_BYTES + SLOT_SPAN_BYTES + SPAN_BODY_BYTES;
pub const RECURSIVE_HEADER_BYTES: usize = 2 * U32_BYTES + SPAN_STATEMENT_BYTES;

pub const STATEMENT_OFFSET: usize = 2 * U32_BYTES;
pub const SPAN_BODY_TAG_OFFSET: usize = STATEMENT_OFFSET + JOB_CONTEXT_BYTES + SLOT_SPAN_BYTES;
pub const SPAN_BODY_PAYLOAD_OFFSET: usize = SPAN_BODY_TAG_OFFSET + U32_BYTES;
pub const STARK_PROOF_OFFSET: usize = RECURSIVE_HEADER_BYTES;

const ABSENT_TAG: u32 = 0;
const PRESENT_TAG: u32 = 1;
const EMPTY_BODY_TAG: u32 = 0;
const EXECUTED_BODY_TAG: u32 = 1;

/// Which universal recursion predicate branch produced this proof.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
#[repr(u32)]
pub enum ProofKind {
    SegmentLeaf = 1,
    BinaryNode = 2,
    EmptyLeaf = 3,
}

impl ProofKind {
    pub const fn tag(self) -> u32 {
        self as u32
    }

    fn from_tag(tag: u32, offset: usize) -> Result<Self, WireError> {
        match tag {
            1 => Ok(Self::SegmentLeaf),
            2 => Ok(Self::BinaryNode),
            3 => Ok(Self::EmptyLeaf),
            _ => Err(WireError::UnknownProofKind { offset, tag }),
        }
    }
}

/// One QM31 value as four canonical M31 tower limbs.
#[derive(Clone, Copy, Debug, Default, Hash, PartialEq, Eq)]
#[repr(transparent)]
pub struct Qm31Wire([M31Word; 4]);

impl Qm31Wire {
    pub const ZERO: Self = Self([M31Word::ZERO; 4]);

    pub const fn new(words: [M31Word; 4]) -> Self {
        Self(words)
    }

    pub const fn words(&self) -> &[M31Word; 4] {
        &self.0
    }
}

impl From<SecureField> for Qm31Wire {
    fn from(value: SecureField) -> Self {
        Self(value.to_m31_array().map(M31Word::from))
    }
}

impl From<Qm31Wire> for SecureField {
    fn from(value: Qm31Wire) -> Self {
        SecureField::from_m31_array(value.0.map(M31::from))
    }
}

/// One independently serialized authentication path.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct MerklePathWire<const MAX_DEPTH: usize> {
    active_depth: u32,
    siblings: [Digest8; MAX_DEPTH],
}

impl<const MAX_DEPTH: usize> MerklePathWire<MAX_DEPTH> {
    pub fn new(active_depth: u32, siblings: [Digest8; MAX_DEPTH]) -> Result<Self, WireError> {
        let active_depth_usize =
            usize::try_from(active_depth).map_err(|_| WireError::MerkleDepthOutOfRange {
                active_depth,
                max_depth: MAX_DEPTH,
            })?;
        if active_depth_usize > MAX_DEPTH {
            return Err(WireError::MerkleDepthOutOfRange {
                active_depth,
                max_depth: MAX_DEPTH,
            });
        }
        if let Some(index) = siblings[active_depth_usize..]
            .iter()
            .position(|sibling| *sibling != Digest8::ZERO)
        {
            return Err(WireError::NonZeroMerklePadding {
                index: active_depth_usize + index,
            });
        }
        Ok(Self {
            active_depth,
            siblings,
        })
    }

    pub const fn active_depth(&self) -> u32 {
        self.active_depth
    }

    pub const fn siblings(&self) -> &[Digest8; MAX_DEPTH] {
        &self.siblings
    }
}

impl<const MAX_DEPTH: usize> Default for MerklePathWire<MAX_DEPTH> {
    fn default() -> Self {
        Self {
            active_depth: 0,
            siblings: [Digest8::ZERO; MAX_DEPTH],
        }
    }
}

/// Full fold inputs and one independent path for a raw FRI query.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct FriQueryWire<const FOLD_WIDTH: usize, const MAX_DEPTH: usize> {
    values: [Qm31Wire; FOLD_WIDTH],
    path: MerklePathWire<MAX_DEPTH>,
}

impl<const FOLD_WIDTH: usize, const MAX_DEPTH: usize> FriQueryWire<FOLD_WIDTH, MAX_DEPTH> {
    pub const fn new(values: [Qm31Wire; FOLD_WIDTH], path: MerklePathWire<MAX_DEPTH>) -> Self {
        Self { values, path }
    }

    pub const fn values(&self) -> &[Qm31Wire; FOLD_WIDTH] {
        &self.values
    }

    pub const fn path(&self) -> &MerklePathWire<MAX_DEPTH> {
        &self.path
    }
}

impl<const FOLD_WIDTH: usize, const MAX_DEPTH: usize> Default
    for FriQueryWire<FOLD_WIDTH, MAX_DEPTH>
{
    fn default() -> Self {
        Self {
            values: [Qm31Wire::ZERO; FOLD_WIDTH],
            path: MerklePathWire::default(),
        }
    }
}

/// One FRI commitment round with fixed raw-query slots.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct FriLayerWire<const N_QUERIES: usize, const FOLD_WIDTH: usize, const MAX_DEPTH: usize> {
    active_width: u32,
    commitment: Digest8,
    queries: Box<[FriQueryWire<FOLD_WIDTH, MAX_DEPTH>; N_QUERIES]>,
}

impl<const N_QUERIES: usize, const FOLD_WIDTH: usize, const MAX_DEPTH: usize>
    FriLayerWire<N_QUERIES, FOLD_WIDTH, MAX_DEPTH>
{
    pub fn new(
        active_width: u32,
        commitment: Digest8,
        queries: Box<[FriQueryWire<FOLD_WIDTH, MAX_DEPTH>; N_QUERIES]>,
    ) -> Result<Self, WireError> {
        let active_width_usize =
            usize::try_from(active_width).map_err(|_| WireError::FriFoldWidthOutOfRange {
                active_width,
                max_width: FOLD_WIDTH,
            })?;
        if active_width_usize == 0 || active_width_usize > FOLD_WIDTH {
            return Err(WireError::FriFoldWidthOutOfRange {
                active_width,
                max_width: FOLD_WIDTH,
            });
        }
        for (query, values) in queries.iter().map(FriQueryWire::values).enumerate() {
            if let Some(index) = values[active_width_usize..]
                .iter()
                .position(|value| *value != Qm31Wire::ZERO)
            {
                return Err(WireError::NonZeroFriValuePadding {
                    query,
                    index: active_width_usize + index,
                });
            }
        }
        Ok(Self {
            active_width,
            commitment,
            queries,
        })
    }

    pub const fn active_width(&self) -> u32 {
        self.active_width
    }

    pub const fn commitment(&self) -> Digest8 {
        self.commitment
    }

    pub const fn queries(&self) -> &[FriQueryWire<FOLD_WIDTH, MAX_DEPTH>; N_QUERIES] {
        &self.queries
    }
}

/// Fixed-array STARK proof data consumed by the shared verifier kernel.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct FixedStarkProofWire<
    const N_COMMITMENTS: usize,
    const N_CLAIMED_SUMS: usize,
    const N_SAMPLED_VALUES: usize,
    const N_QUERY_VALUES: usize,
    const N_TRACE_PATHS: usize,
    const N_FRI_LAYERS: usize,
    const N_QUERIES: usize,
    const FOLD_WIDTH: usize,
    const N_LAST_LAYER_COEFFICIENTS: usize,
    const MAX_MERKLE_DEPTH: usize,
> {
    pub commitments: [Digest8; N_COMMITMENTS],
    pub claimed_sums: [Qm31Wire; N_CLAIMED_SUMS],
    pub sampled_values: [Qm31Wire; N_SAMPLED_VALUES],
    pub queried_values: Box<[M31Word; N_QUERY_VALUES]>,
    pub trace_paths: Box<[MerklePathWire<MAX_MERKLE_DEPTH>; N_TRACE_PATHS]>,
    pub fri_layers: Box<[FriLayerWire<N_QUERIES, FOLD_WIDTH, MAX_MERKLE_DEPTH>; N_FRI_LAYERS]>,
    pub last_layer_coefficients: [Qm31Wire; N_LAST_LAYER_COEFFICIENTS],
    pub interaction_pow: u64,
    pub pcs_pow: u64,
}

impl<
    const N_COMMITMENTS: usize,
    const N_CLAIMED_SUMS: usize,
    const N_SAMPLED_VALUES: usize,
    const N_QUERY_VALUES: usize,
    const N_TRACE_PATHS: usize,
    const N_FRI_LAYERS: usize,
    const N_QUERIES: usize,
    const FOLD_WIDTH: usize,
    const N_LAST_LAYER_COEFFICIENTS: usize,
    const MAX_MERKLE_DEPTH: usize,
>
    FixedStarkProofWire<
        N_COMMITMENTS,
        N_CLAIMED_SUMS,
        N_SAMPLED_VALUES,
        N_QUERY_VALUES,
        N_TRACE_PATHS,
        N_FRI_LAYERS,
        N_QUERIES,
        FOLD_WIDTH,
        N_LAST_LAYER_COEFFICIENTS,
        MAX_MERKLE_DEPTH,
    >
{
    /// Binds every generic wire dimension and active path to one manifest shape.
    pub fn validate_against_shape<
        const N_TABLES: usize,
        const N_TREES: usize,
        const MANIFEST_FRI_LAYERS: usize,
    >(
        &self,
        shape: &FixedProofShape<N_TABLES, N_TREES, MANIFEST_FRI_LAYERS>,
    ) -> Result<(), WireError> {
        validate_wire_count("commitments", N_TREES, N_COMMITMENTS)?;
        validate_wire_word_count("claimed sums", shape.claimed_sum_count, N_CLAIMED_SUMS)?;
        validate_wire_word_count(
            "sampled values",
            shape.sampled_value_count,
            N_SAMPLED_VALUES,
        )?;
        validate_wire_word_count("queried values", shape.queried_value_count, N_QUERY_VALUES)?;
        validate_wire_word_count("trace paths", shape.trace_path_count, N_TRACE_PATHS)?;
        validate_wire_count("FRI layers", MANIFEST_FRI_LAYERS, N_FRI_LAYERS)?;
        validate_wire_word_count("raw queries", shape.raw_query_count, N_QUERIES)?;
        validate_wire_word_count(
            "last-layer coefficients",
            shape.last_layer_coefficient_count,
            N_LAST_LAYER_COEFFICIENTS,
        )?;

        let expected_trace_paths =
            N_TREES
                .checked_mul(N_QUERIES)
                .ok_or(WireError::WireShapeArithmeticOverflow {
                    field: "trace path layout",
                })?;
        validate_wire_count("trace path layout", expected_trace_paths, N_TRACE_PATHS)?;

        let mut described_max_depth = 0;
        for height in &shape.tree_heights {
            described_max_depth =
                described_max_depth.max(wire_word_as_usize("maximum Merkle depth", *height)?);
        }
        for (layer, (height, width)) in shape
            .fri_layer_tree_heights
            .iter()
            .zip(&shape.fri_layer_fold_widths)
            .enumerate()
        {
            let depth = fri_query_path_depth(height.as_u32(), width.as_u32()).ok_or(
                WireError::InvalidFriPathGeometry {
                    layer,
                    tree_height: height.as_u32(),
                    fold_width: width.as_u32(),
                },
            )?;
            described_max_depth =
                described_max_depth.max(usize::try_from(depth).map_err(|_| {
                    WireError::WireShapeValueOutOfRange {
                        field: "maximum FRI authentication depth",
                        value: depth,
                    }
                })?);
        }
        validate_wire_count(
            "maximum Merkle depth",
            described_max_depth,
            MAX_MERKLE_DEPTH,
        )?;

        let mut described_max_width = 0;
        for width in shape.fri_layer_fold_widths {
            described_max_width =
                described_max_width.max(wire_word_as_usize("maximum FRI fold width", width)?);
        }
        validate_wire_count("maximum FRI fold width", described_max_width, FOLD_WIDTH)?;

        for (tree, expected_depth) in shape.tree_heights.iter().enumerate() {
            for query in 0..N_QUERIES {
                let path = tree * N_QUERIES + query;
                let actual_depth = self.trace_paths[path].active_depth();
                if actual_depth != expected_depth.as_u32() {
                    return Err(WireError::MerklePathDepthMismatch {
                        path,
                        expected: expected_depth.as_u32(),
                        actual: actual_depth,
                    });
                }
            }
        }

        for (layer, ((wire_layer, expected_width), tree_height)) in self
            .fri_layers
            .iter()
            .zip(&shape.fri_layer_fold_widths)
            .zip(&shape.fri_layer_tree_heights)
            .enumerate()
        {
            if wire_layer.active_width() != expected_width.as_u32() {
                return Err(WireError::FriLayerWidthMismatch {
                    layer,
                    expected: expected_width.as_u32(),
                    actual: wire_layer.active_width(),
                });
            }
            let expected_depth =
                fri_query_path_depth(tree_height.as_u32(), expected_width.as_u32()).ok_or(
                    WireError::InvalidFriPathGeometry {
                        layer,
                        tree_height: tree_height.as_u32(),
                        fold_width: expected_width.as_u32(),
                    },
                )?;
            for (query, wire_query) in wire_layer.queries().iter().enumerate() {
                let actual_depth = wire_query.path().active_depth();
                if actual_depth != expected_depth {
                    return Err(WireError::FriPathDepthMismatch {
                        layer,
                        query,
                        expected: expected_depth,
                        actual: actual_depth,
                    });
                }
            }
        }
        Ok(())
    }
}

/// One statement plus one fixed recursion STARK proof.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct RecursiveProofWire<
    const N_COMMITMENTS: usize,
    const N_CLAIMED_SUMS: usize,
    const N_SAMPLED_VALUES: usize,
    const N_QUERY_VALUES: usize,
    const N_TRACE_PATHS: usize,
    const N_FRI_LAYERS: usize,
    const N_QUERIES: usize,
    const FOLD_WIDTH: usize,
    const N_LAST_LAYER_COEFFICIENTS: usize,
    const MAX_MERKLE_DEPTH: usize,
> {
    version: ProtocolVersion,
    kind: ProofKind,
    statement: SpanStatement,
    stark: FixedStarkProofWire<
        N_COMMITMENTS,
        N_CLAIMED_SUMS,
        N_SAMPLED_VALUES,
        N_QUERY_VALUES,
        N_TRACE_PATHS,
        N_FRI_LAYERS,
        N_QUERIES,
        FOLD_WIDTH,
        N_LAST_LAYER_COEFFICIENTS,
        MAX_MERKLE_DEPTH,
    >,
}

impl<
    const N_COMMITMENTS: usize,
    const N_CLAIMED_SUMS: usize,
    const N_SAMPLED_VALUES: usize,
    const N_QUERY_VALUES: usize,
    const N_TRACE_PATHS: usize,
    const N_FRI_LAYERS: usize,
    const N_QUERIES: usize,
    const FOLD_WIDTH: usize,
    const N_LAST_LAYER_COEFFICIENTS: usize,
    const MAX_MERKLE_DEPTH: usize,
>
    RecursiveProofWire<
        N_COMMITMENTS,
        N_CLAIMED_SUMS,
        N_SAMPLED_VALUES,
        N_QUERY_VALUES,
        N_TRACE_PATHS,
        N_FRI_LAYERS,
        N_QUERIES,
        FOLD_WIDTH,
        N_LAST_LAYER_COEFFICIENTS,
        MAX_MERKLE_DEPTH,
    >
{
    pub fn new(
        version: ProtocolVersion,
        kind: ProofKind,
        statement: SpanStatement,
        stark: FixedStarkProofWire<
            N_COMMITMENTS,
            N_CLAIMED_SUMS,
            N_SAMPLED_VALUES,
            N_QUERY_VALUES,
            N_TRACE_PATHS,
            N_FRI_LAYERS,
            N_QUERIES,
            FOLD_WIDTH,
            N_LAST_LAYER_COEFFICIENTS,
            MAX_MERKLE_DEPTH,
        >,
    ) -> Result<Self, WireError> {
        validate_kind_statement(kind, &statement)?;
        Ok(Self {
            version,
            kind,
            statement,
            stark,
        })
    }

    pub const fn version(&self) -> ProtocolVersion {
        self.version
    }

    pub const fn kind(&self) -> ProofKind {
        self.kind
    }

    pub const fn statement(&self) -> &SpanStatement {
        &self.statement
    }

    pub const fn stark(
        &self,
    ) -> &FixedStarkProofWire<
        N_COMMITMENTS,
        N_CLAIMED_SUMS,
        N_SAMPLED_VALUES,
        N_QUERY_VALUES,
        N_TRACE_PATHS,
        N_FRI_LAYERS,
        N_QUERIES,
        FOLD_WIDTH,
        N_LAST_LAYER_COEFFICIENTS,
        MAX_MERKLE_DEPTH,
    > {
        &self.stark
    }
}

/// Exact-size raw bytes accepted at the proof boundary.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
#[repr(transparent)]
pub struct RecursiveProofBytes<const N: usize>([u8; N]);

impl<const N: usize> RecursiveProofBytes<N> {
    pub const fn new(bytes: [u8; N]) -> Self {
        Self(bytes)
    }

    pub fn try_from_slice(bytes: &[u8]) -> Result<Self, WireError> {
        let array: [u8; N] = bytes.try_into().map_err(|_| WireError::ByteLength {
            expected: N,
            actual: bytes.len(),
        })?;
        Ok(Self(array))
    }

    pub const fn as_bytes(&self) -> &[u8; N] {
        &self.0
    }

    pub const fn into_bytes(self) -> [u8; N] {
        self.0
    }
}

pub const fn merkle_path_bytes(max_depth: usize) -> usize {
    U32_BYTES + max_depth * DIGEST_BYTES
}

pub const fn fri_query_bytes(fold_width: usize, max_depth: usize) -> usize {
    fold_width * QM31_BYTES + merkle_path_bytes(max_depth)
}

pub const fn fri_layer_bytes(n_queries: usize, fold_width: usize, max_depth: usize) -> usize {
    U32_BYTES + DIGEST_BYTES + n_queries * fri_query_bytes(fold_width, max_depth)
}

#[allow(clippy::too_many_arguments)]
pub const fn fixed_stark_proof_bytes(
    n_commitments: usize,
    n_claimed_sums: usize,
    n_sampled_values: usize,
    n_query_values: usize,
    n_trace_paths: usize,
    n_fri_layers: usize,
    n_queries: usize,
    fold_width: usize,
    n_last_layer_coefficients: usize,
    max_merkle_depth: usize,
) -> usize {
    n_commitments * DIGEST_BYTES
        + n_claimed_sums * QM31_BYTES
        + n_sampled_values * QM31_BYTES
        + n_query_values * M31_WORD_BYTES
        + n_trace_paths * merkle_path_bytes(max_merkle_depth)
        + n_fri_layers * fri_layer_bytes(n_queries, fold_width, max_merkle_depth)
        + n_last_layer_coefficients * QM31_BYTES
        + 2 * U64_BYTES
}

pub const fn recursive_proof_bytes<
    const N_COMMITMENTS: usize,
    const N_CLAIMED_SUMS: usize,
    const N_SAMPLED_VALUES: usize,
    const N_QUERY_VALUES: usize,
    const N_TRACE_PATHS: usize,
    const N_FRI_LAYERS: usize,
    const N_QUERIES: usize,
    const FOLD_WIDTH: usize,
    const N_LAST_LAYER_COEFFICIENTS: usize,
    const MAX_MERKLE_DEPTH: usize,
>() -> usize {
    RECURSIVE_HEADER_BYTES
        + fixed_stark_proof_bytes(
            N_COMMITMENTS,
            N_CLAIMED_SUMS,
            N_SAMPLED_VALUES,
            N_QUERY_VALUES,
            N_TRACE_PATHS,
            N_FRI_LAYERS,
            N_QUERIES,
            FOLD_WIDTH,
            N_LAST_LAYER_COEFFICIENTS,
            MAX_MERKLE_DEPTH,
        )
}

fn validate_kind_statement(kind: ProofKind, statement: &SpanStatement) -> Result<(), WireError> {
    let height = statement.slots().height();
    let empty = statement.body().is_empty();
    let valid = match kind {
        ProofKind::SegmentLeaf => height == 0 && !empty,
        ProofKind::EmptyLeaf => height == 0 && empty,
        ProofKind::BinaryNode => height > 0,
    };
    if valid {
        Ok(())
    } else {
        Err(WireError::ProofKindStatementMismatch {
            kind,
            height,
            empty,
        })
    }
}

fn validate_wire_word_count(
    field: &'static str,
    expected: M31Word,
    actual: usize,
) -> Result<(), WireError> {
    validate_wire_count(field, wire_word_as_usize(field, expected)?, actual)
}

fn validate_wire_count(
    field: &'static str,
    expected: usize,
    actual: usize,
) -> Result<(), WireError> {
    if actual == expected {
        Ok(())
    } else {
        Err(WireError::WireShapeMismatch {
            field,
            expected,
            actual,
        })
    }
}

fn wire_word_as_usize(field: &'static str, value: M31Word) -> Result<usize, WireError> {
    usize::try_from(value.as_u32()).map_err(|_| WireError::WireShapeValueOutOfRange {
        field,
        value: value.as_u32(),
    })
}

impl<
    const N_COMMITMENTS: usize,
    const N_CLAIMED_SUMS: usize,
    const N_SAMPLED_VALUES: usize,
    const N_QUERY_VALUES: usize,
    const N_TRACE_PATHS: usize,
    const N_FRI_LAYERS: usize,
    const N_QUERIES: usize,
    const FOLD_WIDTH: usize,
    const N_LAST_LAYER_COEFFICIENTS: usize,
    const MAX_MERKLE_DEPTH: usize,
>
    RecursiveProofWire<
        N_COMMITMENTS,
        N_CLAIMED_SUMS,
        N_SAMPLED_VALUES,
        N_QUERY_VALUES,
        N_TRACE_PATHS,
        N_FRI_LAYERS,
        N_QUERIES,
        FOLD_WIDTH,
        N_LAST_LAYER_COEFFICIENTS,
        MAX_MERKLE_DEPTH,
    >
{
    /// Encodes the proof only when the caller's byte-array size is exact.
    pub fn encode<const N: usize>(&self) -> Result<RecursiveProofBytes<N>, WireError> {
        let expected = recursive_proof_bytes::<
            N_COMMITMENTS,
            N_CLAIMED_SUMS,
            N_SAMPLED_VALUES,
            N_QUERY_VALUES,
            N_TRACE_PATHS,
            N_FRI_LAYERS,
            N_QUERIES,
            FOLD_WIDTH,
            N_LAST_LAYER_COEFFICIENTS,
            MAX_MERKLE_DEPTH,
        >();
        if N != expected {
            return Err(WireError::ByteLength {
                expected,
                actual: N,
            });
        }

        let mut writer = Writer::with_capacity(expected);
        writer.write_m31_word(self.version.word());
        writer.write_u32(self.kind.tag());
        write_span_statement(&mut writer, &self.statement);
        write_fixed_stark_proof(&mut writer, &self.stark);
        let bytes = writer.finish();
        let actual = bytes.len();
        let bytes = bytes
            .try_into()
            .map_err(|_: Vec<u8>| WireError::ByteLength {
                expected: N,
                actual,
            })?;
        Ok(RecursiveProofBytes::new(bytes))
    }

    /// Decodes an exact-size byte array and reconstructs every checked type.
    pub fn decode<const N: usize>(bytes: &RecursiveProofBytes<N>) -> Result<Self, WireError> {
        let expected = recursive_proof_bytes::<
            N_COMMITMENTS,
            N_CLAIMED_SUMS,
            N_SAMPLED_VALUES,
            N_QUERY_VALUES,
            N_TRACE_PATHS,
            N_FRI_LAYERS,
            N_QUERIES,
            FOLD_WIDTH,
            N_LAST_LAYER_COEFFICIENTS,
            MAX_MERKLE_DEPTH,
        >();
        if N != expected {
            return Err(WireError::ByteLength {
                expected,
                actual: N,
            });
        }

        let mut reader = Reader::new(bytes.as_bytes());
        let version = ProtocolVersion(reader.read_m31_word()?);
        let kind_offset = reader.offset();
        let kind_tag = reader.read_u32()?;
        let kind = ProofKind::from_tag(kind_tag, kind_offset)?;
        let statement = read_span_statement(&mut reader)?;
        let stark = read_fixed_stark_proof(&mut reader)?;
        reader.finish()?;
        Self::new(version, kind, statement, stark)
    }
}

#[allow(clippy::too_many_arguments)]
fn write_fixed_stark_proof<
    const N_COMMITMENTS: usize,
    const N_CLAIMED_SUMS: usize,
    const N_SAMPLED_VALUES: usize,
    const N_QUERY_VALUES: usize,
    const N_TRACE_PATHS: usize,
    const N_FRI_LAYERS: usize,
    const N_QUERIES: usize,
    const FOLD_WIDTH: usize,
    const N_LAST_LAYER_COEFFICIENTS: usize,
    const MAX_MERKLE_DEPTH: usize,
>(
    writer: &mut Writer,
    proof: &FixedStarkProofWire<
        N_COMMITMENTS,
        N_CLAIMED_SUMS,
        N_SAMPLED_VALUES,
        N_QUERY_VALUES,
        N_TRACE_PATHS,
        N_FRI_LAYERS,
        N_QUERIES,
        FOLD_WIDTH,
        N_LAST_LAYER_COEFFICIENTS,
        MAX_MERKLE_DEPTH,
    >,
) {
    for commitment in proof.commitments {
        writer.write_digest(commitment);
    }
    for claimed_sum in proof.claimed_sums {
        writer.write_qm31(claimed_sum);
    }
    for sampled_value in proof.sampled_values {
        writer.write_qm31(sampled_value);
    }
    for queried_value in proof.queried_values.iter().copied() {
        writer.write_m31_word(queried_value);
    }
    for path in proof.trace_paths.iter() {
        write_merkle_path(writer, path);
    }
    for layer in proof.fri_layers.iter() {
        write_fri_layer(writer, layer);
    }
    for coefficient in proof.last_layer_coefficients {
        writer.write_qm31(coefficient);
    }
    writer.write_u64(proof.interaction_pow);
    writer.write_u64(proof.pcs_pow);
}

fn write_merkle_path<const MAX_DEPTH: usize>(
    writer: &mut Writer,
    path: &MerklePathWire<MAX_DEPTH>,
) {
    writer.write_u32(path.active_depth());
    for sibling in path.siblings() {
        writer.write_digest(*sibling);
    }
}

fn write_fri_layer<const N_QUERIES: usize, const FOLD_WIDTH: usize, const MAX_DEPTH: usize>(
    writer: &mut Writer,
    layer: &FriLayerWire<N_QUERIES, FOLD_WIDTH, MAX_DEPTH>,
) {
    writer.write_u32(layer.active_width());
    writer.write_digest(layer.commitment());
    for query in layer.queries() {
        for value in query.values() {
            writer.write_qm31(*value);
        }
        write_merkle_path(writer, query.path());
    }
}

fn write_span_statement(writer: &mut Writer, statement: &SpanStatement) {
    write_complete_execution(writer, statement.job().complete());
    writer.write_u32(statement.job().segment_count());
    writer.write_u64(statement.slots().first());
    writer.write_u32(u32::from(statement.slots().height()));
    match statement.body().executed_span() {
        None => {
            writer.write_u32(EMPTY_BODY_TAG);
            writer.write_zeros(EXECUTED_SPAN_BYTES);
        }
        Some(span) => {
            writer.write_u32(EXECUTED_BODY_TAG);
            write_executed_span(writer, span);
        }
    }
}

fn write_complete_execution(writer: &mut Writer, statement: &CompleteExecutionStatement) {
    writer.write_digest(statement.protocol().into_digest());
    writer.write_digest(statement.program().into_digest());
    write_machine_state(writer, &statement.initial_state());
    write_machine_state(writer, &statement.final_state());
    writer.write_digest(statement.public_input().into_digest());
    writer.write_digest(statement.public_output().into_digest());
    writer.write_u64(statement.total_cycles());
}

fn write_machine_state(writer: &mut Writer, state: &MachineState) {
    writer.write_u32(state.pc());
    for register in state.registers() {
        writer.write_u32(*register);
    }
    writer.write_digest(state.rw_memory().into_digest());
    writer.write_digest(state.public_io_state().into_digest());
}

fn write_executed_span(writer: &mut Writer, span: &ExecutedSpan) {
    writer.write_u32(span.first_segment());
    writer.write_u32(span.segment_count());
    writer.write_u64(span.first_cycle());
    writer.write_u64(span.cycle_count());
    write_machine_state(writer, &span.entry());
    write_machine_state(writer, &span.exit());
    write_edge_claim(writer, span.input());
    write_edge_claim(writer, span.output());
}

fn write_edge_claim(writer: &mut Writer, claim: EdgeClaim) {
    match claim.digest() {
        None => {
            writer.write_u32(ABSENT_TAG);
            writer.write_digest(Digest8::ZERO);
        }
        Some(digest) => {
            writer.write_u32(PRESENT_TAG);
            writer.write_digest(digest.into_digest());
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn read_fixed_stark_proof<
    const N_COMMITMENTS: usize,
    const N_CLAIMED_SUMS: usize,
    const N_SAMPLED_VALUES: usize,
    const N_QUERY_VALUES: usize,
    const N_TRACE_PATHS: usize,
    const N_FRI_LAYERS: usize,
    const N_QUERIES: usize,
    const FOLD_WIDTH: usize,
    const N_LAST_LAYER_COEFFICIENTS: usize,
    const MAX_MERKLE_DEPTH: usize,
>(
    reader: &mut Reader<'_>,
) -> Result<
    FixedStarkProofWire<
        N_COMMITMENTS,
        N_CLAIMED_SUMS,
        N_SAMPLED_VALUES,
        N_QUERY_VALUES,
        N_TRACE_PATHS,
        N_FRI_LAYERS,
        N_QUERIES,
        FOLD_WIDTH,
        N_LAST_LAYER_COEFFICIENTS,
        MAX_MERKLE_DEPTH,
    >,
    WireError,
> {
    let commitments = read_array(|| reader.read_digest())?;
    let claimed_sums = read_array(|| reader.read_qm31())?;
    let sampled_values = read_array(|| reader.read_qm31())?;
    let queried_values = Box::new(read_array(|| reader.read_m31_word())?);
    let trace_paths = Box::new(read_array(|| read_merkle_path(reader))?);
    let fri_layers = Box::new(read_array(|| read_fri_layer(reader))?);
    let last_layer_coefficients = read_array(|| reader.read_qm31())?;
    let interaction_pow = reader.read_u64()?;
    let pcs_pow = reader.read_u64()?;
    Ok(FixedStarkProofWire {
        commitments,
        claimed_sums,
        sampled_values,
        queried_values,
        trace_paths,
        fri_layers,
        last_layer_coefficients,
        interaction_pow,
        pcs_pow,
    })
}

fn read_merkle_path<const MAX_DEPTH: usize>(
    reader: &mut Reader<'_>,
) -> Result<MerklePathWire<MAX_DEPTH>, WireError> {
    let active_depth = reader.read_u32()?;
    let siblings = read_array(|| reader.read_digest())?;
    MerklePathWire::new(active_depth, siblings)
}

fn read_fri_layer<const N_QUERIES: usize, const FOLD_WIDTH: usize, const MAX_DEPTH: usize>(
    reader: &mut Reader<'_>,
) -> Result<FriLayerWire<N_QUERIES, FOLD_WIDTH, MAX_DEPTH>, WireError> {
    let active_width = reader.read_u32()?;
    let commitment = reader.read_digest()?;
    let queries = read_array(|| {
        let values = read_array(|| reader.read_qm31())?;
        let path = read_merkle_path(reader)?;
        Ok(FriQueryWire::new(values, path))
    })?;
    FriLayerWire::new(active_width, commitment, Box::new(queries))
}

fn read_span_statement(reader: &mut Reader<'_>) -> Result<SpanStatement, WireError> {
    let complete = read_complete_execution(reader)?;
    let segment_count = reader.read_u32()?;
    let job = JobContext::new(complete, segment_count)?;
    let first = reader.read_u64()?;
    let height_offset = reader.offset();
    let height_word = reader.read_u32()?;
    let height = u8::try_from(height_word).map_err(|_| WireError::SlotHeightWordOutOfRange {
        offset: height_offset,
        height: height_word,
    })?;
    let slots = SlotSpan::new(first, height)?;
    let body = read_span_body(reader)?;
    SpanStatement::new(job, slots, body).map_err(WireError::from)
}

fn read_complete_execution(
    reader: &mut Reader<'_>,
) -> Result<CompleteExecutionStatement, WireError> {
    let protocol = ProtocolId::from(reader.read_digest()?);
    let program = ProgramDigest::from(reader.read_digest()?);
    let initial_state = read_raw_machine_state(reader)?.into_checked()?;
    let final_state = read_raw_machine_state(reader)?.into_checked()?;
    let public_input = IoDigest::from(reader.read_digest()?);
    let public_output = IoDigest::from(reader.read_digest()?);
    let total_cycles = reader.read_u64()?;
    CompleteExecutionStatement::new(
        protocol,
        program,
        initial_state,
        final_state,
        public_input,
        public_output,
        total_cycles,
    )
    .map_err(WireError::from)
}

fn read_span_body(reader: &mut Reader<'_>) -> Result<SpanBody, WireError> {
    let tag_offset = reader.offset();
    let tag = reader.read_u32()?;
    if tag != EMPTY_BODY_TAG && tag != EXECUTED_BODY_TAG {
        return Err(WireError::UnknownSpanBodyTag {
            offset: tag_offset,
            tag,
        });
    }

    let payload_offset = reader.offset();
    let raw = read_raw_executed_span(reader)?;
    if tag == EMPTY_BODY_TAG {
        if let Some(index) = reader.bytes[payload_offset..reader.offset()]
            .iter()
            .position(|byte| *byte != 0)
        {
            return Err(WireError::NonZeroSpanPadding {
                offset: payload_offset + index,
            });
        }
        Ok(SpanBody::empty())
    } else {
        raw.into_checked().map(SpanBody::executed)
    }
}

fn read_raw_executed_span(reader: &mut Reader<'_>) -> Result<RawExecutedSpan, WireError> {
    Ok(RawExecutedSpan {
        first_segment: reader.read_u32()?,
        segment_count: reader.read_u32()?,
        first_cycle: reader.read_u64()?,
        cycle_count: reader.read_u64()?,
        entry: read_raw_machine_state(reader)?,
        exit: read_raw_machine_state(reader)?,
        input: read_raw_edge_claim(reader)?,
        output: read_raw_edge_claim(reader)?,
    })
}

fn read_raw_machine_state(reader: &mut Reader<'_>) -> Result<RawMachineState, WireError> {
    let pc = reader.read_u32()?;
    let registers = read_array(|| reader.read_u32())?;
    let rw_memory = MemoryDigest::from(reader.read_digest()?);
    let public_io_state = IoDigest::from(reader.read_digest()?);
    Ok(RawMachineState {
        pc,
        registers,
        rw_memory,
        public_io_state,
    })
}

fn read_raw_edge_claim(reader: &mut Reader<'_>) -> Result<RawEdgeClaim, WireError> {
    let tag_offset = reader.offset();
    let tag = reader.read_u32()?;
    let digest_offset = reader.offset();
    let digest = IoDigest::from(reader.read_digest()?);
    Ok(RawEdgeClaim {
        tag,
        tag_offset,
        digest,
        digest_offset,
    })
}

fn read_array<T, const N: usize>(
    mut read: impl FnMut() -> Result<T, WireError>,
) -> Result<[T; N], WireError> {
    let mut values = Vec::with_capacity(N);
    for _ in 0..N {
        values.push(read()?);
    }
    match values.try_into() {
        Ok(array) => Ok(array),
        Err(_) => unreachable!("the decoder fills exactly the fixed array length"),
    }
}

#[derive(Clone, Copy, Debug)]
struct RawMachineState {
    pc: u32,
    registers: [u32; 32],
    rw_memory: MemoryDigest,
    public_io_state: IoDigest,
}

impl RawMachineState {
    fn into_checked(self) -> Result<MachineState, WireError> {
        MachineState::new(
            self.pc,
            self.registers,
            self.rw_memory,
            self.public_io_state,
        )
        .map_err(WireError::from)
    }
}

#[derive(Clone, Copy, Debug)]
struct RawEdgeClaim {
    tag: u32,
    tag_offset: usize,
    digest: IoDigest,
    digest_offset: usize,
}

impl RawEdgeClaim {
    fn into_checked(self) -> Result<EdgeClaim, WireError> {
        match self.tag {
            ABSENT_TAG if self.digest.into_digest() == Digest8::ZERO => Ok(EdgeClaim::absent()),
            ABSENT_TAG => Err(WireError::NonZeroEdgePadding {
                offset: self.digest_offset,
            }),
            PRESENT_TAG => Ok(EdgeClaim::present(self.digest)),
            tag => Err(WireError::UnknownEdgeTag {
                offset: self.tag_offset,
                tag,
            }),
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct RawExecutedSpan {
    first_segment: u32,
    segment_count: u32,
    first_cycle: u64,
    cycle_count: u64,
    entry: RawMachineState,
    exit: RawMachineState,
    input: RawEdgeClaim,
    output: RawEdgeClaim,
}

impl RawExecutedSpan {
    fn into_checked(self) -> Result<ExecutedSpan, WireError> {
        ExecutedSpan::new(
            self.first_segment,
            self.segment_count,
            self.first_cycle,
            self.cycle_count,
            self.entry.into_checked()?,
            self.exit.into_checked()?,
            self.input.into_checked()?,
            self.output.into_checked()?,
        )
        .map_err(WireError::from)
    }
}

struct Writer {
    bytes: Vec<u8>,
}

impl Writer {
    fn with_capacity(capacity: usize) -> Self {
        Self {
            bytes: Vec::with_capacity(capacity),
        }
    }

    fn write_u32(&mut self, value: u32) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    fn write_u64(&mut self, value: u64) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    fn write_m31_word(&mut self, value: M31Word) {
        self.write_u32(value.as_u32());
    }

    fn write_digest(&mut self, digest: Digest8) {
        for word in digest.words() {
            self.write_m31_word(*word);
        }
    }

    fn write_qm31(&mut self, value: Qm31Wire) {
        for word in value.words() {
            self.write_m31_word(*word);
        }
    }

    fn write_zeros(&mut self, count: usize) {
        self.bytes.resize(self.bytes.len() + count, 0);
    }

    fn finish(self) -> Vec<u8> {
        self.bytes
    }
}

struct Reader<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> Reader<'a> {
    const fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    const fn offset(&self) -> usize {
        self.offset
    }

    fn take<const N: usize>(&mut self) -> Result<[u8; N], WireError> {
        let remaining = self.bytes.len().saturating_sub(self.offset);
        let end = self
            .offset
            .checked_add(N)
            .filter(|end| *end <= self.bytes.len())
            .ok_or(WireError::UnexpectedEof {
                offset: self.offset,
                needed: N,
                remaining,
            })?;
        let bytes = self.bytes[self.offset..end]
            .try_into()
            .expect("the checked slice has the requested fixed length");
        self.offset = end;
        Ok(bytes)
    }

    fn read_u32(&mut self) -> Result<u32, WireError> {
        self.take().map(u32::from_le_bytes)
    }

    fn read_u64(&mut self) -> Result<u64, WireError> {
        self.take().map(u64::from_le_bytes)
    }

    fn read_m31_word(&mut self) -> Result<M31Word, WireError> {
        let offset = self.offset;
        let value = self.read_u32()?;
        M31Word::try_from(value).map_err(|source| WireError::NonCanonicalM31 { offset, source })
    }

    fn read_digest(&mut self) -> Result<Digest8, WireError> {
        read_array(|| self.read_m31_word()).map(Digest8::new)
    }

    fn read_qm31(&mut self) -> Result<Qm31Wire, WireError> {
        read_array(|| self.read_m31_word()).map(Qm31Wire::new)
    }

    fn finish(self) -> Result<(), WireError> {
        if self.offset == self.bytes.len() {
            Ok(())
        } else {
            Err(WireError::TrailingBytes {
                offset: self.offset,
                total: self.bytes.len(),
            })
        }
    }
}

/// A precise rejection reason for non-canonical or malformed proof bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WireError {
    ByteLength {
        expected: usize,
        actual: usize,
    },
    UnexpectedEof {
        offset: usize,
        needed: usize,
        remaining: usize,
    },
    TrailingBytes {
        offset: usize,
        total: usize,
    },
    NonCanonicalM31 {
        offset: usize,
        source: NonCanonicalM31Word,
    },
    UnknownProofKind {
        offset: usize,
        tag: u32,
    },
    UnknownSpanBodyTag {
        offset: usize,
        tag: u32,
    },
    UnknownEdgeTag {
        offset: usize,
        tag: u32,
    },
    SlotHeightWordOutOfRange {
        offset: usize,
        height: u32,
    },
    NonZeroSpanPadding {
        offset: usize,
    },
    NonZeroEdgePadding {
        offset: usize,
    },
    MerkleDepthOutOfRange {
        active_depth: u32,
        max_depth: usize,
    },
    NonZeroMerklePadding {
        index: usize,
    },
    FriFoldWidthOutOfRange {
        active_width: u32,
        max_width: usize,
    },
    NonZeroFriValuePadding {
        query: usize,
        index: usize,
    },
    WireShapeValueOutOfRange {
        field: &'static str,
        value: u32,
    },
    WireShapeArithmeticOverflow {
        field: &'static str,
    },
    WireShapeMismatch {
        field: &'static str,
        expected: usize,
        actual: usize,
    },
    MerklePathDepthMismatch {
        path: usize,
        expected: u32,
        actual: u32,
    },
    FriLayerWidthMismatch {
        layer: usize,
        expected: u32,
        actual: u32,
    },
    InvalidFriPathGeometry {
        layer: usize,
        tree_height: u32,
        fold_width: u32,
    },
    FriPathDepthMismatch {
        layer: usize,
        query: usize,
        expected: u32,
        actual: u32,
    },
    ProofKindStatementMismatch {
        kind: ProofKind,
        height: u8,
        empty: bool,
    },
    Statement(StatementError),
}

impl From<StatementError> for WireError {
    fn from(source: StatementError) -> Self {
        Self::Statement(source)
    }
}

impl fmt::Display for WireError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ByteLength { expected, actual } => {
                write!(
                    formatter,
                    "proof length is {actual} bytes, expected {expected}"
                )
            }
            Self::UnexpectedEof {
                offset,
                needed,
                remaining,
            } => write!(
                formatter,
                "proof ends at byte {offset}: need {needed} bytes, only {remaining} remain"
            ),
            Self::TrailingBytes { offset, total } => write!(
                formatter,
                "proof decoder stopped at byte {offset} of {total}"
            ),
            Self::NonCanonicalM31 { offset, source } => {
                write!(
                    formatter,
                    "non-canonical M31 word at byte {offset}: {source}"
                )
            }
            Self::UnknownProofKind { offset, tag } => {
                write!(formatter, "unknown proof-kind tag {tag} at byte {offset}")
            }
            Self::UnknownSpanBodyTag { offset, tag } => {
                write!(formatter, "unknown span-body tag {tag} at byte {offset}")
            }
            Self::UnknownEdgeTag { offset, tag } => {
                write!(formatter, "unknown edge-claim tag {tag} at byte {offset}")
            }
            Self::SlotHeightWordOutOfRange { offset, height } => write!(
                formatter,
                "slot height {height} at byte {offset} does not fit in u8"
            ),
            Self::NonZeroSpanPadding { offset } => {
                write!(formatter, "empty-span padding is nonzero at byte {offset}")
            }
            Self::NonZeroEdgePadding { offset } => {
                write!(formatter, "absent-edge padding is nonzero at byte {offset}")
            }
            Self::MerkleDepthOutOfRange {
                active_depth,
                max_depth,
            } => write!(
                formatter,
                "Merkle depth {active_depth} exceeds fixed maximum {max_depth}"
            ),
            Self::NonZeroMerklePadding { index } => {
                write!(formatter, "inactive Merkle sibling {index} is nonzero")
            }
            Self::FriFoldWidthOutOfRange {
                active_width,
                max_width,
            } => write!(
                formatter,
                "FRI fold width {active_width} is outside 1..={max_width}"
            ),
            Self::NonZeroFriValuePadding { query, index } => write!(
                formatter,
                "inactive FRI value {index} in query {query} is nonzero"
            ),
            Self::WireShapeValueOutOfRange { field, value } => {
                write!(
                    formatter,
                    "manifest {field} value {value} does not fit usize"
                )
            }
            Self::WireShapeArithmeticOverflow { field } => {
                write!(formatter, "manifest {field} overflows usize")
            }
            Self::WireShapeMismatch {
                field,
                expected,
                actual,
            } => write!(
                formatter,
                "wire {field} is {actual}, manifest requires {expected}"
            ),
            Self::MerklePathDepthMismatch {
                path,
                expected,
                actual,
            } => write!(
                formatter,
                "trace path {path} has depth {actual}, manifest requires {expected}"
            ),
            Self::FriLayerWidthMismatch {
                layer,
                expected,
                actual,
            } => write!(
                formatter,
                "FRI layer {layer} has fold width {actual}, manifest requires {expected}"
            ),
            Self::InvalidFriPathGeometry {
                layer,
                tree_height,
                fold_width,
            } => write!(
                formatter,
                "FRI layer {layer} cannot authenticate fold width {fold_width} in tree height {tree_height}"
            ),
            Self::FriPathDepthMismatch {
                layer,
                query,
                expected,
                actual,
            } => write!(
                formatter,
                "FRI layer {layer} query {query} has path depth {actual}, manifest requires {expected}"
            ),
            Self::ProofKindStatementMismatch {
                kind,
                height,
                empty,
            } => write!(
                formatter,
                "proof kind {kind:?} does not match height {height} and empty={empty}"
            ),
            Self::Statement(source) => write!(formatter, "invalid recursion statement: {source}"),
        }
    }
}

impl std::error::Error for WireError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::NonCanonicalM31 { source, .. } => Some(source),
            Self::Statement(source) => Some(source),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use rstest::rstest;
    use stwo::core::fields::m31::P as M31_MODULUS;

    use super::*;

    const N_COMMITMENTS: usize = 1;
    const N_CLAIMED_SUMS: usize = 1;
    const N_SAMPLED_VALUES: usize = 1;
    const N_QUERY_VALUES: usize = 1;
    const N_TRACE_PATHS: usize = 1;
    const N_FRI_LAYERS: usize = 1;
    const N_QUERIES: usize = 1;
    const FOLD_WIDTH: usize = 2;
    const N_LAST_LAYER_COEFFICIENTS: usize = 1;
    const MAX_MERKLE_DEPTH: usize = 2;
    const TEST_PROOF_BYTES: usize = recursive_proof_bytes::<
        N_COMMITMENTS,
        N_CLAIMED_SUMS,
        N_SAMPLED_VALUES,
        N_QUERY_VALUES,
        N_TRACE_PATHS,
        N_FRI_LAYERS,
        N_QUERIES,
        FOLD_WIDTH,
        N_LAST_LAYER_COEFFICIENTS,
        MAX_MERKLE_DEPTH,
    >();

    type TestProof = RecursiveProofWire<
        N_COMMITMENTS,
        N_CLAIMED_SUMS,
        N_SAMPLED_VALUES,
        N_QUERY_VALUES,
        N_TRACE_PATHS,
        N_FRI_LAYERS,
        N_QUERIES,
        FOLD_WIDTH,
        N_LAST_LAYER_COEFFICIENTS,
        MAX_MERKLE_DEPTH,
    >;
    type TestProofBytes = RecursiveProofBytes<TEST_PROOF_BYTES>;

    const TRACE_PATH_OFFSET: usize = STARK_PROOF_OFFSET
        + N_COMMITMENTS * DIGEST_BYTES
        + N_CLAIMED_SUMS * QM31_BYTES
        + N_SAMPLED_VALUES * QM31_BYTES
        + N_QUERY_VALUES * M31_WORD_BYTES;
    const FRI_LAYER_OFFSET: usize =
        TRACE_PATH_OFFSET + N_TRACE_PATHS * merkle_path_bytes(MAX_MERKLE_DEPTH);
    const SLOT_HEIGHT_OFFSET: usize = STATEMENT_OFFSET + JOB_CONTEXT_BYTES + U64_BYTES;
    const INPUT_EDGE_TAG_IN_EXECUTED_SPAN: usize =
        2 * U32_BYTES + 2 * U64_BYTES + 2 * MACHINE_STATE_BYTES;
    const INPUT_EDGE_DIGEST_IN_EXECUTED_SPAN: usize = INPUT_EDGE_TAG_IN_EXECUTED_SPAN + U32_BYTES;

    fn digest(seed: u16) -> Digest8 {
        Digest8::new([
            M31Word::from(seed),
            M31Word::from(seed + 1),
            M31Word::from(seed + 2),
            M31Word::from(seed + 3),
            M31Word::from(seed + 4),
            M31Word::from(seed + 5),
            M31Word::from(seed + 6),
            M31Word::from(seed + 7),
        ])
    }

    fn qm31(seed: u16) -> Qm31Wire {
        Qm31Wire::new([
            M31Word::from(seed),
            M31Word::from(seed + 1),
            M31Word::from(seed + 2),
            M31Word::from(seed + 3),
        ])
    }

    fn state(register: u32, seed: u16) -> MachineState {
        let mut registers = [0_u32; 32];
        registers[1] = register;
        MachineState::new(
            u32::from(seed) * 4,
            registers,
            MemoryDigest::from(digest(seed + 10)),
            IoDigest::from(digest(seed + 20)),
        )
        .expect("the fixture preserves the immutable zero register")
    }

    fn complete(final_register: u32, total_cycles: u64) -> CompleteExecutionStatement {
        CompleteExecutionStatement::new(
            ProtocolId::from(digest(1)),
            ProgramDigest::from(digest(2)),
            state(0, 10),
            state(final_register, 30),
            IoDigest::from(digest(3)),
            IoDigest::from(digest(4)),
            total_cycles,
        )
        .expect("the fixture execution has a nonzero cycle count")
    }

    fn segment_statement(final_register: u32) -> SpanStatement {
        let complete = complete(final_register, 7);
        let job = JobContext::new(complete, 1).expect("the fixture contains one segment");
        let span = ExecutedSpan::new(
            0,
            1,
            0,
            7,
            complete.initial_state(),
            complete.final_state(),
            EdgeClaim::present(complete.public_input()),
            EdgeClaim::present(complete.public_output()),
        )
        .expect("the fixture span has nonzero ranges");
        SpanStatement::segment_leaf(job, 0, span).expect("the fixture leaf covers its job")
    }

    fn empty_statement() -> SpanStatement {
        let job = JobContext::new(complete(3, 12), 3).expect("the fixture contains segments");
        SpanStatement::empty_leaf(job, 3).expect("the last slot is canonical padding")
    }

    fn interior_statement() -> SpanStatement {
        let job = JobContext::new(complete(3, 12), 3).expect("the fixture contains segments");
        let span = ExecutedSpan::new(
            1,
            1,
            4,
            4,
            state(1, 40),
            state(2, 50),
            EdgeClaim::absent(),
            EdgeClaim::absent(),
        )
        .expect("the fixture span has nonzero ranges");
        SpanStatement::segment_leaf(job, 1, span).expect("the interior leaf has no public edges")
    }

    fn binary_statement() -> SpanStatement {
        let complete = complete(2, 8);
        let job = JobContext::new(complete, 2).expect("the fixture contains two segments");
        let middle = state(1, 20);
        let left_span = ExecutedSpan::new(
            0,
            1,
            0,
            4,
            complete.initial_state(),
            middle,
            EdgeClaim::present(complete.public_input()),
            EdgeClaim::absent(),
        )
        .expect("the left fixture span has nonzero ranges");
        let right_span = ExecutedSpan::new(
            1,
            1,
            4,
            4,
            middle,
            complete.final_state(),
            EdgeClaim::absent(),
            EdgeClaim::present(complete.public_output()),
        )
        .expect("the right fixture span has nonzero ranges");
        let left =
            SpanStatement::segment_leaf(job, 0, left_span).expect("the left leaf starts the job");
        let right =
            SpanStatement::segment_leaf(job, 1, right_span).expect("the right leaf ends the job");
        SpanStatement::fold(&left, &right).expect("the fixture leaves form one binary statement")
    }

    fn stark_proof() -> FixedStarkProofWire<
        N_COMMITMENTS,
        N_CLAIMED_SUMS,
        N_SAMPLED_VALUES,
        N_QUERY_VALUES,
        N_TRACE_PATHS,
        N_FRI_LAYERS,
        N_QUERIES,
        FOLD_WIDTH,
        N_LAST_LAYER_COEFFICIENTS,
        MAX_MERKLE_DEPTH,
    > {
        let trace_path = MerklePathWire::new(2, [digest(80), digest(81)])
            .expect("the trace path fills the fixed maximum depth");
        let fri_path = MerklePathWire::new(1, [digest(100), Digest8::ZERO])
            .expect("the FRI path authenticates above the complete fold pair");
        let query = FriQueryWire::new([qm31(90), qm31(94)], fri_path);
        let layer = FriLayerWire::new(2, digest(110), Box::new([query]))
            .expect("the FRI query fills the fixed maximum width");
        FixedStarkProofWire {
            commitments: [digest(60)],
            claimed_sums: [qm31(61)],
            sampled_values: [qm31(65)],
            queried_values: Box::new([M31Word::from(70)]),
            trace_paths: Box::new([trace_path]),
            fri_layers: Box::new([layer]),
            last_layer_coefficients: [qm31(120)],
            interaction_pow: 0x1122_3344_5566_7788,
            pcs_pow: 0x8877_6655_4433_2211,
        }
    }

    fn proof(kind: ProofKind, statement: SpanStatement) -> TestProof {
        TestProof::new(
            ProtocolVersion(M31Word::from(2)),
            kind,
            statement,
            stark_proof(),
        )
        .expect("the fixture kind matches its statement")
    }

    fn segment_proof(final_register: u32) -> TestProof {
        proof(ProofKind::SegmentLeaf, segment_statement(final_register))
    }

    fn empty_proof() -> TestProof {
        proof(ProofKind::EmptyLeaf, empty_statement())
    }

    fn proof_shape() -> FixedProofShape<1, 1, 1> {
        FixedProofShape {
            claimed_sum_count: M31Word::from(1),
            sampled_value_count: M31Word::from(1),
            queried_value_count: M31Word::from(1),
            trace_path_count: M31Word::from(1),
            raw_query_count: M31Word::from(1),
            last_layer_coefficient_count: M31Word::from(1),
            table_log_sizes: [M31Word::from(8)],
            tree_heights: [M31Word::from(2)],
            fri_layer_fold_widths: [M31Word::from(2)],
            fri_layer_tree_heights: [M31Word::from(2)],
        }
    }

    #[rstest]
    fn fixed_profile_has_a_stable_exact_length() {
        assert_eq!(TEST_PROOF_BYTES, 1_348);
    }

    #[rstest]
    fn fixed_stark_wire_matches_its_manifest_shape() {
        assert_eq!(stark_proof().validate_against_shape(&proof_shape()), Ok(()));
    }

    #[rstest]
    fn fixed_stark_wire_rejects_a_manifest_count_mismatch() {
        let mut shape = proof_shape();
        shape.claimed_sum_count = M31Word::from(2);
        assert_eq!(
            stark_proof().validate_against_shape(&shape),
            Err(WireError::WireShapeMismatch {
                field: "claimed sums",
                expected: 2,
                actual: N_CLAIMED_SUMS,
            })
        );
    }

    #[rstest]
    fn fixed_stark_wire_rejects_a_trace_path_depth_mismatch() {
        let mut proof = stark_proof();
        proof.trace_paths[0] = MerklePathWire::new(1, [digest(80), Digest8::ZERO])
            .expect("the substituted path fits the maximum wire depth");
        assert_eq!(
            proof.validate_against_shape(&proof_shape()),
            Err(WireError::MerklePathDepthMismatch {
                path: 0,
                expected: 2,
                actual: 1,
            })
        );
    }

    #[rstest]
    fn fixed_stark_wire_rejects_a_full_tree_fri_path() {
        let mut proof = stark_proof();
        proof.fri_layers[0].queries[0].path = MerklePathWire::new(2, [digest(100), digest(101)])
            .expect("the substituted path fits the maximum wire depth");
        assert_eq!(
            proof.validate_against_shape(&proof_shape()),
            Err(WireError::FriPathDepthMismatch {
                layer: 0,
                query: 0,
                expected: 1,
                actual: 2,
            })
        );
    }

    #[rstest]
    fn segment_leaf_round_trips() {
        let proof = segment_proof(1);
        let encoded = proof
            .encode::<TEST_PROOF_BYTES>()
            .expect("the byte count matches the fixed profile");
        assert_eq!(TestProof::decode(&encoded), Ok(proof));
    }

    #[rstest]
    fn empty_leaf_round_trips() {
        let proof = empty_proof();
        let encoded = proof
            .encode::<TEST_PROOF_BYTES>()
            .expect("the byte count matches the fixed profile");
        assert_eq!(TestProof::decode(&encoded), Ok(proof));
    }

    #[rstest]
    fn binary_node_round_trips() {
        let proof = proof(ProofKind::BinaryNode, binary_statement());
        let encoded = proof
            .encode::<TEST_PROOF_BYTES>()
            .expect("the byte count matches the fixed profile");
        assert_eq!(TestProof::decode(&encoded), Ok(proof));
    }

    #[rstest]
    fn raw_rv32_register_word_round_trips_without_field_reduction() {
        let proof = segment_proof(u32::MAX);
        let encoded = proof
            .encode::<TEST_PROOF_BYTES>()
            .expect("the byte count matches the fixed profile");
        let decoded = TestProof::decode(&encoded).expect("the encoded proof is canonical");
        assert_eq!(
            decoded
                .statement()
                .body()
                .executed_span()
                .expect("the proof is a segment leaf")
                .exit()
                .registers()[1],
            u32::MAX
        );
    }

    #[rstest]
    #[case::truncated(false)]
    #[case::trailing(true)]
    fn exact_proof_bytes_reject_a_wrong_length(#[case] trailing: bool) {
        let encoded = segment_proof(1)
            .encode::<TEST_PROOF_BYTES>()
            .expect("the byte count matches the fixed profile");
        let mut raw = encoded.as_bytes().to_vec();
        if trailing {
            raw.push(0);
        } else {
            raw.truncate(raw.len() - 1);
        }
        assert_eq!(
            TestProofBytes::try_from_slice(&raw),
            Err(WireError::ByteLength {
                expected: TEST_PROOF_BYTES,
                actual: raw.len(),
            })
        );
    }

    #[rstest]
    fn decoder_rejects_a_non_canonical_commitment_limb() {
        let mut raw = segment_proof(1)
            .encode::<TEST_PROOF_BYTES>()
            .expect("the byte count matches the fixed profile")
            .into_bytes();
        raw[STARK_PROOF_OFFSET..STARK_PROOF_OFFSET + U32_BYTES]
            .copy_from_slice(&M31_MODULUS.to_le_bytes());
        assert!(matches!(
            TestProof::decode(&TestProofBytes::new(raw)),
            Err(WireError::NonCanonicalM31 { offset: STARK_PROOF_OFFSET, source })
                if source.value() == M31_MODULUS
        ));
    }

    #[rstest]
    fn decoder_rejects_an_unknown_proof_kind() {
        let mut raw = segment_proof(1)
            .encode::<TEST_PROOF_BYTES>()
            .expect("the byte count matches the fixed profile")
            .into_bytes();
        raw[U32_BYTES..2 * U32_BYTES].copy_from_slice(&9_u32.to_le_bytes());
        assert_eq!(
            TestProof::decode(&TestProofBytes::new(raw)),
            Err(WireError::UnknownProofKind {
                offset: U32_BYTES,
                tag: 9,
            })
        );
    }

    #[rstest]
    fn decoder_rejects_an_unknown_span_body_tag() {
        let mut raw = segment_proof(1)
            .encode::<TEST_PROOF_BYTES>()
            .expect("the byte count matches the fixed profile")
            .into_bytes();
        raw[SPAN_BODY_TAG_OFFSET..SPAN_BODY_TAG_OFFSET + U32_BYTES]
            .copy_from_slice(&2_u32.to_le_bytes());
        assert_eq!(
            TestProof::decode(&TestProofBytes::new(raw)),
            Err(WireError::UnknownSpanBodyTag {
                offset: SPAN_BODY_TAG_OFFSET,
                tag: 2,
            })
        );
    }

    #[rstest]
    fn decoder_rejects_a_kind_statement_mismatch() {
        let mut raw = segment_proof(1)
            .encode::<TEST_PROOF_BYTES>()
            .expect("the byte count matches the fixed profile")
            .into_bytes();
        raw[U32_BYTES..2 * U32_BYTES].copy_from_slice(&ProofKind::BinaryNode.tag().to_le_bytes());
        assert_eq!(
            TestProof::decode(&TestProofBytes::new(raw)),
            Err(WireError::ProofKindStatementMismatch {
                kind: ProofKind::BinaryNode,
                height: 0,
                empty: false,
            })
        );
    }

    #[rstest]
    fn decoder_rejects_nonzero_empty_span_padding() {
        let mut raw = empty_proof()
            .encode::<TEST_PROOF_BYTES>()
            .expect("the byte count matches the fixed profile")
            .into_bytes();
        let offset = SPAN_BODY_PAYLOAD_OFFSET;
        raw[offset] = 1;
        assert_eq!(
            TestProof::decode(&TestProofBytes::new(raw)),
            Err(WireError::NonZeroSpanPadding { offset })
        );
    }

    #[rstest]
    fn decoder_rejects_nonzero_absent_edge_padding() {
        let mut raw = proof(ProofKind::SegmentLeaf, interior_statement())
            .encode::<TEST_PROOF_BYTES>()
            .expect("the byte count matches the fixed profile")
            .into_bytes();
        let offset = SPAN_BODY_PAYLOAD_OFFSET + INPUT_EDGE_DIGEST_IN_EXECUTED_SPAN;
        raw[offset] = 1;
        assert_eq!(
            TestProof::decode(&TestProofBytes::new(raw)),
            Err(WireError::NonZeroEdgePadding { offset })
        );
    }

    #[rstest]
    fn decoder_rejects_an_unknown_edge_tag() {
        let mut raw = proof(ProofKind::SegmentLeaf, interior_statement())
            .encode::<TEST_PROOF_BYTES>()
            .expect("the byte count matches the fixed profile")
            .into_bytes();
        let offset = SPAN_BODY_PAYLOAD_OFFSET + INPUT_EDGE_TAG_IN_EXECUTED_SPAN;
        raw[offset..offset + U32_BYTES].copy_from_slice(&2_u32.to_le_bytes());
        assert_eq!(
            TestProof::decode(&TestProofBytes::new(raw)),
            Err(WireError::UnknownEdgeTag { offset, tag: 2 })
        );
    }

    #[rstest]
    fn decoder_rejects_a_slot_height_that_does_not_fit_the_statement_type() {
        let mut raw = segment_proof(1)
            .encode::<TEST_PROOF_BYTES>()
            .expect("the byte count matches the fixed profile")
            .into_bytes();
        raw[SLOT_HEIGHT_OFFSET..SLOT_HEIGHT_OFFSET + U32_BYTES]
            .copy_from_slice(&256_u32.to_le_bytes());
        assert_eq!(
            TestProof::decode(&TestProofBytes::new(raw)),
            Err(WireError::SlotHeightWordOutOfRange {
                offset: SLOT_HEIGHT_OFFSET,
                height: 256,
            })
        );
    }

    #[rstest]
    fn decoder_rejects_nonzero_inactive_merkle_siblings() {
        let mut raw = segment_proof(1)
            .encode::<TEST_PROOF_BYTES>()
            .expect("the byte count matches the fixed profile")
            .into_bytes();
        raw[TRACE_PATH_OFFSET..TRACE_PATH_OFFSET + U32_BYTES].copy_from_slice(&1_u32.to_le_bytes());
        assert_eq!(
            TestProof::decode(&TestProofBytes::new(raw)),
            Err(WireError::NonZeroMerklePadding { index: 1 })
        );
    }

    #[rstest]
    fn decoder_rejects_a_merkle_depth_above_the_fixed_maximum() {
        let mut raw = segment_proof(1)
            .encode::<TEST_PROOF_BYTES>()
            .expect("the byte count matches the fixed profile")
            .into_bytes();
        raw[TRACE_PATH_OFFSET..TRACE_PATH_OFFSET + U32_BYTES].copy_from_slice(&3_u32.to_le_bytes());
        assert_eq!(
            TestProof::decode(&TestProofBytes::new(raw)),
            Err(WireError::MerkleDepthOutOfRange {
                active_depth: 3,
                max_depth: MAX_MERKLE_DEPTH,
            })
        );
    }

    #[rstest]
    fn decoder_rejects_nonzero_inactive_fri_values() {
        let mut raw = segment_proof(1)
            .encode::<TEST_PROOF_BYTES>()
            .expect("the byte count matches the fixed profile")
            .into_bytes();
        raw[FRI_LAYER_OFFSET..FRI_LAYER_OFFSET + U32_BYTES].copy_from_slice(&1_u32.to_le_bytes());
        assert_eq!(
            TestProof::decode(&TestProofBytes::new(raw)),
            Err(WireError::NonZeroFriValuePadding { query: 0, index: 1 })
        );
    }

    #[rstest]
    #[case::zero(0)]
    #[case::above_maximum(3)]
    fn decoder_rejects_an_invalid_fri_fold_width(#[case] active_width: u32) {
        let mut raw = segment_proof(1)
            .encode::<TEST_PROOF_BYTES>()
            .expect("the byte count matches the fixed profile")
            .into_bytes();
        raw[FRI_LAYER_OFFSET..FRI_LAYER_OFFSET + U32_BYTES]
            .copy_from_slice(&active_width.to_le_bytes());
        assert_eq!(
            TestProof::decode(&TestProofBytes::new(raw)),
            Err(WireError::FriFoldWidthOutOfRange {
                active_width,
                max_width: FOLD_WIDTH,
            })
        );
    }
}
