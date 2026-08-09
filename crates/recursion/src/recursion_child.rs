//! Checked encoding of a native universal proof as one recursion-child wire.
//!
//! STWO deduplicates queries and authentication nodes in its native proof. The
//! retained prover auxiliary maps expand that compressed representation into
//! the fixed independent-query layout consumed by the recursion verifier AIR.

use core::fmt;
use std::collections::BTreeSet;

use air::digest::{Digest8, M31Word};
use prover::poseidon2_channel::{Poseidon2M31Hash, Poseidon2M31MerkleHasher};
use stwo::core::pcs::quotients::CommitmentSchemeProofAux;
use stwo::core::pcs::utils::prepare_preprocessed_query_positions;
use stwo::core::proof::StarkProof;
use stwo::core::vcs_lifted::verifier::LOG_PACKED_LEAF_SIZE;

use crate::profile::{
    FRI_QUERY_COUNT, FrozenProtocolProfile, MAX_FRI_FOLD_WIDTH, RECURSION_FRI_LAYER_COUNT,
    RECURSION_MAX_MERKLE_DEPTH, RECURSION_QUERY_VALUE_COUNT, RECURSION_TRACE_PATH_COUNT,
    RecursionStarkProofWire, RootProofWire,
};
use crate::recursive_proof::RecursionProof;
use crate::wire::{FriLayerWire, FriQueryWire, MerklePathWire, ProofKind, Qm31Wire, WireError};

/// Encodes one verified-shape native recursion proof for use as a child.
pub fn adapt_recursion_child(
    profile: &FrozenProtocolProfile,
    proof: &RecursionProof,
) -> Result<Box<RootProofWire>, RecursionChildError> {
    let manifest = profile.manifest();
    if proof.protocol != manifest.protocol_id()
        || proof.statement.job().complete().protocol() != manifest.protocol_id()
    {
        return Err(RecursionChildError::ProtocolMismatch);
    }
    if proof.component_claim.log_sizes != *profile.recursion_program().component_log_sizes() {
        return Err(RecursionChildError::ComponentLogSizeMismatch);
    }
    if proof.interaction_claim.log_sizes != profile.recursion_program().column_log_sizes()[2] {
        return Err(RecursionChildError::InteractionLogSizeMismatch);
    }
    let expected_kind = proof_kind_for_statement(&proof.statement);
    if proof.component_claim.proof_kind != expected_kind {
        return Err(RecursionChildError::ProofKindMismatch);
    }

    let stark = adapt_recursion_stark_proof(profile, proof)?;
    stark
        .validate_against_shape(&manifest.manifest().recursion_proof_shape)
        .map_err(RecursionChildError::Wire)?;
    let wire = RootProofWire::new(
        manifest.manifest().version,
        expected_kind,
        proof.statement,
        stark,
    )?;
    Ok(Box::new(wire))
}

fn adapt_recursion_stark_proof(
    profile: &FrozenProtocolProfile,
    proof: &RecursionProof,
) -> Result<RecursionStarkProofWire, RecursionChildError> {
    let stark = &proof.stark_proof;
    let aux = &proof.stark_aux;
    if stark.config != profile.manifest().recursion_pcs().config() {
        return Err(RecursionChildError::PcsConfigMismatch);
    }
    validate_topology(profile, proof)?;

    let commitments = stark
        .commitments
        .iter()
        .copied()
        .enumerate()
        .map(|(index, hash)| proof_digest("trace commitment", index, hash))
        .collect::<Result<Vec<_>, _>>()?
        .try_into()
        .map_err(|values: Vec<Digest8>| count_mismatch("trace commitments", 4, values.len()))?;
    let claimed_sums = proof.interaction_claim.claimed_sums.map(Qm31Wire::from);
    let sampled_values = stark
        .sampled_values
        .iter()
        .flatten()
        .flatten()
        .copied()
        .map(Qm31Wire::from)
        .collect::<Vec<_>>()
        .try_into()
        .map_err(|values: Vec<Qm31Wire>| {
            count_mismatch(
                "sampled values",
                profile.recursion_program().sample_coordinates().len(),
                values.len(),
            )
        })?;

    let raw_queries = &aux.unsorted_query_locations;
    let sorted_queries = BTreeSet::from_iter(raw_queries.iter().copied())
        .into_iter()
        .collect::<Vec<_>>();
    let queried_values = expand_queried_values(profile, stark, raw_queries, &sorted_queries)?;
    let trace_paths = expand_trace_paths(profile, aux, raw_queries, &sorted_queries)?;
    let fri_layers = expand_fri_layers(profile, stark, aux, raw_queries)?;
    let last_layer_coefficients = stark
        .fri_proof
        .last_layer_poly
        .iter()
        .copied()
        .map(Qm31Wire::from)
        .collect::<Vec<_>>()
        .try_into()
        .map_err(|values: Vec<Qm31Wire>| {
            count_mismatch("last-layer coefficients", 1, values.len())
        })?;

    Ok(RecursionStarkProofWire {
        commitments,
        claimed_sums,
        sampled_values,
        queried_values,
        trace_paths,
        fri_layers,
        last_layer_coefficients,
        interaction_pow: proof.interaction_pow,
        pcs_pow: stark.proof_of_work,
    })
}

fn validate_topology(
    profile: &FrozenProtocolProfile,
    proof: &RecursionProof,
) -> Result<(), RecursionChildError> {
    let stark = &proof.stark_proof;
    let aux = &proof.stark_aux;
    validate_count("trace commitments", 4, stark.commitments.len())?;
    validate_count("trace decommitments", 4, stark.decommitments.len())?;
    validate_count("trace auxiliary trees", 4, aux.trace_decommitment.len())?;
    validate_count("queried-value trees", 4, stark.queried_values.len())?;
    validate_count("sampled-value trees", 4, stark.sampled_values.len())?;
    validate_count(
        "raw queries",
        FRI_QUERY_COUNT,
        aux.unsorted_query_locations.len(),
    )?;
    let query_bound = 1_usize
        .checked_shl(profile.manifest().recursion_shape().lifting_log_size())
        .ok_or(RecursionChildError::ArithmeticOverflow {
            field: "query domain size",
        })?;
    if let Some((query, raw)) = aux
        .unsorted_query_locations
        .iter()
        .copied()
        .enumerate()
        .find(|(_, raw)| *raw >= query_bound)
    {
        return Err(RecursionChildError::RawQueryOutOfRange {
            query,
            raw,
            bound: query_bound,
        });
    }
    let expected_logs = profile.recursion_program().column_log_sizes();
    for tree in 0..expected_logs.len() {
        validate_count(
            "queried-value columns",
            expected_logs[tree].len(),
            stark.queried_values[tree].len(),
        )?;
        validate_count(
            "sampled-value columns",
            expected_logs[tree].len(),
            stark.sampled_values[tree].len(),
        )?;
    }
    let expected_sample_counts = expected_sample_counts(profile);
    for (tree, tree_counts) in expected_sample_counts.iter().enumerate() {
        for (column, expected) in tree_counts.iter().copied().enumerate() {
            let actual = stark.sampled_values[tree][column].len();
            if actual != expected {
                return Err(RecursionChildError::SampleTopologyMismatch {
                    tree,
                    column,
                    expected,
                    actual,
                });
            }
        }
    }
    validate_count(
        "FRI layers",
        RECURSION_FRI_LAYER_COUNT,
        1 + stark.fri_proof.inner_layers.len(),
    )?;
    validate_count(
        "FRI auxiliary layers",
        RECURSION_FRI_LAYER_COUNT,
        1 + aux.fri.inner_layers.len(),
    )?;
    Ok(())
}

fn expected_sample_counts(profile: &FrozenProtocolProfile) -> Vec<Vec<usize>> {
    let mut counts = profile
        .recursion_program()
        .column_log_sizes()
        .iter()
        .map(|tree| vec![0; tree.len()])
        .collect::<Vec<_>>();
    for coordinate in profile.recursion_program().sample_coordinates() {
        counts[coordinate.tree][coordinate.column] =
            counts[coordinate.tree][coordinate.column].max(coordinate.point + 1);
    }
    counts
}

fn expand_queried_values(
    profile: &FrozenProtocolProfile,
    stark: &StarkProof<Poseidon2M31MerkleHasher>,
    raw_queries: &[usize],
    sorted_queries: &[usize],
) -> Result<Box<[M31Word; RECURSION_QUERY_VALUE_COUNT]>, RecursionChildError> {
    let mut values = Vec::with_capacity(RECURSION_QUERY_VALUE_COUNT);
    for tree in 0..stark.queried_values.len() {
        let positions = trace_tree_positions(profile, tree, sorted_queries);
        for column in &stark.queried_values[tree] {
            validate_count("queried values per column", positions.len(), column.len())?;
            for &raw in raw_queries {
                let position = trace_tree_position(profile, tree, raw);
                let index = positions.binary_search(&position).map_err(|_| {
                    RecursionChildError::QueryPositionMissing {
                        phase: "trace values",
                        tree_or_layer: tree,
                        position,
                    }
                })?;
                values.push(M31Word::from(column[index]));
            }
        }
    }
    values
        .into_boxed_slice()
        .try_into()
        .map_err(|values: Box<[M31Word]>| {
            count_mismatch(
                "expanded queried values",
                RECURSION_QUERY_VALUE_COUNT,
                values.len(),
            )
        })
}

fn expand_trace_paths(
    profile: &FrozenProtocolProfile,
    aux: &CommitmentSchemeProofAux<Poseidon2M31MerkleHasher>,
    raw_queries: &[usize],
    sorted_queries: &[usize],
) -> Result<
    Box<[MerklePathWire<RECURSION_MAX_MERKLE_DEPTH>; RECURSION_TRACE_PATH_COUNT]>,
    RecursionChildError,
> {
    let mut paths = Vec::with_capacity(RECURSION_TRACE_PATH_COUNT);
    for tree in 0..aux.trace_decommitment.len() {
        let positions = trace_tree_positions(profile, tree, sorted_queries);
        for &raw in raw_queries {
            let position = trace_tree_position(profile, tree, raw);
            if positions.binary_search(&position).is_err() {
                return Err(RecursionChildError::QueryPositionMissing {
                    phase: "trace path",
                    tree_or_layer: tree,
                    position,
                });
            }
            paths.push(expand_merkle_path(
                "trace path",
                tree,
                position,
                0,
                &aux.trace_decommitment[tree].all_node_values,
            )?);
        }
    }
    paths.into_boxed_slice().try_into().map_err(
        |paths: Box<[MerklePathWire<RECURSION_MAX_MERKLE_DEPTH>]>| {
            count_mismatch(
                "expanded trace paths",
                RECURSION_TRACE_PATH_COUNT,
                paths.len(),
            )
        },
    )
}

fn expand_fri_layers(
    profile: &FrozenProtocolProfile,
    stark: &StarkProof<Poseidon2M31MerkleHasher>,
    aux: &CommitmentSchemeProofAux<Poseidon2M31MerkleHasher>,
    raw_queries: &[usize],
) -> Result<
    Box<
        [FriLayerWire<FRI_QUERY_COUNT, MAX_FRI_FOLD_WIDTH, RECURSION_MAX_MERKLE_DEPTH>;
            RECURSION_FRI_LAYER_COUNT],
    >,
    RecursionChildError,
> {
    let shape = &profile.manifest().manifest().recursion_proof_shape;
    let mut layers = Vec::with_capacity(RECURSION_FRI_LAYER_COUNT);
    let mut folded = 0_u32;
    for layer in 0..RECURSION_FRI_LAYER_COUNT {
        let (layer_proof, layer_aux) = if layer == 0 {
            (&stark.fri_proof.first_layer, &aux.fri.first_layer)
        } else {
            (
                &stark.fri_proof.inner_layers[layer - 1],
                &aux.fri.inner_layers[layer - 1],
            )
        };
        let width = shape.fri_layer_fold_widths[layer].as_u32();
        let fold_step = width.ilog2();
        let packed_log_size = if fold_step > 1 {
            LOG_PACKED_LEAF_SIZE
        } else {
            0
        };
        let local_subtree_height = fold_step - packed_log_size;
        let value_map = layer_aux
            .all_values
            .first()
            .ok_or(RecursionChildError::MissingFriValueMap { layer })?;
        let queries = raw_queries
            .iter()
            .copied()
            .enumerate()
            .map(|(query, raw)| {
                let layer_position = raw >> folded;
                let subset_start = (layer_position >> fold_step) << fold_step;
                let mut values = [Qm31Wire::ZERO; MAX_FRI_FOLD_WIDTH];
                for (offset, value_slot) in values.iter_mut().enumerate().take(width as usize) {
                    let position = subset_start + offset;
                    let value = value_map.get(&position).copied().ok_or(
                        RecursionChildError::FriValueMissing {
                            layer,
                            query,
                            position,
                        },
                    )?;
                    *value_slot = Qm31Wire::from(value);
                }
                let packed_position = subset_start >> packed_log_size;
                let local_root_position = packed_position >> local_subtree_height;
                let path = expand_merkle_path(
                    "FRI path",
                    layer,
                    local_root_position,
                    local_subtree_height,
                    &layer_aux.decommitment.all_node_values,
                )?;
                Ok(FriQueryWire::new(values, path))
            })
            .collect::<Result<Vec<_>, RecursionChildError>>()?
            .into_boxed_slice()
            .try_into()
            .map_err(
                |queries: Box<[FriQueryWire<MAX_FRI_FOLD_WIDTH, RECURSION_MAX_MERKLE_DEPTH>]>| {
                    count_mismatch("FRI queries", FRI_QUERY_COUNT, queries.len())
                },
            )?;
        let commitment = proof_digest("FRI commitment", layer, layer_proof.commitment)?;
        layers.push(FriLayerWire::new(width, commitment, queries)?);
        folded = folded
            .checked_add(fold_step)
            .ok_or(RecursionChildError::ArithmeticOverflow {
                field: "cumulative FRI folds",
            })?;
    }
    layers.into_boxed_slice().try_into().map_err(
        |layers: Box<
            [FriLayerWire<FRI_QUERY_COUNT, MAX_FRI_FOLD_WIDTH, RECURSION_MAX_MERKLE_DEPTH>],
        >| {
            count_mismatch(
                "expanded FRI layers",
                RECURSION_FRI_LAYER_COUNT,
                layers.len(),
            )
        },
    )
}

fn expand_merkle_path(
    phase: &'static str,
    tree_or_layer: usize,
    mut position: usize,
    skip_layers: u32,
    node_maps: &[hashbrown::HashMap<usize, Poseidon2M31Hash>],
) -> Result<MerklePathWire<RECURSION_MAX_MERKLE_DEPTH>, RecursionChildError> {
    let skip =
        usize::try_from(skip_layers).map_err(|_| RecursionChildError::ArithmeticOverflow {
            field: "Merkle local subtree height",
        })?;
    if skip > node_maps.len() {
        return Err(RecursionChildError::MerkleLayerMissing {
            phase,
            tree_or_layer,
            layer: skip,
        });
    }
    let active_depth = node_maps.len() - skip;
    if active_depth > RECURSION_MAX_MERKLE_DEPTH {
        return Err(count_mismatch(
            "Merkle path depth",
            RECURSION_MAX_MERKLE_DEPTH,
            active_depth,
        ));
    }
    let mut siblings = [Digest8::ZERO; RECURSION_MAX_MERKLE_DEPTH];
    for (wire_level, map) in node_maps.iter().enumerate().skip(skip) {
        let sibling_position = position ^ 1;
        let sibling = map.get(&sibling_position).copied().ok_or(
            RecursionChildError::MerkleSiblingMissing {
                phase,
                tree_or_layer,
                layer: wire_level,
                position: sibling_position,
            },
        )?;
        siblings[wire_level - skip] = proof_digest(phase, wire_level, sibling)?;
        position >>= 1;
    }
    Ok(MerklePathWire::new(active_depth as u32, siblings)?)
}

fn trace_tree_positions(
    profile: &FrozenProtocolProfile,
    tree: usize,
    sorted_queries: &[usize],
) -> Vec<usize> {
    if tree == 0 {
        prepare_preprocessed_query_positions(
            sorted_queries,
            profile.manifest().recursion_shape().lifting_log_size(),
            profile
                .manifest()
                .manifest()
                .recursion_proof_shape
                .tree_heights[0]
                .as_u32(),
        )
    } else {
        sorted_queries.to_vec()
    }
}

fn trace_tree_position(profile: &FrozenProtocolProfile, tree: usize, raw: usize) -> usize {
    if tree == 0 {
        prepare_preprocessed_query_positions(
            &[raw],
            profile.manifest().recursion_shape().lifting_log_size(),
            profile
                .manifest()
                .manifest()
                .recursion_proof_shape
                .tree_heights[0]
                .as_u32(),
        )[0]
    } else {
        raw
    }
}

fn proof_kind_for_statement(statement: &crate::statement::SpanStatement) -> ProofKind {
    if statement.slots().height() == 0 {
        if statement.body().is_empty() {
            ProofKind::EmptyLeaf
        } else {
            ProofKind::SegmentLeaf
        }
    } else {
        ProofKind::BinaryNode
    }
}

fn proof_digest(
    field: &'static str,
    index: usize,
    hash: Poseidon2M31Hash,
) -> Result<Digest8, RecursionChildError> {
    Digest8::try_from(hash.0).map_err(|error| RecursionChildError::NonCanonicalProofDigest {
        field,
        index,
        value: error.value(),
    })
}

fn validate_count(
    field: &'static str,
    expected: usize,
    actual: usize,
) -> Result<(), RecursionChildError> {
    if expected == actual {
        Ok(())
    } else {
        Err(count_mismatch(field, expected, actual))
    }
}

const fn count_mismatch(
    field: &'static str,
    expected: usize,
    actual: usize,
) -> RecursionChildError {
    RecursionChildError::CountMismatch {
        field,
        expected,
        actual,
    }
}

/// A native recursion proof cannot be represented by the frozen child wire.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RecursionChildError {
    Wire(WireError),
    ProtocolMismatch,
    ProofKindMismatch,
    PcsConfigMismatch,
    ComponentLogSizeMismatch,
    InteractionLogSizeMismatch,
    NonCanonicalProofDigest {
        field: &'static str,
        index: usize,
        value: u32,
    },
    CountMismatch {
        field: &'static str,
        expected: usize,
        actual: usize,
    },
    SampleTopologyMismatch {
        tree: usize,
        column: usize,
        expected: usize,
        actual: usize,
    },
    RawQueryOutOfRange {
        query: usize,
        raw: usize,
        bound: usize,
    },
    QueryPositionMissing {
        phase: &'static str,
        tree_or_layer: usize,
        position: usize,
    },
    MissingFriValueMap {
        layer: usize,
    },
    FriValueMissing {
        layer: usize,
        query: usize,
        position: usize,
    },
    MerkleLayerMissing {
        phase: &'static str,
        tree_or_layer: usize,
        layer: usize,
    },
    MerkleSiblingMissing {
        phase: &'static str,
        tree_or_layer: usize,
        layer: usize,
        position: usize,
    },
    ArithmeticOverflow {
        field: &'static str,
    },
}

impl fmt::Display for RecursionChildError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Wire(error) => error.fmt(formatter),
            Self::ProtocolMismatch => formatter.write_str("recursion child protocol differs"),
            Self::ProofKindMismatch => {
                formatter.write_str("recursion child kind differs from its statement")
            }
            Self::PcsConfigMismatch => {
                formatter.write_str("recursion child PCS configuration differs")
            }
            Self::ComponentLogSizeMismatch => {
                formatter.write_str("recursion child component geometry differs")
            }
            Self::InteractionLogSizeMismatch => {
                formatter.write_str("recursion child interaction geometry differs")
            }
            Self::NonCanonicalProofDigest {
                field,
                index,
                value,
            } => write!(
                formatter,
                "recursion child {field} {index} has non-canonical limb {value}"
            ),
            Self::CountMismatch {
                field,
                expected,
                actual,
            } => write!(
                formatter,
                "recursion child has {actual} {field}, expected {expected}"
            ),
            Self::SampleTopologyMismatch {
                tree,
                column,
                expected,
                actual,
            } => write!(
                formatter,
                "recursion sample tree {tree} column {column} has {actual} points, expected {expected}"
            ),
            Self::RawQueryOutOfRange { query, raw, bound } => {
                write!(formatter, "raw query {query} is {raw}, outside {bound}")
            }
            Self::QueryPositionMissing {
                phase,
                tree_or_layer,
                position,
            } => write!(
                formatter,
                "{phase} {tree_or_layer} lacks query position {position}"
            ),
            Self::MissingFriValueMap { layer } => {
                write!(formatter, "FRI layer {layer} has no value expansion map")
            }
            Self::FriValueMissing {
                layer,
                query,
                position,
            } => write!(
                formatter,
                "FRI layer {layer} query {query} lacks position {position}"
            ),
            Self::MerkleLayerMissing {
                phase,
                tree_or_layer,
                layer,
            } => write!(
                formatter,
                "{phase} {tree_or_layer} lacks Merkle layer {layer}"
            ),
            Self::MerkleSiblingMissing {
                phase,
                tree_or_layer,
                layer,
                position,
            } => write!(
                formatter,
                "{phase} {tree_or_layer} layer {layer} lacks sibling {position}"
            ),
            Self::ArithmeticOverflow { field } => write!(formatter, "{field} overflows"),
        }
    }
}

impl std::error::Error for RecursionChildError {}

impl From<WireError> for RecursionChildError {
    fn from(error: WireError) -> Self {
        Self::Wire(error)
    }
}
