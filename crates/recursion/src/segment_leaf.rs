//! Checked adaptation of an in-memory Poseidon VM proof into one fixed leaf.
//!
//! STWO compresses duplicate query positions, shared Merkle siblings, and FRI
//! coset values in its ordinary proof. The prover auxiliary data retains the
//! authenticated expansion maps. This module consumes those maps once and
//! emits the independent raw-query slots required by the recursion AIR.

use core::fmt;
use std::collections::BTreeSet;

use air::digest::{Digest8, IoDigest, M31Word, MemoryDigest, ProgramDigest};
use prover::Proof;
use prover::poseidon2_channel::{Poseidon2M31Hash, Poseidon2M31MerkleHasher};
use prover::public_data::PublicData;
use stwo::core::pcs::utils::prepare_preprocessed_query_positions;
use stwo::core::vcs_lifted::verifier::LOG_PACKED_LEAF_SIZE;

use crate::profile::{
    FRI_QUERY_COUNT, FrozenProtocolProfile, MAX_FRI_FOLD_WIDTH, VM_FRI_LAYER_COUNT,
    VM_MAX_MERKLE_DEPTH, VM_PUBLIC_CLAIM_WORD_COUNT, VmProofWire, vm_component_log_sizes,
};
use crate::statement::{EdgeClaim, ExecutedSpan, JobContext, MachineState, SpanStatement};
use crate::vm_public_claim::{
    VmPublicClaimError, canonical_vm_public_claim_words, public_input_digest, public_output_digest,
};
use crate::wire::{FriLayerWire, FriQueryWire, MerklePathWire, Qm31Wire, WireError};

/// Runner-owned facts retained before proving consumes a segment result.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SegmentRunMetadata {
    segment_index: u32,
    first_cycle: u64,
    cycle_count: u64,
    public_data: PublicData,
}

impl SegmentRunMetadata {
    /// Captures the public runner result that the produced proof must authenticate.
    pub fn from_run_result(
        segment_index: u32,
        first_cycle: u64,
        run_result: &runner::RunResult,
    ) -> Result<Self, SegmentLeafError> {
        u32::try_from(run_result.cycles).map_err(|_| SegmentLeafError::CycleCountOutOfRange {
            cycle_count: run_result.cycles,
        })?;
        first_cycle.checked_add(run_result.cycles).ok_or(
            SegmentLeafError::CycleIntervalOverflow {
                first_cycle,
                cycle_count: run_result.cycles,
            },
        )?;
        Ok(Self {
            segment_index,
            first_cycle,
            cycle_count: run_result.cycles,
            public_data: PublicData::new(run_result),
        })
    }

    pub const fn segment_index(&self) -> u32 {
        self.segment_index
    }

    pub const fn first_cycle(&self) -> u64 {
        self.first_cycle
    }

    pub const fn cycle_count(&self) -> u64 {
        self.cycle_count
    }

    pub const fn public_data(&self) -> &PublicData {
        &self.public_data
    }
}

/// All private leaf inputs in the fixed representation consumed by recursion.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VmSegmentLeafWire {
    statement: SpanStatement,
    public_claim_words: [M31Word; VM_PUBLIC_CLAIM_WORD_COUNT],
    proof: Box<VmProofWire>,
}

impl VmSegmentLeafWire {
    pub const fn statement(&self) -> &SpanStatement {
        &self.statement
    }

    pub const fn public_claim_words(&self) -> &[M31Word; VM_PUBLIC_CLAIM_WORD_COUNT] {
        &self.public_claim_words
    }

    pub const fn proof(&self) -> &VmProofWire {
        &self.proof
    }
}

/// Adapts one real Poseidon VM proof to the frozen segment-leaf representation.
pub fn adapt_vm_segment_leaf(
    profile: &FrozenProtocolProfile,
    proof: &Proof<Poseidon2M31MerkleHasher>,
    metadata: &SegmentRunMetadata,
    job: JobContext,
) -> Result<Box<VmSegmentLeafWire>, SegmentLeafError> {
    validate_runner_metadata(&proof.public_data, metadata)?;
    if job.complete().protocol() != profile.manifest().protocol_id() {
        return Err(SegmentLeafError::ProtocolMismatch);
    }

    let public_claim_words =
        canonical_vm_public_claim_words(&proof.public_data, profile.public_claim_shape())?
            .try_into()
            .map_err(|words: Vec<M31Word>| SegmentLeafError::CountMismatch {
                field: "VM public-claim words",
                expected: VM_PUBLIC_CLAIM_WORD_COUNT,
                actual: words.len(),
            })?;
    let statement = segment_statement(profile, &proof.public_data, metadata, job)?;
    let fixed_proof = adapt_vm_stark_proof(profile, proof)?;
    let shape = &profile.manifest().manifest().vm_proof_shape;
    fixed_proof.validate_against_shape(shape)?;

    Ok(Box::new(VmSegmentLeafWire {
        statement,
        public_claim_words,
        proof: fixed_proof,
    }))
}

fn segment_statement(
    profile: &FrozenProtocolProfile,
    public_data: &PublicData,
    metadata: &SegmentRunMetadata,
    job: JobContext,
) -> Result<SpanStatement, SegmentLeafError> {
    let program = required_root("program root", public_data.program_root)?;
    if ProgramDigest::from(program) != job.complete().program() {
        return Err(SegmentLeafError::ProgramMismatch);
    }
    let entry = MachineState::new(
        public_data.initial_pc,
        public_data.initial_regs,
        MemoryDigest::from(required_root(
            "initial read-write root",
            public_data.initial_rw_root,
        )?),
        IoDigest::from(Digest8::ZERO),
    )?;
    let exit = MachineState::new(
        public_data.final_pc,
        public_data.final_regs,
        MemoryDigest::from(required_root(
            "final read-write root",
            public_data.final_rw_root,
        )?),
        IoDigest::from(Digest8::ZERO),
    )?;
    let input = public_input_digest(&public_data.io_entries, profile.public_claim_shape())?;
    let output = public_output_digest(&public_data.io_entries, profile.public_claim_shape())?;
    let input_edge = if metadata.segment_index == 0 {
        EdgeClaim::present(input)
    } else {
        EdgeClaim::absent()
    };
    let end_segment =
        metadata
            .segment_index
            .checked_add(1)
            .ok_or(SegmentLeafError::SegmentIndexOverflow {
                segment_index: metadata.segment_index,
            })?;
    let output_edge = if end_segment == job.segment_count() {
        EdgeClaim::present(output)
    } else {
        EdgeClaim::absent()
    };
    let span = ExecutedSpan::new(
        metadata.segment_index,
        1,
        metadata.first_cycle,
        metadata.cycle_count,
        entry,
        exit,
        input_edge,
        output_edge,
    )?;
    Ok(SpanStatement::segment_leaf(
        job,
        metadata.segment_index,
        span,
    )?)
}

#[inline(never)]
fn adapt_vm_stark_proof(
    profile: &FrozenProtocolProfile,
    proof: &Proof<Poseidon2M31MerkleHasher>,
) -> Result<Box<VmProofWire>, SegmentLeafError> {
    let stark = &proof.stark_proof;
    let aux = proof
        .stark_aux
        .as_ref()
        .ok_or(SegmentLeafError::MissingProverAuxiliaryData)?;
    let manifest = profile.manifest();
    let expected_config = manifest.vm_pcs().config();
    if stark.config != expected_config {
        return Err(SegmentLeafError::PcsConfigMismatch);
    }
    if proof.claim.component_log_sizes() != vm_component_log_sizes() {
        return Err(SegmentLeafError::ComponentLogSizeMismatch);
    }
    validate_proof_topology(profile, proof)?;

    let commitments = stark
        .commitments
        .iter()
        .copied()
        .enumerate()
        .map(|(index, hash)| proof_digest("trace commitment", index, hash))
        .collect::<Result<Vec<_>, _>>()?
        .try_into()
        .map_err(|values: Vec<Digest8>| count_mismatch("trace commitments", 4, values.len()))?;
    let claimed_sums = proof
        .interaction_claim
        .claimed_sum
        .component_values()
        .map(Qm31Wire::from);
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
                profile.vm_program().sample_coordinates().len(),
                values.len(),
            )
        })?;

    let raw_queries = &aux.unsorted_query_locations;
    let sorted_queries = BTreeSet::from_iter(raw_queries.iter().copied())
        .into_iter()
        .collect::<Vec<_>>();
    let queried_values = expand_queried_values(profile, proof, raw_queries, &sorted_queries)?;
    let trace_paths = expand_trace_paths(profile, proof, raw_queries, &sorted_queries)?;
    let fri_layers = expand_fri_layers(profile, proof, raw_queries)?;
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

    Ok(Box::new(VmProofWire {
        commitments,
        claimed_sums,
        sampled_values,
        queried_values,
        trace_paths,
        fri_layers,
        last_layer_coefficients,
        interaction_pow: proof.interaction_pow,
        pcs_pow: stark.proof_of_work,
    }))
}

fn validate_proof_topology(
    profile: &FrozenProtocolProfile,
    proof: &Proof<Poseidon2M31MerkleHasher>,
) -> Result<(), SegmentLeafError> {
    let stark = &proof.stark_proof;
    let aux = proof
        .stark_aux
        .as_ref()
        .ok_or(SegmentLeafError::MissingProverAuxiliaryData)?;
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
        .checked_shl(profile.vm_layout().lifting_log_size())
        .ok_or(SegmentLeafError::ArithmeticOverflow {
            field: "query domain size",
        })?;
    if let Some((query, raw)) = aux
        .unsorted_query_locations
        .iter()
        .copied()
        .enumerate()
        .find(|(_, raw)| *raw >= query_bound)
    {
        return Err(SegmentLeafError::RawQueryOutOfRange {
            query,
            raw,
            bound: query_bound,
        });
    }
    let expected_logs = profile.vm_program().column_log_sizes();
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
    let expected_interaction_logs = &expected_logs[2];
    if proof.interaction_claim.log_sizes != *expected_interaction_logs {
        return Err(SegmentLeafError::InteractionLogSizeMismatch);
    }
    let expected_sample_counts = expected_sample_counts(profile);
    for (tree, tree_counts) in expected_sample_counts.iter().enumerate() {
        for (column, expected) in tree_counts.iter().copied().enumerate() {
            let actual = stark.sampled_values[tree][column].len();
            if actual != expected {
                return Err(SegmentLeafError::SampleTopologyMismatch {
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
        VM_FRI_LAYER_COUNT,
        1 + stark.fri_proof.inner_layers.len(),
    )?;
    validate_count(
        "FRI auxiliary layers",
        VM_FRI_LAYER_COUNT,
        1 + aux.fri.inner_layers.len(),
    )?;
    Ok(())
}

fn expected_sample_counts(profile: &FrozenProtocolProfile) -> Vec<Vec<usize>> {
    let mut counts = profile
        .vm_program()
        .column_log_sizes()
        .iter()
        .map(|tree| vec![0; tree.len()])
        .collect::<Vec<_>>();
    for coordinate in profile.vm_program().sample_coordinates() {
        counts[coordinate.tree][coordinate.column] =
            counts[coordinate.tree][coordinate.column].max(coordinate.point + 1);
    }
    counts
}

#[inline(never)]
fn expand_queried_values(
    profile: &FrozenProtocolProfile,
    proof: &Proof<Poseidon2M31MerkleHasher>,
    raw_queries: &[usize],
    sorted_queries: &[usize],
) -> Result<Box<[M31Word; crate::profile::VM_QUERY_VALUE_COUNT]>, SegmentLeafError> {
    let mut values = Vec::with_capacity(crate::profile::VM_QUERY_VALUE_COUNT);
    for tree in 0..proof.stark_proof.queried_values.len() {
        let positions = trace_tree_positions(profile, tree, sorted_queries);
        for column in &proof.stark_proof.queried_values[tree] {
            validate_count("queried values per column", positions.len(), column.len())?;
            for &raw in raw_queries {
                let position = trace_tree_position(profile, tree, raw);
                let index = positions.binary_search(&position).map_err(|_| {
                    SegmentLeafError::QueryPositionMissing {
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
                crate::profile::VM_QUERY_VALUE_COUNT,
                values.len(),
            )
        })
}

#[inline(never)]
fn expand_trace_paths(
    profile: &FrozenProtocolProfile,
    proof: &Proof<Poseidon2M31MerkleHasher>,
    raw_queries: &[usize],
    sorted_queries: &[usize],
) -> Result<
    Box<[MerklePathWire<VM_MAX_MERKLE_DEPTH>; crate::profile::VM_TRACE_PATH_COUNT]>,
    SegmentLeafError,
> {
    let aux = proof
        .stark_aux
        .as_ref()
        .ok_or(SegmentLeafError::MissingProverAuxiliaryData)?;
    let mut paths = Vec::with_capacity(crate::profile::VM_TRACE_PATH_COUNT);
    for tree in 0..aux.trace_decommitment.len() {
        let positions = trace_tree_positions(profile, tree, sorted_queries);
        for &raw in raw_queries {
            let position = trace_tree_position(profile, tree, raw);
            if positions.binary_search(&position).is_err() {
                return Err(SegmentLeafError::QueryPositionMissing {
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
        |paths: Box<[MerklePathWire<VM_MAX_MERKLE_DEPTH>]>| {
            count_mismatch(
                "expanded trace paths",
                crate::profile::VM_TRACE_PATH_COUNT,
                paths.len(),
            )
        },
    )
}

#[inline(never)]
fn expand_fri_layers(
    profile: &FrozenProtocolProfile,
    proof: &Proof<Poseidon2M31MerkleHasher>,
    raw_queries: &[usize],
) -> Result<
    Box<
        [FriLayerWire<FRI_QUERY_COUNT, MAX_FRI_FOLD_WIDTH, VM_MAX_MERKLE_DEPTH>;
            VM_FRI_LAYER_COUNT],
    >,
    SegmentLeafError,
> {
    let aux = proof
        .stark_aux
        .as_ref()
        .ok_or(SegmentLeafError::MissingProverAuxiliaryData)?;
    let shape = &profile.manifest().manifest().vm_proof_shape;
    let mut layers = Vec::with_capacity(VM_FRI_LAYER_COUNT);
    let mut folded = 0_u32;
    for layer in 0..VM_FRI_LAYER_COUNT {
        let (layer_proof, layer_aux) = if layer == 0 {
            (
                &proof.stark_proof.fri_proof.first_layer,
                &aux.fri.first_layer,
            )
        } else {
            (
                &proof.stark_proof.fri_proof.inner_layers[layer - 1],
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
            .ok_or(SegmentLeafError::MissingFriValueMap { layer })?;
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
                        SegmentLeafError::FriValueMissing {
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
            .collect::<Result<Vec<_>, SegmentLeafError>>()?
            .into_boxed_slice()
            .try_into()
            .map_err(
                |queries: Box<[FriQueryWire<MAX_FRI_FOLD_WIDTH, VM_MAX_MERKLE_DEPTH>]>| {
                    count_mismatch("FRI queries", FRI_QUERY_COUNT, queries.len())
                },
            )?;
        let commitment = proof_digest("FRI commitment", layer, layer_proof.commitment)?;
        layers.push(FriLayerWire::new(width, commitment, queries)?);
        folded = folded
            .checked_add(fold_step)
            .ok_or(SegmentLeafError::ArithmeticOverflow {
                field: "cumulative FRI folds",
            })?;
    }
    layers.into_boxed_slice().try_into().map_err(
        |layers: Box<[FriLayerWire<FRI_QUERY_COUNT, MAX_FRI_FOLD_WIDTH, VM_MAX_MERKLE_DEPTH>]>| {
            count_mismatch("expanded FRI layers", VM_FRI_LAYER_COUNT, layers.len())
        },
    )
}

fn expand_merkle_path(
    phase: &'static str,
    tree_or_layer: usize,
    mut position: usize,
    skip_layers: u32,
    node_maps: &[hashbrown::HashMap<usize, Poseidon2M31Hash>],
) -> Result<MerklePathWire<VM_MAX_MERKLE_DEPTH>, SegmentLeafError> {
    let skip = usize::try_from(skip_layers).map_err(|_| SegmentLeafError::ArithmeticOverflow {
        field: "Merkle local subtree height",
    })?;
    if skip > node_maps.len() {
        return Err(SegmentLeafError::MerkleLayerMissing {
            phase,
            tree_or_layer,
            layer: skip,
        });
    }
    let active_depth = node_maps.len() - skip;
    if active_depth > VM_MAX_MERKLE_DEPTH {
        return Err(SegmentLeafError::CountMismatch {
            field: "Merkle path depth",
            expected: VM_MAX_MERKLE_DEPTH,
            actual: active_depth,
        });
    }
    let mut siblings = [Digest8::ZERO; VM_MAX_MERKLE_DEPTH];
    for (wire_level, map) in node_maps.iter().enumerate().skip(skip) {
        let sibling_position = position ^ 1;
        let sibling =
            map.get(&sibling_position)
                .copied()
                .ok_or(SegmentLeafError::MerkleSiblingMissing {
                    phase,
                    tree_or_layer,
                    layer: wire_level,
                    position: sibling_position,
                })?;
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
            profile.vm_layout().lifting_log_size(),
            profile.vm_layout().tree_heights()[0],
        )
    } else {
        sorted_queries.to_vec()
    }
}

fn trace_tree_position(profile: &FrozenProtocolProfile, tree: usize, raw: usize) -> usize {
    if tree == 0 {
        prepare_preprocessed_query_positions(
            &[raw],
            profile.vm_layout().lifting_log_size(),
            profile.vm_layout().tree_heights()[0],
        )[0]
    } else {
        raw
    }
}

fn validate_runner_metadata(
    authenticated: &PublicData,
    metadata: &SegmentRunMetadata,
) -> Result<(), SegmentLeafError> {
    if metadata.cycle_count != u64::from(authenticated.clock) {
        return Err(SegmentLeafError::RunnerMetadataMismatch {
            field: "cycle count",
        });
    }
    if metadata.public_data.initial_pc != authenticated.initial_pc {
        return Err(SegmentLeafError::RunnerMetadataMismatch {
            field: "initial PC",
        });
    }
    if metadata.public_data.final_pc != authenticated.final_pc {
        return Err(SegmentLeafError::RunnerMetadataMismatch { field: "final PC" });
    }
    if metadata.public_data.clock != authenticated.clock {
        return Err(SegmentLeafError::RunnerMetadataMismatch { field: "clock" });
    }
    if metadata.public_data.initial_regs != authenticated.initial_regs {
        return Err(SegmentLeafError::RunnerMetadataMismatch {
            field: "initial registers",
        });
    }
    if metadata.public_data.final_regs != authenticated.final_regs {
        return Err(SegmentLeafError::RunnerMetadataMismatch {
            field: "final registers",
        });
    }
    if metadata.public_data.reg_last_clock != authenticated.reg_last_clock {
        return Err(SegmentLeafError::RunnerMetadataMismatch {
            field: "register clocks",
        });
    }
    if metadata.public_data.program_root != authenticated.program_root {
        return Err(SegmentLeafError::RunnerMetadataMismatch {
            field: "program root",
        });
    }
    if metadata.public_data.initial_rw_root != authenticated.initial_rw_root {
        return Err(SegmentLeafError::RunnerMetadataMismatch {
            field: "initial read-write root",
        });
    }
    if metadata.public_data.final_rw_root != authenticated.final_rw_root {
        return Err(SegmentLeafError::RunnerMetadataMismatch {
            field: "final read-write root",
        });
    }
    if metadata.public_data.io_entries != authenticated.io_entries {
        return Err(SegmentLeafError::RunnerMetadataMismatch { field: "public IO" });
    }
    metadata
        .first_cycle
        .checked_add(metadata.cycle_count)
        .ok_or(SegmentLeafError::CycleIntervalOverflow {
            first_cycle: metadata.first_cycle,
            cycle_count: metadata.cycle_count,
        })?;
    Ok(())
}

fn required_root(field: &'static str, root: Option<[u32; 8]>) -> Result<Digest8, SegmentLeafError> {
    let root = root.ok_or(SegmentLeafError::MissingRoot { field })?;
    Digest8::try_from(root).map_err(|error| SegmentLeafError::NonCanonicalRoot {
        field,
        value: error.value(),
    })
}

fn proof_digest(
    field: &'static str,
    index: usize,
    hash: Poseidon2M31Hash,
) -> Result<Digest8, SegmentLeafError> {
    Digest8::try_from(hash.0).map_err(|error| SegmentLeafError::NonCanonicalProofDigest {
        field,
        index,
        value: error.value(),
    })
}

fn validate_count(
    field: &'static str,
    expected: usize,
    actual: usize,
) -> Result<(), SegmentLeafError> {
    if expected == actual {
        Ok(())
    } else {
        Err(count_mismatch(field, expected, actual))
    }
}

const fn count_mismatch(field: &'static str, expected: usize, actual: usize) -> SegmentLeafError {
    SegmentLeafError::CountMismatch {
        field,
        expected,
        actual,
    }
}

/// A proof, auxiliary expansion, runner boundary, or job is not one fixed leaf.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SegmentLeafError {
    PublicClaim(VmPublicClaimError),
    Statement(crate::statement::StatementError),
    Wire(WireError),
    MissingProverAuxiliaryData,
    PcsConfigMismatch,
    ComponentLogSizeMismatch,
    InteractionLogSizeMismatch,
    ProtocolMismatch,
    ProgramMismatch,
    MissingRoot {
        field: &'static str,
    },
    NonCanonicalRoot {
        field: &'static str,
        value: u32,
    },
    NonCanonicalProofDigest {
        field: &'static str,
        index: usize,
        value: u32,
    },
    RunnerMetadataMismatch {
        field: &'static str,
    },
    CycleCountOutOfRange {
        cycle_count: u64,
    },
    CycleIntervalOverflow {
        first_cycle: u64,
        cycle_count: u64,
    },
    SegmentIndexOverflow {
        segment_index: u32,
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

impl fmt::Display for SegmentLeafError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::PublicClaim(error) => error.fmt(formatter),
            Self::Statement(error) => error.fmt(formatter),
            Self::Wire(error) => error.fmt(formatter),
            Self::MissingProverAuxiliaryData => {
                formatter.write_str("VM proof has no prover auxiliary expansion data")
            }
            Self::PcsConfigMismatch => {
                formatter.write_str("VM proof PCS configuration differs from the frozen profile")
            }
            Self::ComponentLogSizeMismatch => {
                formatter.write_str("VM proof component log sizes differ from the frozen profile")
            }
            Self::InteractionLogSizeMismatch => {
                formatter.write_str("VM proof interaction log sizes differ from the frozen profile")
            }
            Self::ProtocolMismatch => {
                formatter.write_str("job protocol differs from the frozen profile")
            }
            Self::ProgramMismatch => {
                formatter.write_str("authenticated program root differs from the job program")
            }
            Self::MissingRoot { field } => write!(formatter, "VM proof has no {field}"),
            Self::NonCanonicalRoot { field, value } => write!(
                formatter,
                "VM proof {field} contains non-canonical limb 0x{value:08x}"
            ),
            Self::NonCanonicalProofDigest {
                field,
                index,
                value,
            } => write!(
                formatter,
                "VM proof {field} {index} contains non-canonical limb 0x{value:08x}"
            ),
            Self::RunnerMetadataMismatch { field } => write!(
                formatter,
                "runner {field} disagrees with authenticated VM public data"
            ),
            Self::CycleCountOutOfRange { cycle_count } => write!(
                formatter,
                "runner cycle count {cycle_count} exceeds the VM public field"
            ),
            Self::CycleIntervalOverflow {
                first_cycle,
                cycle_count,
            } => write!(
                formatter,
                "cycle interval {first_cycle} + {cycle_count} overflows u64"
            ),
            Self::SegmentIndexOverflow { segment_index } => write!(
                formatter,
                "segment index {segment_index} has no exclusive end"
            ),
            Self::CountMismatch {
                field,
                expected,
                actual,
            } => write!(
                formatter,
                "VM proof has {actual} {field}, expected {expected}"
            ),
            Self::SampleTopologyMismatch {
                tree,
                column,
                expected,
                actual,
            } => write!(
                formatter,
                "VM sample tree {tree} column {column} has {actual} points, expected {expected}"
            ),
            Self::RawQueryOutOfRange { query, raw, bound } => write!(
                formatter,
                "raw query {query} is {raw}, outside domain bound {bound}"
            ),
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
            Self::ArithmeticOverflow { field } => {
                write!(formatter, "{field} overflows its host representation")
            }
        }
    }
}

impl std::error::Error for SegmentLeafError {}

impl From<VmPublicClaimError> for SegmentLeafError {
    fn from(error: VmPublicClaimError) -> Self {
        Self::PublicClaim(error)
    }
}

impl From<crate::statement::StatementError> for SegmentLeafError {
    fn from(error: crate::statement::StatementError) -> Self {
        Self::Statement(error)
    }
}

impl From<WireError> for SegmentLeafError {
    fn from(error: WireError) -> Self {
        Self::Wire(error)
    }
}

#[cfg(test)]
mod tests {
    use std::hash::{Hash, Hasher};
    use std::sync::OnceLock;

    use air::digest::{MemoryDigest, ProgramDigest, ProtocolId};
    use prover::components::COMPONENT_COUNT;
    use prover::e2e::{ensure_guest_built, guest_bin_dir};
    use prover::poseidon2_channel::Poseidon2M31MerkleChannel;
    use prover::{preprocess_with_channel, prove_rv32im_with_channel_at_log_sizes_and_transcript};
    use stwo::core::air::Components as CoreComponents;
    use stwo::core::channel::Channel;
    use stwo::core::fields::m31::BaseField;
    use stwo::core::pcs::CommitmentSchemeVerifier;
    use stwo::core::verifier::verify;
    use stwo_constraint_framework::TraceLocationAllocator;

    use super::*;

    struct RealFixture {
        profile: FrozenProtocolProfile,
        proof: Proof<Poseidon2M31MerkleHasher>,
        metadata: SegmentRunMetadata,
        job: JobContext,
        wire: Box<VmSegmentLeafWire>,
        prover_draws: Vec<(crate::kernel::VerifierStep, [M31Word; 8])>,
        preprocessing: prover::Preprocessing<Poseidon2M31MerkleHasher>,
    }

    fn real_fixture() -> &'static RealFixture {
        static FIXTURE: OnceLock<Box<RealFixture>> = OnceLock::new();
        FIXTURE
            .get_or_init(|| {
                std::thread::Builder::new()
                    .name("recursion-real-vm-proof".into())
                    .stack_size(32 * 1024 * 1024)
                    .spawn(build_real_fixture)
                    .expect("real-proof fixture thread starts")
                    .join()
                    .expect("real-proof fixture thread completes")
            })
            .as_ref()
    }

    fn build_real_fixture() -> Box<RealFixture> {
        ensure_guest_built();
        let elf = std::fs::read(guest_bin_dir().join("mulhu_alias"))
            .expect("read the checked-in test guest");
        let mut segments = runner::run_segments_by_capacity(&elf, &[], 1 << 11, 10_000_000)
            .expect("run a capacity-bounded real segment");
        let segment_public_data = segments.iter().map(PublicData::new).collect::<Vec<_>>();
        let segment_count = u32::try_from(segments.len()).expect("fixture segment count fits u32");
        let total_cycles = segments.iter().map(|segment| segment.cycles).sum::<u64>();
        let profile = crate::profile::frozen_protocol_profile().expect("frozen profile is valid");
        let job = complete_job(&profile, &segment_public_data, total_cycles, segment_count);
        let first = segments.remove(0);
        let metadata = SegmentRunMetadata::from_run_result(0, 0, &first)
            .expect("runner metadata is representable");
        let statement = segment_statement(&profile, &segment_public_data[0], &metadata, job)
            .expect("fixture statement is canonical");
        let claim_digest = crate::vm_public_claim::vm_public_claim_digest(
            &segment_public_data[0],
            profile.public_claim_shape(),
        )
        .expect("fixture public claim fits the frozen profile");
        let config = profile.manifest().vm_pcs().config();
        let preprocessing = preprocess_with_channel::<Poseidon2M31MerkleChannel>(config);
        let channel = crate::profiled_channel::ProfiledPoseidon2M31Channel::for_vm_proof(
            profile.vm_plan(),
            profile.manifest().protocol_id(),
            &statement,
        )
        .expect("fixture transcript prefix is valid");
        let transcript = crate::profiled_channel::RecursionVmClaimTranscript::new(claim_digest);
        let (proof, channel) = prove_rv32im_with_channel_at_log_sizes_and_transcript::<
            crate::profiled_channel::ProfiledPoseidon2M31MerkleChannel,
            _,
        >(
            first,
            config,
            &preprocessing,
            vm_component_log_sizes(),
            channel,
            &transcript,
        )
        .expect("capacity-bounded segment fits the frozen VM layout");
        channel
            .finish()
            .expect("the VM prover consumes the complete verifier transcript");
        let prover_draws = channel.draws().to_vec();
        let wire = adapt_vm_segment_leaf(&profile, &proof, &metadata, job)
            .expect("the real proof adapts to one fixed leaf");
        Box::new(RealFixture {
            profile,
            proof,
            metadata,
            job,
            wire,
            prover_draws,
            preprocessing,
        })
    }

    fn complete_job(
        profile: &FrozenProtocolProfile,
        public_data: &[PublicData],
        total_cycles: u64,
        segment_count: u32,
    ) -> JobContext {
        let first = public_data.first().expect("execution has a first segment");
        let last = public_data.last().expect("execution has a last segment");
        let initial = machine_state(first, true);
        let final_state = machine_state(last, false);
        let program = ProgramDigest::from(
            Digest8::try_from(first.program_root.expect("program root is present"))
                .expect("program root is canonical"),
        );
        let input = public_input_digest(&first.io_entries, profile.public_claim_shape())
            .expect("public input fits the profile");
        let output = public_output_digest(&last.io_entries, profile.public_claim_shape())
            .expect("public output fits the profile");
        let complete = crate::statement::CompleteExecutionStatement::new(
            profile.manifest().protocol_id(),
            program,
            initial,
            final_state,
            input,
            output,
            total_cycles,
        )
        .expect("fixture execution is nonempty");
        JobContext::new(complete, segment_count).expect("fixture has at least one segment")
    }

    fn machine_state(public_data: &PublicData, initial: bool) -> MachineState {
        let (pc, registers, root) = if initial {
            (
                public_data.initial_pc,
                public_data.initial_regs,
                public_data.initial_rw_root,
            )
        } else {
            (
                public_data.final_pc,
                public_data.final_regs,
                public_data.final_rw_root,
            )
        };
        MachineState::new(
            pc,
            registers,
            MemoryDigest::from(
                Digest8::try_from(root.expect("read-write root is present"))
                    .expect("read-write root is canonical"),
            ),
            IoDigest::from(Digest8::ZERO),
        )
        .expect("runner boundary is a canonical machine state")
    }

    #[test]
    fn frozen_public_claim_word_count_matches_encoder() {
        let profile = crate::profile::frozen_protocol_profile().expect("frozen profile is valid");
        assert_eq!(
            profile.public_claim_shape().claim_word_count(),
            VM_PUBLIC_CLAIM_WORD_COUNT
        );
    }

    #[test]
    fn real_poseidon_proof_round_trips_to_the_fixed_leaf_shape() {
        let fixture = real_fixture();
        assert_eq!(
            fixture
                .wire
                .proof()
                .validate_against_shape(&fixture.profile.manifest().manifest().vm_proof_shape),
            Ok(())
        );
    }

    #[test]
    fn profiled_prover_and_fixed_executor_draw_identical_randomness() {
        let fixture = real_fixture();
        let claim_digest = crate::vm_public_claim::vm_public_claim_digest_from_words(
            fixture.wire.public_claim_words(),
            fixture.profile.public_claim_shape(),
        )
        .expect("fixed claim digest is canonical");
        let execution = crate::transcript_program::execute_fixed_transcript(
            crate::transcript::RecordingTranscriptBackend::default(),
            fixture.profile.vm_plan(),
            fixture.profile.manifest().protocol_id(),
            fixture.wire.statement(),
            crate::transcript_program::VerifierPublicClaim::Vm(claim_digest),
            fixture.wire.proof(),
        )
        .expect("fixed transcript accepts its produced proof");
        let verifier_draws = execution
            .operations()
            .iter()
            .filter_map(|operation| operation.draw().map(|draw| (operation.step(), draw)))
            .collect::<Vec<_>>();
        assert_eq!(fixture.prover_draws, verifier_draws);
    }

    #[test]
    fn profiled_vm_proof_is_accepted_by_the_native_stwo_verifier() {
        let fixture = real_fixture();
        let claim_digest = crate::vm_public_claim::vm_public_claim_digest_from_words(
            fixture.wire.public_claim_words(),
            fixture.profile.public_claim_shape(),
        )
        .expect("fixed claim digest is canonical");
        let mut channel = crate::profiled_channel::ProfiledPoseidon2M31Channel::for_vm_proof(
            fixture.profile.vm_plan(),
            fixture.profile.manifest().protocol_id(),
            fixture.wire.statement(),
        )
        .expect("fixture transcript prefix is valid");
        let config = fixture.profile.manifest().vm_pcs().config();
        let mut commitment_scheme = CommitmentSchemeVerifier::<
            crate::profiled_channel::ProfiledPoseidon2M31MerkleChannel,
        >::new(config);
        commitment_scheme.commit(
            fixture
                .preprocessing
                .commitment_root()
                .expect("preprocessing has one root"),
            &fixture.preprocessing.log_sizes,
            &mut channel,
        );
        commitment_scheme.commit(
            fixture.proof.stark_proof.commitments[1],
            &fixture.proof.claim.main_trace_log_sizes(),
            &mut channel,
        );
        channel
            .absorb_vm_public_claim(claim_digest)
            .expect("public claim follows the main root");
        let interaction_pow_valid = channel.verify_pow_nonce(
            prover::relations::INTERACTION_POW_BITS,
            fixture.proof.interaction_pow,
        );
        channel.mix_u64(fixture.proof.interaction_pow);
        let relations = prover::relations::Relations::draw(&mut channel);
        channel
            .absorb_claimed_sums(
                &fixture
                    .proof
                    .interaction_claim
                    .claimed_sum
                    .component_values(),
            )
            .expect("claimed sums precede the interaction root");
        commitment_scheme.commit(
            fixture.proof.stark_proof.commitments[2],
            &fixture.proof.interaction_claim.log_sizes,
            &mut channel,
        );
        let ids = fixture.preprocessing.column_ids();
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
        let components = prover::components::Components::new(
            &fixture.proof.claim,
            &mut allocator,
            relations,
            &fixture.proof.interaction_claim.claimed_sum,
        );
        let core_components = CoreComponents {
            components: components.verifiers(),
            n_preprocessed_columns: ids.len(),
        };
        let max_log_degree_bound = core_components.composition_log_degree_bound() - 1;
        let mut compiled_log_sizes = core_components.column_log_sizes();
        compiled_log_sizes.push(vec![max_log_degree_bound; 8]);
        let committed_log_sizes = vec![
            fixture.preprocessing.log_sizes.clone(),
            fixture.proof.claim.main_trace_log_sizes(),
            fixture.proof.interaction_claim.log_sizes.clone(),
            vec![max_log_degree_bound; 8],
        ];
        let log_sizes_match = compiled_log_sizes.0 == committed_log_sizes;
        let verification = verify(
            &components.verifiers(),
            &mut channel,
            &mut commitment_scheme,
            fixture.proof.stark_proof.clone(),
        );
        assert_eq!(
            (
                interaction_pow_valid,
                log_sizes_match,
                format!("{verification:?}"),
                channel.finish(),
            ),
            (true, true, "Ok(())".to_owned(), Ok(()))
        );
    }

    #[test]
    fn real_poseidon_leaf_materializes_the_universal_witness() {
        let fixture = real_fixture();
        let mut channel = prover::poseidon2_channel::Poseidon2M31Channel::default();
        let relations = crate::universal_relations::UniversalRelations::draw(&mut channel);
        let witness = crate::universal_witness::assemble_segment_leaf(
            &fixture.profile,
            &fixture.wire,
            &relations,
        )
        .expect("the real VM leaf fills every universal component");
        let accepted_components = crate::recursion_air_program::assert_universal_constraints(
            witness.traces(),
            witness.preprocessing_ids(),
            &relations,
            witness.proof_kind(),
            witness.component_log_sizes(),
            witness.claimed_sums(),
        );
        let first_fingerprint = universal_witness_fingerprint(&witness);
        let first_shape = (
            witness.proof_kind(),
            witness.traces().len(),
            witness.claimed_sums().len(),
            witness.preprocessing_ids().len(),
            accepted_components,
        );
        drop(witness);
        let second = crate::universal_witness::assemble_segment_leaf(
            &fixture.profile,
            &fixture.wire,
            &relations,
        )
        .expect("repeated assembly accepts the same verifier input");
        assert_eq!(
            (first_shape, first_fingerprint),
            (
                (
                    crate::wire::ProofKind::SegmentLeaf,
                    3,
                    crate::recursion_air_program::UNIVERSAL_COMPONENT_COUNT,
                    493,
                    crate::recursion_air_program::UNIVERSAL_COMPONENT_COUNT,
                ),
                universal_witness_fingerprint(&second),
            )
        );
    }

    fn universal_witness_fingerprint(witness: &crate::universal_witness::UniversalWitness) -> u64 {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        witness.proof_kind().hash(&mut hasher);
        witness.component_log_sizes().hash(&mut hasher);
        for id in witness.preprocessing_ids() {
            id.id.hash(&mut hasher);
        }
        for sum in witness.claimed_sums() {
            sum.to_m31_array().map(|word| word.0).hash(&mut hasher);
        }
        witness
            .public_relation_sum()
            .to_m31_array()
            .map(|word| word.0)
            .hash(&mut hasher);
        for tree in witness.traces().iter() {
            tree.len().hash(&mut hasher);
            for column in tree {
                column.domain.log_size().hash(&mut hasher);
                column
                    .values
                    .as_slice()
                    .iter()
                    .map(|word| word.0)
                    .for_each(|word| word.hash(&mut hasher));
            }
        }
        hasher.finish()
    }

    #[test]
    fn missing_prover_auxiliary_data_is_rejected() {
        let fixture = real_fixture();
        let mut proof = fixture.proof.clone();
        proof.stark_aux = None;
        assert_eq!(
            adapt_vm_segment_leaf(&fixture.profile, &proof, &fixture.metadata, fixture.job),
            Err(SegmentLeafError::MissingProverAuxiliaryData)
        );
    }

    #[test]
    fn public_input_capacity_overflow_is_rejected() {
        let fixture = real_fixture();
        let mut proof = fixture.proof.clone();
        proof.public_data.io_entries.input_words =
            vec![0; crate::profile::MAX_PUBLIC_INPUT_WORDS as usize + 1];
        let mut metadata = fixture.metadata.clone();
        metadata.public_data = proof.public_data.clone();
        assert!(matches!(
            adapt_vm_segment_leaf(&fixture.profile, &proof, &metadata, fixture.job),
            Err(SegmentLeafError::PublicClaim(
                VmPublicClaimError::VectorExceedsShape {
                    field: "input words",
                    ..
                }
            ))
        ));
    }

    #[test]
    fn non_canonical_optional_root_is_rejected() {
        let fixture = real_fixture();
        let mut proof = fixture.proof.clone();
        proof
            .public_data
            .program_root
            .as_mut()
            .expect("root is present")[0] = stwo::core::fields::m31::P;
        let mut metadata = fixture.metadata.clone();
        metadata.public_data = proof.public_data.clone();
        assert!(matches!(
            adapt_vm_segment_leaf(&fixture.profile, &proof, &metadata, fixture.job),
            Err(SegmentLeafError::PublicClaim(
                VmPublicClaimError::NonCanonicalRoot {
                    field: "program root",
                    index: 0,
                    ..
                }
            ))
        ));
    }

    #[test]
    fn runner_cycle_count_disagreement_is_rejected() {
        let fixture = real_fixture();
        let mut metadata = fixture.metadata.clone();
        metadata.cycle_count += 1;
        assert_eq!(
            adapt_vm_segment_leaf(&fixture.profile, &fixture.proof, &metadata, fixture.job),
            Err(SegmentLeafError::RunnerMetadataMismatch {
                field: "cycle count"
            })
        );
    }

    #[test]
    fn runner_machine_boundary_disagreement_is_rejected() {
        let fixture = real_fixture();
        let mut metadata = fixture.metadata.clone();
        metadata.public_data.initial_pc ^= 4;
        assert_eq!(
            adapt_vm_segment_leaf(&fixture.profile, &fixture.proof, &metadata, fixture.job),
            Err(SegmentLeafError::RunnerMetadataMismatch {
                field: "initial PC"
            })
        );
    }

    #[test]
    fn runner_public_io_disagreement_is_rejected() {
        let fixture = real_fixture();
        let mut metadata = fixture.metadata.clone();
        metadata.public_data.io_entries.input_start ^= 4;
        assert_eq!(
            adapt_vm_segment_leaf(&fixture.profile, &fixture.proof, &metadata, fixture.job),
            Err(SegmentLeafError::RunnerMetadataMismatch { field: "public IO" })
        );
    }

    #[test]
    fn first_segment_nonzero_cycle_start_is_rejected() {
        let fixture = real_fixture();
        let mut metadata = fixture.metadata.clone();
        metadata.first_cycle = 1;
        assert!(matches!(
            adapt_vm_segment_leaf(&fixture.profile, &fixture.proof, &metadata, fixture.job),
            Err(SegmentLeafError::Statement(
                crate::statement::StatementError::InitialCycleMismatch
            ))
        ));
    }

    #[test]
    fn segment_index_outside_the_job_is_rejected() {
        let fixture = real_fixture();
        let mut metadata = fixture.metadata.clone();
        metadata.segment_index = fixture.job.segment_count();
        assert!(matches!(
            adapt_vm_segment_leaf(&fixture.profile, &fixture.proof, &metadata, fixture.job),
            Err(SegmentLeafError::Statement(
                crate::statement::StatementError::SlotsOutsideJob
            ))
        ));
    }

    #[test]
    fn mismatched_job_protocol_is_rejected() {
        let fixture = real_fixture();
        let mut complete = *fixture.job.complete();
        let words = [M31Word::from(7); 8];
        complete = crate::statement::CompleteExecutionStatement::new(
            ProtocolId::from(Digest8::new(words)),
            complete.program(),
            complete.initial_state(),
            complete.final_state(),
            complete.public_input(),
            complete.public_output(),
            complete.total_cycles(),
        )
        .expect("replacement complete statement is valid");
        let job = JobContext::new(complete, fixture.job.segment_count())
            .expect("replacement job is valid");
        assert_eq!(
            adapt_vm_segment_leaf(&fixture.profile, &fixture.proof, &fixture.metadata, job),
            Err(SegmentLeafError::ProtocolMismatch)
        );
    }

    #[test]
    fn base_field_conversion_is_canonical() {
        assert_eq!(M31Word::from(BaseField::from(17)).as_u32(), 17);
    }

    #[test]
    fn component_count_matches_frozen_log_sizes() {
        assert_eq!(vm_component_log_sizes().len(), COMPONENT_COUNT);
    }
}
