//! Level-ordered proving from finalized VM segments to one recursive root.
//!
//! The driver derives one complete execution job from runner-authenticated
//! public data, proves every executed leaf, appends the unique canonical padding
//! leaves, and replaces each adjacent pair with one binary recursion proof.
//! Descendant proofs are consumed while building the next level; the returned
//! artifact owns only the root statement and root proof.

use core::fmt;

use crate::profile::{FrozenProtocolProfile, vm_component_log_sizes};
use crate::profiled_channel::{
    ProfiledChannelError, ProfiledPoseidon2M31Channel, ProfiledPoseidon2M31MerkleChannel,
    RecursionVmClaimTranscript,
};
use crate::recursion_child::{RecursionChildError, adapt_recursion_child};
use crate::recursive_proof::{
    RecursionPreprocessing, RecursionProof, RecursionProofError, prove_binary_node,
    prove_empty_leaf, prove_segment_leaf,
};
use crate::segment_leaf::{
    SegmentLeafError, SegmentRunMetadata, adapt_vm_segment_leaf, segment_statement,
};
use crate::statement::{
    CompleteExecutionStatement, JobContext, MachineState, RootStatement, SpanStatement,
    StatementError,
};
use crate::vm_public_claim::{VmPublicClaimError, public_input_digest, public_output_digest};
use air::digest::{Digest8, IoDigest, MemoryDigest, ProgramDigest, VmPublicClaimDigest};
use prover::poseidon2_channel::Poseidon2M31MerkleHasher;
use prover::{
    Preprocessing, PublicData, VmTranscriptProvingError,
    prove_rv32im_with_channel_at_log_sizes_and_transcript,
};
#[cfg(feature = "parallel")]
use rayon::prelude::*;

struct SegmentProofTask {
    run_result: runner::RunResult,
    metadata: SegmentRunMetadata,
    statement: SpanStatement,
    claim_digest: VmPublicClaimDigest,
}

#[cfg(feature = "parallel")]
/// Two simultaneous proofs leave memory headroom for the host and verifier state.
const MAX_PARALLEL_TREE_PROOFS: usize = 2;

/// One complete recursive tree with no retained descendant proofs.
#[derive(Debug)]
pub struct RecursiveTreeProof {
    root_statement: RootStatement,
    proof: RecursionProof,
}

impl RecursiveTreeProof {
    /// Returns the canonical statement covering the complete execution.
    pub const fn root_statement(&self) -> &RootStatement {
        &self.root_statement
    }

    /// Returns the sole proof needed after tree construction.
    pub const fn proof(&self) -> &RecursionProof {
        &self.proof
    }

    /// Transfers ownership of the root statement and proof.
    pub fn into_parts(self) -> (RootStatement, RecursionProof) {
        (self.root_statement, self.proof)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct TreePlan {
    segment_count: u32,
    capacity: usize,
    level_count: u32,
}

impl TreePlan {
    fn new(segment_count: usize) -> Result<Self, TreeProverError> {
        if segment_count == 0 {
            return Err(TreeProverError::EmptySegmentRun);
        }
        let segment_count_u32 = u32::try_from(segment_count)
            .map_err(|_| TreeProverError::SegmentCountOutOfRange { segment_count })?;
        let capacity = segment_count.checked_next_power_of_two().ok_or(
            TreeProverError::TreeCapacityOverflow {
                segment_count: segment_count_u32,
            },
        )?;
        Ok(Self {
            segment_count: segment_count_u32,
            capacity,
            level_count: capacity.ilog2(),
        })
    }
}

/// Proves finalized VM segments and reduces them to one recursion proof.
pub fn prove_recursive_segments(
    profile: &FrozenProtocolProfile,
    vm_preprocessing: &Preprocessing<Poseidon2M31MerkleHasher>,
    recursion_preprocessing: &RecursionPreprocessing,
    run_results: Vec<runner::RunResult>,
) -> Result<RecursiveTreeProof, TreeProverError> {
    let plan = TreePlan::new(run_results.len())?;
    let total_cycles = run_results.iter().try_fold(0_u64, |total, segment| {
        total
            .checked_add(segment.cycles)
            .ok_or(TreeProverError::TotalCycleCountOverflow)
    })?;
    let public_data = run_results.iter().map(PublicData::new).collect::<Vec<_>>();
    let job = execution_job(profile, &public_data, total_cycles, plan.segment_count)?;
    let leaves = prove_segment_leaves(
        profile,
        vm_preprocessing,
        recursion_preprocessing,
        run_results,
        &public_data,
        job,
    )?;
    prove_recursion_tree(profile, recursion_preprocessing, leaves)
}

/// Segments one ELF execution by a runner row budget and proves every segment
/// against the fixed VM profile before returning only its recursive root.
pub fn prove_recursive_run(
    profile: &FrozenProtocolProfile,
    vm_preprocessing: &Preprocessing<Poseidon2M31MerkleHasher>,
    recursion_preprocessing: &RecursionPreprocessing,
    elf_bytes: &[u8],
    input: &[u8],
    max_rows: u32,
    max_cycles: u64,
) -> Result<RecursiveTreeProof, TreeProverError> {
    let run_results = runner::run_segments_by_capacity(elf_bytes, input, max_rows, max_cycles)?;
    prove_recursive_segments(
        profile,
        vm_preprocessing,
        recursion_preprocessing,
        run_results,
    )
}

/// Reduces ordered executed-leaf proofs through canonical padding and binary levels.
pub fn prove_recursion_tree(
    profile: &FrozenProtocolProfile,
    preprocessing: &RecursionPreprocessing,
    leaves: Vec<RecursionProof>,
) -> Result<RecursiveTreeProof, TreeProverError> {
    let plan = TreePlan::new(leaves.len())?;
    let job = *leaves
        .first()
        .expect("the non-empty tree plan has a first leaf")
        .statement
        .job();
    if job.segment_count() != plan.segment_count {
        return Err(TreeProverError::LeafCountMismatch {
            expected: job.segment_count(),
            actual: plan.segment_count,
        });
    }
    for (index, leaf) in leaves.iter().enumerate() {
        let expected_slot = u64::try_from(index).expect("u32-bounded leaf indices fit u64");
        if leaf.statement.job() != &job
            || leaf.statement.slots().height() != 0
            || leaf.statement.slots().first() != expected_slot
            || leaf.statement.body().is_empty()
        {
            return Err(TreeProverError::InvalidExecutedLeaf { index });
        }
    }

    if plan.capacity == 1 {
        let proof = leaves
            .into_iter()
            .next()
            .expect("capacity one has exactly one leaf");
        let root_statement = RootStatement::new(proof.statement)?;
        return Ok(RecursiveTreeProof {
            root_statement,
            proof,
        });
    }

    let mut nodes = leaves
        .iter()
        .map(|proof| adapt_recursion_child(profile, proof))
        .collect::<Result<Vec<_>, _>>()?;
    drop(leaves);
    let padding_statements = (usize::try_from(plan.segment_count).expect("u32 fits usize")
        ..plan.capacity)
        .map(|slot| {
            let slot = u32::try_from(slot)
                .map_err(|_| TreeProverError::PaddingSlotOutOfRange { slot: slot as u64 })?;
            Ok(SpanStatement::empty_leaf(job, slot)?)
        })
        .collect::<Result<Vec<_>, TreeProverError>>()?;
    #[cfg(feature = "parallel")]
    let padding = if padding_statements.len() <= 1 {
        padding_statements
            .into_iter()
            .map(|statement| {
                let proof = prove_empty_leaf(profile, preprocessing, &statement)?;
                Ok(adapt_recursion_child(profile, &proof)?)
            })
            .collect::<Result<Vec<_>, TreeProverError>>()?
    } else {
        let parallel = preprocessing.parallel_template(profile)?;
        let mut pending = padding_statements.into_iter();
        let mut padding = Vec::with_capacity(plan.capacity - nodes.len());
        loop {
            let wave = pending
                .by_ref()
                .take(MAX_PARALLEL_TREE_PROOFS)
                .collect::<Vec<_>>();
            if wave.is_empty() {
                break;
            }
            let proved = wave
                .into_par_iter()
                .map(|statement| {
                    // The fixed commitment is shared, while each worker owns
                    // the recorder arenas used to assemble its witness.
                    let local = parallel.worker_local(profile)?;
                    let proof = prove_empty_leaf(profile, &local, &statement)?;
                    Ok(adapt_recursion_child(profile, &proof)?)
                })
                .collect::<Result<Vec<_>, TreeProverError>>()?;
            padding.extend(proved);
        }
        padding
    };
    #[cfg(not(feature = "parallel"))]
    let padding = padding_statements
        .into_iter()
        .map(|statement| {
            let proof = prove_empty_leaf(profile, preprocessing, &statement)?;
            Ok(adapt_recursion_child(profile, &proof)?)
        })
        .collect::<Result<Vec<_>, TreeProverError>>()?;
    nodes.extend(padding);

    while nodes.len() > 2 {
        #[cfg(feature = "parallel")]
        let parents = {
            let parallel = preprocessing.parallel_template(profile)?;
            let mut parents = Vec::with_capacity(nodes.len() / 2);
            for wave in nodes.chunks(MAX_PARALLEL_TREE_PROOFS * 2) {
                let proved = wave
                    .par_chunks_exact(2)
                    .map(|children| {
                        // Independent parents share fixed commitment data and
                        // retain independent recorder arenas.
                        let local = parallel.worker_local(profile)?;
                        let proof = prove_binary_node(profile, &local, &children[0], &children[1])?;
                        Ok(adapt_recursion_child(profile, &proof)?)
                    })
                    .collect::<Result<Vec<_>, TreeProverError>>()?;
                parents.extend(proved);
            }
            parents
        };
        #[cfg(not(feature = "parallel"))]
        let parents = nodes
            .chunks_exact(2)
            .map(|children| {
                let proof = prove_binary_node(profile, preprocessing, &children[0], &children[1])?;
                Ok(adapt_recursion_child(profile, &proof)?)
            })
            .collect::<Result<Vec<_>, TreeProverError>>()?;
        nodes = parents;
    }

    let mut roots = nodes.into_iter();
    let left = roots.next().expect("the final level has a left child");
    let right = roots.next().expect("the final level has a right child");
    let proof = prove_binary_node(profile, preprocessing, &left, &right)?;
    let root_statement = RootStatement::new(proof.statement)?;
    Ok(RecursiveTreeProof {
        root_statement,
        proof,
    })
}

fn prove_segment_leaves(
    profile: &FrozenProtocolProfile,
    vm_preprocessing: &Preprocessing<Poseidon2M31MerkleHasher>,
    recursion_preprocessing: &RecursionPreprocessing,
    run_results: Vec<runner::RunResult>,
    public_data: &[PublicData],
    job: JobContext,
) -> Result<Vec<RecursionProof>, TreeProverError> {
    let mut tasks = Vec::with_capacity(run_results.len());
    let mut first_cycle = 0_u64;
    for (index, run_result) in run_results.into_iter().enumerate() {
        let segment_index =
            u32::try_from(index).map_err(|_| TreeProverError::SegmentCountOutOfRange {
                segment_count: index,
            })?;
        let metadata =
            SegmentRunMetadata::from_run_result(segment_index, first_cycle, &run_result)?;
        let statement = segment_statement(profile, &public_data[index], &metadata, job)?;
        let claim_digest = crate::vm_public_claim::vm_public_claim_digest(
            &public_data[index],
            profile.public_claim_shape(),
        )?;
        let cycle_count = run_result.cycles;
        tasks.push(SegmentProofTask {
            run_result,
            metadata,
            statement,
            claim_digest,
        });
        first_cycle = first_cycle
            .checked_add(cycle_count)
            .ok_or(TreeProverError::TotalCycleCountOverflow)?;
    }
    #[cfg(feature = "parallel")]
    let leaves = if tasks.len() == 1 {
        tasks
            .into_iter()
            .map(|task| {
                prove_segment_task(
                    profile,
                    vm_preprocessing,
                    recursion_preprocessing,
                    job,
                    task,
                )
            })
            .collect::<Result<Vec<_>, TreeProverError>>()?
    } else {
        let parallel = recursion_preprocessing.parallel_template(profile)?;
        let leaf_count = tasks.len();
        let mut pending = tasks.into_iter();
        let mut leaves = Vec::with_capacity(leaf_count);
        loop {
            let wave = pending
                .by_ref()
                .take(MAX_PARALLEL_TREE_PROOFS)
                .collect::<Vec<_>>();
            if wave.is_empty() {
                break;
            }
            let proved = wave
                .into_par_iter()
                .map(|task| {
                    // Workers reuse the immutable commitment but own the
                    // recorder arenas that materialize their proof witnesses.
                    let local = parallel.worker_local(profile)?;
                    prove_segment_task(profile, vm_preprocessing, &local, job, task)
                })
                .collect::<Result<Vec<_>, TreeProverError>>()?;
            leaves.extend(proved);
        }
        leaves
    };
    #[cfg(not(feature = "parallel"))]
    let leaves = tasks
        .into_iter()
        .map(|task| {
            prove_segment_task(
                profile,
                vm_preprocessing,
                recursion_preprocessing,
                job,
                task,
            )
        })
        .collect::<Result<Vec<_>, TreeProverError>>()?;
    Ok(leaves)
}

fn prove_segment_task(
    profile: &FrozenProtocolProfile,
    vm_preprocessing: &Preprocessing<Poseidon2M31MerkleHasher>,
    recursion_preprocessing: &RecursionPreprocessing,
    job: JobContext,
    task: SegmentProofTask,
) -> Result<RecursionProof, TreeProverError> {
    let channel = ProfiledPoseidon2M31Channel::for_vm_proof(
        profile.vm_plan(),
        profile.manifest().protocol_id(),
        &task.statement,
    )?;
    let transcript = RecursionVmClaimTranscript::new(task.claim_digest);
    let (proof, channel) = prove_rv32im_with_channel_at_log_sizes_and_transcript::<
        ProfiledPoseidon2M31MerkleChannel,
        _,
    >(
        task.run_result,
        profile.manifest().vm_pcs().config(),
        vm_preprocessing,
        vm_component_log_sizes(),
        channel,
        &transcript,
    )?;
    channel.finish()?;
    let leaf = adapt_vm_segment_leaf(profile, &proof, &task.metadata, job)?;
    Ok(prove_segment_leaf(profile, recursion_preprocessing, &leaf)?)
}

fn execution_job(
    profile: &FrozenProtocolProfile,
    public_data: &[PublicData],
    total_cycles: u64,
    segment_count: u32,
) -> Result<JobContext, TreeProverError> {
    let first = public_data
        .first()
        .ok_or(TreeProverError::EmptySegmentRun)?;
    let last = public_data.last().ok_or(TreeProverError::EmptySegmentRun)?;
    let program = ProgramDigest::from(required_root(0, "program root", first.program_root)?);
    let initial_state = machine_state(0, first, true)?;
    let final_index = public_data.len() - 1;
    let final_state = machine_state(final_index, last, false)?;
    let public_input = public_input_digest(&first.io_entries, profile.public_claim_shape())?;
    let public_output = public_output_digest(&last.io_entries, profile.public_claim_shape())?;
    let complete = CompleteExecutionStatement::new(
        profile.manifest().protocol_id(),
        program,
        initial_state,
        final_state,
        public_input,
        public_output,
        total_cycles,
    )?;
    Ok(JobContext::new(complete, segment_count)?)
}

fn machine_state(
    segment: usize,
    public_data: &PublicData,
    initial: bool,
) -> Result<MachineState, TreeProverError> {
    let (pc, registers, root, field) = if initial {
        (
            public_data.initial_pc,
            public_data.initial_regs,
            public_data.initial_rw_root,
            "initial read-write root",
        )
    } else {
        (
            public_data.final_pc,
            public_data.final_regs,
            public_data.final_rw_root,
            "final read-write root",
        )
    };
    Ok(MachineState::new(
        pc,
        registers,
        MemoryDigest::from(required_root(segment, field, root)?),
        IoDigest::from(Digest8::ZERO),
    )?)
}

fn required_root(
    segment: usize,
    field: &'static str,
    root: Option<[u32; 8]>,
) -> Result<Digest8, TreeProverError> {
    let words = root.ok_or(TreeProverError::MissingPublicRoot { segment, field })?;
    Digest8::try_from(words).map_err(|error| TreeProverError::NonCanonicalPublicRoot {
        segment,
        field,
        value: error.value(),
    })
}

/// Failure while deriving, proving, or reducing one recursive execution tree.
#[derive(Debug)]
pub enum TreeProverError {
    EmptySegmentRun,
    SegmentCountOutOfRange {
        segment_count: usize,
    },
    TreeCapacityOverflow {
        segment_count: u32,
    },
    TotalCycleCountOverflow,
    PaddingSlotOutOfRange {
        slot: u64,
    },
    LeafCountMismatch {
        expected: u32,
        actual: u32,
    },
    InvalidExecutedLeaf {
        index: usize,
    },
    MissingPublicRoot {
        segment: usize,
        field: &'static str,
    },
    NonCanonicalPublicRoot {
        segment: usize,
        field: &'static str,
        value: u32,
    },
    Run(runner::RunError),
    PublicClaim(VmPublicClaimError),
    Statement(StatementError),
    SegmentLeaf(SegmentLeafError),
    ProfiledChannel(ProfiledChannelError),
    VmProof(VmTranscriptProvingError<ProfiledChannelError>),
    RecursionProof(RecursionProofError),
    RecursionChild(RecursionChildError),
}

impl fmt::Display for TreeProverError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptySegmentRun => {
                formatter.write_str("a recursive tree needs at least one segment")
            }
            Self::SegmentCountOutOfRange { segment_count } => {
                write!(formatter, "segment count {segment_count} does not fit u32")
            }
            Self::TreeCapacityOverflow { segment_count } => {
                write!(
                    formatter,
                    "segment count {segment_count} has no tree capacity"
                )
            }
            Self::TotalCycleCountOverflow => formatter.write_str("total cycle count overflows u64"),
            Self::PaddingSlotOutOfRange { slot } => {
                write!(formatter, "padding slot {slot} does not fit u32")
            }
            Self::LeafCountMismatch { expected, actual } => {
                write!(formatter, "job declares {expected} leaves, got {actual}")
            }
            Self::InvalidExecutedLeaf { index } => {
                write!(
                    formatter,
                    "recursion leaf {index} is not its ordered executed slot"
                )
            }
            Self::MissingPublicRoot { segment, field } => {
                write!(formatter, "segment {segment} has no {field}")
            }
            Self::NonCanonicalPublicRoot {
                segment,
                field,
                value,
            } => write!(
                formatter,
                "segment {segment} {field} has non-canonical limb {value}"
            ),
            Self::Run(error) => error.fmt(formatter),
            Self::PublicClaim(error) => error.fmt(formatter),
            Self::Statement(error) => error.fmt(formatter),
            Self::SegmentLeaf(error) => error.fmt(formatter),
            Self::ProfiledChannel(error) => error.fmt(formatter),
            Self::VmProof(error) => error.fmt(formatter),
            Self::RecursionProof(error) => error.fmt(formatter),
            Self::RecursionChild(error) => error.fmt(formatter),
        }
    }
}

impl std::error::Error for TreeProverError {}

impl From<runner::RunError> for TreeProverError {
    fn from(error: runner::RunError) -> Self {
        Self::Run(error)
    }
}

impl From<VmPublicClaimError> for TreeProverError {
    fn from(error: VmPublicClaimError) -> Self {
        Self::PublicClaim(error)
    }
}

impl From<StatementError> for TreeProverError {
    fn from(error: StatementError) -> Self {
        Self::Statement(error)
    }
}

impl From<SegmentLeafError> for TreeProverError {
    fn from(error: SegmentLeafError) -> Self {
        Self::SegmentLeaf(error)
    }
}

impl From<ProfiledChannelError> for TreeProverError {
    fn from(error: ProfiledChannelError) -> Self {
        Self::ProfiledChannel(error)
    }
}

impl From<VmTranscriptProvingError<ProfiledChannelError>> for TreeProverError {
    fn from(error: VmTranscriptProvingError<ProfiledChannelError>) -> Self {
        Self::VmProof(error)
    }
}

impl From<RecursionProofError> for TreeProverError {
    fn from(error: RecursionProofError) -> Self {
        Self::RecursionProof(error)
    }
}

impl From<RecursionChildError> for TreeProverError {
    fn from(error: RecursionChildError) -> Self {
        Self::RecursionChild(error)
    }
}

#[cfg(test)]
mod tests {
    use prover::e2e::{ensure_guest_built, guest_bin_dir};
    use prover::poseidon2_channel::Poseidon2M31MerkleChannel;
    use rstest::rstest;

    use super::*;

    fn guest_elf(name: &str) -> Vec<u8> {
        ensure_guest_built();
        std::fs::read(guest_bin_dir().join(name)).expect("read the checked-in test guest")
    }

    #[rstest]
    #[case::one(1, 1, 0)]
    #[case::two(2, 2, 1)]
    #[case::three(3, 4, 2)]
    #[case::four(4, 4, 2)]
    #[case::eight(8, 8, 3)]
    fn tree_plan_uses_the_unique_minimal_capacity(
        #[case] segment_count: usize,
        #[case] capacity: usize,
        #[case] level_count: u32,
    ) {
        let plan = TreePlan::new(segment_count).expect("fixture segment count is valid");
        assert_eq!((plan.capacity, plan.level_count), (capacity, level_count));
    }

    #[test]
    fn tree_plan_rejects_an_empty_run() {
        assert!(matches!(
            TreePlan::new(0),
            Err(TreeProverError::EmptySegmentRun)
        ));
    }

    #[test]
    fn constant_guest_fits_the_frozen_vm_capacity_without_splitting() {
        let elf = guest_elf("constant");
        let run_result =
            runner::run(&elf, 10_000_000).expect("run the unsplit checked-in test guest");
        assert!(run_result.tracer.max_table_len() <= 1 << 11);
    }

    #[test]
    fn one_executed_recursion_leaf_is_the_complete_root() {
        let _assembly_guard = crate::segment_leaf::tests::universal_assembly_guard();
        let elf = guest_elf("constant");
        let run_result =
            runner::run(&elf, 10_000_000).expect("run the unsplit checked-in test guest");
        let profile = crate::profile::frozen_protocol_profile().expect("frozen profile is valid");
        let vm_preprocessing = prover::preprocess_with_channel::<Poseidon2M31MerkleChannel>(
            profile.manifest().vm_pcs().config(),
        );
        let preprocessing = crate::recursive_proof::preprocess_recursion(&profile)
            .expect("universal preprocessing is valid");
        let tree = prove_recursive_segments(
            &profile,
            &vm_preprocessing,
            &preprocessing,
            vec![run_result],
        )
        .expect("the one-segment guest produces a complete recursion tree");
        let (root_statement, proof) = tree.into_parts();
        assert!(
            crate::root::verify_recursive_root(
                &profile,
                &preprocessing,
                root_statement.complete_execution(),
                proof,
            )
            .is_ok()
        );
    }

    #[test]
    #[ignore = "full recursive tree proving is an explicit release conformance test"]
    fn capacity_segmented_guest_produces_a_two_leaf_root() {
        let _assembly_guard = crate::segment_leaf::tests::universal_assembly_guard();
        let elf = guest_elf("mulhu_alias");
        let profile = crate::profile::frozen_protocol_profile().expect("frozen profile is valid");
        let vm_preprocessing = prover::preprocess_with_channel::<Poseidon2M31MerkleChannel>(
            profile.manifest().vm_pcs().config(),
        );
        let preprocessing = crate::recursive_proof::preprocess_recursion(&profile)
            .expect("universal preprocessing is valid");
        let tree = prove_recursive_run(
            &profile,
            &vm_preprocessing,
            &preprocessing,
            &elf,
            &[],
            1 << 11,
            10_000_000,
        )
        .expect("the capacity-bounded guest produces a complete recursion tree");
        assert!(verified_tree_has_segment_count(
            &profile,
            &preprocessing,
            tree,
            2,
        ));
    }

    #[rstest]
    #[case::three(37, 3)]
    #[case::four(20, 4)]
    #[case::eight(8, 8)]
    #[ignore = "full recursive tree proving is an explicit release conformance test"]
    fn cycle_segmented_guest_produces_the_expected_root(
        #[case] segment_cycles: u32,
        #[case] expected_segment_count: u32,
    ) {
        let _assembly_guard = crate::segment_leaf::tests::universal_assembly_guard();
        let elf = guest_elf("mulhu_alias");
        let run_results =
            runner::run_segments_with_input(&elf, &[], Some(segment_cycles), 10_000_000)
                .expect("the measured cycle budget segments the checked-in guest");
        let actual_segment_count =
            u32::try_from(run_results.len()).expect("the measured segment count fits in u32");
        let profile = crate::profile::frozen_protocol_profile().expect("frozen profile is valid");
        let vm_preprocessing = prover::preprocess_with_channel::<Poseidon2M31MerkleChannel>(
            profile.manifest().vm_pcs().config(),
        );
        let preprocessing = crate::recursive_proof::preprocess_recursion(&profile)
            .expect("universal preprocessing is valid");
        let tree =
            prove_recursive_segments(&profile, &vm_preprocessing, &preprocessing, run_results)
                .expect("the measured segments produce a complete recursion tree");
        assert!(
            actual_segment_count == expected_segment_count
                && verified_tree_has_segment_count(
                    &profile,
                    &preprocessing,
                    tree,
                    expected_segment_count,
                )
        );
    }

    fn verified_tree_has_segment_count(
        profile: &FrozenProtocolProfile,
        preprocessing: &RecursionPreprocessing,
        tree: RecursiveTreeProof,
        expected_segment_count: u32,
    ) -> bool {
        let (root_statement, proof) = tree.into_parts();
        let statement = root_statement.statement();
        let span = statement.body().executed_span();
        let expected_span = statement.slots().first() == 0
            && statement.slots().height() == statement.job().slot_height()
            && span.is_some_and(|span| {
                span.first_segment() == 0
                    && span.segment_count() == expected_segment_count
                    && span.first_cycle() == 0
                    && span.cycle_count() == statement.job().total_cycles()
            });
        expected_span
            && crate::recursive_proof::verify_recursion_proof(
                profile,
                preprocessing,
                profile.manifest().protocol_id(),
                statement,
                proof,
            )
            .is_ok()
    }
}
