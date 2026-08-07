//! Frozen protocol profile derived from the live VM and universal AIR rosters.
//!
//! The constructors in this module are the only source of recursive verifier
//! geometry. They compile both AIR rosters, derive fixed proof shapes from the
//! resulting STWO column layouts, bind the trusted control plans, and expose
//! exact wire types. A source change that alters any bound value therefore
//! produces a different protocol identifier or makes profile construction fail.

use core::fmt;

use air::digest::{
    Digest8, HashSuiteDigest, M31Word, Poseidon2AirProgramDigest, RecursionAirProgramDigest,
    RecursionPreprocessingDigest, VmAirProgramDigest, VmPreprocessingDigest,
};
use prover::components::{COMPONENT_COUNT, COMPONENT_NAMES};
use prover::poseidon2_channel::poseidon2_hash_m31_words;
use prover::relations::{PreProcessedTrace, Relations};
use stwo::core::vcs_lifted::verifier::LOG_PACKED_LEAF_SIZE;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;

use crate::kernel::{BoundVerifierPlans, VerifierControlPlan, VerifierProgramSpec, VerifierSchema};
use crate::protocol::{
    FixedProofShape, OptionalM31Word, PcsParameters, ProtocolManifest, ProtocolVersion,
    ValidatedProtocolManifest,
};
use crate::recursion_air_program::{
    RecursionAirProgram, UNIVERSAL_COMPONENT_COUNT, UniversalComponentLogSizes,
    universal_preprocessed_column_ids,
};
use crate::universal_relations::UNIVERSAL_RELATION_COUNT;
use crate::vm_air_program::{Poseidon2AirProgram, VM_AIR_COMPONENT_COUNT, VmAirProgram};
use crate::vm_pcs_layout::VmPcsLayout;
use crate::vm_public_claim::VmPublicClaimShape;
use crate::vm_public_logup_circuit::build_vm_public_logup_reference;
use crate::wire::{
    FixedStarkProofWire, RecursiveProofBytes, RecursiveProofWire, recursive_proof_bytes,
};

const PREPROCESSING_REGISTRY_ENCODING: u16 = 1;
const VM_PREPROCESSING_HASH_DOMAIN: u16 = 0x5056;
const RECURSION_PREPROCESSING_HASH_DOMAIN: u16 = 0x5052;
const HASH_SUITE_HASH_DOMAIN: u16 = 0x4853;

/// Version of the currently supported recursive protocol.
pub const PROTOCOL_VERSION: u16 = 1;
/// Interaction proof-of-work emitted by the generated VM AIR roster.
pub const INTERACTION_POW_BITS: u32 = prover::relations::INTERACTION_POW_BITS;
/// PCS proof-of-work selected for both proof systems.
pub const PCS_POW_BITS: u16 = 16;
/// FRI rate is one half for both proof systems.
pub const FRI_LOG_BLOWUP_FACTOR: u16 = 1;
/// Number of independently authenticated FRI queries.
pub const FRI_QUERY_COUNT: usize = 193;
/// Every full FRI layer folds sixteen evaluations at once.
pub const FRI_FOLD_STEP: u16 = 4;
/// Both fixed proof systems have four commitment rounds.
pub const COMMITMENT_TREE_COUNT: usize = 4;
/// The fixed VM degree bound produces five FRI layers.
pub const VM_FRI_LAYER_COUNT: usize = 5;
/// The universal arithmetic capacity produces six FRI layers.
pub const RECURSION_FRI_LAYER_COUNT: usize = 6;
/// Largest fold subset carried by one fixed FRI query slot.
pub const MAX_FRI_FOLD_WIDTH: usize = 16;
/// Exact largest authentication path in the fixed VM proof.
pub const VM_MAX_MERKLE_DEPTH: usize = 21;
/// Exact largest authentication path in the universal recursion proof.
pub const RECURSION_MAX_MERKLE_DEPTH: usize = 23;
/// Constant final polynomial under a zero last-layer log-degree bound.
pub const LAST_LAYER_COEFFICIENT_COUNT: usize = 1;

/// Maximum public input covered by one recursive VM leaf, in machine words.
pub const MAX_PUBLIC_INPUT_WORDS: u32 = 1024;
/// Maximum public output coverage includes the length word and 4 KiB of data.
pub const MAX_PUBLIC_OUTPUT_WORDS: u32 = 1025;
/// Exact canonical word count of the frozen VM public-claim capacity.
///
/// The profile constructor checks this constant against the canonical claim
/// encoder, so a claim-layout change cannot leave the fixed leaf type stale.
pub const VM_PUBLIC_CLAIM_WORD_COUNT: usize = 10_530;

/// Maximum rows allocated to ordinary instruction and access components.
pub const VM_DYNAMIC_COMPONENT_LOG_SIZE: u32 = 6;
/// Fixed capacity for program, memory, Merkle, and Poseidon commitment work.
///
/// Even a short segment finalizes a complete sparse commitment boundary, so
/// these tables require more rows than its instruction tables.
pub const VM_COMMITMENT_COMPONENT_LOG_SIZE: u32 = 11;
/// VM table count compiled from the checked-in component roster.
pub const VM_TABLE_COUNT: usize = 1556;
/// VM OODS samples compiled from the checked-in component roster.
pub const VM_SAMPLED_VALUE_COUNT: usize = 1664;
/// VM AIR constraints compiled from the checked-in component roster.
pub const VM_AIR_INSTRUCTION_COUNT: usize = 629;
/// VM preprocessing columns in canonical commitment order.
pub const VM_PREPROCESSED_COLUMN_COUNT: usize = 14;
/// Flat authenticated VM values across every raw query.
pub const VM_QUERY_VALUE_COUNT: usize = VM_TABLE_COUNT * FRI_QUERY_COUNT;
/// One trace path exists for every commitment tree and query.
pub const VM_TRACE_PATH_COUNT: usize = COMMITMENT_TREE_COUNT * FRI_QUERY_COUNT;

/// Frozen capacity of the detached Poseidon2 table.
pub const POSEIDON2_COMPONENT_LOG_SIZE: u32 = 11;
/// Detached Poseidon2 committed columns across all four trees.
pub const POSEIDON2_TABLE_COUNT: usize = 461;
/// Detached Poseidon2 OODS samples in STWO order.
pub const POSEIDON2_SAMPLED_VALUE_COUNT: usize = 465;
/// Detached Poseidon2 constraints compiled from the direct DSL component.
pub const POSEIDON2_AIR_INSTRUCTION_COUNT: usize = 432;
/// The detached composition degree produces three FRI layers.
pub const POSEIDON2_FRI_LAYER_COUNT: usize = 3;
/// The detached proof authenticates three nonempty commitment trees.
pub const POSEIDON2_TRACE_PATH_COUNT: usize = 3 * FRI_QUERY_COUNT;
/// Flat detached queried values across every raw query.
pub const POSEIDON2_QUERY_VALUE_COUNT: usize = POSEIDON2_TABLE_COUNT * FRI_QUERY_COUNT;
/// Largest detached trace or FRI authentication path.
pub const POSEIDON2_MAX_MERKLE_DEPTH: usize = 12;

/// Universal table count compiled from the checked-in component roster.
pub const RECURSION_TABLE_COUNT: usize = 2221;
/// Universal OODS samples compiled from the checked-in component roster.
pub const RECURSION_SAMPLED_VALUE_COUNT: usize = 2365;
/// Universal AIR constraints compiled from the checked-in component roster.
pub const RECURSION_AIR_INSTRUCTION_COUNT: usize = 1319;
/// Universal preprocessing columns in canonical commitment order.
pub const RECURSION_PREPROCESSED_COLUMN_COUNT: usize = 587;
/// Flat authenticated recursion values across every raw query.
pub const RECURSION_QUERY_VALUE_COUNT: usize = RECURSION_TABLE_COUNT * FRI_QUERY_COUNT;
/// One recursion trace path exists for every commitment tree and query.
pub const RECURSION_TRACE_PATH_COUNT: usize = COMMITMENT_TREE_COUNT * FRI_QUERY_COUNT;

/// Canonical protocol identifier limbs for cross-language conformance.
pub const PROTOCOL_ID_WORDS: [u32; 8] = [
    1812854606, 380357156, 1799778124, 326217952, 1577751674, 998653010, 10229157, 1305708380,
];
/// Digest of all ordered VM preprocessing identifiers and log sizes.
pub const VM_PREPROCESSING_WORDS: [u32; 8] = [
    1116674675, 115993613, 1828303903, 4516276, 1991287759, 768823330, 1822402021, 923054849,
];
/// Digest of all ordered universal preprocessing identifiers and log sizes.
pub const RECURSION_PREPROCESSING_WORDS: [u32; 8] = [
    688718528, 1094194459, 551156854, 1954590462, 871724839, 1809913092, 834828251, 1240016990,
];

/// Manifest type whose array dimensions are the actual AIR layouts.
pub type FrozenProtocolManifest = ProtocolManifest<
    VM_TABLE_COUNT,
    COMMITMENT_TREE_COUNT,
    VM_FRI_LAYER_COUNT,
    RECURSION_TABLE_COUNT,
    COMMITMENT_TREE_COUNT,
    RECURSION_FRI_LAYER_COUNT,
>;

/// Validated form of [`FrozenProtocolManifest`].
pub type ValidatedFrozenProtocolManifest = ValidatedProtocolManifest<
    VM_TABLE_COUNT,
    COMMITMENT_TREE_COUNT,
    VM_FRI_LAYER_COUNT,
    RECURSION_TABLE_COUNT,
    COMMITMENT_TREE_COUNT,
    RECURSION_FRI_LAYER_COUNT,
>;

/// Fixed wire accepted for one authenticated VM proof.
pub type VmProofWire = FixedStarkProofWire<
    COMMITMENT_TREE_COUNT,
    VM_AIR_COMPONENT_COUNT,
    VM_SAMPLED_VALUE_COUNT,
    VM_QUERY_VALUE_COUNT,
    VM_TRACE_PATH_COUNT,
    VM_FRI_LAYER_COUNT,
    FRI_QUERY_COUNT,
    MAX_FRI_FOLD_WIDTH,
    LAST_LAYER_COEFFICIENT_COUNT,
    VM_MAX_MERKLE_DEPTH,
>;

/// Fixed wire accepted for the detached Poseidon2 constituent.
pub type Poseidon2ProofWire = FixedStarkProofWire<
    COMMITMENT_TREE_COUNT,
    1,
    POSEIDON2_SAMPLED_VALUE_COUNT,
    POSEIDON2_QUERY_VALUE_COUNT,
    POSEIDON2_TRACE_PATH_COUNT,
    POSEIDON2_FRI_LAYER_COUNT,
    FRI_QUERY_COUNT,
    MAX_FRI_FOLD_WIDTH,
    LAST_LAYER_COEFFICIENT_COUNT,
    POSEIDON2_MAX_MERKLE_DEPTH,
>;

/// Fixed STARK payload produced by the universal recursion AIR.
pub type RecursionStarkProofWire = FixedStarkProofWire<
    COMMITMENT_TREE_COUNT,
    UNIVERSAL_COMPONENT_COUNT,
    RECURSION_SAMPLED_VALUE_COUNT,
    RECURSION_QUERY_VALUE_COUNT,
    RECURSION_TRACE_PATH_COUNT,
    RECURSION_FRI_LAYER_COUNT,
    FRI_QUERY_COUNT,
    MAX_FRI_FOLD_WIDTH,
    LAST_LAYER_COEFFICIENT_COUNT,
    RECURSION_MAX_MERKLE_DEPTH,
>;

/// One statement and one fixed-size universal recursion proof.
pub type RootProofWire = RecursiveProofWire<
    COMMITMENT_TREE_COUNT,
    UNIVERSAL_COMPONENT_COUNT,
    RECURSION_SAMPLED_VALUE_COUNT,
    RECURSION_QUERY_VALUE_COUNT,
    RECURSION_TRACE_PATH_COUNT,
    RECURSION_FRI_LAYER_COUNT,
    FRI_QUERY_COUNT,
    MAX_FRI_FOLD_WIDTH,
    LAST_LAYER_COEFFICIENT_COUNT,
    RECURSION_MAX_MERKLE_DEPTH,
>;

/// Exact serialized size of every proof produced by the universal AIR.
pub const ROOT_PROOF_BYTE_SIZE: usize = recursive_proof_bytes::<
    COMMITMENT_TREE_COUNT,
    UNIVERSAL_COMPONENT_COUNT,
    RECURSION_SAMPLED_VALUE_COUNT,
    RECURSION_QUERY_VALUE_COUNT,
    RECURSION_TRACE_PATH_COUNT,
    RECURSION_FRI_LAYER_COUNT,
    FRI_QUERY_COUNT,
    MAX_FRI_FOLD_WIDTH,
    LAST_LAYER_COEFFICIENT_COUNT,
    RECURSION_MAX_MERKLE_DEPTH,
>();

/// Exact-size byte container for [`RootProofWire`].
pub type RootProofBytes = RecursiveProofBytes<ROOT_PROOF_BYTE_SIZE>;

type FrozenVerifierPlans = BoundVerifierPlans<
    VM_TABLE_COUNT,
    COMMITMENT_TREE_COUNT,
    VM_FRI_LAYER_COUNT,
    RECURSION_TABLE_COUNT,
    COMMITMENT_TREE_COUNT,
    RECURSION_FRI_LAYER_COUNT,
>;

/// Fully checked programs, manifest, layouts, and verifier schedules.
pub struct FrozenProtocolProfile {
    public_claim_shape: VmPublicClaimShape,
    vm_program: VmAirProgram,
    poseidon2_program: Poseidon2AirProgram,
    poseidon2_proof_shape:
        FixedProofShape<POSEIDON2_TABLE_COUNT, COMMITMENT_TREE_COUNT, POSEIDON2_FRI_LAYER_COUNT>,
    recursion_program: RecursionAirProgram,
    vm_layout: VmPcsLayout,
    plans: FrozenVerifierPlans,
}

impl FrozenProtocolProfile {
    pub const fn public_claim_shape(&self) -> VmPublicClaimShape {
        self.public_claim_shape
    }

    pub const fn vm_program(&self) -> &VmAirProgram {
        &self.vm_program
    }

    pub const fn poseidon2_program(&self) -> &Poseidon2AirProgram {
        &self.poseidon2_program
    }

    pub const fn poseidon2_proof_shape(
        &self,
    ) -> &FixedProofShape<POSEIDON2_TABLE_COUNT, COMMITMENT_TREE_COUNT, POSEIDON2_FRI_LAYER_COUNT>
    {
        &self.poseidon2_proof_shape
    }

    pub const fn poseidon2_plan(&self) -> &VerifierControlPlan {
        self.plans.poseidon2()
    }

    pub const fn recursion_program(&self) -> &RecursionAirProgram {
        &self.recursion_program
    }

    pub const fn vm_layout(&self) -> &VmPcsLayout {
        &self.vm_layout
    }

    pub const fn manifest(&self) -> &ValidatedFrozenProtocolManifest {
        self.plans.manifest()
    }

    pub const fn vm_plan(&self) -> &VerifierControlPlan {
        self.plans.vm()
    }

    pub const fn recursion_plan(&self) -> &VerifierControlPlan {
        self.plans.recursion()
    }
}

/// A frozen source roster no longer agrees with its checked-in profile.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProfileError {
    stage: &'static str,
    detail: String,
}

impl ProfileError {
    fn at(stage: &'static str, error: impl fmt::Display) -> Self {
        Self {
            stage,
            detail: error.to_string(),
        }
    }

    fn mismatch(
        stage: &'static str,
        expected: impl fmt::Display,
        actual: impl fmt::Display,
    ) -> Self {
        Self {
            stage,
            detail: format!("expected {expected}, found {actual}"),
        }
    }
}

impl fmt::Display for ProfileError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}: {}", self.stage, self.detail)
    }
}

impl std::error::Error for ProfileError {}

/// Builds and cross-checks every verifier-owned value in the frozen profile.
pub fn frozen_protocol_profile() -> Result<FrozenProtocolProfile, ProfileError> {
    let public_claim_shape =
        VmPublicClaimShape::new(MAX_PUBLIC_INPUT_WORDS, MAX_PUBLIC_OUTPUT_WORDS)
            .map_err(|error| ProfileError::at("VM public-claim shape", error))?;
    if public_claim_shape.claim_word_count() != VM_PUBLIC_CLAIM_WORD_COUNT {
        return Err(ProfileError::mismatch(
            "VM public-claim word count",
            VM_PUBLIC_CLAIM_WORD_COUNT,
            public_claim_shape.claim_word_count(),
        ));
    }
    build_frozen_protocol_profile(public_claim_shape)
}

fn build_frozen_protocol_profile(
    public_claim_shape: VmPublicClaimShape,
) -> Result<FrozenProtocolProfile, ProfileError> {
    let vm_program = VmAirProgram::new(vm_component_log_sizes())
        .map_err(|error| ProfileError::at("VM AIR program", error))?;
    validate_vm_program_constants(&vm_program)?;
    let poseidon2_program = Poseidon2AirProgram::new(POSEIDON2_COMPONENT_LOG_SIZE)
        .map_err(|error| ProfileError::at("Poseidon2 AIR program", error))?;
    validate_poseidon2_program_constants(&poseidon2_program)?;

    let recursion_ids = recursion_preprocessed_column_ids();
    let recursion_program =
        RecursionAirProgram::new(recursion_component_log_sizes(), &recursion_ids)
            .map_err(|error| ProfileError::at("recursion AIR program", error))?;
    validate_recursion_program_constants(&recursion_program, recursion_ids.len())?;

    let pcs = pcs_parameters()?;
    let validated_pcs = pcs
        .validate()
        .map_err(|error| ProfileError::at("PCS parameters", error))?;
    let vm_proof_shape = derive_proof_shape::<VM_TABLE_COUNT, VM_FRI_LAYER_COUNT>(
        vm_program.column_log_sizes(),
        VM_AIR_COMPONENT_COUNT,
        VM_SAMPLED_VALUE_COUNT,
    )?;
    let poseidon2_proof_shape =
        derive_proof_shape::<POSEIDON2_TABLE_COUNT, POSEIDON2_FRI_LAYER_COUNT>(
            poseidon2_program.column_log_sizes(),
            1,
            POSEIDON2_SAMPLED_VALUE_COUNT,
        )?;
    let recursion_proof_shape =
        derive_proof_shape::<RECURSION_TABLE_COUNT, RECURSION_FRI_LAYER_COUNT>(
            recursion_program.column_log_sizes(),
            UNIVERSAL_COMPONENT_COUNT,
            RECURSION_SAMPLED_VALUE_COUNT,
        )?;

    let vm_layout = VmPcsLayout::new(&vm_program, validated_pcs, &vm_proof_shape)
        .map_err(|error| ProfileError::at("VM PCS layout", error))?;
    validate_recursion_shape(&recursion_program, validated_pcs, &recursion_proof_shape)?;

    let public_logup = build_vm_public_logup_reference(
        public_claim_shape,
        u32::try_from(VM_AIR_COMPONENT_COUNT)
            .map_err(|error| ProfileError::at("VM claimed-sum count", error))?,
    )
    .map_err(|error| ProfileError::at("VM public LogUp", error))?;
    let vm_spec = VerifierProgramSpec::new(
        VerifierSchema::Vm,
        count_u32("VM relation challenges", Relations::DESCRIPTORS.len())?,
        public_logup.public_term_count(),
        count_u32("VM AIR instructions", vm_program.air_instruction_count())?,
        count_u32("VM relation closures", Relations::DESCRIPTORS.len())?,
    )
    .map_err(|error| ProfileError::at("VM verifier program", error))?;
    let recursion_spec = VerifierProgramSpec::new(
        VerifierSchema::Recursion,
        count_u32("recursion relation challenges", UNIVERSAL_RELATION_COUNT)?,
        0,
        count_u32(
            "recursion AIR instructions",
            recursion_program.air_instruction_count(),
        )?,
        count_u32("recursion relation closures", UNIVERSAL_RELATION_COUNT)?,
    )
    .map_err(|error| ProfileError::at("recursion verifier program", error))?;
    let poseidon2_spec = VerifierProgramSpec::new(
        VerifierSchema::Poseidon2,
        count_u32(
            "Poseidon2 relation challenges",
            Relations::DESCRIPTORS.len(),
        )?,
        0,
        count_u32(
            "Poseidon2 AIR instructions",
            poseidon2_program.air_instruction_count(),
        )?,
        count_u32("Poseidon2 relation closures", Relations::DESCRIPTORS.len())?,
    )
    .map_err(|error| ProfileError::at("Poseidon2 verifier program", error))?;
    let vm_plan = VerifierControlPlan::new(vm_spec, pcs, &vm_proof_shape)
        .map_err(|error| ProfileError::at("VM verifier plan", error))?;
    let recursion_plan = VerifierControlPlan::new(recursion_spec, pcs, &recursion_proof_shape)
        .map_err(|error| ProfileError::at("recursion verifier plan", error))?;
    let poseidon2_plan = VerifierControlPlan::new(poseidon2_spec, pcs, &poseidon2_proof_shape)
        .map_err(|error| ProfileError::at("Poseidon2 verifier plan", error))?;

    let vm_preprocessed_ids = vm_preprocessed_column_ids();
    let vm_preprocessed_log_sizes = PreProcessedTrace::column_log_sizes();
    let recursion_preprocessed_log_sizes = recursion_program
        .column_log_sizes()
        .first()
        .ok_or_else(|| ProfileError::at("recursion preprocessing", "missing tree zero"))?;
    let manifest = ProtocolManifest {
        version: ProtocolVersion(M31Word::from(PROTOCOL_VERSION)),
        hash_suite: hash_suite_digest(),
        vm_preprocessing: VmPreprocessingDigest::from(preprocessing_registry_digest(
            &vm_preprocessed_ids,
            &vm_preprocessed_log_sizes,
            VM_PREPROCESSING_HASH_DOMAIN,
        )?),
        recursion_preprocessing: RecursionPreprocessingDigest::from(preprocessing_registry_digest(
            &recursion_ids,
            recursion_preprocessed_log_sizes,
            RECURSION_PREPROCESSING_HASH_DOMAIN,
        )?),
        vm_air_program: VmAirProgramDigest::from(vm_plan.digest()),
        poseidon2_air_program: Poseidon2AirProgramDigest::from(poseidon2_plan.digest()),
        recursion_air_program: RecursionAirProgramDigest::from(recursion_plan.digest()),
        vm_pcs: pcs,
        recursion_pcs: pcs,
        vm_proof_shape,
        recursion_proof_shape,
    };
    let manifest = manifest
        .validate()
        .map_err(|error| ProfileError::at("protocol manifest", error))?;
    let plans = FrozenVerifierPlans::new(manifest, vm_plan, poseidon2_plan, recursion_plan)
        .map_err(|error| ProfileError::at("verifier plan binding", error))?;
    Ok(FrozenProtocolProfile {
        public_claim_shape,
        vm_program,
        poseidon2_program,
        poseidon2_proof_shape,
        recursion_program,
        vm_layout,
        plans,
    })
}

/// Returns the fixed VM component capacities in generated roster order.
pub fn vm_component_log_sizes() -> [u32; COMPONENT_COUNT] {
    core::array::from_fn(|index| match COMPONENT_NAMES[index] {
        "bitwise" => 18,
        "range_check_20" | "range_check_8_8_4" => 20,
        "range_check_8_11" => 19,
        "range_check_8_8" => 16,
        "range_check_m31" => 15,
        "program" | "memory" | "merkle" | "poseidon2" => VM_COMMITMENT_COMPONENT_LOG_SIZE,
        _ => VM_DYNAMIC_COMPONENT_LOG_SIZE,
    })
}

/// Returns the fixed universal component capacities in canonical roster order.
pub fn recursion_component_log_sizes() -> UniversalComponentLogSizes {
    [
        15, 13, 13, 10, 16, 15, 4, 4, 7, 8, 11, 11, 14, 11, 11, 17, 15, 12, 18, 12, 10, 14, 6, 18,
        21, 16, 14, 13, 13, 18, 22, 16, 22, 16, 19, 16,
    ]
}

/// Returns every VM preprocessing identifier in commitment-column order.
pub fn vm_preprocessed_column_ids() -> Vec<PreProcessedColumnId> {
    PreProcessedTrace::column_ids()
}

/// Returns every universal preprocessing identifier in commitment-column order.
pub fn recursion_preprocessed_column_ids() -> Vec<PreProcessedColumnId> {
    universal_preprocessed_column_ids(&recursion_component_log_sizes())
}

fn pcs_parameters() -> Result<PcsParameters, ProfileError> {
    Ok(PcsParameters {
        interaction_pow_bits: profile_word(INTERACTION_POW_BITS)?,
        pow_bits: M31Word::from(PCS_POW_BITS),
        fri_log_blowup_factor: M31Word::from(FRI_LOG_BLOWUP_FACTOR),
        fri_n_queries: M31Word::from(FRI_QUERY_COUNT as u16),
        fri_log_last_layer_degree_bound: M31Word::ZERO,
        fri_fold_step: M31Word::from(FRI_FOLD_STEP),
        lifting_log_size: OptionalM31Word::None,
    })
}

fn derive_proof_shape<const N_TABLES: usize, const N_FRI_LAYERS: usize>(
    column_log_sizes: &[Vec<u32>],
    claimed_sum_count: usize,
    sampled_value_count: usize,
) -> Result<FixedProofShape<N_TABLES, COMMITMENT_TREE_COUNT, N_FRI_LAYERS>, ProfileError> {
    if column_log_sizes.len() != COMMITMENT_TREE_COUNT {
        return Err(ProfileError::mismatch(
            "commitment tree count",
            COMMITMENT_TREE_COUNT,
            column_log_sizes.len(),
        ));
    }
    let flat_log_sizes = column_log_sizes
        .iter()
        .flatten()
        .copied()
        .map(profile_word)
        .collect::<Result<Vec<_>, _>>()?;
    let table_log_sizes: [M31Word; N_TABLES] =
        flat_log_sizes.try_into().map_err(|actual: Vec<M31Word>| {
            ProfileError::mismatch("committed table count", N_TABLES, actual.len())
        })?;
    let tree_heights = column_log_sizes
        .iter()
        .map(|tree| {
            let Some(max_log_size) = tree.iter().copied().max() else {
                return Ok(M31Word::ZERO);
            };
            max_log_size
                .checked_add(u32::from(FRI_LOG_BLOWUP_FACTOR))
                .ok_or_else(|| ProfileError::at("commitment tree height", "overflow"))
                .and_then(profile_word)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let tree_heights: [M31Word; COMMITMENT_TREE_COUNT] =
        tree_heights.try_into().map_err(|actual: Vec<M31Word>| {
            ProfileError::mismatch("commitment tree count", COMMITMENT_TREE_COUNT, actual.len())
        })?;
    let lifting_log_size = tree_heights
        .last()
        .copied()
        .ok_or_else(|| ProfileError::at("FRI geometry", "missing lifting tree"))?
        .as_u32();
    let (fri_layer_fold_widths, fri_layer_tree_heights) =
        derive_fri_geometry::<N_FRI_LAYERS>(lifting_log_size)?;
    let queried_value_count = N_TABLES
        .checked_mul(FRI_QUERY_COUNT)
        .ok_or_else(|| ProfileError::at("queried value count", "overflow"))?;
    Ok(FixedProofShape {
        claimed_sum_count: count_word("claimed sums", claimed_sum_count)?,
        sampled_value_count: count_word("sampled values", sampled_value_count)?,
        queried_value_count: count_word("queried values", queried_value_count)?,
        trace_path_count: count_word(
            "trace paths",
            tree_heights
                .iter()
                .filter(|height| **height != M31Word::ZERO)
                .count()
                * FRI_QUERY_COUNT,
        )?,
        raw_query_count: count_word("raw queries", FRI_QUERY_COUNT)?,
        last_layer_coefficient_count: count_word(
            "last-layer coefficients",
            LAST_LAYER_COEFFICIENT_COUNT,
        )?,
        table_log_sizes,
        tree_heights,
        fri_layer_fold_widths,
        fri_layer_tree_heights,
    })
}

fn derive_fri_geometry<const N_FRI_LAYERS: usize>(
    lifting_log_size: u32,
) -> Result<([M31Word; N_FRI_LAYERS], [M31Word; N_FRI_LAYERS]), ProfileError> {
    let column_log_degree = lifting_log_size
        .checked_sub(u32::from(FRI_LOG_BLOWUP_FACTOR))
        .ok_or_else(|| ProfileError::at("FRI geometry", "blowup exceeds lifting domain"))?;
    let layer_count = column_log_degree.div_ceil(u32::from(FRI_FOLD_STEP)) as usize;
    if layer_count != N_FRI_LAYERS {
        return Err(ProfileError::mismatch(
            "FRI layer count",
            N_FRI_LAYERS,
            layer_count,
        ));
    }
    let mut widths = [M31Word::ZERO; N_FRI_LAYERS];
    let mut heights = [M31Word::ZERO; N_FRI_LAYERS];
    let mut remaining_folds = column_log_degree;
    let mut layer_domain_log_size = lifting_log_size;
    for layer in 0..N_FRI_LAYERS {
        let layer_fold_step = remaining_folds.min(u32::from(FRI_FOLD_STEP));
        let width = 1_u32
            .checked_shl(layer_fold_step)
            .ok_or_else(|| ProfileError::at("FRI fold width", "overflow"))?;
        let packed_leaf_log_size = if layer_fold_step > 1 {
            LOG_PACKED_LEAF_SIZE.min(layer_domain_log_size)
        } else {
            0
        };
        widths[layer] = profile_word(width)?;
        heights[layer] = profile_word(layer_domain_log_size - packed_leaf_log_size)?;
        layer_domain_log_size -= layer_fold_step;
        remaining_folds -= layer_fold_step;
    }
    Ok((widths, heights))
}

fn validate_vm_program_constants(program: &VmAirProgram) -> Result<(), ProfileError> {
    let actual = [
        program.column_log_sizes().iter().flatten().count(),
        program.sample_coordinates().len(),
        program.air_instruction_count(),
        vm_preprocessed_column_ids().len(),
    ];
    let expected = [
        VM_TABLE_COUNT,
        VM_SAMPLED_VALUE_COUNT,
        VM_AIR_INSTRUCTION_COUNT,
        VM_PREPROCESSED_COLUMN_COUNT,
    ];
    if actual == expected {
        Ok(())
    } else {
        Err(ProfileError::mismatch(
            "VM generated dimensions",
            format_args!("{expected:?}"),
            format_args!("{actual:?}"),
        ))
    }
}

fn validate_poseidon2_program_constants(program: &Poseidon2AirProgram) -> Result<(), ProfileError> {
    let actual = [
        program.column_log_sizes().iter().flatten().count(),
        program.sample_coordinates().len(),
        program.air_instruction_count(),
    ];
    let expected = [
        POSEIDON2_TABLE_COUNT,
        POSEIDON2_SAMPLED_VALUE_COUNT,
        POSEIDON2_AIR_INSTRUCTION_COUNT,
    ];
    if actual == expected {
        Ok(())
    } else {
        Err(ProfileError::mismatch(
            "Poseidon2 generated dimensions",
            format_args!("{expected:?}"),
            format_args!("{actual:?}"),
        ))
    }
}

fn validate_recursion_program_constants(
    program: &RecursionAirProgram,
    preprocessed_count: usize,
) -> Result<(), ProfileError> {
    let actual = [
        program.column_log_sizes().iter().flatten().count(),
        program.sample_coordinates().len(),
        program.air_instruction_count(),
        preprocessed_count,
    ];
    let expected = [
        RECURSION_TABLE_COUNT,
        RECURSION_SAMPLED_VALUE_COUNT,
        RECURSION_AIR_INSTRUCTION_COUNT,
        RECURSION_PREPROCESSED_COLUMN_COUNT,
    ];
    if actual == expected {
        Ok(())
    } else {
        Err(ProfileError::mismatch(
            "recursion generated dimensions",
            format_args!("{expected:?}"),
            format_args!("{actual:?}"),
        ))
    }
}

fn validate_recursion_shape(
    program: &RecursionAirProgram,
    pcs: crate::protocol::ValidatedPcsParameters,
    shape: &FixedProofShape<
        RECURSION_TABLE_COUNT,
        COMMITMENT_TREE_COUNT,
        RECURSION_FRI_LAYER_COUNT,
    >,
) -> Result<(), ProfileError> {
    let validated = shape
        .validate(pcs)
        .map_err(|error| ProfileError::at("recursion proof shape", error))?;
    let actual_logs = program
        .column_log_sizes()
        .iter()
        .flatten()
        .copied()
        .collect::<Vec<_>>();
    let expected_logs = shape
        .table_log_sizes
        .iter()
        .copied()
        .map(M31Word::as_u32)
        .collect::<Vec<_>>();
    if actual_logs != expected_logs {
        return Err(ProfileError::at(
            "recursion table log sizes",
            "generated and serialized layouts differ",
        ));
    }
    if validated.column_log_degree() != program.max_log_degree_bound() {
        return Err(ProfileError::mismatch(
            "recursion maximum degree",
            program.max_log_degree_bound(),
            validated.column_log_degree(),
        ));
    }
    Ok(())
}

fn preprocessing_registry_digest(
    ids: &[PreProcessedColumnId],
    log_sizes: &[u32],
    domain: u16,
) -> Result<Digest8, ProfileError> {
    if ids.len() != log_sizes.len() {
        return Err(ProfileError::mismatch(
            "preprocessing registry lengths",
            ids.len(),
            log_sizes.len(),
        ));
    }
    let mut words = vec![
        M31Word::from(PREPROCESSING_REGISTRY_ENCODING),
        count_word("preprocessing columns", ids.len())?,
    ];
    for (index, (id, log_size)) in ids.iter().zip(log_sizes).enumerate() {
        words.extend([
            count_word("preprocessing column index", index)?,
            profile_word(*log_size)?,
            count_word("preprocessing identifier bytes", id.id.len())?,
        ]);
        words.extend(id.id.bytes().map(|byte| M31Word::from(u16::from(byte))));
    }
    Ok(poseidon2_hash_m31_words(&words, M31Word::from(domain)))
}

fn hash_suite_digest() -> HashSuiteDigest {
    let mut words = vec![
        M31Word::from(1_u16),
        M31Word::from(air::poseidon2::T as u16),
        M31Word::from(air::poseidon2::DIGEST_WORDS as u16),
        M31Word::from(air::poseidon2::FULL_ROUNDS as u16),
        M31Word::from(air::poseidon2::PARTIAL_ROUNDS as u16),
    ];
    words.extend(
        air::poseidon2::EXTERNAL_ROUND_CONSTS
            .iter()
            .flatten()
            .copied()
            .map(|value| M31Word::try_from(value).expect("Poseidon2 constants are canonical M31")),
    );
    words.extend(
        air::poseidon2::INTERNAL_ROUND_CONSTS
            .into_iter()
            .chain(air::poseidon2::INTERNAL_MATRIX)
            .map(|value| M31Word::try_from(value).expect("Poseidon2 constants are canonical M31")),
    );
    // This output binds the sponge's additive absorption and end-marker rules,
    // which the permutation constants alone cannot describe.
    let sponge_vector = poseidon2_hash_m31_words(
        &[
            M31Word::from(1_u16),
            M31Word::from(2_u16),
            M31Word::from(3_u16),
        ],
        M31Word::from(7_u16),
    );
    words.extend(sponge_vector.into_words());
    HashSuiteDigest::from(poseidon2_hash_m31_words(
        &words,
        M31Word::from(HASH_SUITE_HASH_DOMAIN),
    ))
}

fn count_word(field: &'static str, count: usize) -> Result<M31Word, ProfileError> {
    let count = u32::try_from(count).map_err(|error| ProfileError::at(field, error))?;
    profile_word(count)
}

fn count_u32(field: &'static str, count: usize) -> Result<u32, ProfileError> {
    u32::try_from(count).map_err(|error| ProfileError::at(field, error))
}

fn profile_word(value: u32) -> Result<M31Word, ProfileError> {
    M31Word::try_from(value).map_err(|error| ProfileError::at("profile word", error))
}

#[cfg(test)]
mod tests {
    use air::poseidon2::{T, poseidon2_traced_state};
    use air::trace::Poseidon2Table;
    use stwo::core::fields::m31::M31;

    use super::*;
    use crate::protocol::CanonicalWords;

    #[test]
    fn generated_profile_geometry_matches_the_checked_in_dimensions() {
        let profile = frozen_protocol_profile().expect("the frozen profile is internally valid");
        let actual = [
            profile
                .vm_program()
                .column_log_sizes()
                .iter()
                .flatten()
                .count(),
            profile.vm_program().column_log_sizes().len(),
            profile.vm_program().sample_coordinates().len(),
            profile.vm_program().max_log_degree_bound() as usize,
            profile.vm_program().air_instruction_count(),
            vm_preprocessed_column_ids().len(),
            profile
                .recursion_program()
                .column_log_sizes()
                .iter()
                .flatten()
                .count(),
            profile.recursion_program().column_log_sizes().len(),
            profile.recursion_program().sample_coordinates().len(),
            profile.recursion_program().max_log_degree_bound() as usize,
            profile.recursion_program().air_instruction_count(),
            recursion_preprocessed_column_ids().len(),
            UNIVERSAL_COMPONENT_COUNT,
        ];
        assert_eq!(
            actual,
            [1556, 4, 1664, 20, 629, 14, 2221, 4, 2365, 22, 1319, 587, 36]
        );
    }

    #[test]
    fn manifest_hash_matches_the_dsl_poseidon_permutation() {
        let profile = frozen_protocol_profile().expect("the frozen profile is internally valid");
        let manifest = profile.manifest().manifest();
        assert_eq!(
            air_manifest_digest(&manifest.canonical_words()),
            manifest.protocol_id().into_digest()
        );
    }

    #[test]
    fn profile_digests_match_the_checked_in_conformance_vectors() {
        let profile = frozen_protocol_profile().expect("the frozen profile is internally valid");
        let manifest = profile.manifest().manifest();
        let actual = [
            manifest.protocol_id().into_digest(),
            manifest.hash_suite.into_digest(),
            manifest.vm_preprocessing.into_digest(),
            manifest.recursion_preprocessing.into_digest(),
            manifest.vm_air_program.into_digest(),
            manifest.recursion_air_program.into_digest(),
        ];
        let expected = [
            digest(PROTOCOL_ID_WORDS),
            digest([
                1528067299, 1666361919, 1105974213, 1043934209, 1261895099, 1795736067, 1756110080,
                1727227838,
            ]),
            digest(VM_PREPROCESSING_WORDS),
            digest(RECURSION_PREPROCESSING_WORDS),
            digest([
                1150624488, 1921625284, 1150277924, 591183324, 1430805914, 109481434, 173677670,
                1962108186,
            ]),
            digest([
                1270421312, 1168180329, 1487888523, 1859018076, 1573466635, 85579857, 111495589,
                650827603,
            ]),
        ];
        assert_eq!(actual, expected);
    }

    #[test]
    fn serialized_root_size_is_derived_from_the_recursion_shape() {
        assert_eq!(ROOT_PROOF_BYTE_SIZE, 3_479_096);
    }

    #[test]
    fn every_vm_preprocessing_identifier_is_bound_by_the_registry_digest() {
        let ids = vm_preprocessed_column_ids();
        let logs = PreProcessedTrace::column_log_sizes();
        let baseline = preprocessing_registry_digest(&ids, &logs, VM_PREPROCESSING_HASH_DOMAIN)
            .expect("the VM preprocessing registry is valid");
        let mut changed = ids;
        changed[0].id.push('#');
        assert_ne!(
            preprocessing_registry_digest(&changed, &logs, VM_PREPROCESSING_HASH_DOMAIN),
            Ok(baseline)
        );
    }

    #[test]
    fn every_recursion_preprocessing_identifier_is_bound_by_the_registry_digest() {
        let profile = frozen_protocol_profile().expect("the frozen profile is internally valid");
        let ids = recursion_preprocessed_column_ids();
        let logs = &profile.recursion_program().column_log_sizes()[0];
        let baseline =
            preprocessing_registry_digest(&ids, logs, RECURSION_PREPROCESSING_HASH_DOMAIN)
                .expect("the recursion preprocessing registry is valid");
        let mut changed = ids;
        changed[0].id.push('#');
        assert_ne!(
            preprocessing_registry_digest(&changed, logs, RECURSION_PREPROCESSING_HASH_DOMAIN),
            Ok(baseline)
        );
    }

    #[test]
    fn public_io_capacity_changes_the_protocol_identifier() {
        let baseline = frozen_protocol_profile().expect("the frozen profile is internally valid");
        let narrower = build_frozen_protocol_profile(
            VmPublicClaimShape::new(MAX_PUBLIC_INPUT_WORDS - 1, MAX_PUBLIC_OUTPUT_WORDS)
                .expect("the narrower public claim is representable"),
        )
        .expect("the narrower profile is internally valid");
        assert_ne!(
            baseline.manifest().protocol_id(),
            narrower.manifest().protocol_id()
        );
    }

    fn air_manifest_digest(words: &[M31Word]) -> Digest8 {
        let mut table = Poseidon2Table::default();
        let mut state = [0_u32; T];
        state[T - 1] = 0x5632;
        let mut filled = 0;
        for word in words
            .iter()
            .copied()
            .chain(core::iter::once(M31Word::from(1_u16)))
        {
            state[filled] = (M31::from(state[filled]) + M31::from(word)).0;
            filled += 1;
            if filled == air::poseidon2::DIGEST_WORDS {
                state = poseidon2_traced_state(&mut table, state, false, true);
                filled = 0;
            }
        }
        if filled != 0 {
            state = poseidon2_traced_state(&mut table, state, false, true);
        }
        let digest_words: [u32; air::poseidon2::DIGEST_WORDS] = state
            [..air::poseidon2::DIGEST_WORDS]
            .try_into()
            .expect("Poseidon2 digest is the first half of the state");
        Digest8::try_from(digest_words).expect("Poseidon2 outputs canonical M31 words")
    }

    fn digest(words: [u32; 8]) -> Digest8 {
        Digest8::try_from(words).expect("conformance vectors contain canonical M31 words")
    }
}
