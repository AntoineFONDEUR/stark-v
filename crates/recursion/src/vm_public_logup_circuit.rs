//! Fixed VM public-LogUp arithmetic for recursion segment leaves.
//!
//! The circuit reconstructs the three VM relation challenges from constrained
//! transcript words, evaluates every fixed public boundary term, adds every
//! interaction claimed sum, and constrains the global result to zero. Optional
//! roots and padded IO slots select denominator one while inactive, so their
//! unused values can never trigger or hide a zero-denominator inverse.

use core::fmt;

use air::digest::M31Word;
use num_traits::{One, Zero};
use prover::relations::Relations;
use stwo::core::fields::FieldExpOps;
use stwo::core::fields::m31::{BaseField, M31, P as M31_MODULUS};
use stwo::core::fields::qm31::SecureField;

use crate::recorder::{CircuitBuilder, ConstraintCircuit, Rec};

use super::vm_public_claim::{
    VmPublicClaimShape, VmPublicClaimWordKind, canonical_layout as claim_layout,
    canonical_vm_public_claim_word_kinds,
};

const U16_BASE: u32 = 1 << 16;
const BYTE_COUNT: usize = 2;
const CHALLENGE_WORD_COUNT: usize = 8;
const REGISTERS_STATE_CHALLENGE: u32 = 0;
const MEMORY_ACCESS_CHALLENGE: u32 = 1;
const MERKLE_CHALLENGE: u32 = 3;
const REGISTERS_STATE_ARITY: usize = 2;
const MEMORY_ACCESS_ARITY: usize = 7;
const MERKLE_ARITY: usize = 18;
const REGISTER_COUNT: usize = 32;
const FIXED_PUBLIC_TERM_COUNT: u32 = 69;

/// Transcript words for the three VM relations used by public boundary terms.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VmPublicLogupChallengeWords {
    registers_state: [M31Word; CHALLENGE_WORD_COUNT],
    memory_access: [M31Word; CHALLENGE_WORD_COUNT],
    merkle: [M31Word; CHALLENGE_WORD_COUNT],
}

impl VmPublicLogupChallengeWords {
    pub const fn new(
        registers_state: [M31Word; CHALLENGE_WORD_COUNT],
        memory_access: [M31Word; CHALLENGE_WORD_COUNT],
        merkle: [M31Word; CHALLENGE_WORD_COUNT],
    ) -> Self {
        Self {
            registers_state,
            memory_access,
            merkle,
        }
    }

    /// Converts native verifier relation elements into their transcript limbs.
    pub fn from_relations(relations: &Relations) -> Self {
        Self::new(
            relation_words(
                relations.registers_state.0.z,
                relations.registers_state.0.alpha,
            ),
            relation_words(relations.memory_access.0.z, relations.memory_access.0.alpha),
            relation_words(relations.merkle.0.z, relations.merkle.0.alpha),
        )
    }

    fn words(self, challenge: u32) -> [M31Word; CHALLENGE_WORD_COUNT] {
        match challenge {
            REGISTERS_STATE_CHALLENGE => self.registers_state,
            MEMORY_ACCESS_CHALLENGE => self.memory_access,
            MERKLE_CHALLENGE => self.merkle,
            _ => unreachable!("public LogUp requests only fixed VM relation challenges"),
        }
    }

    fn inactive_reference() -> Self {
        let mut words = [M31Word::ZERO; CHALLENGE_WORD_COUNT];
        // z = 7 and alpha = 0 keep every inactive reference denominator safe.
        words[0] = M31Word::from(7);
        Self::new(words, words, words)
    }
}

fn relation_words(z: SecureField, alpha: SecureField) -> [M31Word; CHALLENGE_WORD_COUNT] {
    let mut words = [M31Word::ZERO; CHALLENGE_WORD_COUNT];
    for (destination, value) in words[..4].iter_mut().zip(z.to_m31_array()) {
        *destination = M31Word::from(value);
    }
    for (destination, value) in words[4..].iter_mut().zip(alpha.to_m31_array()) {
        *destination = M31Word::from(value);
    }
    words
}

/// Exact source relation of one public-LogUp circuit input node.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum VmPublicLogupInputSource {
    ClaimWord { index: u32 },
    ClaimByte { word_index: u32, byte_index: u32 },
    RelationChallengeWord { challenge: u32, word_index: u32 },
    ClaimedSumWord { item_index: u32, limb_index: u32 },
    SharedRelationSumWord { limb_index: u32 },
    SegmentSelector,
}

/// Circuit input node and the AIR relation that owns its value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VmPublicLogupInputBinding {
    pub node_id: u32,
    pub source: VmPublicLogupInputSource,
}

/// Fixed public-LogUp circuit and verifier-owned input metadata.
#[derive(Debug)]
pub struct VmPublicLogupCircuit {
    shape: VmPublicClaimShape,
    claimed_sum_count: u32,
    public_term_count: u32,
    circuit: ConstraintCircuit,
    input_bindings: Vec<VmPublicLogupInputBinding>,
}

impl VmPublicLogupCircuit {
    pub const fn shape(&self) -> VmPublicClaimShape {
        self.shape
    }

    pub const fn claimed_sum_count(&self) -> u32 {
        self.claimed_sum_count
    }

    pub const fn public_term_count(&self) -> u32 {
        self.public_term_count
    }

    pub const fn circuit(&self) -> &ConstraintCircuit {
        &self.circuit
    }

    pub fn input_bindings(&self) -> &[VmPublicLogupInputBinding] {
        &self.input_bindings
    }

    pub fn constrained_sum(&self) -> SecureField {
        let output = *self
            .circuit
            .outputs()
            .first()
            .expect("public LogUp circuit has one global-sum output");
        self.circuit.arena().nodes[output].value
    }

    pub fn nonzero_output_count(&self) -> usize {
        usize::from(!self.constrained_sum().is_zero())
    }
}

/// Values for one universal VM public-LogUp circuit instance.
pub struct VmPublicLogupWitness<'a> {
    pub segment_selector: bool,
    pub claim_words: &'a [M31Word],
    pub relation_challenges: VmPublicLogupChallengeWords,
    pub claimed_sums: &'a [SecureField],
    pub shared_relation_sum: SecureField,
}

struct TrackedBuilder {
    circuit: CircuitBuilder,
    bindings: Vec<VmPublicLogupInputBinding>,
}

impl TrackedBuilder {
    fn new() -> Self {
        Self {
            circuit: CircuitBuilder::default(),
            bindings: Vec::new(),
        }
    }

    fn input(&mut self, source: VmPublicLogupInputSource, value: u32) -> Rec {
        let (node_id, value) = self
            .circuit
            .input(SecureField::from(BaseField::from(value)));
        self.bindings.push(VmPublicLogupInputBinding {
            node_id: u32::try_from(node_id).expect("public LogUp circuit input count fits u32"),
            source,
        });
        value
    }

    fn finish(
        self,
        shape: VmPublicClaimShape,
        claimed_sum_count: u32,
        public_term_count: u32,
    ) -> VmPublicLogupCircuit {
        VmPublicLogupCircuit {
            shape,
            claimed_sum_count,
            public_term_count,
            circuit: self.circuit.finish(),
            input_bindings: self.bindings,
        }
    }
}

struct BoundClaim {
    words: Vec<Rec>,
    bytes: Vec<Option<[Rec; BYTE_COUNT]>>,
}

impl BoundClaim {
    fn new(
        builder: &mut TrackedBuilder,
        shape: VmPublicClaimShape,
        words: &[M31Word],
    ) -> Result<Self, VmPublicLogupCircuitError> {
        let kinds = canonical_vm_public_claim_word_kinds(shape);
        if words.len() != kinds.len() {
            return Err(VmPublicLogupCircuitError::ClaimWordCountMismatch {
                expected: kinds.len(),
                actual: words.len(),
            });
        }
        let mut bound_words = Vec::with_capacity(words.len());
        let mut bytes = Vec::with_capacity(words.len());
        for (index, (word, kind)) in words.iter().copied().zip(kinds).enumerate() {
            let word_index = u32::try_from(index)
                .map_err(|_| VmPublicLogupCircuitError::WordIndexOutOfRange { index })?;
            bound_words.push(builder.input(
                VmPublicLogupInputSource::ClaimWord { index: word_index },
                word.as_u32(),
            ));
            if kind == VmPublicClaimWordKind::U16 {
                let value = u16::try_from(word.as_u32()).map_err(|_| {
                    VmPublicLogupCircuitError::ClaimU16OutOfRange {
                        index,
                        value: word.as_u32(),
                    }
                })?;
                let raw_bytes = value.to_le_bytes();
                bytes.push(Some(core::array::from_fn(|byte_index| {
                    builder.input(
                        VmPublicLogupInputSource::ClaimByte {
                            word_index,
                            byte_index: u32::try_from(byte_index).expect("u16 byte index fits u32"),
                        },
                        u32::from(raw_bytes[byte_index]),
                    )
                })));
            } else {
                bytes.push(None);
            }
        }
        Ok(Self {
            words: bound_words,
            bytes,
        })
    }

    fn word(&self, index: usize) -> Rec {
        self.words[index].clone()
    }

    fn u32(&self, start: usize) -> Rec {
        self.word(start) + self.word(start + 1) * constant(U16_BASE)
    }

    fn u32_bytes(&self, start: usize) -> Result<[Rec; 4], VmPublicLogupCircuitError> {
        let low = self
            .bytes
            .get(start)
            .and_then(Option::as_ref)
            .ok_or(VmPublicLogupCircuitError::ClaimByteSourceMissing { index: start })?;
        let high = self
            .bytes
            .get(start + 1)
            .and_then(Option::as_ref)
            .ok_or(VmPublicLogupCircuitError::ClaimByteSourceMissing { index: start + 1 })?;
        Ok([
            low[0].clone(),
            low[1].clone(),
            high[0].clone(),
            high[1].clone(),
        ])
    }
}

struct BoundChallenge {
    z: Rec,
    alpha_powers: Vec<Rec>,
}

impl BoundChallenge {
    fn new(
        builder: &mut TrackedBuilder,
        challenge: u32,
        words: [M31Word; CHALLENGE_WORD_COUNT],
        arity: usize,
    ) -> Self {
        let limbs = words.map(M31Word::as_u32);
        let z = compose_secure_inputs(builder, challenge, 0, &limbs[..4]);
        let alpha = compose_secure_inputs(builder, challenge, 4, &limbs[4..]);
        let mut power = Rec::one();
        let alpha_powers = (0..arity)
            .map(|_| {
                let current = power.clone();
                power *= alpha.clone();
                current
            })
            .collect();
        Self { z, alpha_powers }
    }

    fn combine(&self, values: &[Rec]) -> Rec {
        debug_assert!(values.len() <= self.alpha_powers.len());
        values
            .iter()
            .zip(&self.alpha_powers)
            .fold(Rec::zero(), |sum, (value, power)| {
                sum + value.clone() * power.clone()
            })
            - self.z.clone()
    }
}

fn compose_secure_inputs(
    builder: &mut TrackedBuilder,
    challenge: u32,
    first_word: u32,
    limbs: &[u32],
) -> Rec {
    let values = core::array::from_fn::<_, 4, _>(|limb| {
        builder.input(
            VmPublicLogupInputSource::RelationChallengeWord {
                challenge,
                word_index: first_word
                    + u32::try_from(limb).expect("secure-field limb index fits u32"),
            },
            limbs[limb],
        )
    });
    compose_secure(values)
}

fn compose_secure(values: [Rec; 4]) -> Rec {
    let [v0, v1, v2, v3] = values;
    let basis_1 = SecureField::from_m31_array([0.into(), 1.into(), 0.into(), 0.into()]);
    let basis_2 = SecureField::from_m31_array([0.into(), 0.into(), 1.into(), 0.into()]);
    let basis_3 = SecureField::from_m31_array([0.into(), 0.into(), 0.into(), 1.into()]);
    v0 + v1 * basis_1 + v2 * basis_2 + v3 * basis_3
}

/// Builds the canonical inactive circuit used to fix preprocessing structure.
pub fn build_vm_public_logup_reference(
    shape: VmPublicClaimShape,
    claimed_sum_count: u32,
) -> Result<VmPublicLogupCircuit, VmPublicLogupCircuitError> {
    let claim = vec![M31Word::ZERO; shape.claim_word_count()];
    let claimed_sums = vec![
        SecureField::zero();
        usize::try_from(claimed_sum_count).map_err(|_| {
            VmPublicLogupCircuitError::ClaimedSumCountOutOfRange {
                count: claimed_sum_count,
            }
        })?
    ];
    build_vm_public_logup_circuit(
        shape,
        claimed_sum_count,
        VmPublicLogupWitness {
            segment_selector: false,
            claim_words: &claim,
            relation_challenges: VmPublicLogupChallengeWords::inactive_reference(),
            claimed_sums: &claimed_sums,
            shared_relation_sum: SecureField::zero(),
        },
    )
}

/// Builds one fixed public-LogUp instance from transcript-bound witness values.
pub fn build_vm_public_logup_circuit(
    shape: VmPublicClaimShape,
    claimed_sum_count: u32,
    witness: VmPublicLogupWitness<'_>,
) -> Result<VmPublicLogupCircuit, VmPublicLogupCircuitError> {
    validate_input_address_offsets(shape)?;
    let expected_claimed_sums = usize::try_from(claimed_sum_count).map_err(|_| {
        VmPublicLogupCircuitError::ClaimedSumCountOutOfRange {
            count: claimed_sum_count,
        }
    })?;
    if witness.claimed_sums.len() != expected_claimed_sums {
        return Err(VmPublicLogupCircuitError::ClaimedSumCountMismatch {
            expected: expected_claimed_sums,
            actual: witness.claimed_sums.len(),
        });
    }
    let public_term_count = FIXED_PUBLIC_TERM_COUNT
        .checked_add(shape.max_input_words())
        .and_then(|count| count.checked_add(shape.max_output_words()))
        .ok_or(VmPublicLogupCircuitError::PublicTermCountOverflow)?;
    M31Word::try_from(public_term_count).map_err(|_| {
        VmPublicLogupCircuitError::PublicTermCountOutOfRange {
            count: public_term_count,
        }
    })?;

    let mut builder = TrackedBuilder::new();
    let segment = builder.input(
        VmPublicLogupInputSource::SegmentSelector,
        u32::from(witness.segment_selector),
    );
    let claim = BoundClaim::new(&mut builder, shape, witness.claim_words)?;
    let registers = BoundChallenge::new(
        &mut builder,
        REGISTERS_STATE_CHALLENGE,
        witness.relation_challenges.words(REGISTERS_STATE_CHALLENGE),
        REGISTERS_STATE_ARITY,
    );
    let memory = BoundChallenge::new(
        &mut builder,
        MEMORY_ACCESS_CHALLENGE,
        witness.relation_challenges.words(MEMORY_ACCESS_CHALLENGE),
        MEMORY_ACCESS_ARITY,
    );
    let merkle = BoundChallenge::new(
        &mut builder,
        MERKLE_CHALLENGE,
        witness.relation_challenges.words(MERKLE_CHALLENGE),
        MERKLE_ARITY,
    );

    let mut total = Rec::zero();
    let mut term_index = 0_u32;
    add_public_term(
        &mut total,
        segment.clone(),
        registers.combine(&[claim.u32(claim_layout::INITIAL_PC_START), constant(1)]),
        TermSign::Positive,
        &mut term_index,
    )?;
    add_public_term(
        &mut total,
        segment.clone(),
        registers.combine(&[
            claim.u32(claim_layout::FINAL_PC_START),
            claim.u32(claim_layout::CLOCK_START) + constant(1),
        ]),
        TermSign::Negative,
        &mut term_index,
    )?;

    for (present, root_start) in [
        (
            claim_layout::PROGRAM_ROOT_PRESENT,
            claim_layout::PROGRAM_ROOT_START,
        ),
        (
            claim_layout::INITIAL_RW_ROOT_PRESENT,
            claim_layout::INITIAL_RW_ROOT_START,
        ),
        (
            claim_layout::FINAL_RW_ROOT_PRESENT,
            claim_layout::FINAL_RW_ROOT_START,
        ),
    ] {
        let root = (0..8)
            .map(|offset| claim.word(root_start + offset))
            .collect::<Vec<_>>();
        let mut tuple = Vec::with_capacity(MERKLE_ARITY);
        tuple.extend([constant(0), constant(0)]);
        tuple.extend(root.iter().cloned());
        tuple.extend(root);
        add_public_term(
            &mut total,
            segment.clone() * claim.word(present),
            merkle.combine(&tuple),
            TermSign::Positive,
            &mut term_index,
        )?;
    }

    for register in 0..REGISTER_COUNT {
        let register_address =
            constant(u32::try_from(register).expect("fixed register index fits u32"));
        let initial_start = claim_layout::INITIAL_REGISTERS_START + register * 2;
        let initial_bytes = claim.u32_bytes(initial_start)?;
        let mut initial_tuple = vec![constant(0), register_address.clone(), constant(0)];
        initial_tuple.extend(initial_bytes);
        add_public_term(
            &mut total,
            segment.clone(),
            memory.combine(&initial_tuple),
            TermSign::Positive,
            &mut term_index,
        )?;

        let final_start = claim_layout::FINAL_REGISTERS_START + register * 2;
        let final_bytes = claim.u32_bytes(final_start)?;
        let last_clock = claim.u32(claim_layout::REGISTER_LAST_CLOCKS_START + register * 2);
        let mut final_tuple = vec![constant(0), register_address, last_clock];
        final_tuple.extend(final_bytes);
        add_public_term(
            &mut total,
            segment.clone(),
            memory.combine(&final_tuple),
            TermSign::Negative,
            &mut term_index,
        )?;
    }

    let input_start = claim.u32(claim_layout::INPUT_START_START);
    for index in 0..shape.max_input_words() as usize {
        let present = claim.word(claim_layout::input_slot_present(index));
        let value_start = claim_layout::input_slot_value_start(index);
        let bytes = claim.u32_bytes(value_start)?;
        let offset = u32::try_from(index)
            .expect("validated input capacity fits u32")
            .saturating_mul(4);
        let mut tuple = vec![
            constant(1),
            input_start.clone() + constant(offset),
            constant(0),
        ];
        tuple.extend(bytes);
        add_public_term(
            &mut total,
            segment.clone() * present,
            memory.combine(&tuple),
            TermSign::Positive,
            &mut term_index,
        )?;
    }

    for index in 0..shape.max_output_words() as usize {
        let present = claim.word(claim_layout::output_slot_present(shape, index));
        let address = claim.u32(claim_layout::output_slot_address_start(shape, index));
        let clock = claim.u32(claim_layout::output_slot_clock_start(shape, index));
        let bytes = claim.u32_bytes(claim_layout::output_slot_value_start(shape, index))?;
        let mut tuple = vec![constant(1), address, clock];
        tuple.extend(bytes);
        add_public_term(
            &mut total,
            segment.clone() * present,
            memory.combine(&tuple),
            TermSign::Negative,
            &mut term_index,
        )?;
    }
    debug_assert_eq!(term_index, public_term_count);

    for (item_index, claimed_sum) in witness.claimed_sums.iter().copied().enumerate() {
        let item_index = u32::try_from(item_index).map_err(|_| {
            VmPublicLogupCircuitError::ClaimedSumIndexOutOfRange { index: item_index }
        })?;
        let limbs = claimed_sum.to_m31_array();
        let values = core::array::from_fn(|limb_index| {
            builder.input(
                VmPublicLogupInputSource::ClaimedSumWord {
                    item_index,
                    limb_index: u32::try_from(limb_index)
                        .expect("secure-field limb index fits u32"),
                },
                limbs[limb_index].0,
            )
        });
        total += segment.clone() * compose_secure(values);
    }
    let shared_relation_sum = compose_secure(core::array::from_fn(|limb_index| {
        builder.input(
            VmPublicLogupInputSource::SharedRelationSumWord {
                limb_index: u32::try_from(limb_index).expect("secure-field limb index fits u32"),
            },
            witness.shared_relation_sum.to_m31_array()[limb_index].0,
        )
    }));
    builder
        .circuit
        .constrain_zero(total - segment * shared_relation_sum);
    Ok(builder.finish(shape, claimed_sum_count, public_term_count))
}

fn validate_input_address_offsets(
    shape: VmPublicClaimShape,
) -> Result<(), VmPublicLogupCircuitError> {
    let last_index = shape.max_input_words().saturating_sub(1);
    let offset = u64::from(last_index) * 4;
    let largest_sum = u64::from(M31_MODULUS - 1) + offset;
    if largest_sum > u64::from(u32::MAX) {
        return Err(VmPublicLogupCircuitError::InputAddressMayWrap {
            max_input_words: shape.max_input_words(),
        });
    }
    Ok(())
}

#[derive(Clone, Copy)]
enum TermSign {
    Positive,
    Negative,
}

fn add_public_term(
    total: &mut Rec,
    activation: Rec,
    denominator: Rec,
    sign: TermSign,
    term_index: &mut u32,
) -> Result<(), VmPublicLogupCircuitError> {
    // Selecting one for inactive slots makes inversion total without placing
    // any condition on a padded tuple's otherwise irrelevant denominator.
    let selected = activation.clone() * denominator + (Rec::one() - activation.clone());
    if selected.value().is_zero() {
        return Err(VmPublicLogupCircuitError::ZeroDenominator { term: *term_index });
    }
    let contribution = activation * selected.inverse();
    *total += match sign {
        TermSign::Positive => contribution,
        TermSign::Negative => -contribution,
    };
    *term_index = term_index
        .checked_add(1)
        .ok_or(VmPublicLogupCircuitError::PublicTermCountOverflow)?;
    Ok(())
}

fn constant(value: u32) -> Rec {
    Rec::from(M31::from(value))
}

/// Invalid fixed public-LogUp shape or witness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VmPublicLogupCircuitError {
    ClaimWordCountMismatch { expected: usize, actual: usize },
    ClaimU16OutOfRange { index: usize, value: u32 },
    ClaimByteSourceMissing { index: usize },
    WordIndexOutOfRange { index: usize },
    ClaimedSumCountOutOfRange { count: u32 },
    ClaimedSumCountMismatch { expected: usize, actual: usize },
    ClaimedSumIndexOutOfRange { index: usize },
    PublicTermCountOverflow,
    PublicTermCountOutOfRange { count: u32 },
    InputAddressMayWrap { max_input_words: u32 },
    ZeroDenominator { term: u32 },
}

impl fmt::Display for VmPublicLogupCircuitError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for VmPublicLogupCircuitError {}

#[cfg(test)]
mod tests {
    use prover::poseidon2_channel::Poseidon2M31Channel;
    use prover::public_data::{OutputWord, PublicData};
    use rstest::rstest;

    use super::*;
    use crate::vm_public_claim::{canonical_vm_public_claim_words, tests};

    fn active_circuit(claimed_sums: &[SecureField], relations: &Relations) -> VmPublicLogupCircuit {
        active_circuit_for(&tests::public_data(), claimed_sums, relations)
    }

    fn active_circuit_for(
        public_data: &PublicData,
        claimed_sums: &[SecureField],
        relations: &Relations,
    ) -> VmPublicLogupCircuit {
        let shape = tests::shape();
        let claim = canonical_vm_public_claim_words(public_data, shape)
            .expect("fixture claim is canonical");
        build_vm_public_logup_circuit(
            shape,
            u32::try_from(claimed_sums.len()).expect("fixture claimed-sum count fits u32"),
            VmPublicLogupWitness {
                segment_selector: true,
                claim_words: &claim,
                relation_challenges: VmPublicLogupChallengeWords::from_relations(relations),
                claimed_sums,
                shared_relation_sum: SecureField::zero(),
            },
        )
        .expect("fixture public denominators are nonzero")
    }

    #[derive(Clone, Copy, Debug)]
    enum DifferentialCase {
        Baseline,
        NoRootsOrIo,
        FullIoCapacity,
        HighRegisterWords,
        InputAddressCrossesM31,
        MaximumCanonicalClock,
    }

    fn public_data_for(case: DifferentialCase) -> PublicData {
        let mut public_data = tests::public_data();
        match case {
            DifferentialCase::Baseline => {}
            DifferentialCase::NoRootsOrIo => {
                public_data.program_root = None;
                public_data.initial_rw_root = None;
                public_data.final_rw_root = None;
                public_data.io_entries.input_len = 0;
                public_data.io_entries.input_words.clear();
                public_data.io_entries.output_len = 0;
                public_data.io_entries.output_words.clear();
            }
            DifferentialCase::FullIoCapacity => {
                public_data.io_entries.input_len = 12;
                public_data.io_entries.input_words.push(0xffff_0001);
                public_data.io_entries.output_len = 8;
                public_data.io_entries.output_words.push(OutputWord {
                    addr: 0x10_000c,
                    value: 0x8000_0000,
                    clock: 8,
                });
            }
            DifferentialCase::HighRegisterWords => {
                public_data.initial_regs[31] = u32::MAX;
                public_data.final_regs[30] = 0x8000_0000;
                public_data.reg_last_clock[30] = public_data.clock;
            }
            DifferentialCase::InputAddressCrossesM31 => {
                public_data.io_entries.input_start = M31_MODULUS - 2;
            }
            DifferentialCase::MaximumCanonicalClock => {
                public_data.clock = M31_MODULUS - 2;
                public_data.reg_last_clock.fill(public_data.clock);
                for output in &mut public_data.io_entries.output_words {
                    output.clock = public_data.clock;
                }
            }
        }
        public_data
    }

    #[rstest]
    #[case(DifferentialCase::Baseline)]
    #[case(DifferentialCase::NoRootsOrIo)]
    #[case(DifferentialCase::FullIoCapacity)]
    #[case(DifferentialCase::HighRegisterWords)]
    #[case(DifferentialCase::InputAddressCrossesM31)]
    #[case(DifferentialCase::MaximumCanonicalClock)]
    fn circuit_public_sum_matches_native_vm_public_data(
        #[case] differential_case: DifferentialCase,
    ) {
        let mut channel = Poseidon2M31Channel::default();
        let relations = Relations::draw(&mut channel);
        let public_data = public_data_for(differential_case);
        let circuit = active_circuit_for(&public_data, &[SecureField::zero()], &relations);
        assert_eq!(circuit.constrained_sum(), public_data.logup_sum(&relations));
    }

    #[rstest]
    fn valid_claimed_sums_close_the_global_logup_equation() {
        let mut channel = Poseidon2M31Channel::default();
        let relations = Relations::draw(&mut channel);
        let claimed_sum = -tests::public_data().logup_sum(&relations);
        assert_eq!(
            active_circuit(&[claimed_sum], &relations).nonzero_output_count(),
            0
        );
    }

    #[rstest]
    fn incorrect_claimed_sum_keeps_the_global_output_nonzero() {
        let mut channel = Poseidon2M31Channel::default();
        let relations = Relations::draw(&mut channel);
        assert_eq!(
            active_circuit(&[SecureField::zero()], &relations).nonzero_output_count(),
            1
        );
    }

    #[rstest]
    fn inactive_reference_has_the_same_fixed_public_term_count() {
        let shape = tests::shape();
        assert_eq!(
            build_vm_public_logup_reference(shape, 1)
                .expect("fixture reference is representable")
                .public_term_count(),
            FIXED_PUBLIC_TERM_COUNT + shape.max_input_words() + shape.max_output_words()
        );
    }

    #[rstest]
    fn relation_challenge_kinds_cannot_be_swapped() {
        let mut channel = Poseidon2M31Channel::default();
        let relations = Relations::draw(&mut channel);
        let challenges = VmPublicLogupChallengeWords::from_relations(&relations);
        let swapped = VmPublicLogupChallengeWords::new(
            challenges.memory_access,
            challenges.registers_state,
            challenges.merkle,
        );
        let shape = tests::shape();
        let claim = canonical_vm_public_claim_words(&tests::public_data(), shape)
            .expect("fixture claim is canonical");
        let claimed_sum = -tests::public_data().logup_sum(&relations);
        let circuit = build_vm_public_logup_circuit(
            shape,
            1,
            VmPublicLogupWitness {
                segment_selector: true,
                claim_words: &claim,
                relation_challenges: swapped,
                claimed_sums: &[claimed_sum],
                shared_relation_sum: SecureField::zero(),
            },
        )
        .expect("swapped fixture denominators remain nonzero");
        assert_eq!(circuit.nonzero_output_count(), 1);
    }

    #[rstest]
    fn absent_io_slots_select_one_before_inversion() {
        let shape = tests::shape();
        let mut public_data = tests::public_data();
        public_data.io_entries.input_words.clear();
        public_data.io_entries.output_words.clear();
        let claim = canonical_vm_public_claim_words(&public_data, shape)
            .expect("empty fixture vectors fit the shape");
        let safe = VmPublicLogupChallengeWords::inactive_reference();
        let mut memory = [M31Word::ZERO; CHALLENGE_WORD_COUNT];
        // With alpha zero, every inactive RW tuple has denominator 1 - z = 0.
        memory[0] = M31Word::from(1);
        let challenges =
            VmPublicLogupChallengeWords::new(safe.registers_state, memory, safe.merkle);
        assert!(
            build_vm_public_logup_circuit(
                shape,
                1,
                VmPublicLogupWitness {
                    segment_selector: true,
                    claim_words: &claim,
                    relation_challenges: challenges,
                    claimed_sums: &[SecureField::zero()],
                    shared_relation_sum: SecureField::zero(),
                },
            )
            .is_ok()
        );
    }

    #[rstest]
    fn active_zero_relation_denominator_is_rejected() {
        let shape = tests::shape();
        let claim = canonical_vm_public_claim_words(&tests::public_data(), shape)
            .expect("fixture claim is canonical");
        let safe = VmPublicLogupChallengeWords::inactive_reference();
        let mut memory = [M31Word::ZERO; CHALLENGE_WORD_COUNT];
        memory[0] = M31Word::from(1);
        let challenges =
            VmPublicLogupChallengeWords::new(safe.registers_state, memory, safe.merkle);
        assert!(matches!(
            build_vm_public_logup_circuit(
                shape,
                1,
                VmPublicLogupWitness {
                    segment_selector: true,
                    claim_words: &claim,
                    relation_challenges: challenges,
                    claimed_sums: &[SecureField::zero()],
                    shared_relation_sum: SecureField::zero(),
                },
            ),
            Err(VmPublicLogupCircuitError::ZeroDenominator { term: 69 })
        ));
    }
}
