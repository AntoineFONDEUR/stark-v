//! Fiat-Shamir transcript replay for a stark-v proof.
//!
//! The recursive verifier AIR (docs/recursion.md) needs every channel draw
//! of the inner proof as witness data, and its composition-check component
//! must recompute the composition polynomial value at the OODS point from
//! the proof's sampled mask values — through the same
//! `FrameworkEval::evaluate` code the prover and host verifier use.
//!
//! This module performs that replay natively: it advances the channel
//! exactly as `verify_rv32im` + `stwo::core::verifier::verify` do, then
//! evaluates the composition through `Components::eval_composition_polynomial_at_point`
//! (which instantiates each component's `evaluate()` with `PointEvaluator`).
//! No constraint is copied: an edit to `define_trace_tables!` changes the
//! replayed value in the same compilation.

use stwo::core::air::Components as CoreComponents;
use stwo::core::channel::Channel;
use stwo::core::channel::MerkleChannel;
use stwo::core::circle::CirclePoint;
use stwo::core::fields::qm31::{SECURE_EXTENSION_DEGREE, SecureField};
use stwo::core::pcs::PcsConfig;
use stwo::core::pcs::utils::try_get_lifting_log_size;
use stwo::core::vcs_lifted::blake2_merkle::{Blake2sMerkleChannel, Blake2sMerkleHasher};
use stwo::core::vcs_lifted::merkle_hasher::MerkleHasherLifted;
use stwo::core::verifier::{COMPOSITION_LOG_SPLIT, VerificationError as StwoVerificationError};
use stwo_constraint_framework::{PREPROCESSED_TRACE_IDX, TraceLocationAllocator};

use prover::VerificationError;
use prover::components::Components;
use prover::verifier::replay_claim_phase;
use prover::{Preprocessing, Proof};

/// The OODS composition check of a proof, replayed outside the verifier.
#[derive(Debug, Clone, Copy)]
pub struct OodsCheck {
    /// The OODS point drawn from the replayed channel.
    pub oods_point: CirclePoint<SecureField>,
    /// The constraint-combination coefficient drawn from the replayed channel.
    pub random_coeff: SecureField,
    /// Composition value claimed by the proof (combined from the sampled
    /// composition coordinate polynomials).
    pub claimed: SecureField,
    /// Composition value recomputed from the sampled mask values through the
    /// components' `evaluate()`.
    pub replayed: SecureField,
}

impl OodsCheck {
    /// Whether the proof's claimed composition value matches the replay
    /// (the DEEP-ALI check).
    pub fn holds(&self) -> bool {
        self.claimed == self.replayed
    }
}

/// Everything the recursion binding needs to re-evaluate a proof's
/// composition check in-AIR: the constructed components (with drawn
/// relations), the channel draws, and the sampled mask values.
pub struct CompositionBindingData {
    pub components: Components,
    pub relations: prover::relations::Relations,
    pub oods_point: CirclePoint<SecureField>,
    pub random_coeff: SecureField,
    pub max_log_degree_bound: u32,
    /// Sampled mask values, as committed in the proof.
    pub sampled_values: stwo::core::pcs::TreeVec<Vec<Vec<SecureField>>>,
    /// The composition value the proof claims at the OODS point.
    pub claimed_composition: SecureField,
    /// Per-component claimed LogUp sums, as in the proof.
    pub claimed_sums: prover::components::ClaimedSum,
}

/// State of the polynomial commitment scheme at the OODS point: the channel
/// (advanced past the OODS draw), the committed tree shapes, and the mask
/// sample points — everything the post-OODS protocol (sampled-value mixing,
/// FRI, proof of work, query openings) consumes.
pub struct PcsBindingData<MC: MerkleChannel> {
    /// Channel state right after the OODS draw.
    pub channel: MC::C,
    /// Per tree, the committed (blowup-extended) column log sizes, in commit
    /// order — exactly `CommitmentSchemeVerifier::column_log_sizes`.
    pub column_log_sizes: stwo::core::pcs::TreeVec<Vec<u32>>,
    /// Per tree, the Merkle height (the lifting size of the commitment).
    pub tree_heights: Vec<u32>,
    /// Per tree, the commitment root.
    pub roots: Vec<<MC::H as MerkleHasherLifted>::Hash>,
    /// Mask sample points per tree per column (composition points included),
    /// as passed to `verify_values`.
    pub sample_points: stwo::core::pcs::TreeVec<Vec<Vec<CirclePoint<SecureField>>>>,
    /// The lifting log size (height of the largest tree, FRI input size).
    pub lifting_log_size: u32,
}

/// Replay the transcript and return the full composition-binding data
/// (Blake2s channel).
pub fn composition_binding_data(
    proof: &Proof<Blake2sMerkleHasher>,
    config: PcsConfig,
    preprocessing: &Preprocessing,
) -> Result<CompositionBindingData, VerificationError> {
    composition_binding_data_with_channel::<Blake2sMerkleChannel>(proof, config, preprocessing)
}

/// Replay the transcript and return the full composition-binding data with
/// any Merkle channel.
pub fn composition_binding_data_with_channel<MC: MerkleChannel>(
    proof: &Proof<MC::H>,
    config: PcsConfig,
    preprocessing: &Preprocessing<MC::H>,
) -> Result<CompositionBindingData, VerificationError> {
    full_binding_data_with_channel::<MC>(proof, config, preprocessing).map(|(data, _)| data)
}

/// Replay the transcript and return both the composition-binding data and
/// the PCS state at the OODS point, with any Merkle channel.
pub fn full_binding_data_with_channel<MC: MerkleChannel>(
    proof: &Proof<MC::H>,
    config: PcsConfig,
    preprocessing: &Preprocessing<MC::H>,
) -> Result<(CompositionBindingData, PcsBindingData<MC>), VerificationError> {
    let (mut channel, mut commitment_scheme, relations) =
        replay_claim_phase::<MC>(proof, config, preprocessing)?;

    let preprocessed_ids = preprocessing.column_ids();
    let mut location_allocator =
        TraceLocationAllocator::new_with_preprocessed_columns(&preprocessed_ids);
    let components = Components::new(
        &proof.claim,
        &mut location_allocator,
        relations.clone(),
        &proof.interaction_claim.claimed_sum,
    );
    let n_preprocessed_columns = commitment_scheme.trees[PREPROCESSED_TRACE_IDX]
        .column_log_sizes
        .len();
    let core_components = CoreComponents {
        n_preprocessed_columns,
        components: components.verifiers(),
    };

    let split_composition_log_degree_bound =
        core_components.composition_log_degree_bound() - COMPOSITION_LOG_SPLIT;
    let lifting_log_size = try_get_lifting_log_size(
        &commitment_scheme.config,
        split_composition_log_degree_bound + commitment_scheme.config.fri_config.log_blowup_factor,
    )
    .map_err(StwoVerificationError::from)?;
    let max_log_degree_bound =
        lifting_log_size - commitment_scheme.config.fri_config.log_blowup_factor;

    let random_coeff = channel.draw_secure_felt();
    commitment_scheme.commit(
        *proof
            .stark_proof
            .commitments
            .last()
            .expect("proof has a composition commitment"),
        &[max_log_degree_bound; 2 * SECURE_EXTENSION_DEGREE],
        &mut channel,
    );
    let oods_point = CirclePoint::<SecureField>::get_random_point(&mut channel);

    let claimed_composition =
        extract_composition_oods_eval(&proof.stark_proof, oods_point, max_log_degree_bound)
            .ok_or_else(|| {
                StwoVerificationError::InvalidStructure(
                    "Unexpected sampled_values structure".to_string(),
                )
            })?;

    // Mask sample points, with the composition polynomial points appended —
    // exactly the `sample_points` `verify_ex` hands to `verify_values`.
    let include_all_preprocessed_columns = false;
    let mut sample_points = core_components.mask_points(
        oods_point,
        max_log_degree_bound,
        include_all_preprocessed_columns,
    );
    sample_points.push(vec![vec![oods_point]; 2 * SECURE_EXTENSION_DEGREE]);

    let pcs = PcsBindingData::<MC> {
        channel,
        column_log_sizes: commitment_scheme
            .trees
            .as_ref()
            .map(|tree| tree.column_log_sizes.clone()),
        tree_heights: commitment_scheme
            .trees
            .iter()
            .map(|tree| tree.height)
            .collect(),
        roots: commitment_scheme
            .trees
            .iter()
            .map(|tree| tree.root)
            .collect(),
        sample_points,
        lifting_log_size,
    };

    drop(core_components);
    Ok((
        CompositionBindingData {
            components,
            relations,
            oods_point,
            random_coeff,
            max_log_degree_bound,
            sampled_values: proof.stark_proof.sampled_values.clone(),
            claimed_composition,
            claimed_sums: proof.interaction_claim.claimed_sum.clone(),
        },
        pcs,
    ))
}

/// Replay the transcript of a proof up to the OODS point and recompute the
/// composition polynomial value from the sampled mask values.
pub fn replay_composition_oods(
    proof: &Proof<Blake2sMerkleHasher>,
    config: PcsConfig,
    preprocessing: &Preprocessing,
) -> Result<OodsCheck, VerificationError> {
    let (mut channel, mut commitment_scheme, relations) =
        replay_claim_phase::<Blake2sMerkleChannel>(proof, config, preprocessing)?;

    let preprocessed_ids = preprocessing.column_ids();
    let mut location_allocator =
        TraceLocationAllocator::new_with_preprocessed_columns(&preprocessed_ids);
    let components = Components::new(
        &proof.claim,
        &mut location_allocator,
        relations,
        &proof.interaction_claim.claimed_sum,
    );
    let verifiers = components.verifiers();
    let core_components = CoreComponents {
        n_preprocessed_columns: commitment_scheme.trees[PREPROCESSED_TRACE_IDX]
            .column_log_sizes
            .len(),
        components: verifiers,
    };

    // Mirror `stwo::core::verifier::verify_ex` up to the OODS draw.
    let split_composition_log_degree_bound =
        core_components.composition_log_degree_bound() - COMPOSITION_LOG_SPLIT;
    let lifting_log_size = try_get_lifting_log_size(
        &commitment_scheme.config,
        split_composition_log_degree_bound + commitment_scheme.config.fri_config.log_blowup_factor,
    )
    .map_err(StwoVerificationError::from)?;
    let max_log_degree_bound =
        lifting_log_size - commitment_scheme.config.fri_config.log_blowup_factor;

    let random_coeff = channel.draw_secure_felt();
    commitment_scheme.commit(
        *proof
            .stark_proof
            .commitments
            .last()
            .expect("proof has a composition commitment"),
        &[max_log_degree_bound; 2 * SECURE_EXTENSION_DEGREE],
        &mut channel,
    );
    let oods_point = CirclePoint::<SecureField>::get_random_point(&mut channel);

    let claimed =
        extract_composition_oods_eval(&proof.stark_proof, oods_point, max_log_degree_bound)
            .ok_or_else(|| {
                StwoVerificationError::InvalidStructure(
                    "Unexpected sampled_values structure".to_string(),
                )
            })?;
    let replayed = core_components.eval_composition_polynomial_at_point(
        oods_point,
        &proof.stark_proof.sampled_values,
        random_coeff,
        max_log_degree_bound,
    );

    Ok(OodsCheck {
        oods_point,
        random_coeff,
        claimed,
        replayed,
    })
}

/// Combine the sampled composition coordinate polynomials into the claimed
/// composition value at the OODS point.
///
/// The composition polynomial is committed as two splits of
/// `SECURE_EXTENSION_DEGREE` base-field coordinate polynomials each; the
/// full value is `left + oods_point.repeated_double(max_log_degree_bound - 1).x * right`.
pub(crate) fn extract_composition_oods_eval<H: MerkleHasherLifted>(
    stark_proof: &stwo::core::proof::StarkProof<H>,
    oods_point: CirclePoint<SecureField>,
    max_log_degree_bound: u32,
) -> Option<SecureField> {
    let [.., left_and_right_composition_mask] = &**stark_proof.sampled_values else {
        return None;
    };
    let left_and_right_coordinate_evals: [SecureField; 2 * SECURE_EXTENSION_DEGREE] =
        left_and_right_composition_mask
            .iter()
            .map(|columns| {
                let &[eval] = &columns[..] else {
                    return None;
                };
                Some(eval)
            })
            .collect::<Option<Vec<_>>>()?
            .try_into()
            .ok()?;

    let (left_coordinate_evals, right_coordinate_evals) =
        left_and_right_coordinate_evals.split_at(SECURE_EXTENSION_DEGREE);

    let left_eval = SecureField::from_partial_evals(left_coordinate_evals.try_into().ok()?);
    let right_eval = SecureField::from_partial_evals(right_coordinate_evals.try_into().ok()?);
    Some(left_eval + oods_point.repeated_double(max_log_degree_bound - 1).x * right_eval)
}

// =============================================================================
// Constraint seam: the stark-v constraint system as data
// =============================================================================
//
// The 2-to-1 recursive verifier consumes the same `FrameworkEval::evaluate`
// code as the prover and the host verifier, so constraints are never copied:
// an edit to `define_trace_tables!` changes the prover, the host verifier,
// and everything built on these helpers in the same compilation.

use stwo_constraint_framework::expr::ExprEvaluator;
use stwo_constraint_framework::{FrameworkEval, InfoEvaluator};

/// Extract a component's constraints as expression trees.
///
/// The result contains every polynomial constraint (`constraints`) and the
/// formal LogUp fractions (`logup.fracs`) with relation parameters
/// (`<relation>_z`, `<relation>_alpha<i>`) left symbolic.
pub fn constraint_exprs<E: FrameworkEval>(eval: &E) -> ExprEvaluator {
    eval.evaluate(ExprEvaluator::new())
}

/// Extract a component's structural summary: mask offsets per interaction
/// and the number of constraints, as used for trace layout.
pub fn constraint_info<E: FrameworkEval>(eval: &E) -> InfoEvaluator {
    eval.evaluate(InfoEvaluator::empty())
}

#[cfg(test)]
mod tests {
    use super::*;
    use prover::relations::Relations;

    fn lui_eval() -> prover::components::lui::air::Eval {
        prover::components::lui::air::Eval {
            log_size: 4,
            relations: Relations::dummy(),
        }
    }

    fn base_alu_imm_eval() -> prover::components::base_alu_imm::air::Eval {
        prover::components::base_alu_imm::air::Eval {
            log_size: 4,
            relations: Relations::dummy(),
        }
    }

    #[test]
    fn test_lui_constraint_exprs_match_info_count() {
        let exprs = constraint_exprs(&lui_eval());
        let info = constraint_info(&lui_eval());
        assert_eq!(exprs.constraints.len(), info.n_constraints);
    }

    #[test]
    fn test_lui_logup_batches_become_constraints() {
        let exprs = constraint_exprs(&lui_eval());
        // 1 enabler booleanity + ceil(7 LogUp entries / 2) = 4 batch constraints
        assert_eq!(exprs.constraints.len(), 5);
    }

    #[test]
    fn test_base_alu_imm_constraint_exprs_match_info_count() {
        let exprs = constraint_exprs(&base_alu_imm_eval());
        let info = constraint_info(&base_alu_imm_eval());
        assert_eq!(exprs.constraints.len(), info.n_constraints);
    }

    #[test]
    fn test_lui_constraints_are_nonempty_expressions() {
        let exprs = constraint_exprs(&lui_eval());
        // The enabler booleanity constraint formats to a real expression
        // referencing the trace column, proving constraints flow from the
        // macro into expression data.
        assert!(!exprs.format_constraints().is_empty());
    }
}
