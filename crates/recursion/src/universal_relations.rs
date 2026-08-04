//! Canonical relation registry for the recursion universal AIR.
//!
//! Every universal component draws its LogUp relations from one bundle. The
//! bundle fixes the draw order, and that order is load-bearing beyond the
//! proof itself: a recursion child's transcript replays one
//! `DrawRelationChallenge` step per registry entry, so the recursion control
//! plan's challenge count and the self-program's formal parameter binding are
//! both indexed by this registry. Reordering or renaming an entry changes
//! what every recursion verifier must replay, so the registry is defined from
//! the drawn relation instances themselves rather than from strings.
//!
//! The VM relation registry comes first: the shared poseidon2, Merkle-path,
//! and byte-range components consume the VM `Relations` bundle, whose draw
//! order is fixed by the generated `Relations::DESCRIPTORS`. The recursion
//! and current protocol-local structs follow in component-dependency order.

use stwo::core::channel::Channel;

use prover::relations::{RelationDescriptor, Relations};

use super::control_air::ControlRelations;
use super::fri_merkle_air::FriMerkleRelations;
use super::fri_verifier_input_air::FriVerifierRouteRelations;
use super::pcs_deep_input_air::PcsDeepRelations;
use super::pow::PowRelations;
use super::query_position_air::QueryPositionRelations;
use super::relation_challenge_air::RelationChallengeRelations;
use super::statement_input_air::StatementInputRelations;
use super::trace_merkle_air::TraceMerkleRelations;
use super::transcript_air::TranscriptAirRelations;
use super::transcript_binding_air::TranscriptBindingRelations;
use super::transcript_payload_air::VerifierInputRelations;
use super::transcript_state_air::TranscriptStateRelations;
use super::transcript_word_air::TranscriptWordRelations;
use super::verifier_randomness_air::VerifierRandomnessRelations;
use super::vm_public_claim_hash_air::VmPublicClaimHashRelations;
use super::vm_public_claim_input_air::VmPublicClaimInputRelations;
use super::vm_public_io_hash_air::VmPublicIoHashRelations;
use crate::relations::RecursionRelations;

/// Total relation challenges drawn for one recursion verification.
pub const UNIVERSAL_RELATION_COUNT: usize = 48;

/// Every relation bundle drawn by the universal AIR, in canonical draw order.
#[derive(Clone)]
pub struct UniversalRelations {
    pub vm: Relations,
    pub recursion: RecursionRelations,
    pub control: ControlRelations,
    pub transcript: TranscriptAirRelations,
    pub transcript_binding: TranscriptBindingRelations,
    pub transcript_state: TranscriptStateRelations,
    pub transcript_word: TranscriptWordRelations,
    pub verifier_input: VerifierInputRelations,
    pub pow: PowRelations,
    pub relation_challenge: RelationChallengeRelations,
    pub verifier_randomness: VerifierRandomnessRelations,
    pub statement_input: StatementInputRelations,
    pub vm_public_claim_input: VmPublicClaimInputRelations,
    pub vm_public_claim_hash: VmPublicClaimHashRelations,
    pub vm_public_io_hash: VmPublicIoHashRelations,
    pub query_position: QueryPositionRelations,
    pub trace_merkle: TraceMerkleRelations,
    pub pcs_deep: PcsDeepRelations,
    pub fri_merkle: FriMerkleRelations,
    pub fri_verifier_route: FriVerifierRouteRelations,
}

impl UniversalRelations {
    pub fn dummy() -> Self {
        Self {
            vm: Relations::dummy(),
            recursion: RecursionRelations::dummy(),
            control: ControlRelations::dummy(),
            transcript: TranscriptAirRelations::dummy(),
            transcript_binding: TranscriptBindingRelations::dummy(),
            transcript_state: TranscriptStateRelations::dummy(),
            transcript_word: TranscriptWordRelations::dummy(),
            verifier_input: VerifierInputRelations::dummy(),
            pow: PowRelations::dummy(),
            relation_challenge: RelationChallengeRelations::dummy(),
            verifier_randomness: VerifierRandomnessRelations::dummy(),
            statement_input: StatementInputRelations::dummy(),
            vm_public_claim_input: VmPublicClaimInputRelations::dummy(),
            vm_public_claim_hash: VmPublicClaimHashRelations::dummy(),
            vm_public_io_hash: VmPublicIoHashRelations::dummy(),
            query_position: QueryPositionRelations::dummy(),
            trace_merkle: TraceMerkleRelations::dummy(),
            pcs_deep: PcsDeepRelations::dummy(),
            fri_merkle: FriMerkleRelations::dummy(),
            fri_verifier_route: FriVerifierRouteRelations::dummy(),
        }
    }

    /// Draws every relation in registry order: the VM bundle first, then the
    /// recursion and current protocol-local structs. Each struct draws its own fields in
    /// declaration order, which is the order
    /// [`universal_relation_descriptors`] lists them.
    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            vm: Relations::draw(channel),
            recursion: RecursionRelations::draw(channel),
            control: ControlRelations::draw(channel),
            transcript: TranscriptAirRelations::draw(channel),
            transcript_binding: TranscriptBindingRelations::draw(channel),
            transcript_state: TranscriptStateRelations::draw(channel),
            transcript_word: TranscriptWordRelations::draw(channel),
            verifier_input: VerifierInputRelations::draw(channel),
            pow: PowRelations::draw(channel),
            relation_challenge: RelationChallengeRelations::draw(channel),
            verifier_randomness: VerifierRandomnessRelations::draw(channel),
            statement_input: StatementInputRelations::draw(channel),
            vm_public_claim_input: VmPublicClaimInputRelations::draw(channel),
            vm_public_claim_hash: VmPublicClaimHashRelations::draw(channel),
            vm_public_io_hash: VmPublicIoHashRelations::draw(channel),
            query_position: QueryPositionRelations::draw(channel),
            trace_merkle: TraceMerkleRelations::draw(channel),
            pcs_deep: PcsDeepRelations::draw(channel),
            fri_merkle: FriMerkleRelations::draw(channel),
            fri_verifier_route: FriVerifierRouteRelations::draw(channel),
        }
    }
}

/// One descriptor per drawn relation, in the exact order
/// [`UniversalRelations::draw`] consumes them from the channel.
///
/// The VM entries reuse the generated `Relations::DESCRIPTORS` so the shared
/// VM components keep their established challenge layout. The remaining
/// entries mirror the `relation!` declarations; `Relation::get_name` borrows
/// the instance, so the names are spelled out here and pinned by
/// `registry_matches_drawn_relation_instances`, which fails on any rename or
/// resize that forgets to update this registry.
pub fn universal_relation_descriptors() -> [RelationDescriptor; UNIVERSAL_RELATION_COUNT] {
    let vm_descriptors = Relations::DESCRIPTORS;
    let local = local_relation_descriptors();
    debug_assert_eq!(vm_descriptors.len() + local.len(), UNIVERSAL_RELATION_COUNT);
    let mut descriptors = [RelationDescriptor { name: "", size: 0 }; UNIVERSAL_RELATION_COUNT];
    descriptors[..vm_descriptors.len()].copy_from_slice(&vm_descriptors);
    descriptors[vm_descriptors.len()..].copy_from_slice(&local);
    descriptors
}

/// The recursion-local half of the registry, in struct draw order.
const fn local_relation_descriptors() -> [RelationDescriptor; 36] {
    [
        RelationDescriptor {
            name: "MerkleNodeRelation",
            size: 11,
        },
        RelationDescriptor {
            name: "OpDefRelation",
            size: 5,
        },
        RelationDescriptor {
            name: "WireRelation",
            size: 6,
        },
        RelationDescriptor {
            name: "VerifierStepRelation",
            size: 7,
        },
        RelationDescriptor {
            name: "HashStateRelation",
            size: 19,
        },
        RelationDescriptor {
            name: "HashDataRelation",
            size: 11,
        },
        RelationDescriptor {
            name: "HashOutputRelation",
            size: 12,
        },
        RelationDescriptor {
            name: "HashCallControlRelation",
            size: 7,
        },
        RelationDescriptor {
            name: "TranscriptFrameWordRelation",
            size: 4,
        },
        RelationDescriptor {
            name: "TranscriptFrameOutputRelation",
            size: 10,
        },
        RelationDescriptor {
            name: "TranscriptPowFrameRelation",
            size: 14,
        },
        RelationDescriptor {
            name: "TranscriptDigestStateRelation",
            size: 10,
        },
        RelationDescriptor {
            name: "TranscriptDrawOutputRelation",
            size: 15,
        },
        RelationDescriptor {
            name: "TranscriptPayloadWordRelation",
            size: 9,
        },
        RelationDescriptor {
            name: "VerifierInputWordRelation",
            size: 5,
        },
        RelationDescriptor {
            name: "PowCheckRelation",
            size: 5,
        },
        RelationDescriptor {
            name: "RelationChallengeWordRelation",
            size: 5,
        },
        RelationDescriptor {
            name: "VerifierRandomnessWordRelation",
            size: 5,
        },
        RelationDescriptor {
            name: "StatementWordRelation",
            size: 3,
        },
        RelationDescriptor {
            name: "VmPublicClaimWordRelation",
            size: 3,
        },
        RelationDescriptor {
            name: "VmPublicClaimByteRelation",
            size: 3,
        },
        RelationDescriptor {
            name: "VmPublicIoWordRelation",
            size: 3,
        },
        RelationDescriptor {
            name: "VmPublicClaimHashStateRelation",
            size: 17,
        },
        RelationDescriptor {
            name: "VmPublicIoHashStateRelation",
            size: 18,
        },
        RelationDescriptor {
            name: "VmPublicIoDigestRelation",
            size: 3,
        },
        RelationDescriptor {
            name: "QueryBitsRelation",
            size: 33,
        },
        RelationDescriptor {
            name: "QueryBitValueRelation",
            size: 4,
        },
        RelationDescriptor {
            name: "QueryPositionRelation",
            size: 6,
        },
        RelationDescriptor {
            name: "TraceLeafHashStateRelation",
            size: 20,
        },
        RelationDescriptor {
            name: "TraceQueryValueRelation",
            size: 5,
        },
        RelationDescriptor {
            name: "PcsDeepAnswerWordRelation",
            size: 4,
        },
        RelationDescriptor {
            name: "FriMerkleLeafStateRelation",
            size: 21,
        },
        RelationDescriptor {
            name: "FriMerkleValueWordRelation",
            size: 6,
        },
        RelationDescriptor {
            name: "FriMerkleRouteRelation",
            size: 4,
        },
        RelationDescriptor {
            name: "FriMerkleLocalRootRelation",
            size: 11,
        },
        RelationDescriptor {
            name: "FriVerifierRouteWordRelation",
            size: 6,
        },
    ]
}

#[cfg(test)]
mod tests {
    use std::collections::{HashMap, HashSet};

    use stwo::core::fields::m31::M31;
    use stwo::core::fields::qm31::SecureField;
    use stwo_constraint_framework::expr::ExprEvaluator;
    use stwo_constraint_framework::{FrameworkEval, Relation};

    use super::super::wire::ProofKind;
    use super::*;
    use crate::{linear_ops, merkle_path, qm31_inv, qm31_mul};

    /// Relations drawn inside a shared struct that no roster component
    /// combines: the VM `Relations` bundle is drawn atomically (its components
    /// take the whole struct), so the relations only VM-side tables use come
    /// along unused. The narrow `poseidon2` relation joins them: every
    /// universal hash row is an atomic `poseidon2_io` row, so the narrow and
    /// wide emission lanes stay at zero multiplicity in the recursion AIR.
    const DRAWN_BUT_UNUSED: [&str; 10] = [
        "registers_state",
        "memory_access",
        "program_access",
        "merkle",
        "poseidon2",
        "bitwise",
        "range_check_20",
        "range_check_8_11",
        "range_check_8_8_4",
        "range_check_m31",
    ];

    #[test]
    fn registry_has_forty_eight_unique_relations() {
        let descriptors = universal_relation_descriptors();
        let names: HashSet<_> = descriptors.iter().map(|entry| entry.name).collect();
        assert_eq!(descriptors.len(), UNIVERSAL_RELATION_COUNT);
        assert_eq!(names.len(), UNIVERSAL_RELATION_COUNT);
    }

    #[test]
    fn registry_opens_with_the_vm_relation_layout() {
        let descriptors = universal_relation_descriptors();
        assert_eq!(
            &descriptors[..Relations::DESCRIPTORS.len()],
            &Relations::DESCRIPTORS[..]
        );
    }

    fn collect_usage(usage: &mut HashMap<String, usize>, evaluator: &ExprEvaluator) {
        let mut scan = |expr: &stwo_constraint_framework::expr::ExtExpr| {
            for param in expr.collect_variables().ext_params {
                if let Some(name) = param.strip_suffix("_z") {
                    usage.entry(name.to_owned()).or_insert(1);
                } else if let Some((name, index)) = param.rsplit_once("_alpha") {
                    if let Ok(index) = index.parse::<usize>() {
                        usage
                            .entry(name.to_owned())
                            .and_modify(|size| *size = (*size).max(index + 1))
                            .or_insert(index + 1);
                    }
                }
            }
        };
        // Relation combines are stored as extension intermediates and only
        // referenced by name from fractions and constraints, so the scan must
        // cover the intermediate bodies themselves.
        for constraint in &evaluator.constraints {
            scan(constraint);
        }
        for ext_intermediate in evaluator.ext_intermediates.values() {
            scan(ext_intermediate);
        }
        for fraction in &evaluator.logup.fracs {
            scan(&fraction.numerator);
            scan(&fraction.denominator);
        }
    }

    fn usage_of<E: FrameworkEval>(usage: &mut HashMap<String, usize>, eval: E) {
        eprintln!("evaluating {}", core::any::type_name::<E>());
        collect_usage(usage, &eval.evaluate(ExprEvaluator::new()));
        eprintln!("done {}", core::any::type_name::<E>());
    }

    fn universal_relation_usage() -> HashMap<String, usize> {
        const LOG_SIZE: u32 = 5;
        const KIND: ProofKind = ProofKind::SegmentLeaf;
        let relations = UniversalRelations::dummy();
        let mut usage = HashMap::new();
        usage_of(
            &mut usage,
            super::super::control_air::eval_for_proof_kind(
                LOG_SIZE,
                KIND,
                relations.control.clone(),
            ),
        );
        usage_of(
            &mut usage,
            super::super::transcript_air::Eval {
                log_size: LOG_SIZE,
                relations: super::super::transcript_air::TranscriptHashCallRelations::new(
                    &relations.vm,
                    &relations.transcript,
                ),
            },
        );
        usage_of(
            &mut usage,
            super::super::transcript_binding_air::eval_for_proof_kind(
                LOG_SIZE,
                KIND,
                &relations.control,
                &relations.transcript,
                &relations.transcript_binding,
            ),
        );
        usage_of(
            &mut usage,
            super::super::transcript_state_air::eval_for_proof_kind(
                LOG_SIZE,
                KIND,
                &relations.transcript_binding,
                &relations.transcript_state,
            ),
        );
        usage_of(
            &mut usage,
            super::super::transcript_word_air::eval_for_proof_kind(
                LOG_SIZE,
                KIND,
                &relations.transcript_binding,
                &relations.transcript_word,
            ),
        );
        usage_of(
            &mut usage,
            super::super::transcript_payload_air::eval_for_proof_kind(
                LOG_SIZE,
                KIND,
                &relations.transcript_word,
                &relations.verifier_input,
            ),
        );
        usage_of(
            &mut usage,
            super::super::pow::Eval {
                log_size: LOG_SIZE,
                relations: relations.pow.clone(),
            },
        );
        usage_of(
            &mut usage,
            super::super::pow::frame_eval(LOG_SIZE, &relations.pow, &relations.transcript_binding),
        );
        usage_of(
            &mut usage,
            super::super::relation_challenge_air::eval_for_proof_kind(
                LOG_SIZE,
                KIND,
                &relations.transcript_state,
                &relations.relation_challenge,
            ),
        );
        usage_of(
            &mut usage,
            super::super::verifier_randomness_air::eval_for_proof_kind(
                LOG_SIZE,
                KIND,
                &relations.transcript_state,
                &relations.verifier_randomness,
            ),
        );
        usage_of(
            &mut usage,
            super::super::statement_input_air::eval_for_proof_kind(
                LOG_SIZE,
                KIND,
                &relations.verifier_input,
                &relations.statement_input,
            ),
        );
        usage_of(
            &mut usage,
            super::super::statement_semantics_input_air::eval_for_proof_kind(
                LOG_SIZE,
                KIND,
                &relations.statement_input,
                &relations.recursion,
                &relations.vm,
            ),
        );
        usage_of(
            &mut usage,
            super::super::vm_public_claim_input_air::eval_for_proof_kind(
                LOG_SIZE,
                KIND,
                &relations.vm_public_claim_input,
                &relations.vm,
            ),
        );
        usage_of(
            &mut usage,
            super::super::vm_public_claim_hash_air::eval_for_proof_kind(
                LOG_SIZE,
                KIND,
                &relations.vm,
                &relations.vm_public_claim_input,
                &relations.vm_public_claim_hash,
                &relations.verifier_input,
            ),
        );
        usage_of(
            &mut usage,
            super::super::vm_public_io_hash_air::eval_for_proof_kind(
                LOG_SIZE,
                KIND,
                &relations.vm,
                &relations.vm_public_claim_input,
                &relations.vm_public_io_hash,
            ),
        );
        usage_of(
            &mut usage,
            super::super::vm_public_claim_semantics_input_air::eval_for_proof_kind(
                LOG_SIZE,
                KIND,
                &relations.vm_public_claim_input,
                &relations.statement_input,
                &relations.recursion,
                &relations.vm_public_io_hash,
            ),
        );
        usage_of(
            &mut usage,
            super::super::vm_public_logup_input_air::eval_for_proof_kind(
                LOG_SIZE,
                KIND,
                &relations.vm_public_claim_input,
                &relations.relation_challenge,
                &relations.verifier_input,
                &relations.recursion,
            ),
        );
        usage_of(
            &mut usage,
            super::super::vm_public_logup_control_air::eval_for_proof_kind(
                LOG_SIZE,
                KIND,
                relations.control.clone(),
            ),
        );
        usage_of(
            &mut usage,
            super::super::vm_air_composition_input_air::eval_for_proof_kind(
                LOG_SIZE,
                KIND,
                &relations.relation_challenge,
                &relations.verifier_input,
                &relations.verifier_randomness,
                &relations.recursion,
            ),
        );
        usage_of(
            &mut usage,
            super::super::vm_air_composition_control_air::eval_for_proof_kind(
                LOG_SIZE,
                KIND,
                relations.control.clone(),
            ),
        );
        usage_of(
            &mut usage,
            super::super::query_position_air::BitsEval {
                log_size: LOG_SIZE,
                proof_kind: KIND,
                randomness_relations: relations.verifier_randomness.clone(),
                query_relations: relations.query_position.clone(),
            },
        );
        usage_of(
            &mut usage,
            super::super::query_position_air::MappingEval {
                log_size: LOG_SIZE,
                proof_kind: KIND,
                query_relations: relations.query_position.clone(),
            },
        );
        usage_of(
            &mut usage,
            super::super::merkle_root_air::Eval {
                log_size: LOG_SIZE,
                proof_kind: KIND,
                verifier_input_relations: relations.verifier_input.clone(),
                recursion_relations: relations.recursion.clone(),
            },
        );
        usage_of(
            &mut usage,
            super::super::trace_merkle_air::Eval {
                log_size: LOG_SIZE,
                proof_kind: KIND,
                vm_relations: relations.vm.clone(),
                control_relations: relations.control.clone(),
                query_relations: relations.query_position.clone(),
                trace_relations: relations.trace_merkle.clone(),
                recursion_relations: relations.recursion.clone(),
            },
        );
        usage_of(
            &mut usage,
            super::super::pcs_deep_input_air::Eval {
                log_size: LOG_SIZE,
                proof_kind: KIND,
                verifier_input_relations: relations.verifier_input.clone(),
                trace_relations: relations.trace_merkle.clone(),
                randomness_relations: relations.verifier_randomness.clone(),
                query_relations: relations.query_position.clone(),
                deep_relations: relations.pcs_deep.clone(),
                circuit_relations: relations.recursion.clone(),
            },
        );
        usage_of(
            &mut usage,
            super::super::fri_merkle_air::LeafEval {
                log_size: LOG_SIZE,
                proof_kind: KIND,
                vm_relations: relations.vm.clone(),
                fri_relations: relations.fri_merkle.clone(),
                recursion_relations: relations.recursion.clone(),
            },
        );
        usage_of(
            &mut usage,
            super::super::fri_merkle_air::NodeEval {
                log_size: LOG_SIZE,
                proof_kind: KIND,
                vm_relations: relations.vm.clone(),
                fri_relations: relations.fri_merkle.clone(),
                recursion_relations: relations.recursion.clone(),
            },
        );
        usage_of(
            &mut usage,
            super::super::fri_merkle_air::AnchorEval {
                log_size: LOG_SIZE,
                proof_kind: KIND,
                control_relations: relations.control.clone(),
                query_relations: relations.query_position.clone(),
                fri_relations: relations.fri_merkle.clone(),
                recursion_relations: relations.recursion.clone(),
            },
        );
        usage_of(
            &mut usage,
            super::super::fri_verifier_control_air::Eval {
                log_size: LOG_SIZE,
                proof_kind: KIND,
                control_relations: relations.control.clone(),
                query_relations: relations.query_position.clone(),
                route_relations: relations.fri_verifier_route.clone(),
            },
        );
        usage_of(
            &mut usage,
            super::super::fri_verifier_input_air::Eval {
                log_size: LOG_SIZE,
                proof_kind: KIND,
                verifier_input_relations: relations.verifier_input.clone(),
                randomness_relations: relations.verifier_randomness.clone(),
                query_relations: relations.query_position.clone(),
                deep_relations: relations.pcs_deep.clone(),
                fri_merkle_relations: relations.fri_merkle.clone(),
                route_relations: relations.fri_verifier_route.clone(),
                circuit_relations: relations.recursion.clone(),
            },
        );
        usage_of(
            &mut usage,
            qm31_mul::Eval {
                log_size: LOG_SIZE,
                relations: crate::relations::SharedPrimitiveRelations::for_circuit(
                    &relations.recursion,
                ),
            },
        );
        usage_of(
            &mut usage,
            qm31_inv::Eval {
                log_size: LOG_SIZE,
                relations: crate::relations::SharedPrimitiveRelations::for_circuit(
                    &relations.recursion,
                ),
            },
        );
        usage_of(
            &mut usage,
            linear_ops::Eval {
                log_size: LOG_SIZE,
                relations: crate::relations::SharedPrimitiveRelations::for_circuit(
                    &relations.recursion,
                ),
            },
        );
        usage_of(
            &mut usage,
            merkle_path::Eval {
                log_size: LOG_SIZE,
                relations: crate::relations::SharedPrimitiveRelations::for_merkle(
                    &relations.vm,
                    &relations.recursion,
                ),
            },
        );
        usage_of(
            &mut usage,
            prover::components::lookups::range_check_8_8::air::Eval {
                log_size: LOG_SIZE,
                relations: relations.vm.clone(),
            },
        );
        usage
    }

    // The poseidon2 permutation nests its round expressions without shared
    // intermediates, so the formal-forest evaluator is exponential for it;
    // its VM relations are covered by the authoritative DESCRIPTORS registry.
    #[test]
    fn poseidon2_relations_are_covered_by_the_vm_registry() {
        let descriptors = universal_relation_descriptors();
        for name in ["poseidon2", "poseidon2_io"] {
            assert!(
                Relations::DESCRIPTORS
                    .iter()
                    .any(|entry| entry.name == name)
                    && descriptors[..Relations::DESCRIPTORS.len()]
                        .iter()
                        .any(|entry| entry.name == name),
                "poseidon2 relation {name} is not in the registry prefix"
            );
        }
    }

    #[test]
    fn every_component_relation_is_registered_with_enough_alpha_powers() {
        let descriptors = universal_relation_descriptors();
        let usage = universal_relation_usage();
        for (name, needed) in &usage {
            let entry = descriptors
                .iter()
                .find(|entry| entry.name == name)
                .unwrap_or_else(|| panic!("relation {name} used by a component is unregistered"));
            assert!(
                entry.size >= *needed,
                "relation {name} needs {needed} alpha powers, registry has {}",
                entry.size
            );
        }
    }

    #[test]
    fn only_shared_struct_passengers_are_registered_but_unused() {
        let descriptors = universal_relation_descriptors();
        let usage = universal_relation_usage();
        let mut unused: Vec<&str> = descriptors
            .iter()
            .map(|entry| entry.name)
            .filter(|name| !usage.contains_key(*name))
            .collect();
        unused.sort_unstable();
        let mut expected = DRAWN_BUT_UNUSED;
        expected.sort_unstable();
        assert_eq!(unused, expected);
    }

    fn instance_descriptor<R: Relation<M31, SecureField>>(relation: &R) -> (String, usize) {
        (
            Relation::<M31, SecureField>::get_name(relation).to_owned(),
            Relation::<M31, SecureField>::get_size(relation),
        )
    }

    #[test]
    fn registry_matches_drawn_relation_instances() {
        let relations = UniversalRelations::dummy();
        let instances = [
            instance_descriptor(&relations.recursion.merkle_node),
            instance_descriptor(&relations.recursion.op_def),
            instance_descriptor(&relations.recursion.wire),
            instance_descriptor(&relations.control.step),
            instance_descriptor(&relations.transcript.state),
            instance_descriptor(&relations.transcript.data),
            instance_descriptor(&relations.transcript.output),
            instance_descriptor(&relations.transcript.control),
            instance_descriptor(&relations.transcript_binding.frame_word),
            instance_descriptor(&relations.transcript_binding.frame_output),
            instance_descriptor(&relations.transcript_binding.pow_frame),
            instance_descriptor(&relations.transcript_state.digest_state),
            instance_descriptor(&relations.transcript_state.draw_output),
            instance_descriptor(&relations.transcript_word.payload_word),
            instance_descriptor(&relations.verifier_input.input_word),
            instance_descriptor(&relations.pow.check),
            instance_descriptor(&relations.relation_challenge.word),
            instance_descriptor(&relations.verifier_randomness.word),
            instance_descriptor(&relations.statement_input.statement_word),
            instance_descriptor(&relations.vm_public_claim_input.claim_word),
            instance_descriptor(&relations.vm_public_claim_input.claim_byte),
            instance_descriptor(&relations.vm_public_claim_input.io_word),
            instance_descriptor(&relations.vm_public_claim_hash.state),
            instance_descriptor(&relations.vm_public_io_hash.state),
            instance_descriptor(&relations.vm_public_io_hash.digest),
            instance_descriptor(&relations.query_position.bits),
            instance_descriptor(&relations.query_position.bit_value),
            instance_descriptor(&relations.query_position.position),
            instance_descriptor(&relations.trace_merkle.state),
            instance_descriptor(&relations.trace_merkle.value),
            instance_descriptor(&relations.pcs_deep.answer_word),
            instance_descriptor(&relations.fri_merkle.state),
            instance_descriptor(&relations.fri_merkle.value_word),
            instance_descriptor(&relations.fri_merkle.route),
            instance_descriptor(&relations.fri_merkle.local_root),
            instance_descriptor(&relations.fri_verifier_route.word),
        ];
        let registered: Vec<(String, usize)> = local_relation_descriptors()
            .iter()
            .map(|entry| (entry.name.to_owned(), entry.size))
            .collect();
        assert_eq!(registered, instances);
    }
}
