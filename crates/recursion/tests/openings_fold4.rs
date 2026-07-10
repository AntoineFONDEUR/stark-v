//! Real-proof coverage for fold-step-4 FRI opening replay.

use num_traits::One;
use prover::poseidon2_channel::{Poseidon2M31MerkleChannel, Poseidon2M31MerkleHasher};
use prover::{
    FriConfig, PcsConfig, Preprocessing, Proof, preprocess_with_channel, prove_rv32im_with_channel,
    verify_rv32im_with_channel,
};
use recursion::aggregate_tree::prove_base_node;
use recursion::node::{prove_node_compressed_n, verify_node_compressed};
use recursion::openings::replay_pcs_openings;
use recursion::prover::RecursionTraces;
use recursion::transcript::{PcsBindingData, full_binding_data_with_channel};
use std::sync::OnceLock;
use stwo::core::vcs_lifted::verifier::LOG_PACKED_LEAF_SIZE;

struct Fold4Fixture {
    config: PcsConfig,
    preprocessing: Preprocessing<Poseidon2M31MerkleHasher>,
    proof: Proof<Poseidon2M31MerkleHasher>,
    pcs: PcsBindingData<Poseidon2M31MerkleChannel>,
}

fn real_fold4_proof() -> &'static Fold4Fixture {
    static FIXTURE: OnceLock<Fold4Fixture> = OnceLock::new();
    FIXTURE.get_or_init(|| {
        prover::e2e::ensure_guest_built();
        let elf_path = prover::e2e::guest_bin_dir().join("constant");
        let elf = std::fs::read(&elf_path)
            .unwrap_or_else(|error| panic!("failed to read {elf_path:?}: {error}"));
        let run = runner::run(&elf, 10_000_000).expect("constant guest run failed");
        let config = PcsConfig {
            pow_bits: 0,
            fri_config: FriConfig::new(0, 1, 3, 4),
            lifting_log_size: None,
        };
        let preprocessing = preprocess_with_channel::<Poseidon2M31MerkleChannel>(config);
        let proof =
            prove_rv32im_with_channel::<Poseidon2M31MerkleChannel>(run, config, &preprocessing);
        verify_rv32im_with_channel::<Poseidon2M31MerkleChannel>(
            proof.clone(),
            config,
            &preprocessing,
        )
        .expect("Stwo rejected its fold-step-4 proof");
        let (_, pcs) = full_binding_data_with_channel::<Poseidon2M31MerkleChannel>(
            &proof,
            config,
            &preprocessing,
        )
        .expect("fold-step-4 transcript replay failed");
        Fold4Fixture {
            config,
            preprocessing,
            proof,
            pcs,
        }
    })
}

#[test]
fn replay_accepts_real_fold4_openings() {
    let fixture = real_fold4_proof();

    let replay = replay_pcs_openings(
        &fixture.proof.stark_proof.0,
        &fixture.pcs,
        fixture.config,
        0,
        None,
    );

    assert!(replay.is_ok(), "fold-step-4 replay failed: {replay:?}");
}

#[test]
fn replay_anchors_fold4_first_layer_at_packed_tree_depth() {
    let fixture = real_fold4_proof();
    let mut traces = RecursionTraces::default();

    let claims = replay_pcs_openings(
        &fixture.proof.stark_proof.0,
        &fixture.pcs,
        fixture.config,
        0,
        Some(&mut traces),
    )
    .expect("fold-step-4 replay failed");
    let first_fri_tree = fixture.pcs.tree_heights.len() as u32;
    let packed_depth = fixture.pcs.lifting_log_size - LOG_PACKED_LEAF_SIZE;

    assert!(
        claims
            .leaves
            .iter()
            .any(|leaf| leaf.tree_id == first_fri_tree && leaf.depth == packed_depth)
    );
}

#[test]
fn replay_rejects_tampered_fold4_witness() {
    let fixture = real_fold4_proof();
    let mut proof = fixture.proof.stark_proof.0.clone();
    let witness = proof
        .fri_proof
        .first_layer
        .fri_witness
        .first_mut()
        .expect("fold-step-4 proof has a first-layer witness");
    *witness += stwo::core::fields::qm31::SecureField::one();

    let replay = replay_pcs_openings(&proof, &fixture.pcs, fixture.config, 0, None);

    assert!(replay.is_err());
}

#[test]
fn fold4_packed_merkle_rows_verify_in_recursion_air() {
    let fixture = real_fold4_proof();
    let leaf = prove_base_node(
        std::slice::from_ref(&fixture.proof),
        fixture.config,
        &fixture.preprocessing,
    )
    .expect("fold-step-4 base node proving failed");
    let root = prove_node_compressed_n(vec![leaf], fixture.config)
        .expect("fold-step-4 node proving failed");

    let verification = verify_node_compressed(root, fixture.config);

    assert!(
        verification.is_ok(),
        "fold-step-4 recursion verification failed: {verification:?}"
    );
}
