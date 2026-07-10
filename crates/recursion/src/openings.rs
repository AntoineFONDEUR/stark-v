//! Merkle-opening replay: the post-OODS commitment-scheme protocol of an
//! inner Poseidon2-channel proof, with every value check run natively and
//! every Merkle opening expressed as recursion-AIR path rows.
//!
//! This mirrors `CommitmentSchemeVerifier::verify_values` exactly — sampled
//! values mixed, the FRI quotient coefficient and folding alphas drawn, the
//! proof of work checked, query positions drawn, FRI answers and the fold
//! chain recomputed down to the last-layer polynomial — but where stwo's
//! verifier hashes decommitment paths, this module instead:
//! - on the prove side, walks the decommitments and pushes one root-to-leaf
//!   `merkle_path` row chain per opened position (shared upper rows are
//!   pushed once per path; the duplicated claims telescope in LogUp), and
//! - on both sides, derives the public anchors: a `RootClaim` per tree and a
//!   `LeafClaim` per opened position, whose digests the final verifier
//!   recomputes from the public queried values.
//!
//! Every fold and quotient formula is stwo's own public function
//! (`fri_answers`, `fold_circle_into_line`, `fold_coset`); only the
//! decommitment walk is re-derived here, because the recursion AIR needs the
//! intermediate node digests stwo's verifier does not expose.

use std::collections::BTreeMap;

use crate::transcript::PcsBindingData;
use prover::poseidon2_channel::{
    Poseidon2M31Channel, Poseidon2M31Hash, Poseidon2M31MerkleChannel, Poseidon2M31MerkleHasher,
};
use stwo::core::channel::{Channel, MerkleChannel};
use stwo::core::circle::Coset;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::{SECURE_EXTENSION_DEGREE, SecureField};
use stwo::core::fri::{fold_circle_into_line, fold_coset};
use stwo::core::pcs::PcsConfig;
use stwo::core::pcs::quotients::{CommitmentSchemeProof, PointSample, fri_answers};
use stwo::core::pcs::utils::prepare_preprocessed_query_positions;
use stwo::core::poly::circle::{CanonicCoset, CircleDomain};
use stwo::core::poly::line::LineDomain;
use stwo::core::queries::{Queries, draw_queries};
use stwo::core::utils::bit_reverse_index;
use stwo::core::vcs_lifted::merkle_hasher::MerkleHasherLifted;
use stwo::core::vcs_lifted::verifier::{LOG_PACKED_LEAF_SIZE, MerkleDecommitmentLifted};

use crate::merkle_path::{PathStep, push_path_step};
use crate::prover::{LeafClaim, RecursionTraces, RootClaim};

/// Number of distinct tree ids a single segment's openings may use: the
/// commitment trees plus one per FRI layer. Segments space their
/// `tree_id_base` by this stride.
pub const TREE_ID_STRIDE: u32 = 64;

/// Largest FRI folding step accepted by the recursion opening replay.
const MAX_FRI_FOLD_STEP: u32 = 4;

/// The public anchors of a proof's openings.
#[derive(Default, Clone, Debug)]
pub struct OpeningClaims {
    pub roots: Vec<RootClaim>,
    pub leaves: Vec<LeafClaim>,
}

/// Replay the post-OODS protocol of an inner proof. Runs every native value
/// check; with `traces`, also pushes the in-AIR path rows from the proof's
/// decommitments. Returns the public opening anchors.
pub fn replay_pcs_openings(
    stark_proof: &CommitmentSchemeProof<Poseidon2M31MerkleHasher>,
    pcs: &PcsBindingData<Poseidon2M31MerkleChannel>,
    config: PcsConfig,
    tree_id_base: u32,
    mut traces: Option<&mut RecursionTraces>,
) -> Result<OpeningClaims, String> {
    let fold_step = config.fri_config.fold_step;
    if !(1..=MAX_FRI_FOLD_STEP).contains(&fold_step) {
        return Err(format!(
            "unsupported FRI fold step {fold_step}; expected 1..={MAX_FRI_FOLD_STEP}"
        ));
    }
    let log_blowup = config.fri_config.log_blowup_factor;
    let lifting_log_size = pcs.lifting_log_size;
    let mut channel: Poseidon2M31Channel = pcs.channel.clone();

    // Sampled values and the FRI quotient-combination coefficient.
    channel.mix_felts(&stark_proof.sampled_values.clone().flatten_cols());
    let random_coeff = channel.draw_secure_felt();

    // FRI commit phase: roots mixed and folding alphas drawn per layer,
    // domains tracked exactly as `FriVerifier::commit`.
    let fri_proof = &stark_proof.fri_proof;
    Poseidon2M31MerkleChannel::mix_root(&mut channel, fri_proof.first_layer.commitment);
    let first_alpha = channel.draw_secure_felt();
    let column_bound = lifting_log_size - log_blowup;
    let first_layer_domain = CanonicCoset::new(column_bound + log_blowup).circle_domain();

    struct InnerLayer {
        domain: LineDomain,
        alpha: SecureField,
        fold_step: u32,
        pack_leaves: bool,
        commitment: Poseidon2M31Hash,
    }
    let mut inner_layers = Vec::new();
    let mut layer_log_degree = column_bound
        .checked_sub(fold_step)
        .ok_or("invalid number of FRI layers")?;
    let mut layer_domain = LineDomain::new(Coset::half_odds(layer_log_degree + log_blowup));
    let n_inner_layers = fri_proof.inner_layers.len();
    for (layer_index, layer_proof) in fri_proof.inner_layers.iter().enumerate() {
        Poseidon2M31MerkleChannel::mix_root(&mut channel, layer_proof.commitment);
        let is_last = layer_index == n_inner_layers - 1;
        let layer_fold_step = if !is_last {
            fold_step
        } else {
            let res = layer_log_degree
                .checked_sub(config.fri_config.log_last_layer_degree_bound)
                .ok_or("invalid number of FRI layers")?;
            if !(1..=fold_step).contains(&res) {
                return Err("invalid number of FRI layers".to_string());
            }
            res
        };
        inner_layers.push(InnerLayer {
            domain: layer_domain,
            alpha: channel.draw_secure_felt(),
            fold_step: layer_fold_step,
            pack_leaves: layer_domain.log_size() >= LOG_PACKED_LEAF_SIZE && layer_fold_step > 1,
            commitment: layer_proof.commitment,
        });
        layer_log_degree = layer_log_degree
            .checked_sub(layer_fold_step)
            .ok_or("invalid number of FRI layers")?;
        layer_domain = layer_domain.repeated_double(layer_fold_step);
    }
    if layer_log_degree != config.fri_config.log_last_layer_degree_bound {
        return Err("invalid number of FRI layers".to_string());
    }
    let last_layer_domain = layer_domain;
    let last_layer_poly = &fri_proof.last_layer_poly;
    if last_layer_poly.len() > (1 << config.fri_config.log_last_layer_degree_bound) {
        return Err("last layer degree invalid".to_string());
    }
    channel.mix_felts(last_layer_poly);

    // Proof of work.
    if !channel.verify_pow_nonce(config.pow_bits, stark_proof.proof_of_work) {
        return Err("proof of work verification failed".to_string());
    }
    channel.mix_u64(stark_proof.proof_of_work);

    // Query positions on the lifting domain.
    let unsorted = draw_queries(&mut channel, lifting_log_size, config.fri_config.n_queries);
    let queries = Queries::new(&unsorted, lifting_log_size);
    let query_positions = queries.positions.clone();

    // Commitment-tree openings. Tree 0 (preprocessed) may have a different
    // height; its positions are re-mapped exactly as the stwo verifier does.
    let mut claims = OpeningClaims::default();
    let preprocessed_positions = prepare_preprocessed_query_positions(
        &query_positions,
        lifting_log_size,
        pcs.tree_heights[0],
    );
    for (tree_index, height) in pcs.tree_heights.iter().copied().enumerate() {
        let positions: &[usize] = if tree_index == 0 {
            &preprocessed_positions
        } else {
            assert_eq!(
                height, lifting_log_size,
                "non-preprocessed trees commit at the lifting size"
            );
            &query_positions
        };
        open_lifted_tree(
            tree_id_base + tree_index as u32,
            pcs.roots[tree_index],
            height,
            &pcs.column_log_sizes[tree_index],
            positions,
            &stark_proof.queried_values[tree_index],
            traces
                .as_deref_mut()
                .map(|t| (&stark_proof.decommitments[tree_index], t)),
            &mut claims,
        )?;
    }

    // FRI answers: the DEEP quotients at every query position, from the
    // public sampled and queried values.
    let samples = pcs
        .sample_points
        .clone()
        .zip_cols(stark_proof.sampled_values.clone())
        .map_cols(|(points, values)| {
            points
                .into_iter()
                .zip(values)
                .map(|(point, value)| PointSample { point, value })
                .collect::<Vec<_>>()
        });
    let first_layer_evals = fri_answers(
        pcs.column_log_sizes.clone(),
        samples,
        random_coeff,
        &query_positions,
        stark_proof.queried_values.clone(),
        lifting_log_size,
    )
    .map_err(|e| format!("fri answers: {e}"))?;

    let n_trace_trees = pcs.tree_heights.len() as u32;

    // FRI first layer: open the committed quotient column and fold
    // circle -> line.
    let mut fri_witness = fri_proof.first_layer.fri_witness.iter().copied();
    let (positions, subsets, initials) =
        rebuild_subset_evals(&queries, &first_layer_evals, &mut fri_witness, fold_step)?;
    if fri_witness.next().is_some() {
        return Err("first layer witness too long".to_string());
    }
    open_secure_column_tree(
        tree_id_base + n_trace_trees,
        fri_proof.first_layer.commitment,
        first_layer_domain.log_size(),
        &positions,
        subsets.iter().flatten().copied(),
        first_layer_domain.log_size() >= LOG_PACKED_LEAF_SIZE && fold_step > 1,
        traces
            .as_deref_mut()
            .map(|t| (&fri_proof.first_layer.decommitment, t)),
        &mut claims,
    )?;
    let mut layer_queries = queries.fold(fold_step);
    let mut layer_evals: Vec<SecureField> = subsets
        .iter()
        .zip(&initials)
        .map(|(subset, &initial)| {
            fold_circle_subset(subset, initial, first_layer_domain, first_alpha, fold_step)
        })
        .collect();

    // FRI inner layers: open each layer's tree and fold line -> line.
    for (layer_index, layer) in inner_layers.iter().enumerate() {
        let mut fri_witness = fri_proof.inner_layers[layer_index]
            .fri_witness
            .iter()
            .copied();
        let (positions, subsets, initials) = rebuild_subset_evals(
            &layer_queries,
            &layer_evals,
            &mut fri_witness,
            layer.fold_step,
        )?;
        if fri_witness.next().is_some() {
            return Err(format!("inner layer {layer_index} witness too long"));
        }
        open_secure_column_tree(
            tree_id_base + n_trace_trees + 1 + layer_index as u32,
            layer.commitment,
            layer.domain.log_size(),
            &positions,
            subsets.iter().flatten().copied(),
            layer.pack_leaves,
            traces
                .as_deref_mut()
                .map(|t| (&fri_proof.inner_layers[layer_index].decommitment, t)),
            &mut claims,
        )?;
        layer_evals = subsets
            .iter()
            .zip(&initials)
            .map(|(subset, &initial)| {
                let fold_domain_initial = layer.domain.coset().index_at(initial);
                let fold_domain = LineDomain::new(Coset::new(fold_domain_initial, layer.fold_step));
                fold_coset(subset.clone(), fold_domain, layer.alpha)
            })
            .collect();
        layer_queries = layer_queries.fold(layer.fold_step);
    }

    // Last layer: every folded value must lie on the public polynomial.
    for (&query, eval) in layer_queries.positions.iter().zip(&layer_evals) {
        let x = last_layer_domain.at(bit_reverse_index(query, last_layer_domain.log_size()));
        if *eval != last_layer_poly.eval_at_point(x.into()) {
            return Err("last layer evaluation invalid".to_string());
        }
    }

    Ok(claims)
}

/// Fold one circle-domain subset with Stwo's first-layer challenge schedule.
fn fold_circle_subset(
    subset: &[SecureField],
    domain_initial_index: usize,
    source_domain: CircleDomain,
    alpha: SecureField,
    fold_step: u32,
) -> SecureField {
    let fold_domain_initial = source_domain.index_at(domain_initial_index);
    let circle_fold_domain = CircleDomain::new(Coset::new(fold_domain_initial, fold_step - 1));
    let line_evals = fold_circle_into_line(subset, circle_fold_domain, alpha);
    if fold_step == 1 {
        return line_evals[0];
    }
    let line_fold_step = fold_step - 1;
    let line_fold_domain = LineDomain::new(Coset::new(fold_domain_initial, line_fold_step));
    fold_coset(line_evals, line_fold_domain, alpha * alpha)
}

/// A FRI layer's rebuilt openings: the decommitted positions, the per-subset
/// evaluations, and each subset's initial domain index.
type SubsetEvals = (Vec<usize>, Vec<Vec<SecureField>>, Vec<usize>);

/// Rebuild the per-subset evaluations of a FRI layer: queried positions take
/// the values computed so far, off-query positions take proof witness values
/// (the committed siblings). Mirrors stwo's
/// `compute_decommitment_positions_and_rebuild_evals`.
fn rebuild_subset_evals(
    queries: &Queries,
    query_evals: &[SecureField],
    witness_evals: &mut impl Iterator<Item = SecureField>,
    fold_step: u32,
) -> Result<SubsetEvals, String> {
    let mut query_evals = query_evals.iter().copied();
    let mut decommitment_positions = Vec::new();
    let mut subset_evals = Vec::new();
    let mut subset_domain_index_initials = Vec::new();

    for subset_queries in queries
        .positions
        .chunk_by(|a, b| a >> fold_step == b >> fold_step)
    {
        let subset_start = (subset_queries[0] >> fold_step) << fold_step;
        let subset_positions = subset_start..subset_start + (1 << fold_step);
        decommitment_positions.extend(subset_positions.clone());

        let mut subset_queries_iter = subset_queries.iter().copied().peekable();
        let subset_eval = subset_positions
            .map(|position| match subset_queries_iter.next_if_eq(&position) {
                Some(_) => Ok(query_evals.next().expect("one eval per query")),
                None => witness_evals.next().ok_or("insufficient FRI witness"),
            })
            .collect::<Result<Vec<_>, _>>()?;
        subset_evals.push(subset_eval);
        subset_domain_index_initials.push(bit_reverse_index(subset_start, queries.log_domain_size));
    }
    Ok((
        decommitment_positions,
        subset_evals,
        subset_domain_index_initials,
    ))
}

/// Open a lifted commitment tree: recompute the leaf digests from the public
/// queried values (every column contributes one value per leaf, columns
/// sorted by log size as in `MerkleVerifierLifted::verify`), derive the
/// public anchors, and — with decommitments — push the in-AIR path rows.
#[allow(clippy::too_many_arguments)]
fn open_lifted_tree(
    tree_id: u32,
    root: Poseidon2M31Hash,
    height: u32,
    column_log_sizes: &[u32],
    query_positions: &[usize],
    queried_values: &[Vec<BaseField>],
    decommit: Option<(
        &MerkleDecommitmentLifted<Poseidon2M31MerkleHasher>,
        &mut RecursionTraces,
    )>,
    claims: &mut OpeningClaims,
) -> Result<(), String> {
    if height == 0 {
        return Ok(());
    }
    // Duplicate positions must carry duplicate values.
    for i in 1..query_positions.len() {
        if query_positions[i - 1] == query_positions[i] {
            for col in queried_values {
                if col[i - 1] != col[i] {
                    return Err("inconsistent values at duplicate query position".to_string());
                }
            }
        }
    }

    // Columns sorted by log size (stable), values deduplicated per position.
    let mut column_order: Vec<usize> = (0..queried_values.len()).collect();
    column_order.sort_by_key(|&c| column_log_sizes[c]);

    let mut dedup_positions: Vec<usize> = Vec::new();
    let mut dedup_indices: Vec<usize> = Vec::new();
    for (i, &pos) in query_positions.iter().enumerate() {
        if dedup_positions.last() != Some(&pos) {
            dedup_positions.push(pos);
            dedup_indices.push(i);
        }
    }

    let mut leaf_digests: BTreeMap<usize, [u32; 8]> = BTreeMap::new();
    for (&pos, &value_index) in dedup_positions.iter().zip(&dedup_indices) {
        let row: Vec<BaseField> = column_order
            .iter()
            .map(|&c| queried_values[c][value_index])
            .collect();
        let mut hasher = Poseidon2M31MerkleHasher::default();
        hasher.update_leaf(&row);
        leaf_digests.insert(pos, hasher.finalize().0);
    }

    finish_tree_opening(tree_id, root, height, leaf_digests, decommit, claims)
}

/// Open a FRI layer tree using STWO's fixed multi-evaluation leaf packing.
#[allow(clippy::too_many_arguments)]
fn open_secure_column_tree(
    tree_id: u32,
    root: Poseidon2M31Hash,
    domain_log_size: u32,
    positions: &[usize],
    values: impl Iterator<Item = SecureField>,
    pack_leaves: bool,
    decommit: Option<(
        &MerkleDecommitmentLifted<Poseidon2M31MerkleHasher>,
        &mut RecursionTraces,
    )>,
    claims: &mut OpeningClaims,
) -> Result<(), String> {
    let leaf_log_size = if pack_leaves { LOG_PACKED_LEAF_SIZE } else { 0 };
    let height = domain_log_size
        .checked_sub(leaf_log_size)
        .ok_or("packed FRI leaf exceeds its domain")?;
    let leaf_size = 1usize << leaf_log_size;
    let values: Vec<SecureField> = values.collect();
    if positions.len() != values.len() || !positions.len().is_multiple_of(leaf_size) {
        return Err("invalid FRI leaf value count".to_string());
    }

    let mut leaf_digests: BTreeMap<usize, [u32; 8]> = BTreeMap::new();
    for (position_chunk, value_chunk) in positions
        .chunks_exact(leaf_size)
        .zip(values.chunks_exact(leaf_size))
    {
        let leaf_position = position_chunk[0] >> leaf_log_size;
        let row_start = leaf_position << leaf_log_size;
        if position_chunk
            .iter()
            .copied()
            .ne(row_start..row_start + leaf_size)
        {
            return Err("FRI leaf positions are not consecutive".to_string());
        }
        let row: Vec<BaseField> = value_chunk
            .iter()
            .flat_map(|value| value.to_m31_array())
            .collect();
        debug_assert_eq!(row.len(), SECURE_EXTENSION_DEGREE * leaf_size);
        let mut hasher = Poseidon2M31MerkleHasher::default();
        hasher.update_leaf(&row);
        if leaf_digests
            .insert(leaf_position, hasher.finalize().0)
            .is_some()
        {
            return Err("duplicate FRI Merkle leaf".to_string());
        }
    }
    finish_tree_opening(tree_id, root, height, leaf_digests, decommit, claims)
}

/// Derive the public anchors of one tree and, with decommitments, push the
/// path rows: one full root-to-leaf chain per opened position.
fn finish_tree_opening(
    tree_id: u32,
    root: Poseidon2M31Hash,
    height: u32,
    leaf_digests: BTreeMap<usize, [u32; 8]>,
    decommit: Option<(
        &MerkleDecommitmentLifted<Poseidon2M31MerkleHasher>,
        &mut RecursionTraces,
    )>,
    claims: &mut OpeningClaims,
) -> Result<(), String> {
    for (&pos, &digest) in &leaf_digests {
        claims.leaves.push(LeafClaim {
            tree_id,
            depth: height,
            index: pos as u32,
            digest,
        });
    }
    claims.roots.push(RootClaim {
        tree_id,
        root: root.0,
        n_paths: leaf_digests.len() as u32,
    });

    let Some((decommitment, traces)) = decommit else {
        return Ok(());
    };
    let levels = walk_tree(height, &leaf_digests, &decommitment.hash_witness)?;
    if levels[0].get(&0) != Some(&root.0) {
        return Err("decommitment root mismatch".to_string());
    }
    for &pos in leaf_digests.keys() {
        let mut child = leaf_digests[&pos];
        // Bottom-up: the row at depth d hashes the on-path child at depth
        // d+1 with its sibling, consuming its own node claim and emitting
        // the child's.
        for depth in (0..height).rev() {
            let child_index = pos >> (height - 1 - depth);
            let sibling = levels[(depth + 1) as usize]
                .get(&(child_index ^ 1))
                .copied()
                .ok_or("missing sibling digest")?;
            let parent = push_path_step(
                &mut traces.merkle_path,
                &mut traces.poseidon2,
                tree_id,
                depth,
                (pos >> (height - depth)) as u32,
                child,
                PathStep {
                    direction: (child_index & 1) as u32,
                    sibling,
                },
                false,
            );
            debug_assert_eq!(
                levels[depth as usize].get(&(pos >> (height - depth))),
                Some(&parent),
                "path step digest diverges from the decommitment walk"
            );
            child = parent;
        }
        if child != root.0 {
            return Err("path does not terminate at the root".to_string());
        }
    }
    Ok(())
}

/// Walk a decommitment bottom-up, exactly as `MerkleVerifierLifted::verify`:
/// siblings missing from a level come from the hash witness. Returns every
/// node digest per depth (depth 0 = root), witness siblings included.
fn walk_tree(
    height: u32,
    leaf_digests: &BTreeMap<usize, [u32; 8]>,
    hash_witness: &[Poseidon2M31Hash],
) -> Result<Vec<BTreeMap<usize, [u32; 8]>>, String> {
    let mut levels: Vec<BTreeMap<usize, [u32; 8]>> = vec![BTreeMap::new(); height as usize + 1];
    levels[height as usize] = leaf_digests.clone();
    let mut witness = hash_witness.iter();

    for depth in (0..height).rev() {
        let prev: Vec<(usize, [u32; 8])> = levels[depth as usize + 1]
            .iter()
            .map(|(&i, &d)| (i, d))
            .collect();
        let mut current = BTreeMap::new();
        let mut witnesses_used: Vec<(usize, [u32; 8])> = Vec::new();
        let mut iter = prev.iter().peekable();
        while let Some(&(index, digest)) = iter.next() {
            let children = if let Some(&&(next_index, next_digest)) = iter.peek() {
                if index % 2 == 0 && next_index == index ^ 1 {
                    iter.next();
                    (digest, next_digest)
                } else {
                    let sibling = witness.next().ok_or("witness too short")?.0;
                    witnesses_used.push((index ^ 1, sibling));
                    if index % 2 == 0 {
                        (digest, sibling)
                    } else {
                        (sibling, digest)
                    }
                }
            } else {
                let sibling = witness.next().ok_or("witness too short")?.0;
                witnesses_used.push((index ^ 1, sibling));
                if index % 2 == 0 {
                    (digest, sibling)
                } else {
                    (sibling, digest)
                }
            };
            let parent = Poseidon2M31MerkleHasher::hash_children((
                Poseidon2M31Hash(children.0),
                Poseidon2M31Hash(children.1),
            ));
            current.insert(index >> 1, parent.0);
        }
        for (index, digest) in witnesses_used {
            levels[depth as usize + 1].insert(index, digest);
        }
        levels[depth as usize] = current;
    }
    if witness.next().is_some() {
        return Err("witness too long".to_string());
    }
    Ok(levels)
}
