//! Recursion-local LogUp relations.
//!
//! `merkle_node` carries node claims `(tree_id, depth, index, digest words)`
//! along decommitment paths: rows of the `merkle_path` component consume
//! their own claim and emit the on-path child's, and roots are anchored by
//! the verifier's public root terms, so a path balances to exactly one public
//! root emission.

use stwo::core::channel::Channel;
use stwo_constraint_framework::relation;

relation!(MerkleNodeRelation, 11);
// Circuit values: (circuit_id, node_id, value words). Emitted by the row
// computing a node (with multiplicity = its use count) or by fixed input and
// constant anchors, and consumed once per use.
relation!(WireRelation, 6);

#[derive(Clone)]
pub struct RecursionRelations {
    pub merkle_node: MerkleNodeRelation,
    pub wire: WireRelation,
}

/// Relation bundle consumed by the macro-generated shared recursion
/// primitives. It contains the recursion-local circuit/path relations and the
/// VM Poseidon2 IO relation used by Merkle hashing, all cloned from the one
/// universal registry draw.
#[derive(Clone)]
pub struct SharedPrimitiveRelations {
    pub merkle_node: MerkleNodeRelation,
    pub wire: WireRelation,
    pub poseidon2_io: air::relations::relation_types::poseidon2_io,
}

impl SharedPrimitiveRelations {
    /// Bundle for circuit arithmetic, where the Poseidon2 relation is unused.
    pub fn for_circuit(recursion: &RecursionRelations) -> Self {
        Self {
            merkle_node: recursion.merkle_node.clone(),
            wire: recursion.wire.clone(),
            poseidon2_io: air::relations::relation_types::poseidon2_io::dummy(),
        }
    }

    /// Bundle for Merkle-path verification using the universal VM relation
    /// draw and recursion-local path relation draw.
    pub fn for_merkle(vm: &prover::relations::Relations, recursion: &RecursionRelations) -> Self {
        Self {
            merkle_node: recursion.merkle_node.clone(),
            wire: recursion.wire.clone(),
            poseidon2_io: vm.poseidon2_io.clone(),
        }
    }
}

impl RecursionRelations {
    /// Deterministic relations for component-level tests.
    pub fn dummy() -> Self {
        Self {
            merkle_node: MerkleNodeRelation::dummy(),
            wire: WireRelation::dummy(),
        }
    }

    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            merkle_node: MerkleNodeRelation::draw(channel),
            wire: WireRelation::draw(channel),
        }
    }
}
