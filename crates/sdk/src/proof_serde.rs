//! Proof serialization utilities.
//!
//! stark-v proofs are serialized using postcard for efficient binary encoding.
//! The serialized VM proof omits prover-retained query-expansion maps: those
//! maps are unnecessary for native verification, and recursion callers must
//! adapt an in-memory Poseidon proof to its fixed leaf wire before serialization.
//!
//! The proof type is `prover::Proof<Blake2sMerkleHasher>` which contains:
//! - `claim`: Component log sizes
//! - `interaction_claim`: LogUp claimed sums
//! - `public_data`: Execution state (PC, registers, I/O)
//! - `stark_proof`: The underlying STARK proof
//! - `stark_aux`: In-memory expansion data omitted from serialization
//! - `interaction_pow`: Proof-of-work nonce
