//! Proof serialization utilities.
//!
//! stark-v proofs are serialized using postcard for efficient binary encoding.
//! The serialized VM proof omits prover-retained query-expansion maps: those
//! maps are unnecessary for native verification, and recursion callers must
//! adapt the in-memory split segment proof to its fixed leaf wire before
//! serialization.
//!
//! The proof type is `prover::SegmentProof<Blake2sMerkleHasher>` which contains
//! the VM and standalone Poseidon2 proofs plus their joint interaction claim.
//! Each constituent carries its component shape, LogUp sum, and STARK proof;
//! the VM constituent also carries execution public data. In-memory query
//! expansion is omitted from serialization, while the segment artifact retains
//! the joint proof-of-work nonce needed to replay the shared relation draw.
