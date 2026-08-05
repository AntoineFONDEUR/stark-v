# Recursive proving

## Terminology and crate boundary

`continuation` and `recursion` solve different problems:

- `continuation` proves every execution segment independently and verifies all
  resulting proofs on the host. It also checks that adjacent public machine
  states match. A run with `n` segments produces `n` proofs, and both proof
  bytes and verification work grow with `n`. This is not recursion.
- `recursion` defines a universal AIR with a segment-leaf branch and a binary
  node branch. A completed binary tree will replace two child proofs with one
  proof of the same protocol and shape. Only this path can produce one
  constant-size root proof.

The recursion crate has no version suffix. Its root modules are the only active
recursion design.

## Current status

The recursion crate exposes a manifest-bound outer prover and verifier for
segment leaves, canonical empty leaves, and binary parents that verify two
recursion proofs. The repository does not yet expose the tree builder or
application root-proof API, so no code should describe the project as already
producing a constant-size root proof for a complete run.

The implemented foundation includes:

- a canonical protocol manifest and fixed-width proof wire;
- one frozen protocol profile without a version suffix, derived from both
  generated AIR rosters, with 193 FRI queries, 4 KiB public-input and
  public-output capacities, and an exact 3,459,396-byte universal proof wire;
- fixed VM trace generation that pads ordinary instruction and access tables to
  log size 6 and the finalized program, memory, Merkle, and Poseidon2 tables to
  log size 11, rejecting a segment instead of changing verifier-owned geometry;
- checked adaptation of an in-memory Poseidon VM proof into the fixed leaf wire,
  including expansion of deduplicated query values, Merkle siblings, and FRI
  cosets from prover-retained authentication data;
- typed complete-execution, job, slot, executed-span, and empty-span statements;
- a fixed verifier control plan shared by the manifest-bound recursion-targeted
  prover, fixed verifier execution, and AIR tables; ordinary VM proofs retain
  the public prover's native transcript;
- canonical transcript recording, payload ownership, digest-state chaining,
  proof-of-work checks, and relation-challenge binding;
- VM public-claim decoding and hashing;
- statement semantics for segment leaves, empty leaves, and binary folds;
- VM AIR composition evaluation generated from the prover component roster;
- DEEP quotient, trace-Merkle, FRI-Merkle, FRI-fold, last-layer, and query
  position constraints;
- deterministic segment-leaf and canonical empty-leaf witness assembly across
  all 36 universal components, including preprocessing, committed traces,
  interactions, public relation terms, exact global LogUp closure, and direct
  constraint acceptance;
- complete segment-leaf replay through VM claim semantics, AIR composition,
  trace and FRI authentication, DEEP quotient evaluation, both proofs of work,
  and the last-layer polynomial check;
- proof-free empty-leaf assembly that binds one checked height-zero padding
  statement and materializes every inactive verifier lane as zero;
- manifest-bound outer preprocessing, proving, and verification for segment,
  empty, and binary witnesses over the complete 36-component roster;
- an AIR self-program for verifying a recursion child;
- checked adaptation of an outer recursion proof into the fixed child wire,
  including raw-query expansion from prover-retained authentication data;
- two independent recursion-child verifier lanes whose transcript, claimed sums,
  composition, openings, DEEP quotient, FRI, and final polynomial checks close
  inside one binary-parent witness;
- shared QM31 multiplication, inversion, linear-operation, and Merkle-path trace
  tables;
- component, malformed-witness, relation-closure, and leaf-binding tests.

Segment, empty, and binary witnesses produce recursion proofs that bind the
expected protocol, statement, component claims, interaction claims, and STWO
proof. A real recursion proof can be encoded and verified as either binary
child. Adversarial binary-fold coverage, tree construction, and the public root
API remain unfinished.

The live universal roster has 36 components. Every recursion-local component is
authored directly through `define_air_fns!`; Poseidon2 uses the same macro, and
the range-check and other inner VM components are generated through
`define_air!`. The structural guard in `crates/recursion/tests/air_dsl_guard.rs`
pins the universal and inner VM rosters, their owning source files, and their
accepted macro counts. It rejects hand-written `FrameworkEval` implementations,
standalone `define_component_tables!` declarations, and wrapper macros in those
sources.

The host continuation remains useful while recursion is incomplete, but it is
not a final statement-verification API. Its public data does not currently bind
segment roles, and its verifier does not accept an application-supplied
complete-execution statement. Callers must not treat those helpers as a
constant-size or fully statement-bound proof system.

## Recursive statement

`CompleteExecutionStatement` is the application claim. It binds:

- protocol identity;
- program digest;
- initial and final machine state;
- public input and output digests;
- total cycle count.

`JobContext` adds the prover-internal segment count and derives the unique
minimal binary-tree height. `SpanStatement` binds one exact slot range inside
that tree. An executed span carries its first segment, number of segments, first
cycle, number of cycles, entry and exit state, and optional input/output edge
claims. An empty span has one canonical representation.

A valid binary node has two adjacent children of equal height. They must share
one job, occupy the exact left and right child slots, and agree at their
machine-state boundary. Folding them yields the unique parent span. Padding is
represented by canonical empty leaves, not by omitted children or proof-selected
tree shapes.

## Universal verifier

The proof kind selects one of three branches:

- `SegmentLeaf`: verify one stark-v VM proof and derive its height-zero
  statement;
- `BinaryNode`: verify two proofs produced by this recursion AIR and fold their
  statements;
- `EmptyLeaf`: prove the canonical unused slot required to complete the tree.

The protocol manifest fixes PCS parameters and the exact proof shapes for the VM
and recursion lanes. `VerifierControlPlan` derives the mandatory verifier
schedule from that trusted manifest. Proof bytes supply values only; they do not
choose operation counts, transcript phases, Merkle depths, FRI widths, or
relation closures.

The universal relation registry fixes relation draw order. The VM relation
bundle comes first so shared VM components preserve their established challenge
layout. Recursion-local relations then connect control, transcript, statement,
arithmetic, query, Merkle, DEEP, and FRI tables. Every branch rejects a nonzero
global LogUp sum across the complete roster. The outer proof carries the same
component claims and public terms, and verification recomputes the public
relation sum before accepting the STWO proof.

## Soundness invariants

The finished system must preserve all of these properties:

- The verifier schedule is derived from a trusted manifest and cannot be
  shortened or reordered by proof bytes.
- Every wire integer and field word has one canonical encoding; inactive
  fixed-capacity slots are all zero.
- The transcript absorbs the protocol, statement, PCS parameters, commitments,
  claims, sampled values, FRI data, and proof-of-work nonces in the same order
  in the manifest-bound prover, fixed verifier executor, and AIR.
- Every VM or recursion AIR constraint contributes to the composition value.
- Every opened value is bound to an authenticated trace or FRI path.
- Every public LogUp term is accumulated, and the global relation sum is zero.
- A segment leaf binds the VM public claim to exactly one height-zero span.
- A binary node verifies both children, checks adjacency, and exposes only the
  unique folded parent statement.
- Empty leaves can only pad slots beyond the declared segment count.
- The root statement equals the application-supplied complete-execution
  statement.
- Recursive proof shape and root verification work are independent of the number
  of segment leaves supported by the fixed protocol profile.

## Implementation ledger

[`docs/roadmap.md`](roadmap.md) is the single execution ledger. It owns stable
task IDs, dependencies, task status, acceptance gates, and test evidence for the
macro migration and recursive proving pipeline. This document remains the
technical design and soundness specification; it does not maintain a second task
list that can drift from the implementation order.

## Finish-line definition

The project reaches the recursion finish line only when an application can
submit one expected complete-execution statement and one root proof, the root
verifier checks that statement without descendant proofs, and the serialized
proof size is unchanged across the supported segment counts of the frozen
profile. Passing component tests alone is not completion.
