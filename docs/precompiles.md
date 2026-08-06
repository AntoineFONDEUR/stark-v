# Hash precompiles: proving Poseidon2 outside the RV32IM prover

> **Status: production split in progress.** `crates/prover/src/precompile.rs`
> proves the central cross-proof mechanism: two independent STWO proofs share a
> LogUp relation drawn from both committed traces, and their claimed sums must
> cancel. It includes a square exemplar and a Poseidon2 exemplar over the
> 32-word `poseidon2_io` tuple. The VM prover does not yet offload Poseidon2,
> segment artifacts do not contain a precompile proof, and recursion does not
> yet verify the pair. All three prototype binding components are expressed
> directly through `define_air_fns!`. The prototype commits both main traces,
> grinds one joint interaction PoW over their ordered post-commitment seeds, and
> only then draws the shared relations.
> `crates/prover/src/poseidon2_precompile.rs` now provides the production
> standalone Poseidon2 instance: its fixed main trace is committed before its
> seed is exposed, its proof carries the shared claimed sum and exact trace
> shapes, and verification works with both Blake2s and the recursion profile's
> Poseidon2-M31 channel. The VM proof still contains Poseidon2, so segment
> artifacts and recursion do not yet consume this instance.

Goal: take the Poseidon2 table out of the rv32im stwo instance and prove it in
its own instance, binding the two proofs through their shared LogUp relation.
The rv32im prover keeps emitting `(input, output)` permutation tuples; a
separate hash prover consumes them and attests they are real permutations. The
two instances prove in parallel, the rv32im trace loses its widest component,
and every further hash function (Keccak, Blake, SHA) follows the same pattern as
an additional precompile prover.

## Why LogUp binding, not preprocessing

The tempting framing — "prove the poseidon2 table first and hand the
`(input, output)` pairs to the rv32im prove as a preprocessed trace" — does not
fit what preprocessing means here: preprocessed columns are
execution-independent, committed once, cached on disk, and known to the verifier
(`prover::preprocess`). Hash IO pairs change with every execution, so they would
be a fresh per-proof committed tree, not preprocessing — and the verifier would
still need a reason to believe the pairs are valid permutations.

The codebase already has the required relation:
`poseidon2_io(in_0..in_15, out_0..out_15)` binds a permutation's ends
atomically. Inside the current VM proof, the Poseidon2 component's emissions
cancel the merkle/sponge components' consumptions and the total claimed sum is
zero. Splitting the prover just means the cancellation happens **across two
proofs**: each proof publishes its (non-zero) claimed sum for the shared
relation, and the binder checks they cancel.

## Trust argument

For LogUp sums from two proofs to be addable, both must be computed with the
same relation parameters `(z, alphas)` — and `z` must be drawn after both
multisets are committed, or a malicious prover picks its multiset knowing `z`.
This forces a transcript handshake between the instances:

```text
rv32im prover                      hash prover
  commit main trace ──── root_a ──┐
                                  ├── mix(root_a, root_b) ── joint PoW
  commit poseidon2 IO ◄─ root_b ──┘                    │
                                   draw (z, alphas) ◄──┘
  interaction phase ◄─────────────────────────────────┤
  STARK proof A                                       └─► interaction phase
                                                          STARK proof B
```

Both provers can run their trace-commitment phase in parallel, synchronize once
to grind the joint interaction nonce and derive the shared relation draw, then
finish independently. The ordered roots and joint nonce are absorbed into both
constituent proof transcripts. The continuation verifier first, and the
recursive verifier once implemented, replay the same PoW and draw from both
proofs' commitments and check `claimed_sum_A + claimed_sum_B = 0` for the shared
relation (A's own internal relations still balance to zero on their own, as do
B's).

The recursive verifier must treat the VM proof and precompile proof as one leaf
artifact: it verifies both proof transcripts and binds their shared relation sum
before deriving the segment statement.

## What changes where

1. **AIR definitions**: keep the `poseidon2` function and table in
   `define_air_fns!`; `poseidon2_io` already exists in the VM relation schema.
   The prototype's square emit, square consume, and 32-word host binding tables
   already use `define_air_fns!`; production adapters must preserve that direct
   DSL ownership.
2. **hash prover**: `poseidon2_precompile` stages the production STWO instance
   over `Poseidon2Table` around the joint channel handshake. It directly reuses
   the `define_air_fns!`-generated Poseidon2 component, retains raw query
   expansion for recursion, and publishes the aggregate shared-relation sum
   without requiring that standalone sum to be zero.
3. **rv32im prover**: drop the poseidon2 component from `components!` (or its
   successor); its `poseidon2`/`poseidon2_io` relation deficit becomes a public
   claim instead of an in-proof cancellation. `InteractionClaim` gains the
   per-shared-relation sum.
4. **binders**: extend `continuation::verify_segments` and the segment-leaf
   recursion branch with the cross-proof sum check and shared-draw replay.
5. **SDK/proof format**: a segment artifact becomes
   `(RV32IM proof, hash proof)`; recursive statement folding remains over the
   segment's `SpanStatement`.

## What it buys

- Separating Poseidon2 removes its 16-lane, 8-external-round, 14-internal-round
  permutation trace from the VM proof. Whether the second proof's fixed cost is
  a net performance win remains unmeasured.
- A dedicated hash instance can be sized independently and can overlap work with
  the VM instance once the joint-transcript synchronization is defined.
- Each additional hash precompile is the same shape: a relation, a
  `define_air_fns!` table, a prover instance, one sum check in the binder. A
  guest-visible precompile call (ecall) reduces to emitting the relation from a
  small adapter component.

## Open questions

- **Two-phase draw vs sequential mixing**: the handshake above costs one sync
  point; the simpler alternative (hash prover commits first, rv32im mixes its
  root) serializes the commitment phases. Measure before choosing — the sync is
  only needed if commitments genuinely overlap in time.
- **Lifting/log-size mismatch**: the two instances have independent trace sizes
  and PCS configs; the sum check is config-agnostic, but the recursive
  verifier's replay components must handle two distinct transcript shapes.
- **Cost crossover**: for tiny segments the fixed cost of a second proof
  (commitments, FRI) may exceed the column savings; the segment size at which
  the split wins needs the fibonacci-style benchmark treatment.
