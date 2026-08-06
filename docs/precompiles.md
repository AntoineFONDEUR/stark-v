# Hash precompiles: proving Poseidon2 outside the RV32IM prover

> **Status: production split implemented; hardening and measurement remain.**
> The VM component router detaches the DSL-owned Poseidon2 table. One
> `SegmentProof` carries the VM proof, standalone Poseidon2 proof, and joint
> interaction nonce. Host verification, continuation, and the recursive segment
> leaf replay both constituent transcripts and require exact cancellation of
> their shared `poseidon2_io` relation sum. The active profile has produced and
> verified one real split-proof recursive root. PRE-001 still requires
> adversarial tuple-pairing tests, binary and padded-root conformance for the
> changed profile, and comparative performance measurements.

The implemented split takes the Poseidon2 table out of the RV32IM STWO instance
and proves it in its own instance, binding the two proofs through their shared
LogUp relation. The VM constituent emits `(input, output)` permutation tuples;
the hash constituent consumes them and attests they are real permutations. The
current prover stages the two ordered commitments around one joint transcript
handshake. Scheduling independent work concurrently remains a measured
optimization, not a soundness requirement. Further hash functions can follow the
same relation-bound segment-artifact pattern.

## Why LogUp binding, not preprocessing

The tempting framing — "prove the poseidon2 table first and hand the
`(input, output)` pairs to the rv32im prove as a preprocessed trace" — does not
fit what preprocessing means here: preprocessed columns are
execution-independent, committed once, cached on disk, and known to the verifier
(`prover::preprocess`). Hash IO pairs change with every execution, so they would
be a fresh per-proof committed tree, not preprocessing — and the verifier would
still need a reason to believe the pairs are valid permutations.

The `poseidon2_io(in_0..in_15, out_0..out_15)` relation binds a permutation's
ends atomically. The VM constituent publishes the deficit left by its Merkle and
sponge consumers, while the standalone Poseidon2 constituent publishes the
matching emission sum. The segment verifier requires the two public sums to
cancel exactly instead of requiring either constituent to close alone.

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

The ordered roots and joint nonce are absorbed into both constituent proof
transcripts before the shared relation challenges are drawn. The host verifier,
continuation verifier, and recursive leaf all replay the same PoW and draw from
both proofs' commitments and check `claimed_sum_A + claimed_sum_B = 0` for the
shared relation. Each constituent's other relations still close within that
constituent.

The recursive verifier treats the VM proof and precompile proof as one leaf
artifact: it verifies both proof transcripts and binds their shared relation sum
before deriving the segment statement.

## Implemented boundaries

1. **AIR definitions**: the `poseidon2` function and table remain in
   `define_air_fns!`; `poseidon2_io` already exists in the VM relation schema.
   The prototype's square emit, square consume, and 32-word host binding tables
   also use `define_air_fns!`. The structural guard permits Poseidon2 only as a
   detached DSL-owned component and rejects handwritten AIR compatibility code.
2. **hash prover**: `poseidon2_precompile` stages the production STWO instance
   over `Poseidon2Table` around the joint channel handshake. It directly reuses
   the `define_air_fns!`-generated Poseidon2 component, retains raw query
   expansion for recursion, and publishes the aggregate shared-relation sum
   without requiring that standalone sum to be zero.
3. **RV32IM prover**: the component router marks Poseidon2 as detached, and the
   VM `InteractionClaim` exposes the shared-relation deficit instead of closing
   it inside the VM constituent.
4. **binders**: `verify_rv32im_with_channel`, `continuation::verify_segments`,
   and the segment-leaf recursion branch replay the joint draw, verify both
   proofs, and require exact sum cancellation.
5. **SDK/proof format**: `SegmentProof` contains the VM proof, Poseidon2 proof,
   and joint interaction nonce; recursive statement folding remains over the
   segment's `SpanStatement`.

## What it buys

- Separating Poseidon2 removes its 16-lane, 8-external-round, 14-internal-round
  permutation trace from the VM proof. Whether the second proof's fixed cost is
  a net performance win remains unmeasured.
- A dedicated hash instance can be sized independently. Safe outer scheduling
  can overlap independent work only where measurements justify the extra memory.
- Each additional hash precompile is the same shape: a relation, a
  `define_air_fns!` table, a prover instance, one sum check in the binder. A
  guest-visible precompile call (ecall) reduces to emitting the relation from a
  small adapter component.

## Remaining work

- **Adversarial pairing**: forged, missing, extra, and reordered permutation
  tuples must fail through both continuation and recursive-root verification.
- **Current-profile conformance**: rerun binary and padded-root constructions
  after the manifest change; the real one-segment split-proof root already
  passes.
- **Cost crossover**: for tiny segments the fixed cost of a second proof
  (commitments, FRI) may exceed the column savings. Measure representative
  segment sizes before selecting an outer scheduling policy or claiming a
  performance win.
