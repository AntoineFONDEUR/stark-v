# Hash precompiles: proving Poseidon2 outside the rv32im prover (design)

> **Status:** the cross-proof binding mechanism is implemented and tested in
> `crates/prover/src/precompile.rs` — two independent stwo proofs sharing one
> LogUp relation drawn via the two-phase handshake below, whose claimed sums
> must cancel. Two instances exist side by side: the didactic "square
> precompile" (`y = x²`, `prove_binding`/`verify_binding`) and the real
> Poseidon2 binding (`prove_hash_binding`/`verify_hash_binding`) over the
> 32-word `poseidon2_io` tuple, whose precompile side is the reused stark-v
> `poseidon2` component itself proving io rows — the exact component the zkVM
> commits, in its own instance. Eleven tests cover both roundtrips and the
> soundness failures (unvalidated/unused/forged tuples, forged claimed sum).
> What remains to actually offload the zkVM is the pipeline switch: the rv32im
> prover keeps `poseidon2` rows out of its trace and emits `poseidon2_io` tuples
> instead, proven against a hash-precompile instance via this binding.

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

The codebase already has the right mechanism, and it is the one mechanism used
everywhere else: a LogUp relation. `poseidon2_io(in_0..in_15, out_0..out_15)`
(docs/recursion.md, channel-replay design) binds a permutation's ends
atomically. Inside today's single proof, the poseidon2 component's emissions
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
                                  ├── mix(root_a, root_b) ── draw (z, alphas)
  commit poseidon2 IO ◄─ root_b ──┘         │
  interaction phase ◄───────────────────────┤
  STARK proof A                             └─► interaction phase
                                                STARK proof B
```

Both provers run their (dominant) trace-commitment phase fully in parallel,
synchronize once to derive the shared relation draw from both commitment roots,
then finish independently. The verifier — host first, the 2-to-1 aggregation AIR
later — replays the same draw from the two proofs' commitments and checks
`claimed_sum_A + claimed_sum_B = 0` for the shared relation (A's own internal
relations still balance to zero on their own, as do B's).

This is the same trust split the recursion crate already uses
(`recursion::aggregate`): a node binds two child proofs by checks on their
public claims; here the bound claim is a relation sum instead of a boundary.

## What changes where

1. **air crate**: nothing — the `poseidon2` function and table stay defined by
   `define_air_fns!` exactly as today. The relation set gains nothing new
   (`poseidon2_io` is already planned for channel replay).
2. **hash prover** (new, small): a stwo instance over `Poseidon2Table` alone.
   `define_air_fns!` already generates standalone `prove_air_fns` /
   `verify_air_fns` for its tables (see `stwo-macros/tests/air_fns.rs`); this
   needs the channel-handshake variant of that path plus a public claim carrying
   the relation's claimed sum.
3. **rv32im prover**: drop the poseidon2 component from `components!` (or its
   successor); its `poseidon2`/`poseidon2_io` relation deficit becomes a public
   claim instead of an in-proof cancellation. `InteractionClaim` gains the
   per-shared-relation sum.
4. **binder**: extend `verify_segments` and (in-AIR) the aggregation node with
   the cross-proof sum check and the shared-draw replay.
5. **SDK/proof format**: a segment artifact becomes
   `(rv32im proof, hash proof)`; `Boundary` chaining is untouched.

## What it buys

- The poseidon2 component is by far the widest in the composition (16-lane state
  across 8 external + 14 internal rounds); removing it cuts the rv32im
  instance's committed column count and its max log-size pressure.
- The hash workload (memory commitment trees, and after M4 the proof-tree paths
  and channel replay) is bursty and embarrassingly parallel: a dedicated
  instance can be sized and parallelized independently — including proving while
  the rv32im instance is still committing.
- Each additional hash precompile is the same shape: a relation, a
  `define_air_fns!` table, a prover instance, one sum check in the binder. A
  guest-visible precompile call (ecall) reduces to emitting the relation from a
  small adapter component.

## Open questions

- **Two-phase draw vs sequential mixing**: the handshake above costs one sync
  point; the simpler alternative (hash prover commits first, rv32im mixes its
  root) serializes the commitment phases. Measure before choosing — the sync is
  only needed if commitments genuinely overlap in time.
- **Interaction PoW**: today one `interaction_pow` guards the relation draw;
  with two instances the PoW must cover the joint transcript (one grind over
  `mix(root_a, root_b)` shared by both).
- **Lifting/log-size mismatch**: the two instances have independent trace sizes
  and PCS configs; the sum check is config-agnostic, but the aggregation AIR's
  replay components must handle two distinct transcript shapes.
- **Cost crossover**: for tiny segments the fixed cost of a second proof
  (commitments, FRI) may exceed the column savings; the segment size at which
  the split wins needs the fibonacci-style benchmark treatment.
