# 2-to-1 Recursion Design (native stwo verifier AIR)

Goal: prove unlimited program lengths by splitting execution into fixed-size
segments (e.g. 100k or 1M steps, configurable), proving each segment, then
aggregating proofs pairwise (2-to-1) up a binary tree until a single root proof
remains.

The aggregator is **not** a RISC-V guest re-executing a Rust verifier. It is a
**native stwo AIR**: a set of stwo components whose constraints assert "these
two stark-v proofs verify, and their boundaries chain". The recursion prover
takes two stwo proofs as witness input and produces a stwo proof of their
verification.

Working in our favor: the inner and outer proofs share the same field
(M31/QM31), so no field emulation is needed anywhere — channel, FRI, and
composition arithmetic are all native.

## Single source of definition

The hard requirement: **no copy of any constraint, ever**. Editing
`define_trace_tables!` must flow through to the recursive verifier.

The mechanism is `EvalAtRow` genericity, and it is already load-bearing in stwo:

- The prover instantiates each component's
  `FrameworkEval::evaluate<E: EvalAtRow>` with a SIMD trace evaluator.
- The verifier instantiates the same function with `PointEvaluator`
  (`constraint-framework/src/point.rs`) to evaluate the composition polynomial
  at the OODS point from sampled mask values.
- `ExprEvaluator` (`constraint-framework/src/expr/`) instantiates it with
  `F = BaseExpr, EF = ExtExpr`, turning the constraint set into expression
  _data_ — including formal LogUp parameters — without any transcription.

The verifier AIR uses the same seam: its composition-check sub-circuit is driven
by the inner components' `evaluate()` — either executed at witness generation
time with `PointEvaluator`-style QM31 values, or instantiated with an evaluator
whose field type is the verifier AIR's own cell/variable type. Either way, a
macro edit changes the inner AIR and the recursive verifier in the same
compilation, with zero copies.

## What the verifier AIR must assert

Mirroring `prover::verifier::verify_rv32im` + `stwo::core::verifier::verify`,
for each of the two child proofs:

1. **Fiat-Shamir channel replay** (Blake2s): mix public data, commitments,
   claims; draw `Relations`, OODS point, FRI alphas, query positions. Requires a
   Blake2s hash component (stwo has a Blake AIR example as reference).
2. **Proof of work** checks (interaction PoW + FRI PoW).
3. **LogUp sum check**: total claimed sum + public data logup sum = 0. The
   public-data logup terms reuse the same `Relations::combine` code.
4. **Composition check at OODS**: recompute the composition polynomial value
   from the sampled mask values via the inner components' `evaluate()` — the
   single-source seam described above.
5. **Merkle decommitments** (Blake2s) of the queried positions against the
   commitments for every trace tree.
6. **FRI verification**: fold query evaluations through all FRI layers and check
   consistency with the last-layer polynomial.
7. **Boundary chaining** (aggregation logic): `child_0.exit == child_1.entry` on
   `(pc, clock, memory/register state)` public data, and exposure of
   `(child_0.entry, child_1.exit)` as the aggregate's public data.

The output proof must be verifiable by the same verifier AIR (fixed-point proof
shape), so aggregation composes up the tree.

## Milestones

- **M1 — constraints as data (seam validation)**: expose the full stark-v
  constraint system programmatically through `ExprEvaluator`/`PointEvaluator`
  from the existing components; test that composition replay from a real proof's
  sampled values matches the verifier. This validates the no-copy seam the
  verifier AIR builds on.
- **M2 — segmentation**: runner support for stopping at N steps with entry/exit
  boundary public data; prove/verify a 2-segment run on the host (no recursion
  yet). Boundary soundness comes from the existing `registers_state` /
  `memory_access` relations plus Merkle-root chaining:
  `final_rw_root(k) == initial_rw_root(k + 1)`. Chaining works because the
  partial Merkle trees use zero-valued default leaves, so an address first
  written in segment `k + 1` (present in its initial tree as 0) hashes
  identically to its absence from segment `k`'s final tree. IO special-casing is
  gated by `runner::SegmentRole`: inputs are LogUp-anchored in the first segment
  only, public outputs consumed in the last only; middle segments treat the IO
  regions as ordinary RW memory. Constraint: a guest taking input must access
  every input word within the first segment (unconsumed input emissions make
  segment 1's LogUp sum non-zero — verification fails safe, but the run is
  unprovable).
- **M3 — QM31 arithmetic components** (started): verifier-AIR building blocks
  for QM31 mul/inverse, point operations, and FRI folding steps. Lives in
  `crates/recursion`, built on `define_component_tables!` (the trace-table DSL
  without the zkVM `Tracer`), so recursion constraints share the single-source
  pipeline. First component: `qm31_mul` (c = a·b over the extension tower, 4
  degree-2 limb constraints, tested against stwo's field arithmetic).
- **M4 — channel + Merkle components**: hash sub-AIR and decommitment paths;
  channel state replay as a trace. Direction: a Poseidon2-M31 `MerkleChannel` so
  inner proofs commit with the hash the existing `poseidon2`/`merkle` components
  already prove — in-AIR Merkle verification becomes component reuse with zero
  new hash constraints. Crucially this needs **no fork changes**: `Channel`,
  `MerkleChannel`, `MerkleHasherLifted`, `MerkleOps`, and
  `BackendForChannel<MC>` are public stwo traits, and the orphan rules permit
  implementing them all for stark-v-local types
  (`impl BackendForChannel<LocalChannel> for SimdBackend` is a legal
  local-type-parameter impl). The permutation already exists in
  `runner::poseidon2`.
- **M5 — composition-check component**: wire the inner `evaluate()` into the
  verifier AIR (witness side via `PointEvaluator` values; constraint side via
  the generic seam).
- **M6 — full verifier AIR + 2-to-1 aggregation**: assemble 1–7, fixed-point
  proof shape, SDK wiring for the aggregation tree.

## M4 remaining: proof-tree Merkle paths (integration design)

The existing `merkle` + `poseidon2` components prove the memory-commitment
trees, whose node values are single M31 words. Proof commitment trees use 8-word
digests (`Poseidon2M31Hash`), so:

1. The 16-wide `poseidon2` relation already covers both digest widths: `combine`
   zero-pads short tuples, so the memory trees' `(l, r)` inputs and the proof
   trees' `(l_0..l_7, r_0..r_7)` inputs share the relation, as do the `(out_0)`
   and `(out_0..out_7)` outputs. No new relation.
2. Add a `wide` flag column to the `poseidon2` component: emit `(out_0)` with
   multiplicity `(1 - wide) * enabler` and `(out_0..out_7)` with
   `wide * enabler` (degree-2 numerators keep the same batch degree as the
   existing pairs). One edit to the one existing component — no copy.
3. A recursion `merkle_path` table walks a decommitment path: each row emits
   `(left || right)` (16 words) and consumes `(parent_0..parent_7)` through the
   poseidon2 relation, chains parent into the next row's child slot, and exposes
   the root for binding against the channel-replayed commitment.
4. `prove_recursion` draws the stark-v `Relations` (the recursion crate gains a
   real `prover` dependency; no cycle) and instantiates the reused `poseidon2`
   component with a second table fed from the proofs' decommitment paths.

## Channel replay (design) and a soundness observation

The Poseidon2-M31 channel is a sponge: every mix/draw is a chain of permutations
where the full 16-word state carries between chunks. Replaying it in-AIR
therefore needs each replay row bound to a permutation's **input and output
atomically**. The current poseidon2 relation emits inputs and outputs as
separate tuples, and LogUp multiset equality alone does not pair them: with two
permutation rows, a malicious witness could consume the inputs and outputs in
swapped combination.

- **Soundness review item (pre-existing pattern):** the memory-tree `merkle`
  component uses the same split shape — emit `(l, r)`, consume `(out)` as
  independent poseidon2-relation entries. Whether output-swapping is exploitable
  there depends on the surrounding tree chaining; it deserves a dedicated
  review.
- **Channel-replay design:** add a `poseidon2_io: in_0..in_15, out_0..out_15`
  relation (32 elements) to the `relations!` set, emitted by the poseidon2
  component under a third flag (`io`), binding each permutation's ends
  atomically. Replay rows then: consume `(prev_state, prev_out)` pairs along a
  `sponge_step(channel_id, step, state16)` chain (mirroring `merkle_node`), add
  the absorbed chunk into the rate in-row (degree-1 arithmetic), and anchor the
  final digest against the channel claim. Mixed-data binding (what gets
  absorbed: commitments, claims) comes from the recursion proof's public claim,
  exactly like `RootClaim`.

## The single final proof (`recursion::final_proof`)

A segmented execution of any length is proven as ONE artifact:

```text
prove_segments_with_channel::<Poseidon2M31MerkleChannel>  (one proof per segment)
        |
prove_final ──────────────► FinalProof {
   per segment:                recursion_proof   (ONE stwo proof)
   - composition circuit       segments          (public bodies,
     (CompositionRecorder       NO decommitments anywhere)
      → lower_arena)         }
   - every Merkle opening
     (openings::replay_pcs_openings
      → merkle_path rows + poseidon2 rows)
```

`verify_final` is the only verification step. Its work splits in two:

- **Public-data recomputation** (deterministic, no trust): replay each segment's
  Fiat-Shamir transcript natively (the bodies are the final proof's public input
  — hashing them is the cost of reading the proof), re-record the canonical
  composition circuits from the same `evaluate()`, recompute DEEP quotients
  (`stwo`'s `fri_answers`), the FRI fold chain, last-layer evaluations, proofs
  of work, LogUp sums, and the boundary chain across segments.
- **ONE stwo verification** of the recursion proof, which attests the two things
  public data cannot: that the composition circuits evaluate to the claimed OODS
  values (every inner constraint, through the single-source seam), and that the
  queried values open against the committed roots — the decommitment paths are
  witness to the recursion proof and absent from the artifact. Leaf digests
  anchor as public `LeafClaim`s (recomputed by the verifier from queried
  values), roots as `RootClaim`s (equal to the in-transcript commitments), one
  path per opened position per tree — trace trees and every FRI layer tree.

Shared upper path rows of converging queries are simply pushed once per path:
each duplicated row consumes its own node claim and re-emits its child's, so the
multiset telescopes with `RootClaim.n_paths` at the top.

Validated end to end by `tests/final_proof.rs`: a 2-segment roundtrip with
tamper vectors (forged queried value, forged root claim, broken boundary), and
`test_final_proof_of_10m_cycle_run` — the 10.8M-cycle `long_run` guest, 11
segments, proven as one final proof in ~220s (release, `parallel`).

### Remaining deepening (succinctness, not soundness)

The trust structure above is complete; what remains shrinks the public remainder
so `verify_final` approaches statement-size work:

1. Record the FRI quotient/fold formulas as Rec circuits (protocol arithmetic,
   not constraint copy) so queried values can become witness.
2. Replay the inner transcripts through the in-AIR channel (machinery exists and
   is validated against the real channel) with absorbed chunks as witness, drawn
   values and query-index bits bound by wires.
3. Circuit structure as preprocessed columns (removes the per-proof re-record),
   then true 2-to-1 node compression (a recursion proof attesting two child
   recursion proofs) for unbounded depth at constant artifact size.

The preprocessed-columns half of item 3 is sequenced AFTER item 2 for a
soundness reason, not a preference: the recorded circuit's `Const` nodes carry
per-proof values — the inner relations' drawn `z`/`alphas` and each component's
`cumsum_shift` — and the canonical re-record is precisely what pins those values
to the child's Fiat-Shamir transcript (the recorder re-derives them from the
replay before recomputing the arena). Moving the structure to preprocessed
columns and dropping the re-record would leave the relation randomness claimed
but unchecked; only the draws-binding of item 2 (drawn values bound to circuit
wires through the in-AIR channel) can replace that check. Until then the
re-record stays: it costs O(one fixed circuit) per immediate child of the root —
constant in tree depth and in leaf program size.

Item 3 is the end state: a binary tree whose leaves are segment proofs, whose
every internal node is one constant-size recursion proof attesting that its two
children verify and chain, and whose root is the single artifact for the whole
execution — not a concatenation of per-segment bodies as `FinalProof` carries
today. `FinalProof { recursion_proof, segments }` is the bridge: it already
collapses verification to one stwo check, but its public remainder grows
linearly with segment count; node compression caps the artifact at one node
regardless of depth.

The node is **implemented** in `recursion::node`:

- `replay_recursion_composition` replays a recursion proof's own Fiat-Shamir
  transcript and records its composition check through the recursion components'
  `evaluate()` — the recursion-level analogue of the M1 seam
  (`test_recursion_composition_replay_matches_claim`).
- `prove_node_compressed_n` / `verify_node_compressed` take Poseidon2-M31 child
  recursion proofs, record each child's composition (lowered into the parent
  trace) **and replay its Merkle/FRI openings** (recorded as `merkle_path` rows
  anchored by public root/leaf claims), and prove one parent recursion proof
  attesting them all. The children's decommitments are stripped from the
  artifact — the parent carries them as component rows, exactly as `FinalProof`
  does for inner proofs (`test_compressed_node_attests_children_openings`).
- Every `RecursionProof` carries a public **boundary claim** (entry/exit pc,
  register file, memory and program roots), mixed into its transcript like the
  root/leaf/circuit claims. `prove_base_node` chains the segment boundaries into
  the leaf's claim; each node chains its children's claims into its own;
  `verify_node_compressed` recomputes the chain from the children's
  transcript-bound claims, rejects a mismatched root claim, and returns the
  verified span (`test_compressed_node_folds_child_boundaries`, swap/forge/
  cross-run tamper tests). The root therefore publicly states _which_ execution
  it proves, not just that some valid proofs were folded.

The full driver is **implemented**: `prove_tree_compressed` folds any leaf set
`arity`-to-1 to a single root (a lone trailing proof rides up a level; a
single-leaf tree wraps into a 1-child root), and
`aggregate_tree::prove_guest_recursive[_by_capacity]` runs the whole pipeline —
guest → capacity-bounded segments → base-node leaves → tree — with the root
boundary asserted against an independent unsegmented reference run
(`test_guest_recursive_arity_2_root_spans_the_run`). The root's trace shape is
depth-invariant (`test_compressed_tree_root_shape_is_depth_invariant`).

## Production topology (streaming)

The host-side helpers (`prover::e2e::prove_segments`, batch `prove_final`) are
test infrastructure. The production deployment is a pipeline, not a batch:

```text
runner (own cadence) ──► segment queue ──► leaf prover pool (N workers)
                                                 │  one leaf proof per segment
                                                 ▼
                                          leaf-proof queue ──► 2-to-1 prover pool
                                                                     │  any same-level
                                                                     │  adjacent pair
                                                                     ▼
                                                               node-proof queue
                                                                     │ (loops back)
                                                                     ▼
                                                                root proof
```

- The runner executes at its own frequency and dumps each segment the moment it
  is full; it never waits for provers. Backpressure lands in the segment queue
  (segments are serializable run results), not in execution.
- Leaf provers are stateless workers: any idle one picks the next segment and
  produces a leaf proof. Per the fibonacci benchmark (README "Parallelization
  Strategy"), workers run single-threaded stwo — process-level parallelism beats
  intra-proof rayon for aggregate throughput.
- 2-to-1 provers consume any two level-adjacent proofs as soon as both exist, so
  the tree builds bottom-up while execution and leaf proving are still running.
  Total latency ≈ run time + one leaf prove + log2(segments) node proves.
- Pairing and chaining rules are exactly `recursion::aggregate`'s; the topology
  needs no protocol work beyond node compression (item 3 above).

## Notes

- stwo's `examples/` contain Blake and Poseidon AIRs to draw on for M4; a
  Poseidon-based channel variant may be cheaper inside the AIR than Blake2s and
  is worth evaluating early (it changes the channel of the _inner_ proofs, a
  config choice, not a constraint copy).
- The remaining single-source gap inside stark-v itself: LogUp relation entries
  are written in both `air.rs` (`add_to_relation!`) and `witness.rs`
  (`combine!`/`write_pair!`). Extending `define_trace_tables!` with a
  `relations:` block closes it; the verifier AIR is unaffected either way since
  it consumes `evaluate()`.
- The recursion crate still declares its components through
  `define_component_tables!` (constraints single-sourced, lookups hand-paired in
  witness modules) while the zkVM tables moved to `define_air!` (lookups in the
  schema). The port target is not `define_air!` though — it is the felt function
  DSL (docs/felt-air-compiler.md, step 4): the QM31 arithmetic components
  (`qm31_mul`, `qm31_inv`, `fri_fold`, `circle_double`) are pure felt functions
  and the circuit `op_def`/`wire` relations are literally its calling
  convention, so they should migrate first, as the proving ground for the opcode
  migration.
