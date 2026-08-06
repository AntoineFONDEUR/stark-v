# Project execution ledger

This file is the canonical entry point for all unfinished project work. It is
both the dependency-ordered implementation plan and the progress ledger. Design
documents explain the target in more depth, but they do not own task status or
execution order.

## How to execute this ledger

Status values have one meaning:

- `[done]`: implementation, focused tests, relevant end-to-end tests,
  documentation, repository hooks, commit, and push are complete;
- `[active]`: the only task currently being implemented;
- `[pending]`: a dependency is unfinished or work has not started;
- `[blocked]`: work cannot continue without an explicitly recorded external
  dependency or user decision.

There must be at most one `[active]` task. Work proceeds by task ID in the order
below unless a task explicitly lists a different dependency. An agent taking
over the repository must:

1. read this file and the design documents referenced by the active task;
2. verify the worktree and current source state rather than trusting prose;
3. finish the active task without starting a later task;
4. run focused release-mode tests before broader release-mode tests;
5. update the task status and evidence in this file;
6. run `prek run --all-files`, commit, and push the milestone;
7. mark the next dependency-satisfied task `[active]` in the same handoff.

A task is not done merely because its happy-path test passes. Every new binding
requires focused malformed-witness or statement-mutation coverage. Commands in
the evidence log are commands that were actually run; future work must append
its real commands and results rather than predicted output.

Recursive proof E2Es are memory-bound. Run exactly one heavy proof process at a
time and keep full recursion suites at `--test-threads=1`; the REC-008
two-worker driver measured up to 36.01 GB maximum RSS in one process. Do not use
process-level test parallelism for these gates until a checked-in lower-memory
measurement replaces this limit.

Scope recursive proof tests by the boundary being changed. Fast statement,
planner, wire, profile, and malformed-witness tests cover every supported count
and boundary first. Real proof E2Es cover the three distinct root constructions:
one segment for a segment-leaf root, two segments for a binary root, and three
segments for a padded binary tree. Repeat the 4- and 8-segment E2Es only when
tree reduction, padding, or protocol geometry changes; fixed root encoding and
profile-owned verifier scheduling do not gain coverage from repeating the same
binary shape at larger counts.

## Non-negotiable architecture gates

- Host continuation and recursive proving remain separate crates and APIs.
- `recursion` has no version-suffixed module tree or compatibility layer.
- Every AIR component reachable from a recursive proof uses `define_air!` or
  `define_air_fns!`, including shared and precompile components.
- No active recursion dependency contains a handwritten `FrameworkEval` or a
  standalone `define_component_tables!` declaration.
- Columns, constraints, witness filling, relation registration, interaction
  traces, component claims, and composition evaluation derive from the same
  macro definition.
- Protocol configuration is trusted and manifest-bound. Proof bytes never choose
  verifier phases, operation counts, table shapes, or FRI shapes.
- Public verification accepts the expected statement and protocol and compares
  both before returning success.
- No document claims recursion, constant proof size, a precompile, syscall
  support, or a performance result before a release-mode end-to-end test or
  checked-in measurement establishes it.

## Documentation map

| Document                    | Class                          | Authority                                                                   |
| --------------------------- | ------------------------------ | --------------------------------------------------------------------------- |
| `docs/roadmap.md`           | Current execution ledger       | Task order, task status, completion gates, and evidence                     |
| `README.md`                 | Current state                  | Supported user-facing behavior and measured commands                        |
| `docs/airs.md`              | Current state                  | Active AIR architecture; source remains authoritative for exact constraints |
| `docs/recursion.md`         | Current design                 | Recursive statements, verifier architecture, and soundness invariants       |
| `docs/felt-air-compiler.md` | Partially implemented design   | Compiler facilities and opcode/runner target                                |
| `docs/precompiles.md`       | Planned feature with prototype | Cross-proof hash binding target                                             |
| `docs/syscalls.md`          | Planned feature                | Syscall and output-journal target                                           |
| `CONTRIBUTING.md`           | Current process                | Development and submission workflow                                         |
| `SECURITY.md`               | Current policy                 | Security scope and private reporting                                        |

A planned document is not stale merely because its feature is absent. It is
wrong if it presents the target as implemented, references an API that no longer
exists, or contradicts a current invariant. Historical audits and superseded
implementation notes belong in version control, not in the active documentation
set.

## Current checkpoint

- `[done] BASE-001` Establish the cleanup baseline.
  - Host continuation lives in `crates/continuation` and returns one proof per
    segment.
  - `crates/recursion` exposes the active universal verifier design at the crate
    root; abandoned aggregation wrappers are absent.
  - Current and planned documentation are explicitly distinguished.
  - Evidence: commit `54d55fc8`; focused recursion and continuation tests, the
    full release workspace suite, and repository hooks passed.

- `[done] AIR-001` Migrate shared recursion primitives to the macro DSL.
  - `qm31_mul`, `qm31_inv`, `linear_ops`, and `merkle_path` own their tables,
    constraints, relations, evaluators, and interaction traces through
    `define_air_fns!`.
  - The macro supports host-selected relation bundles, row-activity gating,
    pair-batched LogUp columns, and optional dynamic component evaluation.
  - Handwritten recursion evaluators decreased from 34 to 30.
  - Evidence: commit `ae5f8cc8`; focused negative tests, the macro suite, the
    recursion library suite, and repository hooks passed.
- `[done] AIR-002` Migrate trusted recursion control components.
  - `control`, `vm_public_logup_control`, and `vm_air_composition_control`
    derive their preprocessed IDs, evaluators, relation entries, and interaction
    witnesses from `define_air_fns!`.
  - Trusted schedule columns remain verifier preprocessing; proof-kind selectors
    remain verifier-owned constants rather than witness columns.
  - Handwritten recursion evaluators decreased from 30 to 27.
  - Evidence: commit `ad656d26`; focused control tests, the macro suite, the
    recursion library suite, and repository hooks passed.
- `[done] AIR-003` Migrate recursion transcript components.
  - Transcript hashing, call binding, frame state, typed words, semantic
    payloads, PoW checks and frames, relation challenges, and verifier
    randomness derive their tables, evaluators, and interactions from
    `define_air_fns!`.
  - Mixed components keep trusted schedules in preprocessing, verifier-owned
    selectors as fixed parameters, and proof values in committed columns.
  - Handwritten recursion evaluators decreased from 27 to 18.
  - Evidence: commit `9ca4fd1d`; independent changed, missing, duplicated, and
    reordered payload tests, the macro suite, the recursion library suite, and
    repository hooks passed.
- `[done] AIR-004` Migrate statement and VM-public-input adapters.
  - Statement words, statement-semantic inputs, canonical VM claim words, claim
    and public-IO hashes, claim-semantic inputs, public-LogUp inputs, and
    VM-composition inputs derive their tables, evaluators, and interactions from
    `define_air_fns!`.
  - Trusted schedules remain preprocessing; proof-kind selectors and protocol
    tags remain verifier-owned fixed parameters; committed columns contain only
    proof-dependent values.
  - Handwritten recursion evaluators decreased from 18 to 10.
  - Evidence: commit `16ac9d55`; malformed wire, statement substitution,
    inactive-input, hash-domain, sponge-state, lane-swap, circuit-ownership,
    macro, and full recursion tests passed; repository hooks passed.
- `[done] AIR-005` Migrate recursion PCS and FRI components.
  - Query decomposition and mapping, Merkle roots and openings, PCS DEEP inputs,
    FRI subtree authentication, FRI control, and FRI circuit inputs now derive
    their tables, evaluators, and interactions from direct `define_air_fns!`
    definitions.
  - Trusted preprocessing fixes proof-shape geometry, verifier lanes, query
    routes, and FRI endpoint masks; committed columns contain only
    proof-dependent values.
  - Handwritten recursion evaluators decreased from 10 to zero.
  - Evidence: commit `6bfdb9d7`; focused query, root, opening, FRI-width, route,
    and final-value tests, the macro suite, the full recursion suite, structural
    inventories, and repository hooks passed.
- `[done] AIR-006` Enforce zero handwritten recursion AIRs.
  - A checked-in structural guard pins all 36 universal components and all 27
    inner VM components to 32 AIR owner files.
  - Every owner directly invokes `define_air!` or `define_air_fns!`; the guard
    rejects handwritten evaluators, standalone component-table declarations,
    wrapper macros, unexpected item macros, roster drift, and unapproved VM
    component routing.
  - Current-state AIR, recursion, and felt-compiler documentation reflects the
    completed migration while planned syscall and precompile documents remain
    explicitly future goals.
  - Evidence: commit `59ef6b42`; the structural guard, complete recursion suite,
    full release workspace suite, structural searches, and repository hooks
    passed.
- `[done] PRO-001` Freeze the first recursive protocol profile.
  - The generated VM and universal rosters derive both fixed proof geometries,
    verifier plans, preprocessing registries, exact wire types, and the protocol
    identifier from one profile constructor.
  - The profile fixes 193 FRI queries, 4 KiB public-input and public-output
    capacities, and a 3,459,396-byte universal proof wire.
  - Evidence: commit `b0a3f2ae`; focused profile, manifest mutation, macro,
    recursion, full release workspace, and repository hook suites passed.
- `[done] REC-001` Adapt a real VM proof to the recursive leaf wire.
  - The recursion-targeted fixed-layout Poseidon prover uses the manifest-bound
    verifier transcript and retains STWO's authenticated expansion maps long
    enough to materialize all 193 independent raw-query slots. The ordinary
    prover keeps its native transcript and compact in-memory behavior.
  - The adapter checks the frozen geometry, canonical public claim, runner
    boundary, job identity, segment slot, cycle interval, and every trace and
    FRI opening before producing the fixed leaf input.
  - Evidence: commit `93dc88b3`; focused real-proof, malformed metadata, fixed
    wire, fixed trace, macro, clippy, full recursion, full release workspace,
    and repository hook suites passed.
- `[done] REC-002` Build the universal trace assembler.
  - Recursion-targeted VM proofs use the trusted manifest transcript while the
    ordinary prover retains its native public transcript and compact proof
    auxiliary state.
  - `UniversalWitness` deterministically fills preprocessing, original, and
    interaction trees for all 36 components, derives all claimed sums and
    verifier-owned public terms, and validates every emitted column against the
    frozen program registry.
  - STWO-omitted FRI query values are reconstructed from the DEEP answer and
    prior folds before both Merkle and folding checks; PCS periodicity uses the
    committed-domain log sizes.
  - The active profile has 22 recursion FRI layers, a 3,459,396-byte fixed proof
    wire, and protocol identifier limbs
    `[996130352, 439599105, 1840972074, 322360417, 2002034527, 739270897, 775019197, 1167228932]`.
  - Evidence: commit `827ec9a9`; deterministic real-proof assembly, all 36
    direct component checks, focused malformed-FRI tests, the ordinary prover
    integration, the full recursion and workspace release suites, clippy, DSL
    guards, and repository hooks passed.
- `[done] REC-003` Close the segment-leaf branch end to end.
  - Real VM proofs now replay through every verifier circuit, reject nonzero
    circuit outputs, and require exact global relation closure.
  - Verifier-owned terminal control terms, active-lane wire multiplicities, and
    both PCS and FRI query-bit consumers close the complete relation roster.
  - Thirteen independent mutations cover the statement, public claim, every
    proof region, and both proof-of-work values; removing terminal control terms
    also makes an otherwise valid witness fail closure.
  - Evidence: commit `058023c6`; focused circuit-closure and mutation tests, the
    630-test recursion suite, all 5 DSL guards, the full release workspace
    suite, release clippy for the recursion crate, and repository hooks passed.
- `[done] REC-004` Close the canonical empty-leaf branch.
  - One proof-free entry point accepts only a checked height-zero empty
    statement and routes it through the same 36-component universal assembler.
  - Empty witnesses lower only the existing statement-semantics DSL circuit;
    every verifier, transcript, claim, query, Merkle, PCS, and FRI lane is
    materialized through its existing inactive-zero path.
  - Executed statements, folded empty spans, interior empties, out-of-capacity
    slots, and nonzero inactive component wires are rejected.
  - Evidence: commit `4374b123`; focused empty-branch and segment-regression
    tests, the 635-test recursion suite, all 5 DSL guards, the full release
    workspace suite, release clippy for the recursion crate, and repository
    hooks passed.
- `[done] REC-005` Implement the outer recursion prover and verifier.
  - Segment and empty witnesses now produce one native STWO proof over the
    complete 36-component universal roster and one fixed preprocessing
    commitment.
  - Verification binds the expected protocol, expected statement, proof kind,
    component geometry, claimed sums, public relation sum, PCS parameters,
    interaction proof of work, and every proof commitment and opening.
  - The existing `define_air_fns!` DSL supports selectively unbatched LogUp tail
    entries, keeping the two quadratic FRI endpoint relations inside the
    declared cubic constraint domain without any standalone compatibility macro
    or handwritten evaluator.
  - Evidence: commit `396f6ade`; focused outer-proof, FRI-degree, native-STWO,
    profile, macro, mutation, DSL-guard, and release-clippy tests, the 640-test
    recursion suite, the full release workspace suite, and repository hooks
    passed.
- `[done] REC-006` Verify a real recursion proof as a child.
  - Native recursion proofs retain STWO's authenticated expansion data and
    encode into the fixed child wire with independent raw-query values, trace
    paths, FRI cosets, commitments, claimed sums, and final polynomial data.
  - Each child replays the trusted recursion transcript and closes its public
    LogUp sum, AIR composition, PCS DEEP quotient, Merkle openings, FRI folds,
    proofs of work, and final polynomial inside the universal witness.
  - Binary mode activates two verifier-owned child lanes through the existing
    `define_air_fns!` components; no handwritten AIR, component-table macro, or
    wrapper macro was added.
  - Evidence: commit `9f849f7d`; five independent child-proof mutations were
    rejected, two real recursion children produced and verified one parent
    proof, profile/control/empty regressions and all direct-DSL guards passed,
    release clippy and compilation passed, and repository hooks passed.
- `[done] REC-007` Prove the two-child binary branch.
  - Binary witnesses materialize independent left and right recursion-verifier
    lanes under distinct verifier and circuit identifiers, then route both
    through the same universal DSL-owned component roster.
  - The unique statement fold enforces common jobs, equal heights, aligned
    adjacency, execution and cycle continuity, machine-state equality, and
    edge-claim placement before parent proving.
  - Evidence: commits `9f849f7d` and `b6f6c9be`; two valid child proofs produced
    and verified one parent, all five required invalid pair classes failed at
    the fold boundary, the statement model and AIR substitution matrices passed,
    all direct-DSL guards passed, release compilation and clippy passed, and
    repository hooks passed.
- `[done] REC-008` Build the recursive tree driver.
  - Finalized VM segments are proved as ordered recursion leaves, padded to the
    unique minimal power-of-two capacity, and reduced through adjacent binary
    levels to one retained root statement and proof.
  - Same-level proof work shares immutable fixed preprocessing while every
    worker owns its recorder-backed witness state. The `parallel` feature caps
    tree proof waves at two workers to preserve measured host memory headroom.
  - Evidence: commit `c212200d`; release E2Es produced and verified roots for 1,
    2, 3, 4, and 8 executed segments, the full recursion and direct-DSL suites
    passed, release checks and clippy passed, and repository hooks passed.
- `[done] REC-009` Expose and bind the application root API.
  - `root::verify_recursive_root` accepts one segmentation-free
    `CompleteExecutionStatement` and one recursion proof, requires canonical
    root geometry, compares every application-owned field, and then runs the
    manifest-bound recursion verifier.
  - Host continuation remains isolated in `continuation`; no multi-proof API was
    added to `recursion`.
  - Evidence: commit `8c36c61e`; all 7 independent expected-field mutations were
    rejected, one real segment root passed the application verifier, the full
    recursion and direct-DSL suites passed, release checks and clippy passed,
    and repository hooks passed.
- `[done] REC-010` Demonstrate constant root-proof size.
  - Every successfully produced canonical root encodes as the profile-owned
    3,459,396-byte `RootProofBytes` type and uses the same 4,937-step verifier
    plan with one checked digest.
  - Real release roots cover the segment-leaf, binary, and padded-binary root
    constructions. REC-008 separately establishes valid 4- and 8-segment roots;
    their root wire and verifier plan are the same profile-owned types.
  - Evidence: real 1-, 2-, and 3-segment roots encoded and verified, fixed wire
    and verifier-shape vectors passed, and outer-only proof parallelism was
    measured and rejected as slower than the retained shared-pool strategy.
- `[active] PRE-001` Prepare the hash-precompile proof split for production.
  - Completed slice: prototype square emit, square consume, and Poseidon host
    binding components derive their tables, constraints, evaluators, and
    interaction traces directly from `define_air_fns!`.
  - Completed slice: both prototype main commitments feed one ordered joint
    interaction PoW; relation challenges are drawn afterward and the same joint
    prefix is bound into both proof transcripts.
  - Completed slice: `poseidon2_precompile` commits a fixed DSL-generated hash
    trace before the joint draw, produces a standalone STARK carrying its
    nonzero shared-relation sum and exact trace shapes, retains recursion query
    expansion, and verifies under both Blake2s and Poseidon2-M31 channels.
  - Focused release evidence: all 5 standalone round-trip, recursion-channel,
    nonzero-sum, forged-sum, and fixed-capacity tests passed; all 13 binding
    prototype regressions passed; prover clippy passed with warnings denied.
  - Next slice: remove Poseidon2 from the VM proof roster and expose the VM
    proof's matching shared-relation deficit.
- `[pending] SYS-001` Implement proof-bound syscalls and output journal.
- `[pending] FELT-001` Complete witness-side felt-function VM access.
- `[pending] FELT-002` Migrate opcode execution and retire duplicate semantics.
- `[pending] REL-001` Harden and measure the completed system.

## Macro-only recursion migration

The live universal roster contains 36 components. Every recursion-owned
component now uses `define_air!` or `define_air_fns!`; `poseidon2` and
`range_check_8_8` use the same accepted DSL in their owning crates. `AIR-006`
pins the complete reachable AIR graph and structurally enforces this invariant.

### `[done] AIR-001` Shared primitives

Dependencies: `BASE-001`.

Scope: `qm31_mul`, `qm31_inv`, `linear_ops`, and `merkle_path`.

Required work:

1. Express every column, constraint, relation entry, witness row, interaction
   trace, and component claim through `define_air!` or `define_air_fns!`.
2. Preserve circuit identifiers, wire multiplicities, Merkle direction and leaf
   semantics, and all-zero padding behavior.
3. Extend the macro implementation and its tests when the accepted DSL cannot
   express a required feature. Do not retain a manual fallback.
4. Remove the corresponding handwritten `FrameworkEval` implementation and
   standalone `define_component_tables!` declaration only after equivalence
   tests pass.

Done when:

- all four components are generated from an accepted macro;
- existing component and circuit-lowering tests pass in release mode;
- one focused negative test per component rejects an invalid result or binding;
- the structural manual-evaluator inventory decreases from 34 to 30;
- repository hooks pass and the milestone is committed and pushed.

### `[done] AIR-002` Trusted controls

Dependencies: `AIR-001`.

Scope: `control`, `vm_public_logup_control`, and `vm_air_composition_control`.

Required work:

1. Generate the trusted verifier schedule tables from the same macro source as
   their witnesses and relation entries.
2. Keep proof-supplied values unable to shorten, reorder, or replace the trusted
   schedule.
3. Preserve proof-kind gating and constrained inactive rows.

Done when all three components are macro-generated, skipped/reordered control
steps fail focused tests, the manual inventory is 27, and the milestone is
tested, committed, and pushed.

### `[done] AIR-003` Transcript family

Dependencies: `AIR-002`.

Scope: `transcript_air`, `transcript_binding`, `transcript_state`,
`transcript_word`, `transcript_payload`, `pow_check`, `pow_frame`,
`relation_challenge`, and `verifier_randomness`.

Required work:

1. Generate transcript payload ownership, state transitions, word framing,
   challenge draws, and proof-of-work constraints from macro definitions.
2. Preserve the exact trusted-control-plan absorption order and domain
   separation across the recursion-targeted prover, fixed verifier executor, and
   AIR.
3. Test changed, missing, duplicated, and reordered payloads independently.

Done when all nine components are macro-generated, manifest-bound prover,
executor, and AIR transcript vectors agree, the manual inventory is 18, and the
milestone is tested, committed, and pushed.

### `[done] AIR-004` Statement and VM adapters

Dependencies: `AIR-003`.

Scope: `statement_input`, `statement_semantics_input`, `vm_public_claim_input`,
`vm_public_claim_hash`, `vm_public_io_hash`, `vm_public_claim_semantics_input`,
`vm_public_logup_input`, and `vm_air_composition_input`.

Required work:

1. Generate canonical wire decoding, statement hashing, public-claim semantics,
   public LogUp terms, and VM-composition inputs from macro definitions.
2. Preserve canonical optional-root encodings and proof-kind-specific statement
   rules.
3. Reject every independently mutated public statement field.

Done when all eight components are macro-generated, malformed-wire and
statement-substitution tests pass, the manual inventory is 10, and the milestone
is tested, committed, and pushed.

### `[done] AIR-005` PCS and FRI family

Dependencies: `AIR-004`.

Scope: `query_bits`, `query_mapping`, `merkle_root`, `trace_merkle`,
`pcs_deep_input`, `fri_merkle_leaf`, `fri_merkle_node`, `fri_merkle_anchor`,
`fri_verifier_control`, and `fri_verifier_input`.

Required work:

1. Generate query decomposition, position mapping, Merkle authentication, DEEP
   inputs, FRI control, and FRI input tables from macro definitions.
2. Preserve fixed proof-shape bounds and trusted control ownership.
3. Reject incorrect bits, directions, roots, openings, layer widths, and final
   polynomial values with focused tests.

Done when all ten components are macro-generated, the manual inventory is zero,
and the milestone is tested, committed, and pushed.

### `[done] AIR-006` Zero-manual-AIR enforcement

Dependencies: `AIR-005`.

Required work:

1. Inventory the complete dependency graph reachable from every recursive proof
   branch, including components outside `crates/recursion`.
2. Add a checked-in structural guard that rejects a handwritten `FrameworkEval`
   implementation or standalone `define_component_tables!` declaration in that
   graph.
3. Remove migration-only macro dependencies, adapters, and comments.
4. Re-run the complete recursion library tests and full release workspace suite.

Done when the guard reports zero exceptions, every recursive component derives
AIR and witness behavior from one accepted macro, and the milestone is tested,
committed, and pushed.

## Recursive root proof

The design and soundness invariants are in `docs/recursion.md`. Tasks below own
the implementation order and status.

### `[done] PRO-001` Freeze the protocol profile

Dependencies: `AIR-006`.

Required work:

1. Select VM and recursion PCS parameters, table capacities, query count, proof
   shapes, and FRI layer capacities for one supported profile.
2. Derive all manifest fields from the actual component rosters and serialized
   proof types.
3. Pin the protocol identifier and every preprocessing-column identifier with
   conformance vectors.
4. Bind any later profile change to a different protocol identifier.

Done when native and AIR manifest encodings have the same digest, every field
mutation changes the identity or fails validation, and the profile is tested,
committed, and pushed.

### `[done] REC-001` Real VM-proof adapter

Dependencies: `PRO-001`.

Required work:

1. Convert `prover::Proof<Poseidon2M31MerkleHasher>` and authenticated public
   data into the fixed segment-leaf wire.
2. Derive the exact height-zero span from the public claim, job context, segment
   index, and cycle interval.
3. Reject capacity overflow, non-canonical optional roots, and disagreement
   between runner metadata and authenticated proof data.

Done when a real proof round-trips and one focused test rejects each malformed
wire or metadata field.

### `[done] REC-002` Universal trace assembler

Dependencies: `REC-001`.

Required work:

1. Define one witness container covering all 36 universal components.
2. Execute the trusted control plan to fill transcript, statement, public-claim,
   randomness, composition, PCS, FRI, arithmetic, Merkle, Poseidon2, and range
   tables.
3. Derive log sizes from populated tables and pad every table with its
   constrained inactive representation.
4. Generate every interaction trace and public relation term.

Done when assembling the same verifier input twice produces identical traces,
claims, log sizes, and preprocessing identifiers and every component accepts the
assembled witness.

### `[done] REC-003` Segment-leaf closure

Dependencies: `REC-002`.

Required work:

1. Replay one real VM proof through public-claim semantics, VM AIR composition,
   authenticated openings, DEEP quotient evaluation, FRI, proof of work, and
   final-polynomial checks.
2. Accumulate every verifier-owned public term and enforce zero global LogUp sum
   over the universal roster.
3. Bind the authenticated VM claim to exactly one height-zero span.

Done when a valid VM proof satisfies the entire universal AIR and an independent
mutation in every proof region or omitted control phase fails.

### `[done] REC-004` Canonical empty leaf

Dependencies: `REC-003`.

Required work:

1. Emit the unique empty-span statement and minimal valid universal witness.
2. Constrain empty leaves to slots at or beyond the declared segment count and
   below the fixed tree capacity.
3. Constrain every inactive wire to zero.

Done when canonical padding verifies and executed-slot empties, out-of-capacity
slots, and non-zero inactive wires fail.

### `[done] REC-005` Outer prover and verifier

Dependencies: `REC-004`.

Required work:

1. Preprocess the universal AIR for `PRO-001`.
2. Define one recursion proof artifact containing the protocol identity, parent
   statement, component claims, interaction claims, and STWO proof.
3. Prove and verify the complete roster with the Poseidon2-M31 channel.
4. Require callers to supply the expected protocol and expected statement.

Done when real segment and empty leaves produce valid recursion proofs and each
public claim or proof mutation is rejected.

### `[done] REC-006` Recursion-child closure

Dependencies: `REC-005`.

Required work:

1. Encode the real proof produced by `REC-005` into the recursion-child wire.
2. Replay its transcript through the trusted recursion control plan and
   recursion AIR self-program.
3. Verify claimed sums, composition, authenticated openings, DEEP quotient, FRI,
   proof of work, and final polynomial inside the universal AIR.

Done when one real recursion proof closes every relation as a child and one
focused test rejects each mutated statement, commitment, opening, sum, and FRI
value.

### `[done] REC-007` Binary node

Dependencies: `REC-006`.

Required work:

1. Materialize independent left and right child-verifier lanes with distinct
   verifier identifiers.
2. Prove equal heights, exact slot adjacency, common job identity, machine-state
   boundary equality, valid edge-claim placement, and the unique parent fold.
3. Feed the complete binary witness through `REC-005`.

Done when two valid adjacent child proofs produce one verified parent proof and
swapped, duplicated, gapped, overlapping, or mismatched children fail.

### `[done] REC-008` Tree driver

Dependencies: `REC-007`.

Required work:

1. Segment a run and prove its VM leaves.
2. Append canonical empty leaves to the unique minimal power-of-two capacity.
3. Prove successive binary levels; parallelism is allowed only among independent
   nodes within one level.
4. Return one root proof and root statement without descendant proofs.

Done when runs with 1, 2, 3, 4, and 8 executed segments each produce one valid
root proof with the expected span.

### `[done] REC-009` Application root API

Dependencies: `REC-008`.

Required work:

1. Accept the expected protocol, program, initial and final machine state,
   public input, public output, and total cycles.
2. Verify exactly one root proof and compare every complete-execution statement
   field before returning success.
3. Keep all multi-proof host APIs exclusively in `continuation`.

Done when the expected statement verifies and one focused test rejects each
independently changed statement field.

### `[done] REC-010` Constant-size demonstration

Dependencies: `REC-009`.

Required work:

1. Serialize actual roots for the segment-leaf, binary-root, and padded-binary
   root constructions under `PRO-001`; combine this with REC-008 validity for
   the larger supported binary trees.
2. Record root proof bytes and root-verifier operation shape independently from
   total tree-prover work.
3. Add checked-in conformance vectors for the exact serialized size and trusted
   verifier shape shared by all roots in the profile.

Done when every supported count yields exactly one root proof through the same
fixed-size wire type and profile-owned verifier plan, with actual serialization
covering every distinct root construction.

## Planned VM capabilities

These features remain project goals. They may not change the meaning of a
completed `PRO-001` profile silently: any changed roster, public claim, or proof
artifact receives a new manifest identity and repeats affected recursion
conformance tests.

### `[active] PRE-001` Hash precompile

Dependencies: `REC-010`.

Design authority: `docs/precompiles.md`.

Required work, in order:

1. Replace the prototype binding tables and handwritten evaluators with
   `define_air!` or `define_air_fns!` while preserving malformed-pair tests.
2. Implement the joint post-commitment transcript draw and joint interaction
   proof of work for VM and Poseidon2 instances.
3. Produce a standalone Poseidon2 proof carrying its shared-relation sum.
4. Remove the Poseidon2 component from the VM proof and expose its deficit as a
   public shared-relation claim.
5. Define one segment artifact containing the VM proof, hash proof, proof
   shapes, and shared claimed sums.
6. Extend `continuation` and the recursive leaf branch to replay the joint draw,
   verify both proofs, and require exact sum cancellation.
7. Bind the changed artifact to a new protocol manifest and rerun root
   conformance tests.
8. Measure the split against the integrated Poseidon2 component and record the
   supported profile rather than assuming a performance win.

Done when forged, missing, extra, or reordered permutation tuples fail both host
continuation and recursive-root verification and the result is tested,
committed, and pushed.

### `[pending] SYS-001` Syscalls and output journal

Dependencies: `PRE-001`.

Design authority: `docs/syscalls.md`.

Required work, in order:

1. Add `ecall` decoding and internal runner dispatch without exposing an
   unauthenticated journal value.
2. Define the COMMIT syscall AIR through `define_air!` or `define_air_fns!`.
3. Prove standard relation multiplicities and interaction closure for the new
   table before adding journal logic.
4. Bind the register value, Poseidon2 transition, ordered journal relation, and
   public initial/final endpoints.
5. Add the endpoints to VM public data and the Fiat-Shamir transcript.
6. Chain endpoints in `continuation` and map them into recursive leaf and root
   statements under a new protocol identity.
7. Expose the guest SDK only after VM, continuation, and recursive-root tests
   reject changed words, broken states, dropped, inserted, and reordered steps.

Done when an application verifies one proof-bound journal digest at the root and
no runner-only value can affect it.

### `[pending] FELT-001` Witness-side VM access

Dependencies: `SYS-001`.

Design authority: `docs/felt-air-compiler.md`.

Required work:

1. Add generated register read/write and memory read/write abstractions backed
   by `Tracer::trace_reg_access` and `Tracer::trace_mem_access`.
2. Generate clock-gap activations and range checks from those access operations.
3. Preserve write-once witness behavior, gap filling, x0 semantics, and memory
   roots.
4. Prove the access layer on a toy generated opcode before migrating production
   handlers.

Done when generated felt functions can execute and fill real VM access rows and
focused tests reject stale clocks, incorrect prior values, and illegal writes.

### `[pending] FELT-002` Opcode and runner migration

Dependencies: `FELT-001`.

Required work, in order:

1. Migrate `lui` end to end and delete its handwritten runner semantics.
2. Migrate `auipc`, `jal`, and `jalr`.
3. Migrate `base_alu_imm`, `base_alu_reg`, `lt_imm`, `lt_reg`, `branch_eq`, and
   `branch_lt`.
4. Migrate `shifts_imm`, `shifts_reg`, `mul`, and `mulh`.
5. Migrate `load_store`.
6. Migrate `div` last.
7. Preserve one real guest prove/verify test plus focused malformed-witness
   coverage for every family before deleting its old schema and handler.
8. Delete the obsolete opcode `define_air!` trace block, `components!` support,
   and `runner/src/ops` only after the last family moves.
9. Re-derive the VM AIR program and recursion manifest from the final roster and
   rerun every root conformance test under a new protocol identity.

Done when opcode execution, witness filling, and AIR constraints have one
felt-function source and no duplicated per-opcode semantics remain.

## Final hardening

### `[pending] REL-001` Security, performance, and release evidence

Dependencies: `FELT-002`.

Required work:

1. Add adversarial tests for non-canonical wires, transcript reordering, omitted
   relation challenges, wrong Merkle directions, reused paths, altered OODS
   values, incorrect FRI positions, non-zero relation sums, invalid padding,
   boundary discontinuities, precompile substitutions, journal forgeries, and
   root-statement substitution.
2. Run focused release tests, previous failures, the complete release workspace
   suite, and all repository hooks without ignored soundness tests.
3. Measure serialized root proof size, peak memory, leaf throughput, per-level
   node proving time, and root verification time on each supported profile.
4. Update current-state documentation from checked-in results and keep any
   unfinished design explicitly labeled.
5. Commit and push the release evidence.

Done when one expected complete-execution statement and one constant-size root
proof verify the final supported execution, all planned capabilities above are
proof-bound, and every published claim is reproducible.

## Evidence log

Append one entry after each completed task. Include the task ID, date, exact
commands run, observed test counts or measurements, and the pushed commit.

### `BASE-001` — 2026-08-04

- `cargo test --release -p recursion --lib`: 583 passed.
- `cargo test --release -p continuation`: 6 unit and 1 integration test passed.
- `cargo test --release --workspace`: passed in 102.78 seconds.
- `prek run --all-files`: passed.
- Commit `54d55fc8` pushed to `origin/chore/scratchpad-cleanups`.

### `AIR-001` — 2026-08-04

- `cargo test --release -p recursion qm31_inv`: 3 passed.
- `cargo test --release -p recursion test_linear_ops_constraints_reject_wrong_addition_result`:
  1 passed.
- `cargo test --release -p recursion test_merkle_path_constraints_reject_child_from_wrong_branch`:
  1 passed.
- `cargo test --release -p stwo-macros --test air_fns`: 21 passed.
- `cargo test --release -p recursion --lib`: 585 passed.
- `sg -p 'impl FrameworkEval for $TYPE { $$$BODY }' -l rust --json=compact crates/recursion/src`:
  30 matches.
- `prek run --all-files`: passed.
- Commit `ae5f8cc8` pushed to `origin/chore/scratchpad-cleanups`.

### `AIR-002` — 2026-08-04

- `cargo test --release -p recursion control_air::tests`: 26 matching control
  tests passed.
- `cargo test --release -p recursion vm_public_logup_control_air::tests`: 5
  passed.
- `cargo test --release -p recursion vm_air_composition_control_air::tests`: 7
  passed.
- `cargo test --release -p stwo-macros --test air_fns`: 22 passed.
- `cargo test --release -p recursion --lib`: 585 passed, including missing and
  reordered control-step rejection.
- `sg -p 'impl FrameworkEval for $TYPE { $$$BODY }' -l rust --json=compact crates/recursion/src`:
  27 matches.
- `prek run --all-files`: passed.
- Commit `ad656d26` pushed to `origin/chore/scratchpad-cleanups`.

### `AIR-003` — 2026-08-04

- `cargo test --release -p recursion transcript_air::tests`: 5 passed.
- `cargo test --release -p recursion relation_challenge_air`: 6 passed.
- `cargo test --release -p recursion verifier_randomness_air`: 11 passed.
- `cargo test --release -p recursion pow::tests`: 13 passed.
- `cargo test --release -p recursion transcript_payload_is_rejected_by_the_trusted_layout`:
  4 independent payload-mutation tests passed.
- `cargo test --release -p stwo-macros`: 25 integration tests passed; 11
  documentation tests remained intentionally ignored.
- `cargo test --release -p recursion --lib`: 589 passed.
- `sg -p 'impl FrameworkEval for $TYPE { $$$BODY }' -l rust --json=compact crates/recursion/src`:
  18 matches.
- `prek run --all-files`: passed.
- Commit `9ca4fd1d` pushed to `origin/chore/scratchpad-cleanups`.

### `AIR-004` — 2026-08-04

- Focused statement, VM-claim, public-IO, public-LogUp, and VM-composition
  adapter release tests passed.
- `cargo test --release -p stwo-macros`: 25 integration tests passed; 11
  documentation tests remained intentionally ignored.
- `cargo test --release -p recursion`: 589 passed.
- `sg -p 'impl FrameworkEval for $TYPE { $$$BODY }' -l rust --json=compact crates/recursion/src`:
  10 matches.
- `prek run --all-files`: passed.
- Commit `16ac9d55` pushed to `origin/chore/scratchpad-cleanups`.

### `AIR-005` — 2026-08-04

- `cargo test --release -p recursion query_position_air::tests`: 12 passed.
- `cargo test --release -p recursion merkle_root_air::tests`: 6 passed.
- `cargo test --release -p recursion trace_merkle_air::tests`: 10 passed.
- `cargo test --release -p recursion pcs_deep_input_air::tests`: 6 passed.
- `cargo test --release -p recursion fri_merkle_air::tests`: 24 passed.
- `cargo test --release -p recursion fri_verifier_control_air::tests`: 5 passed.
- `cargo test --release -p recursion fri_verifier_input_air::tests`: 6 passed.
- `cargo test --release -p stwo-macros`: 25 integration tests passed; 11
  documentation tests remained intentionally ignored.
- `cargo test --release -p recursion`: 589 passed in 48.70 seconds.
- `sg -p 'impl FrameworkEval for $TYPE { $$$BODY }' -l rust --json=compact crates/recursion/src`:
  zero matches.
- `rg -n 'define_component_tables!|define_component_tables' crates/recursion/src`:
  zero matches.
- `prek run --all-files`: passed.
- Commit `6bfdb9d7` pushed to `origin/chore/scratchpad-cleanups`.

### `AIR-006` — 2026-08-04

- `cargo test --release -p recursion --test air_dsl_guard`: 5 passed, covering
  both exact rosters, complete owner-policy coverage, direct-DSL structure, and
  the sole approved VM component route.
- `sg -p 'impl FrameworkEval for $TYPE { $$$BODY }' -l rust --json=compact crates/recursion/src crates/air/src/schema.rs crates/air/src/poseidon2.rs`:
  zero matches.
- `rg -n 'define_component_tables!|define_component_tables' crates/recursion/src crates/air/src/schema.rs crates/air/src/poseidon2.rs`:
  zero matches.
- `cargo test --release -p recursion`: 589 unit and 5 structural integration
  tests passed in 43.27 seconds.
- `cargo test --release --workspace`: passed in 204.43 seconds.
- `prek run --all-files`: passed.
- Commit `59ef6b42` pushed to `origin/chore/scratchpad-cleanups`.

### `PRO-001` — 2026-08-04

- `cargo test --release -p recursion profile::tests`: 7 profile construction,
  conformance-vector, preprocessing-registry, DSL-hash, capacity-binding, and
  wire-size tests passed.
- `cargo test --release -p recursion protocol::tests::every_manifest_field_changes_the_canonical_encoding`:
  all 40 independently generated field cases passed.
- `cargo test --release -p stwo-macros`: 25 integration tests passed; 11
  documentation tests remained intentionally ignored.
- `cargo test --release -p recursion`: 596 unit and 5 structural integration
  tests passed.
- `cargo test --release --workspace`: passed in 200.72 seconds.
- `prek run --all-files`: passed.
- Current protocol identifier limbs are recorded by the active profile
  conformance test. A real finalized VM segment requires log-size 11 capacity
  for its program, memory, Merkle, and Poseidon2 commitment tables; changing
  that geometry changes the identifier.
- Commit `b0a3f2ae` pushed to `origin/chore/scratchpad-cleanups`.

### `REC-001` — 2026-08-04

- `cargo test --release -p recursion segment_leaf::tests::`: 13 passed in 55.00
  seconds, including one real Poseidon VM proof and independent malformed proof,
  public-claim, runner-boundary, protocol, slot, and cycle cases.
- `cargo test --release -p recursion wire::tests::`: 24 fixed-wire round-trip
  and malformed-encoding tests passed.
- `cargo test --release -p prover --lib fixed_trace_generation_`: 2
  verifier-owned geometry tests passed.
- `cargo test --release -p prover --test integration test_prove_verify_poseidon2_channel -- --exact`:
  the ordinary Poseidon proof verified without retaining recursion-only
  expansion maps.
- `cargo test --release -p recursion`: 609 unit and 5 structural integration
  tests passed in 55.66 seconds.
- `cargo test --release -p stwo-macros`: 25 integration tests passed; 11
  documentation tests remained intentionally ignored.
- `cargo clippy --release -p stwo-macros -p air -p prover -p recursion --all-targets --no-deps -- -D warnings`:
  passed.
- `cargo test --release --workspace`: passed in 271.02 seconds.
- `prek run --all-files`: passed.
- Commit `93dc88b3` pushed to `origin/chore/scratchpad-cleanups`.

### `REC-002` — 2026-08-05

- `cargo test --release -p recursion fri_verifier_circuit::tests:: -- --nocapture`:
  15 FRI arithmetic and malformed-query tests passed.
- `cargo test --release -p recursion segment_leaf::tests:: -- --nocapture`: 16
  tests passed in 88.41 seconds, including profiled-prover transcript parity,
  direct STWO verification, deterministic double assembly, and acceptance by all
  36 macro-generated components.
- `cargo test --release -p recursion profile::tests:: -- --nocapture`: 7 active
  profile construction and conformance tests passed.
- `cargo test --release -p recursion universal_witness::tests:: -- --nocapture`:
  2 structural-capacity tests passed.
- `cargo test --release -p recursion vm_public_claim -- --nocapture`: 51 claim,
  hashing, semantics, and malformed-witness tests passed.
- `cargo test --release -p prover --test integration test_prove_verify_poseidon2_channel -- --exact --nocapture`:
  the ordinary native-transcript Poseidon proof verified in 65.00 seconds.
- `cargo test --release -p recursion --test air_dsl_guard -- --nocapture`: all 5
  universal and inner-VM direct-DSL structural guards passed.
- `cargo clippy --release -p stwo-macros -p air -p prover -p recursion --all-targets --no-deps -- -D warnings`:
  passed.
- `cargo test --release -p recursion`: 617 unit and 5 structural integration
  tests passed in 169.80 seconds.
- `cargo test --release --workspace`: passed in 280.89 seconds.
- `prek run --all-files`: passed.
- Commit `827ec9a9` pushed to `origin/chore/scratchpad-cleanups`.

### `REC-003` — 2026-08-05

- `cargo test --release -p recursion universal_leaf_rejects_each_independently_mutated_proof_region -- --nocapture && cargo test --release -p recursion real_poseidon_leaf_materializes_the_universal_witness -- --nocapture`:
  all 13 proof-region mutations were rejected and the valid real segment witness
  passed all 36 universal components.
- `cargo test --release -p recursion --test air_dsl_guard -- --nocapture`: all 5
  structural DSL guards passed.
- `cargo clippy --release -p recursion --all-targets --no-deps -- -D warnings`:
  passed.
- `/usr/bin/time -p cargo test --release -p recursion`: 630 unit tests and 5
  structural integration tests passed after the three previous fixture failures
  were rerun successfully.
- `/usr/bin/time -p cargo test --release --workspace`: passed in 246.60 seconds.
- `prek run --all-files`: passed.
- Commit `058023c6` pushed to `origin/chore/scratchpad-cleanups`.

### `REC-004` — 2026-08-05

- `cargo test --release -p recursion universal_witness::tests::canonical_empty_leaf_satisfies_the_complete_universal_air -- --nocapture && cargo test --release -p recursion universal_witness::tests::empty_branch -- --nocapture && cargo test --release -p recursion statement::tests::empty_leaf_is_rejected_outside_the_tree_capacity -- --nocapture`:
  canonical padding passed; executed, folded, and out-of-capacity empty
  statements were rejected.
- `cargo test --release -p recursion segment_leaf::tests::real_poseidon_leaf_materializes_the_universal_witness -- --nocapture`:
  the real segment branch remained valid after the shared-assembler change.
- `cargo clippy --release -p recursion --all-targets --no-deps -- -D warnings`:
  passed.
- `/usr/bin/time -p cargo test --release -p recursion`: 635 unit tests and 5
  structural integration tests passed in 115.20 seconds.
- `/usr/bin/time -p cargo test --release --workspace`: passed in 261.83 seconds.
- `prek run --all-files`: passed.
- Commit `4374b123` pushed to `origin/chore/scratchpad-cleanups`.

### `REC-005` — 2026-08-05

- `cargo test --release -p stwo-macros --test air_fns -- --nocapture`: all 26
  existing-DSL integration tests passed, including the selective unbatched LogUp
  tail layout.
- `cargo test --release -p recursion fri_merkle_air::tests::leaf_component_degree_includes_preprocessed_endpoint_products -- --exact --nocapture`:
  the measured FRI-leaf maximum constraint degree is three when trusted
  preprocessing columns are treated as degree-one expressions.
- `cargo test --release -p recursion fri_merkle_air::tests::leaf_component_proves_at_the_declared_constraint_degree_bound -- --exact --nocapture`:
  the isolated macro-generated FRI-leaf component produced and verified a native
  STWO proof at its declared degree bound.
- `cargo test --release -p recursion recursive_proof::tests::real_segment_leaf_produces_a_valid_recursion_proof -- --exact --nocapture`:
  one real VM segment produced and verified a universal recursion proof in
  432.09 seconds; measured wall time was 432.27 seconds.
- `cargo test --release -p recursion recursive_proof::tests::empty_proof_binds_every_public_claim_and_stark_region -- --exact --nocapture`:
  one valid empty proof verified and all 18 independent protocol, statement,
  kind, geometry, sum, PCS, proof-of-work, commitment, and sampled-value
  mutations were rejected in 396.06 seconds; measured wall time was 397.06
  seconds.
- `cargo test --release -p recursion profile::tests -- --nocapture`: all 7
  active profile and conformance tests passed, pinning the then-current
  universal geometry and fixed proof-wire size.
- `cargo test --release -p recursion --test air_dsl_guard -- --nocapture`: all 5
  structural DSL guards passed; no recursion-reachable owner contains a
  handwritten evaluator, standalone table macro, wrapper macro, or unapproved
  component route.
- `cargo clippy --release -p stwo-macros -p prover -p recursion --all-targets --features recursion/parallel,prover/parallel --no-deps -- -D warnings`:
  passed in 11.33 seconds.
- `/usr/bin/time -p cargo test --release -p recursion --features parallel`: 640
  unit tests and 5 structural integration tests passed in 827.24 seconds.
- `/usr/bin/time -p cargo test --release --workspace --features recursion/parallel,prover/parallel`:
  the full release workspace passed in 1,015.40 seconds.
- `prek run --all-files`: passed after formatter output was applied and checked
  explicitly.
- Commit `396f6ade` pushed to `origin/chore/scratchpad-cleanups`.

### `REC-006` — 2026-08-05

`<temporary-cache>` below denotes the test-only local cache directory used by
the recorded command without committing a machine-specific path.

- `cargo test --release -p recursion profile::tests -- --nocapture`: all 7
  profile and conformance tests passed with 2,196 table columns, 2,340 sampled
  values, 1,313 AIR instructions, 577 preprocessing columns, and a
  3,459,396-byte fixed proof wire.
- `cargo test --release -p recursion vm_air_composition_control_air::tests -- --nocapture`:
  all 9 segment, binary, empty, and malformed-control tests passed.
- `cargo test --release -p recursion vm_public_logup_control_air::tests -- --nocapture`:
  all 7 public-LogUp control tests passed.
- `cargo test --release -p recursion statement_input_air::tests -- --nocapture`:
  all 10 statement-routing and inactive-lane tests passed.
- `cargo test --release -p recursion universal_witness::tests::canonical_empty_leaf_satisfies_the_complete_universal_air -- --exact --nocapture`:
  the complete empty witness passed all universal components in 30.05 seconds.
- `STARK_V_RECURSION_CHILD_CACHE_DIR=<temporary-cache> cargo test --release -p recursion recursive_proof::tests::recursion_child_rejects_a_mutated_proof_region -- --nocapture`:
  statement, commitment, queried-opening, claimed-sum, and final-layer FRI
  mutations were independently rejected; all 5 tests passed in 1,027.41 seconds.
- `STARK_V_RECURSION_CHILD_CACHE_DIR=<temporary-cache> cargo test --release -p recursion recursive_proof::tests::two_recursion_children_produce_a_valid_binary_proof -- --exact --nocapture`:
  two independently proved recursion children produced one binary parent proof,
  and the outer verifier accepted its folded statement in 785.29 seconds.
- `cargo test --release -p recursion --test air_dsl_guard -- --nocapture`: all 5
  roster, owner-policy, and direct-DSL structural guards passed.
- `sg -p 'impl FrameworkEval for $TYPE { $$$BODY }' -l rust --json=compact crates/recursion/src crates/air/src/schema.rs crates/air/src/poseidon2.rs`:
  zero matches.
- `rg -n 'define_component_tables!|define_component_tables' crates/recursion/src crates/air/src/schema.rs crates/air/src/poseidon2.rs`:
  zero matches.
- `cargo check --release -p recursion`,
  `cargo test --release -p recursion --no-run`, and
  `cargo clippy --release -p recursion --all-targets --no-deps -- -D warnings`:
  passed.
- `prek run --all-files`: passed.
- Commit `9f849f7d` pushed to `origin/chore/scratchpad-cleanups`.

### `REC-007` — 2026-08-05

- The REC-006 end-to-end command proved and verified the valid adjacent-child
  branch in 785.29 seconds from two independently generated recursion proofs.
- `STARK_V_RECURSION_CHILD_CACHE_DIR=<temporary-cache> cargo test --release -p recursion recursive_proof::tests::binary_node_rejects_an_invalid_child_pair -- --nocapture`:
  swapped, duplicated, gapped, overlapping, and job-mismatched pairs were each
  rejected specifically as statement-fold failures; all 5 generated tests passed
  in 169.69 seconds after sharing one trusted preprocessing instance.
- `cargo test --release -p recursion statement::tests::binary_fold_rejects_adversarial_children -- --nocapture`:
  all 9 statement-model attacks passed, including height, state, cycle, empty,
  and edge-claim violations.
- `cargo test --release -p recursion statement_semantics_circuit::tests::every_binary_fold_boundary_rejects_substitution -- --nocapture`:
  all 10 AIR-circuit substitution attacks passed.
- `cargo test --release -p recursion --test air_dsl_guard -- --nocapture`: all 5
  roster, owner-policy, and direct-DSL structural guards passed.
- `cargo test --release -p recursion --no-run` and
  `cargo clippy --release -p recursion --all-targets --no-deps -- -D warnings`:
  passed.
- `prek run --all-files`: passed.
- Commit `b6f6c9be` pushed to `origin/chore/scratchpad-cleanups`.

### `REC-008` — 2026-08-06

- `cargo test --release -p recursion --features parallel tree_plan -- --nocapture`:
  all 6 empty-run and minimal-capacity planner tests passed.
- `cargo test --release -p recursion --features parallel recursive_proof::tests::parallel_workers_reuse_the_fixed_preprocessing_commitment -- --exact --nocapture`:
  the worker template reused the immutable fixed preprocessing commitment; the
  test passed in 150.19 seconds with 7.64 GB maximum RSS and zero swaps.
- `/usr/bin/time -l cargo test --release -p recursion --features parallel tree::tests::capacity_segmented_guest_produces_a_two_leaf_root -- --ignored --exact --nocapture`:
  the two-segment root passed in 938.57 seconds with 30.31 GB maximum RSS and
  zero swaps.
- The same release command selected
  `tree::tests::cycle_segmented_guest_produces_the_expected_root::case_1_three`,
  `case_2_four`, and `case_3_eight` independently. All three roots passed in
  2,069.78, 1,759.19, and 3,354.26 seconds with 35.94, 36.01, and 35.48 GB
  maximum RSS respectively and zero swaps.
- `cargo test --release -p recursion --features parallel vm_air_composition_lowering::tests -- --nocapture`:
  all 3 composition-lowering regressions passed.
- `cargo test --release -p recursion --features parallel --test air_dsl_guard -- --nocapture`:
  all 5 roster, owner-policy, direct-DSL, and component-route guards passed.
- `cargo check --release -p recursion`,
  `cargo check --release -p recursion --features parallel`,
  `cargo test --release -p recursion --features parallel --no-run`, and
  `cargo clippy --release -p recursion --all-targets --features parallel --no-deps -- -D warnings`:
  passed.
- `/usr/bin/time -l cargo test --release -p recursion --features parallel -- --test-threads=1`:
  665 unit tests and 5 structural integration tests passed, 4 explicit tree
  conformance tests remained ignored, and the one-segment root was covered. The
  suite finished in 3,980.25 seconds with 20.23 GB maximum RSS and zero swaps.
- `sg -p 'impl FrameworkEval for $TYPE { $$$BODY }' -l rust --json=compact crates/recursion/src crates/air/src/schema.rs crates/air/src/poseidon2.rs`:
  zero matches.
- `rg -n 'define_component_tables!|define_component_tables' crates/recursion/src crates/air/src/schema.rs crates/air/src/poseidon2.rs`:
  zero matches.
- `prek run --all-files`: passed.
- Commit `c212200d` pushed to `origin/chore/scratchpad-cleanups`.

### `REC-009` — 2026-08-06

- `cargo test --release -p recursion root::tests -- --nocapture`: all 7
  independent protocol, program, initial-state, final-state, public-input,
  public-output, and total-cycle mutations were rejected, and the unchanged
  complete execution was accepted; all 8 tests passed.
- `/usr/bin/time -l cargo test --release -p recursion tree::tests::one_executed_recursion_leaf_is_the_complete_root -- --exact --nocapture`:
  one real segment produced a recursive root that passed
  `root::verify_recursive_root` in 667.46 seconds with 18.99 GB maximum RSS and
  zero swaps.
- `cargo test --release -p recursion --test air_dsl_guard -- --nocapture`: all 5
  universal and inner-VM direct-DSL structural guards passed.
- `cargo check --release -p recursion`,
  `cargo check --release -p recursion --features parallel`,
  `cargo test --release -p recursion --features parallel --no-run`, and
  `cargo clippy --release -p recursion --all-targets --features parallel --no-deps -- -D warnings`:
  passed.
- `/usr/bin/time -l cargo test --release -p recursion --features parallel -- --test-threads=1`:
  673 unit tests and 5 structural integration tests passed, 4 explicit tree
  conformance tests remained ignored, and the suite finished in 3,991.63 seconds
  with 20.56 GB maximum RSS and zero swaps.
- `sg -p 'impl FrameworkEval for $TYPE { $$$BODY }' -l rust --json=compact crates/recursion/src crates/air/src/schema.rs crates/air/src/poseidon2.rs`:
  zero matches.
- `rg -n 'define_component_tables!|define_component_tables' crates/recursion/src crates/air/src/schema.rs crates/air/src/poseidon2.rs`:
  zero matches.
- `prek run --all-files`: passed.
- Commit `8c36c61e` pushed to `origin/chore/scratchpad-cleanups`.

### `REC-010` — 2026-08-06

- `cargo test --release -p recursion --features parallel root::tests -- --nocapture`:
  all 7 application-field mutations, the unchanged execution, and the frozen
  4,937-step verifier-plan digest passed; all 9 tests passed.
- `cargo test --release -p recursion --features parallel tree_plan -- --nocapture`:
  all 6 empty-run and minimal-capacity planner tests passed for 1, 2, 3, 4, and
  8 segment counts.
- `cargo test --release -p recursion --features parallel profile::tests::serialized_root_size_is_derived_from_the_recursion_shape -- --exact --nocapture`:
  the frozen profile's derived `ROOT_PROOF_BYTE_SIZE` matched the checked
  3,459,396-byte conformance value.
- `/usr/bin/time -l cargo test --release -p recursion --features parallel tree::tests::one_executed_recursion_leaf_is_the_complete_root -- --exact --nocapture`:
  one real segment-leaf root encoded to the frozen size and passed the
  application verifier in 666.93 seconds with 19.30 GB maximum RSS and zero
  swaps.
- The same release command selected
  `tree::tests::capacity_segmented_guest_produces_a_two_leaf_root` and
  `tree::tests::cycle_segmented_guest_produces_the_expected_root::case_1_three`
  independently. The real binary and padded-binary roots encoded to the same
  frozen size, matched the same verifier plan, and verified in 940.10 and
  2,091.22 seconds with 33.04 and 36.33 GB maximum RSS respectively and zero
  swaps.
- A temporary outer-only Rayon feature composition ran the two-segment command
  in 1,132.14 seconds with 34.54 GB maximum RSS and zero swaps. It was 20.4%
  slower and used more peak memory than the 940.10-second shared-pool run, so
  the checked-in feature retains STWO proof-kernel parallelism alongside the
  bounded outer proof waves. Source inspection found no separate Rayon pool.
- `cargo test --release -p recursion --features parallel --test air_dsl_guard -- --nocapture`:
  all 5 roster, owner-policy, direct-DSL, and component-route guards passed.
- `cargo check --release -p recursion --features parallel`,
  `cargo test --release -p recursion --features parallel --no-run`, and
  `cargo clippy --release -p recursion --all-targets --features parallel --no-deps -- -D warnings`:
  passed.
- `sg -p 'impl FrameworkEval for $TYPE { $$$BODY }' -l rust --json=compact crates/recursion/src crates/air/src/schema.rs crates/air/src/poseidon2.rs`:
  zero matches.
- `rg -n 'define_component_tables!|define_component_tables' crates/recursion/src crates/air/src/schema.rs crates/air/src/poseidon2.rs`:
  zero matches.
- `prek run --all-files`: passed.
- Commit `f1614b7e` pushed to `origin/chore/scratchpad-cleanups`.

## Project finish line

The project is complete only when all tasks are `[done]`, one application
statement and one root proof verify the final execution without descendant
proofs, root proof size is constant across supported segment counts, every AIR
reachable from recursion uses an accepted macro DSL, and every current-state or
performance claim is backed by checked-in release evidence.
