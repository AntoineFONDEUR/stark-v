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

Opcode migrations use a smaller ladder: runner boundary tests, component AIR
tests with focused malformed rows, then one proof-capable single-chunk VM
prove/verify per migrated family. Opcode-local geometry changes do not rerun a
recursive root; the three root shapes are revalidated after the final VM roster
is frozen. Small component tests may run concurrently, while proof jobs remain
sequential unless a checked-in memory measurement establishes a safe bound.

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

| Document                    | Class                         | Authority                                                                   |
| --------------------------- | ----------------------------- | --------------------------------------------------------------------------- |
| `docs/roadmap.md`           | Current execution ledger      | Task order, task status, completion gates, and evidence                     |
| `README.md`                 | Current state                 | Supported user-facing behavior and measured commands                        |
| `docs/airs.md`              | Current state                 | Active AIR architecture; source remains authoritative for exact constraints |
| `docs/recursion.md`         | Current design                | Recursive statements, verifier architecture, and soundness invariants       |
| `docs/felt-air-compiler.md` | Partially implemented design  | Compiler facilities and opcode/runner target                                |
| `docs/precompiles.md`       | Current implementation design | Cross-proof hash binding and measured scheduling policy                     |
| `docs/syscalls.md`          | Active feature design         | Implemented journal semantics and remaining root/SDK gates                  |
| `CONTRIBUTING.md`           | Current process               | Development and submission workflow                                         |
| `SECURITY.md`               | Current policy                | Security scope and private reporting                                        |

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
    completed migration; the syscall design remains explicitly planned and the
    precompile design tracks its active implementation state.
  - Evidence: commit `59ef6b42`; the structural guard, complete recursion suite,
    full release workspace suite, structural searches, and repository hooks
    passed.
- `[done] PRO-001` Freeze the first recursive protocol profile.
  - The generated VM, detached Poseidon2, and universal AIR programs derive
    their fixed proof geometries, verifier plans, preprocessing registries,
    exact wire types, and the protocol identifier from one profile constructor.
  - The profile fixes 193 FRI queries, 4 KiB public-input and public-output
    capacities, and a 3,479,096-byte universal proof wire.
  - Evidence: commit `b0a3f2ae`; focused profile, manifest mutation, macro,
    recursion, full release workspace, and repository hook suites passed.
- `[done] REC-001` Adapt a real segment proof to the recursive leaf wire.
  - Recursion-targeted VM and Poseidon2 constituents use manifest-bound verifier
    transcripts and retain STWO's authenticated expansion maps long enough to
    materialize all 193 independent raw-query slots. Ordinary segment proving
    keeps native transcripts and compact in-memory behavior.
  - The adapter checks both frozen constituent geometries, their shared-relation
    cancellation, canonical public claim, runner boundary, job identity, segment
    slot, cycle interval, and every trace and FRI opening before producing the
    fixed leaf input.
  - Evidence: commit `93dc88b3`; focused real-proof, malformed metadata, fixed
    wire, fixed trace, macro, clippy, full recursion, full release workspace,
    and repository hook suites passed.
- `[done] REC-002` Build the universal trace assembler.
  - Recursion-targeted segment constituents use trusted manifest transcripts
    while the ordinary prover retains native public transcripts and compact
    proof auxiliary state.
  - `UniversalWitness` deterministically fills preprocessing, original, and
    interaction trees for all 36 components, derives all claimed sums and
    verifier-owned public terms, and validates every emitted column against the
    frozen program registry.
  - STWO-omitted FRI query values are reconstructed from the DEEP answer and
    prior folds before both Merkle and folding checks; PCS periodicity uses the
    committed-domain log sizes.
  - The assembler derives its exact verifier geometry and conformance vectors
    from the generated AIR programs; a VM AIR change therefore changes the
    protocol identity instead of silently reusing an incompatible profile.
  - Evidence: commit `827ec9a9`; deterministic real-proof assembly, all 36
    direct component checks, focused malformed-FRI tests, the ordinary prover
    integration, the full recursion and workspace release suites, clippy, DSL
    guards, and repository hooks passed.
- `[done] REC-003` Close the segment-leaf branch end to end.
  - Real segment proofs replay every active constituent through its verifier
    circuit, reject nonzero circuit outputs, and require exact global relation
    closure.
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
    3,479,096-byte `RootProofBytes` type and uses the same 4,945-step verifier
    plan with one checked digest.
  - The earlier integrated-Poseidon profile produced real segment-leaf, binary,
    padded-binary, 4-segment, and 8-segment roots through the same fixed wire
    and verifier plan. The active split-proof profile has revalidated real
    segment-leaf, binary, and padded roots through the same fixed interface.
  - Evidence: real 1-, 2-, and 3-segment roots encoded and verified under the
    prior profile, fixed wire and verifier-shape vectors passed, and outer-only
    proof parallelism was measured and rejected as slower than the retained
    shared-pool strategy. The active PRE-001 evidence records the split-profile
    root.
- `[done] PRE-001` Prepare the hash-precompile proof split for production.
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
  - Completed slice: the VM router detaches Poseidon2, `SegmentProof` carries
    both constituent proofs plus the joint nonce, and host verification and
    continuation replay the shared draw and require exact sum cancellation.
  - Completed slice: the recursive leaf uses four verifier lanes for the VM,
    Poseidon2, left child, and right child. Its direct DSL-owned binder closes
    both transcript nonces and the cross-proof relation without a handwritten
    component or compatibility macro.
  - Active-profile evidence: 21 payload, 11 binder, 6 relation-challenge, and 5
    direct-DSL guard tests passed in release mode. One real split segment closed
    all 36 universal components in 98.26 seconds with 9.25 GB peak RSS. Host
    split verification passed in 67.38 seconds with 2.15 GB peak RSS. One real
    split-proof root passed in 554.23 seconds with 19.34 GB peak RSS and zero
    swaps. Workspace release check and clippy with warnings denied passed.
  - Implementation slice: commit `d80b2d97` pushed to
    `origin/chore/scratchpad-cleanups`.
  - Completed slice: two individually valid missing/extra tuple proof pairs fail
    continuation shared-sum verification; re-paired outputs fail the generated
    Poseidon2 AIR during proving; and 25 recursive tests reject a sum mismatch
    plus mutations across every VM and detached-Poseidon proof region.
  - Adversarial release evidence: missing/extra continuation cases passed in
    6.86 seconds under one outer Rayon batch with 3.52 GB peak RSS; re-paired
    output rejection passed in 6.70 seconds with 2.06 GB peak RSS; the shared
    real-proof recursive matrix passed all 25 cases in 121.08 seconds with 4.24
    GB peak RSS. Every run reported zero swaps.
  - Adversarial slice: commit `51aeb2f1` pushed to
    `origin/chore/scratchpad-cleanups`.
  - Completed slice: binary recursion lanes no longer publish unused
    interaction-PoW nonce input tuples. Focused binary transcript-root, query,
    trace-Merkle, and FRI-Merkle relation tests close exactly, and two real
    recursion-child proofs close the complete prepared binary witness before
    parent proving.
  - Binary-closure evidence: 20 focused relation-boundary tests and all 9
    transcript-payload tests passed in release mode. The proof-backed binary
    witness test passed in 314.88 seconds with 10.57 GB peak RSS and zero swaps
    using two cached child proofs. The direct-DSL guard and scoped release
    clippy with warnings denied passed.
  - Binary-closure slice: commit `ba793a61` pushed to
    `origin/chore/scratchpad-cleanups`.
  - Completed slice: the real active-profile binary root encoded to the frozen
    wire size, matched the frozen verifier plan, and passed the application
    verifier in 949.04 seconds with 34.62 GB peak RSS and zero swaps.
  - Completed slice: the real active-profile padded three-segment root encoded
    to the same frozen wire size, matched the same verifier plan, and passed in
    2,095.59 seconds with 35.56 GB peak RSS and zero swaps.
  - Completed slice: compared with the integrated profile, the split is 16.90%
    faster for a segment-leaf root, 0.95% slower for a binary root, and 0.21%
    slower for a padded root. It is a modularity boundary with a leaf benefit,
    not a blanket speedup.
  - Completed slice: the active binary root is 20.10% faster and uses 0.55 GB
    less peak RSS with the checked-in capped-outer plus STWO-inner scheduler
    than with outer Rayon alone.
  - Completion slice: step 8 evidence is recorded below; PRE-001 is complete.
- `[done] SYS-001` Implement proof-bound syscalls and output journal.
  - Completed slice: canonical `ecall` decoding, canonical program tuples, and
    an internal `a7`/`a0` dispatcher are implemented. Unsupported calls remain
    rejected before state mutation.
  - Front-end evidence: commit `8289ca1d`; focused decoder, program, dispatcher,
    and real guest-ELF tests passed, the complete air and runner release suites
    passed, scoped clippy with warnings denied passed, and repository hooks
    passed.
  - Completed slice: the minimal COMMIT AIR is defined directly through the
    existing DSL, authenticates both the syscall selector and argument reads,
    and closes its program, state, register, and range relations in one focused
    VM proof.
  - Completed slice: each COMMIT now proves an eight-word Poseidon2 digest
    transition and participates in one journal chain keyed by ordinal and
    strictly increasing execution clock. VM public data binds the segment
    entry/exit digests, COMMIT count, and last COMMIT clock; continuation and
    recursion leaf statements carry the digest endpoints.
  - Adversarial one-chunk tests reject changed words, public-state changes,
    dropped rows, inserted endpoint counts, last-clock changes, and backward
    clock links. Four-cycle segment tests preserve adjacent digest boundaries.
  - The measured VM profile is now 1,385 tables, 1,493 sampled values, and 515
    AIR instructions. The protocol identifier is
    `[845272597, 933819972, 383440221, 543106310, 36774074, 98392354, 1154621472, 1552689827]`,
    while the universal root wire remains 3,479,096 bytes.
  - Completed slice: a real COMMIT-bearing VM chunk assembled into the universal
    leaf, encoded as the 3,479,096-byte root, matched the 4,945-step verifier
    plan, and passed native application verification.
  - Completed slice: `guest_lib::commit(u32)` exposes the proved ABI without a
    new macro. The SDK-backed one- and two-COMMIT fixtures pass the unit,
    runner, ordered-journal, segmented-boundary, VM-proof, and application-root
    gates.
  - Completion slice: step 7 evidence is recorded below; SYS-001 is complete.
- `[done] FELT-001` Complete witness-side felt-function VM access.
  - `define_air_fns!` now owns generated register and aligned-memory reads and
    writes through its `vm_access` configuration; no helper or standalone macro
    was added.
  - Generated access rows call the existing tracer, automatically contribute the
    memory and clock-range relations, preserve gap filling and memory-root
    inputs, and constrain read immutability plus x0 writes.
  - Completion slice: the focused generated-row, malformed-boundary, embedded
    tracer-table, toy proof, and runner state-interface tests pass in release
    mode; detailed evidence is recorded below.
- `[in progress] FELT-002` Migrate opcode execution and retire duplicate
  semantics.
  - Every RV32IM opcode family now derives execution, witness rows, AIR,
    interactions, and its VM component route from a direct `define_air_fns!`
    definition; runner modules retain decode adapters only.
  - The existing felt DSL now provides proof-bound canonical M31 splitting and
    byte-level AND/OR/XOR intrinsics plus wrapping `u32` add/subtract with a
    constrained carry/borrow chain. Dynamic word access selects register or
    aligned-memory state while preserving x0. Division witnesses come from the
    same DSL and are explicitly bound by the wide-product identity, remainder
    magnitude, exceptional cases, and range relations. Batched LogUp arguments
    with nonlinear expressions are materialized by the compiler so generated
    constraints stay within the declared cubic degree.
  - The final opcode roster has 1,905 VM tables, 2,013 sampled values, and 787
    VM AIR instructions. Its protocol identifier is
    `[1201321936, 1233882972, 279865999, 1954284523, 1154633417, 1357347584, 450458594, 1504555888]`.
  - Fast boundary, component, and malformed-relation tests precede one
    sequential single-chunk VM proof per migrated family. The final roster is
    frozen; the one-, two-, and padded-root reruns are the next gate.
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

### `[done] REC-001` Real segment-proof adapter

Dependencies: `PRO-001`.

Required work:

1. Convert `prover::SegmentProof<Poseidon2M31MerkleHasher>` and authenticated
   public data into the fixed segment-leaf wire, including every constituent
   proof required by the active profile.
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

1. Replay one real segment proof through public-claim semantics, every
   constituent AIR composition, joint relation binding, authenticated openings,
   DEEP quotient evaluation, FRI, proof of work, and final-polynomial checks.
2. Accumulate every verifier-owned public term and enforce zero global LogUp sum
   over the universal roster.
3. Bind the authenticated VM claim to exactly one height-zero span.

Done when a valid segment proof satisfies the entire universal AIR and an
independent mutation in every proof region or omitted control phase fails.

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

### `[done] PRE-001` Hash precompile

Dependencies: `REC-010`.

Design authority: `docs/precompiles.md`.

Required work, in order:

1. `[done]` Replace the prototype binding tables and handwritten evaluators with
   `define_air!` or `define_air_fns!` while preserving malformed-pair tests.
2. `[done]` Implement the joint post-commitment transcript draw and joint
   interaction proof of work for VM and Poseidon2 instances.
3. `[done]` Produce a standalone Poseidon2 proof carrying its shared-relation
   sum.
4. `[done]` Remove the Poseidon2 component from the VM proof and expose its
   deficit as a public shared-relation claim.
5. `[done]` Define one segment artifact containing the VM proof, hash proof,
   proof shapes, and shared claimed sums.
6. `[done]` Extend `continuation` and the recursive leaf branch to replay the
   joint draw, verify both proofs, and require exact sum cancellation.
7. `[done]` Bind the changed artifact to a new protocol manifest and rerun root
   conformance tests. Real segment-leaf, binary, and padded roots pass through
   the same fixed wire and verifier plan.
8. `[done]` Measure the split against the integrated Poseidon2 component and
   record the supported profile rather than assuming a performance win.

Done when forged outputs, missing or extra tuples, and input/output re-pairing
fail both host continuation and recursive leaf/root construction and the result
is tested, committed, and pushed. Reordering complete tuples remains valid
because the shared LogUp relation binds a multiset.

### `[done] SYS-001` Syscalls and output journal

Dependencies: `PRE-001`.

Design authority: `docs/syscalls.md`.

Required work, in order:

1. `[done]` Add `ecall` decoding and internal runner dispatch without exposing
   an unauthenticated journal value.
2. `[done]` Define the COMMIT syscall AIR through `define_air!` or
   `define_air_fns!`.
3. `[done]` Prove standard relation multiplicities and interaction closure for
   the new table before adding journal logic.
4. `[done]` Bind the register value, Poseidon2 transition, ordered journal
   relation, and public initial/final endpoints.
5. `[done]` Add the endpoints to VM public data and the Fiat-Shamir transcript.
6. `[done]` Chain endpoints in `continuation` and map them into recursive leaf
   and root statements under a new protocol identity.
7. `[done]` Expose the guest SDK only after VM, continuation, and recursive-root
   tests reject changed words, broken states, dropped, inserted, and reordered
   steps.

Done when an application verifies one proof-bound journal digest at the root and
no runner-only value can affect it.

### `[done] FELT-001` Witness-side VM access

Dependencies: `SYS-001`.

Design authority: `docs/felt-air-compiler.md`.

Required work:

1. `[done]` Add generated register read/write and memory read/write abstractions
   backed by `Tracer::trace_reg_access` and `Tracer::trace_mem_access`.
2. `[done]` Generate clock-gap activations and range checks from those access
   operations.
3. `[done]` Preserve write-once witness behavior, gap filling, x0 semantics, and
   memory roots.
4. `[done]` Prove the access layer on a toy generated opcode before migrating
   production handlers.

Done when generated felt functions can execute and fill real VM access rows and
focused tests reject stale clocks, incorrect prior values, and illegal writes.

### `[in progress] FELT-002` Opcode and runner migration

Dependencies: `FELT-001`.

Required work, in order:

1. `[done]` Migrate `lui` end to end and delete its handwritten runner
   semantics.
2. `[done]` Migrate `auipc`, `jal`, and `jalr`.
3. `[done]` Migrate `base_alu_imm` and `base_alu_reg`.
4. `[done]` Migrate `lt_imm`, `lt_reg`, `branch_eq`, and `branch_lt`.
5. `[done]` Migrate `shifts_imm` and `shifts_reg`.
6. `[done]` Migrate `mul` and `mulh`.
7. `[done]` Migrate `load_store`.
8. `[done]` Migrate `div` last.
9. `[done]` Preserve one real guest prove/verify test plus focused
   malformed-witness coverage for every family before deleting its old schema
   and handler. Every family has both gates.
10. `[done]` Delete obsolete opcode `define_air!` trace blocks, bare opcode
    component routes, and handwritten runner witnesses after the last family
    moves.
11. `[in progress]` Re-derive the VM AIR program and recursion manifest from the
    final roster and rerun every root conformance test under the new protocol
    identity. The manifest is frozen; root reruns remain.

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
Values in dated entries describe the checked-in profile at that milestone; the
Current checkpoint section above is authoritative for the active profile.

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

### `PRE-001` — 2026-08-06

- The first active-profile binary-root rerun reached the prepared parent witness
  and rejected a nonzero universal relation sum after 811.73 seconds; peak RSS
  was 29.54 GB and no swaps occurred.
- Focused binary boundary tests isolated the imbalance to the child transcript
  interaction-PoW nonce. VM and Poseidon2 segment lanes consume their nonce
  through the joint binder, while left and right recursion lanes only absorb the
  nonce into their child transcript and therefore publish no typed
  verifier-input use.
- `cargo test --release -p recursion --lib transcript_payload_air::tests:: -- --nocapture`:
  all 9 lane-routing and active-profile payload tests passed.
- `cargo test --release -p recursion --lib close_exactly -- --nocapture`: all 20
  segment and binary relation-boundary tests passed, including transcript root,
  query position, trace Merkle, FRI Merkle, PCS, FRI, control, and lowering
  closure.
- `STARK_V_RECURSION_CHILD_CACHE_DIR=<temporary-cache> cargo test --release -p recursion --features parallel --lib recursive_proof::tests::two_recursion_children_close_binary_witness_relations -- --exact --nocapture --test-threads=1`:
  two real recursion-child proofs closed the complete prepared parent witness in
  314.88 seconds with 10.57 GB maximum RSS and zero swaps, without paying for a
  parent STARK proof.
- `cargo test --release -p recursion --test air_dsl_guard -- --nocapture`: all 5
  direct-DSL structural guards passed.
- `cargo clippy --release -p recursion --features parallel --all-targets --no-deps -- -D warnings`:
  passed in 11.06 seconds. The dependency-inclusive form reports existing
  warnings from `external/stwo`; the submodule remains unchanged.
- `prek run --files <changed-files>` and repository commit hooks passed.
- Commit `ba793a61` pushed to `origin/chore/scratchpad-cleanups`.
- `/usr/bin/time -l cargo test --release -p recursion --features parallel --lib tree::tests::capacity_segmented_guest_produces_a_two_leaf_root -- --ignored --exact --nocapture --test-threads=1`:
  the active-profile binary root encoded to the 3,479,096-byte wire, matched the
  pre-journal 4,943-step verifier plan, and passed the application verifier. The
  test took 949.04 seconds; the command took 1,002.32 seconds including
  compilation, with 34.62 GB maximum RSS and zero swaps.
- `/usr/bin/time -l cargo test --release -p recursion --features parallel --lib tree::tests::cycle_segmented_guest_produces_the_expected_root::case_1_three -- --ignored --exact --nocapture --test-threads=1`:
  the active-profile three-segment run padded to four leaves, encoded to the
  same fixed wire, matched the same verifier plan, and passed the application
  verifier in 2,095.59 seconds with 35.56 GB maximum RSS and zero swaps.
- PRE-001 step 7 is complete. The one-, two-, and padded three-segment roots
  cover every distinct tree construction without repeating the same binary shape
  at larger exact powers.
- The integrated profile took 666.93, 940.10, and 2,091.22 seconds for the same
  segment-leaf, binary, and padded constructions. The active split profile took
  554.23, 949.04, and 2,095.59 seconds respectively: -16.90%, +0.95%, and
  +0.21%.
- A detached current-source feature composition enabled outer Rayon while
  disabling `stwo/parallel` and `stwo-constraint-framework/parallel`;
  `cargo tree -e features` confirmed neither inner feature was active.
- `/usr/bin/time -l env CARGO_TARGET_DIR=<shared-target> cargo test --release -p recursion --features parallel --lib tree::tests::capacity_segmented_guest_produces_a_two_leaf_root -- --ignored --exact --nocapture --test-threads=1`:
  the outer-only binary root passed in 1,139.75 seconds with 35.17 GB maximum
  RSS and zero swaps. Against the checked-in 949.04-second, 34.62-GB shared
  configuration, outer-only was 20.10% slower and used 0.55 GB more peak RSS.
- The supported scheduler remains the checked-in two-proof outer wave plus STWO
  inner parallelism in one Rayon pool. PRE-001 is complete.

### `SYS-001` — 2026-08-06

- `cargo test --release -p air instructions::tests:: -- --nocapture`: canonical
  ECALL decoded as `Opcode::Ecall` and EBREAK remained unsupported; both cases
  passed.
- `cargo test --release -p runner syscalls::tests:: -- --nocapture` and the
  exact program-row test passed, pinning the internal `a7` dispatch and
  canonical `[Opcode::Ecall, 0, 0, 0]` tuple.
- `cargo test --release -p runner --test syscalls unsupported_ecall_reaches_the_internal_dispatcher -- --exact --nocapture`:
  a real RISC-V guest containing `ecall` reached
  `RunError::UnsupportedSyscall { id: 7, .. }` instead of failing instruction
  decode; the test passed in 0.37 seconds.
- `cargo test --release -p air -p runner -- --test-threads=1`: all 62 air unit,
  1 air integration, 51 runner unit, 15 existing runner integration, and 1 new
  syscall integration tests passed.
- `cargo clippy --release -p air -p runner --all-targets --no-deps -- -D warnings`,
  focused repository hooks, and the commit hooks passed.
- Commit `8289ca1d` pushed to `origin/chore/scratchpad-cleanups`.
- The SYS-001 step-1 checkpoint rejected every syscall ID and intentionally
  contained no journal value in `RunResult` or public data.
- The direct `define_air!` COMMIT table authenticates canonical `ecall`, the
  `a7 == 1` selector read, the `a0` argument read, the execution-state
  transition, and both register clock gaps. The existing DSL access-field
  generator was extended; no standalone macro or manual component was added.
- `cargo test --release -p air commit_ -- --nocapture`: all 3 focused COMMIT
  constraint-boundary tests passed.
- `cargo test --release -p runner --test syscalls commit_ecall_records_the_authenticated_register_reads -- --exact --nocapture`:
  the one-COMMIT guest chunk emitted the expected selector and argument reads.
- `/usr/bin/time -lp cargo test --release -p prover --test integration commit_standard_relations_prove_and_verify -- --exact --nocapture`:
  the one-chunk VM proof verified in 6.72 seconds with 1.95 GB maximum RSS and
  zero swaps.
- At commit `01c6eb4c`, the exact DSL-owner and VM-roster guards passed and the
  then-current profile pinned 1,347 VM tables, 1,455 sampled values, 512 AIR
  instructions, and the unchanged 3,479,096-byte universal root wire.
- `/usr/bin/time -lp cargo test --release -p stwo-macros -p air -p runner -- --test-threads=8`:
  all macro DSL, AIR, and runner release tests passed in 76.52 seconds with 1.40
  GB maximum RSS and zero swaps.
- `cargo clippy --release -p stwo-macros -p air -p runner -p prover -p recursion --all-targets --no-deps -- -D warnings`:
  the affected crates passed with warnings denied.
- Commit `01c6eb4c` contains the proof-bound COMMIT register boundary and frozen
  profile update.
- Commit `01c6eb4c` completed SYS-001 steps 2 and 3; the active checkpoint above
  records the later journal implementation.
- Focused release tests passed for the journal AIR, runner rows, four-cycle
  segment boundaries, host continuation, VM public-claim semantics, public LogUp
  ownership, relation challenges, universal relation registry, fixed profile,
  tree job context, and all five direct-DSL guards.
- Adversarial release tests rejected changed committed words, changed public
  journal endpoints, counts, and clocks, dropped COMMIT rows, and backward clock
  links. Root application-field tests reject changed initial and final machine
  states, including their public journal digests.
- `/usr/bin/time -l cargo test --release -p recursion --features parallel tree::tests::one_commit_recursion_leaf_is_the_complete_root --lib -- --exact --nocapture --test-threads=1`
  (run before marking the test as opt-in): one real COMMIT-bearing VM chunk
  assembled into a universal segment leaf, encoded to the 3,479,096-byte root
  wire, matched the 4,945-step verifier plan, and passed native application
  verification. The test took 554.16 seconds; the command took 554.34 seconds
  with 18.89 GB maximum RSS and zero swaps.
- The root test is now an explicit conformance gate. Its current selector is
  `cargo test --release -p recursion --features parallel --lib -- --ignored --exact --list | rg 'tree::tests::one_commit_recursion_leaf_is_the_complete_root'`;
  the release test list resolves exactly that case.
- `cargo test --release -p recursion --features parallel root::tests:: --lib -- --nocapture --test-threads=1`
  passed all 9 application-binding and root-conformance tests. The normal tree
  filter passed all 8 fast cases and reported all 5 cryptographic roots as
  explicit opt-in gates.
- `cargo clippy --release -p stwo-macros -p air -p runner -p prover -p continuation -p recursion --all-targets --no-deps -- -D warnings`
  passed in 11.62 seconds with 0.76 GB maximum RSS and zero swaps. All 5
  direct-DSL guards and the changed-file repository hooks passed.
- The first root attempt exposed the stale pre-journal verifier-plan fixture
  before native verification. Its focused conformance test now pins the
  4,945-step plan and recursion AIR digest
  `[1270421312, 1168180329, 1487888523, 1859018076, 1573466635, 85579857, 111495589, 650827603]`.
- At commit `978886e1`, SYS-001 step 6 was complete and the guest SDK plus its
  segmented application test remained step 7.
- `cargo test --release -p guest-lib syscalls::tests::commit_selector_matches_the_proved_abi -- --exact --nocapture --test-threads=1`:
  the SDK selector test passed. The wrapper places selector 1 in `a7`, the word
  in `a0`, and executes `ecall` through one ordinary function call.
- `cargo test --release -p runner --test syscalls -- --nocapture --test-threads=1`:
  all 7 SDK-backed syscall tests passed in 0.11 seconds, including distinct-word
  ordering and adjacent journal state across four-cycle segments.
- `/usr/bin/time -l cargo test --release -p prover --test integration commit_standard_relations_prove_and_verify -- --exact --nocapture --test-threads=1`:
  the SDK-backed one-chunk VM proof passed in 6.74 seconds with 1.97 GB maximum
  RSS and zero swaps.
- `/usr/bin/time -l cargo test --release -p recursion --features parallel tree::tests::one_commit_recursion_leaf_is_the_complete_root --lib -- --ignored --exact --nocapture --test-threads=1`:
  the SDK-backed COMMIT execution encoded to the fixed 3,479,096-byte root,
  matched the 4,945-step verifier plan, and passed native application
  verification in 553.98 seconds. The command took 645.18 seconds including
  release recompilation, with 19.95 GB maximum RSS and zero swaps.
- Workspace release clippy passed for `guest-lib`, `runner`, and `recursion`.
  Standalone `guest-bin` release clippy passed for its production library and
  RISC-V binaries; `--all-targets` is invalid for this no-std target because it
  requests an unavailable Rust test harness. Changed-file repository hooks
  passed.
- SYS-001 step 7 is complete. SYS-001 is complete.

### `FELT-001` — 2026-08-06

- `define_air_fns!` accepts `vm_access: { state: ..., tracer: ... }` and the
  `read_reg`, `write_reg`, `read_mem`, and `write_mem` statements. These are
  additions to the existing felt DSL, not wrapper or standalone macros.
- Each access generates the prior/next limb and prior-clock columns, paired
  `memory_access` entries, and a `range_check_20` clock-difference entry. Reads
  constrain `prev == next`; register writes use an inverse witness to select x0
  and force its next word to zero.
- Witness calls use `air::vm::MachineState`, invoke the existing
  `Tracer::trace_reg_access` or `Tracer::trace_mem_access`, and push embedded
  rows directly into the configured tracer table. The existing `define_air!`
  `clock_gap:` component owns gap-row constraints; `ClockGapTable` remains only
  its columnar witness container.
- `cargo test --release -p runner machine::tests:: --lib -- --nocapture`: all 3
  focused architectural-state tests passed.
- `/usr/bin/time -l cargo test --release -p stwo-macros --test air_fns generated_ -- --nocapture --test-threads=1`:
  all 10 generated access tests passed in 0.03 seconds after release
  compilation, with 1.20 GB maximum RSS and zero swaps. They cover register and
  aligned-memory reads/writes, initial-memory capture, gap filling, valid toy
  proofs, stale clocks, incorrect prior values, read-side mutation, and x0.
- `/usr/bin/time -l cargo test --release -p stwo-macros --test air_fns -- --nocapture --test-threads=1`:
  the complete 37-test fn-DSL suite passed in 0.02 seconds with a warm build,
  60.46 MB maximum RSS, and zero swaps.
- `cargo clippy --release -p stwo-macros -p air -p runner --all-targets --no-deps -- -D warnings`:
  the affected crates and targets passed with warnings denied.
- FELT-001 does not change the production component roster or recursion
  protocol, so no VM or recursion-root conformance run is required at this
  boundary. FELT-002 starts with the production `lui` migration, where component
  geometry and protocol identity first change.

### `FELT-002 LUI checkpoint` — 2026-08-07

- `crates/air/src/opcodes/lui.rs` is the single source for LUI state mutation,
  witness rows, constraints, and relation entries through `define_air_fns!`. The
  runner only converts decoded fields to felt arguments and applies the
  generated next-PC output. The old `define_air!` table and handwritten write
  and PC semantics are gone.
- `/usr/bin/time -lp cargo test --release -p runner lui_generated_execution_ -- --nocapture --test-threads=1`:
  all 4 generated execution boundary tests passed; the test body took 0.00
  seconds after a 41.94-second release build, with 1.35 GB maximum RSS and zero
  swaps.
- `/usr/bin/time -lp cargo test --release -p prover --lib components::tests::test_lui_e2e -- --exact --nocapture --test-threads=1`:
  the LUI-only trace and AIR constraint gate passed in 0.18 seconds.
- `/usr/bin/time -lp cargo test --release -p prover --test integration lui_standard_relations_prove_and_verify -- --exact --nocapture --test-threads=1`:
  the proof-capable single-chunk LUI guest proved and verified in 6.76 seconds,
  with 2.03 GB maximum RSS and zero swaps.
- `/usr/bin/time -lp cargo test --release -p prover --test integration lui_destination_limb_mutation_is_rejected -- --exact --nocapture --test-threads=1`:
  changing one generated destination limb failed with `ConstraintsNotSatisfied`;
  the rejection test took 6.73 seconds, with 2.10 GB maximum RSS and zero swaps.
- `cargo test --release -p recursion --test air_dsl_guard -- --nocapture --test-threads=1`:
  all 5 roster, owner, direct-DSL, and component-route guards passed.
- `/usr/bin/time -lp cargo test --release -p recursion --lib profile::tests:: -- --nocapture --test-threads=1`:
  all 7 generated-geometry, digest, registry, and fixed-root-wire checks passed
  in 0.31 seconds. The LUI checkpoint has VM geometry 1,387 tables, 1,495
  sampled values, and 521 AIR instructions under a new protocol identifier.
- `cargo clippy --release -p air -p runner -p prover -p recursion --all-targets --no-deps -- -D warnings`
  and standalone guest `cargo clippy --release --bin lui_output -- -D warnings`:
  both release lint gates passed.
- Root proof E2Es remain deferred until the final opcode roster. LUI changes VM
  geometry but not tree reduction, padding, or the constant-size root wire, so
  repeating one-, two-, and three-segment roots here would add cost without a
  new recursion boundary.

### `FELT-002 AUIPC/JAL/JALR checkpoint` — 2026-08-07

- `crates/air/src/opcodes/{auipc,jal,jalr}.rs` are the sole sources for those
  instructions' state mutation, witness rows, constraints, relation entries, and
  component evaluators through direct `define_air_fns!` invocations. Their
  runner functions retain decoded-argument adapters and apply the generated
  next-PC output; the three obsolete `define_air!` blocks are gone.
- The existing felt DSL now provides `split_m31`, `bitand`, `bitor`, and
  `bitxor`. The split commits canonical little-endian limbs, constrains their
  recomposition, and registers both range relations. Each bit operation commits
  its output and registers the corresponding preprocessed bitwise tuple. JALR
  additionally preserves the source-register M31 range boundary.
- `/usr/bin/time -lp cargo test --release -p stwo-macros --test air_fns -- --nocapture --test-threads=1`:
  all 45 compiler, access, proof, relation, hint, and intrinsic tests passed in
  0.04 seconds after release compilation; the command used 1.21 GB maximum RSS
  and zero swaps.
- `/usr/bin/time -lp cargo test --release -p runner generated_execution -- --nocapture --test-threads=1`:
  all 12 generated LUI/AUIPC/JAL/JALR execution-boundary tests passed in 0.00
  seconds; release compilation used 1.35 GB maximum RSS and zero swaps.
- `/usr/bin/time -lp cargo nextest run --release -p prover --lib -E 'test(/components::tests::test_(auipc|jal|jalr)_e2e/)' --test-threads=3`:
  all three component AIR gates passed concurrently in 0.24 seconds with 59.88
  MB maximum RSS and zero swaps.
- `/usr/bin/time -lp cargo nextest run --release -p prover --test integration -E 'test(/(auipc_destination_limb_mutation_fails_component_constraints|jalr_target_lsb_mutation_leaves_a_relation_deficit)/)' --test-threads=2`:
  both malformed boundaries were rejected in 0.32 seconds with 213.66 MB maximum
  RSS and zero swaps. LUI's malformed split test was also reduced from full
  proving to a 0.18-second component constraint check.
- `/usr/bin/time -lp cargo nextest run --release -p prover --test integration -E 'test(/(auipc|jal|jalr)_standard_relations_prove_and_verify/)' --test-threads=1`:
  the three proof-capable single-chunk guests proved and verified sequentially
  in 20.58 seconds with 2.01 GB maximum RSS and zero swaps. The final JALR
  source range check was revalidated by its 6.86-second single-chunk proof.
- `/usr/bin/time -lp cargo test --release -p recursion profile::tests:: -- --nocapture --test-threads=1`:
  all seven generated-geometry, digest, registry, and fixed-root-wire checks
  passed in 0.35 seconds. The active checkpoint has 1,416 VM tables, 1,524
  sampled values, 544 AIR instructions, protocol identifier
  `[260724498, 1056429239, 162301300, 1188550917, 1596141750, 682600581, 863947950, 344096256]`,
  and VM AIR digest
  `[1382158882, 639948062, 696853649, 1967380268, 1649896554, 286238969, 116982786, 411321569]`.
- `cargo test --release -p recursion --test air_dsl_guard -- --nocapture --test-threads=1`:
  all five roster, owner, direct-DSL, and generated-component route guards
  passed.
- `cargo clippy --release -p stwo-macros -p air -p runner -p prover -p recursion --all-targets --no-deps -- -D warnings`
  and guest-bin release clippy for `auipc_output`, `jal_output`, and
  `jalr_output` passed with warnings denied.
- `prek run --all-files`: both the external-directory guard and Trunk checks
  passed.
- Implementation commit `ec4db511` was pushed to
  `origin/chore/scratchpad-cleanups`.
- Recursive-root proofs remain deferred until the final opcode roster: this
  slice changes VM component geometry but not the leaf, binary, padded-tree, or
  constant-size root boundary.

### `FELT-002 base ALU checkpoint` — 2026-08-07

- `crates/air/src/opcodes/{base_alu_reg,base_alu_imm}.rs` are the sole sources
  for base arithmetic and bitwise state mutation, witness rows, constraints,
  relation entries, and component evaluators. Their runner functions decode a
  one-hot operation tuple and call the generated fill; both obsolete
  `define_air!` blocks and the stale manual-column tests are gone.
- The existing `define_air_fns!` compiler now provides `add_u32` and `sub_u32`
  intrinsics. Each commits the four wrapping result bytes and its carry/borrow
  chain, constrains the byte equations and boolean chain, and range-checks the
  selected result. Existing bitwise intrinsics accept an optional relation
  multiplicity, so one family function can gate each lookup with its opcode
  flag. No standalone macro or manual component was added.
- `/usr/bin/time -l cargo test --release -p stwo-macros --test air_fns -- --test-threads=12`:
  all 56 compiler, access, proof, relation, hint, and intrinsic tests passed in
  0.01 seconds after release compilation, with 63.37 MB maximum RSS and zero
  swaps.
- `/usr/bin/time -l cargo nextest run --release -p runner -j 9 -E 'test(generated_register_alu_honors_word_boundaries) | test(generated_immediate_alu_sign_extends_the_twelve_bit_operand)'`:
  all nine wrapping-arithmetic, bitwise, and sign-extension boundary cases
  passed concurrently in 0.01 seconds. Release compilation dominated the
  44.52-second command and used 1.36 GB maximum RSS with zero swaps.
- A release nextest command selected the nine exact base-ALU component test
  names plus `mutated_generated_add_result_fails_component_constraints` and
  `mutated_generated_xori_result_leaves_a_relation_deficit`, with `-j 11`: all
  11 component and adversarial gates passed concurrently in 0.68 seconds. The
  malformed add result violated component constraints, while the malformed XOR
  result left a non-zero relation sum. Release linking dominated the
  76.27-second command and used 1.50 GB maximum RSS with zero swaps.
- `/usr/bin/time -l cargo nextest run --release -p prover -j 1 -E 'test(base_alu_reg_single_chunk_proves_and_verifies) | test(base_alu_imm_single_chunk_proves_and_verifies)'`:
  the register and immediate proof-capable guests proved and verified
  sequentially in 13.68 seconds, with 2.05 GB maximum RSS and zero swaps. The
  opcode-only component fixtures were explicitly rejected as proof fixtures
  because they never access their declared output address.
- `cargo test --release -p air --lib -- --test-threads=12`: all 47 AIR tests
  passed after the broader check exposed and corrected a stale pre-migration JAL
  column-count assertion.
- `/usr/bin/time -l cargo test --release -p recursion profile::tests:: -- --nocapture --test-threads=7`:
  all seven generated-geometry, digest, registry, and fixed-root-wire checks
  passed in 0.64 seconds after release linking. The active checkpoint has 1,512
  VM tables, 1,620 sampled values, 597 AIR instructions, protocol identifier
  `[1696431044, 1504695671, 1975523688, 1955391245, 877564173, 18316442, 885929987, 784128183]`,
  and VM AIR digest
  `[1178552387, 2032963711, 526923786, 1772398340, 1481691220, 779525080, 1670936839, 1173528054]`.
- `cargo test --release -p recursion --test air_dsl_guard -- --nocapture --test-threads=1`:
  all five roster, owner, direct-DSL, and generated-component route guards
  passed after adding both new owner files to the exact inventory.
- `cargo clippy --release -p stwo-macros -p air -p runner -p prover -p recursion --all-targets --no-deps -- -D warnings`
  and guest-bin release clippy for `base_alu_reg_output` and
  `base_alu_imm_output` passed with warnings denied.
- `prek run --all-files`: the external-directory guard and Trunk checks passed
  after replacing spell-check-hostile hexadecimal fixture notation with the
  equivalent named boundary.
- Recursive-root proofs remain deferred until the final opcode roster: this
  slice changes the VM component geometry and protocol identity, but not a root
  construction boundary.
- Crash-history and scheduling measurements keep proof-capable tests sequential.
  Independent runner and component gates use outer test-process parallelism,
  while a single proof retains STWO's shared Rayon pool: the measured binary
  root took 949.04 seconds and 34.62 GB maximum RSS with the shared pool versus
  1,139.85 seconds and 35.17 GB with outer-only Rayon.
- Implementation commit `16888749` was pushed to
  `origin/chore/scratchpad-cleanups`.

### `FELT-002 comparison and branch checkpoint` — 2026-08-07

- `crates/air/src/opcodes/{lt_reg,lt_imm,branch_eq,branch_lt}.rs` are the sole
  sources for comparison and branch state transitions, witness rows,
  constraints, relations, and component evaluators. Their runner functions now
  decode only the one-hot opcode tuple and immediate representation before
  calling the generated fill. The four obsolete `define_air!` blocks, manual
  first-difference witnesses, equality inverse markers, and their stale tests
  are gone.
- The migration composes existing DSL primitives and adds no macro surface.
  `sub_u32(lhs, rhs)` authenticates unsigned less-than through its terminal
  borrow. Signed comparisons use the standard sign-bit order transform by
  proving `msb XOR 0x80` through the existing bitwise relation. Equality is
  equivalent to neither directional subtraction borrowing.
- `/usr/bin/time -l cargo nextest run --release -p runner -j 16` with exact
  filters for the new comparison and branch boundary cases: all 16 signed,
  unsigned, sign-extension, polarity, and negative-displacement cases passed
  concurrently in 0.017 seconds. Release compilation dominated the 44.91-second
  command and used 1.49 GB maximum RSS with zero swaps.
- `/usr/bin/time -l cargo nextest run --release -p prover -j 14` with exact
  filters for the ten opcode component fixtures and four malformed-witness
  checks: all 14 passed concurrently in 0.816 seconds. Corrupted subtraction
  results violated component constraints; corrupted signed-order transforms left
  non-zero relation sums. Release linking dominated the 73.81-second command and
  used 1.47 GB maximum RSS with zero swaps.
- `/usr/bin/time -l cargo nextest run --release -p prover -j 1` with exact
  filters for the four single-chunk tests: the register comparison, immediate
  comparison, equality branch, and ordered branch guests proved and verified
  sequentially in 27.10 seconds, with 2.05 GB maximum RSS and zero swaps.
- `cargo test --release -p air --lib -- --test-threads=12`: all 46 AIR tests
  passed in 0.04 seconds after removing the stale manual branch-column test.
- `/usr/bin/time -l cargo test --release -p recursion profile::tests:: -- --nocapture --test-threads=7`:
  all seven generated-geometry, digest, registry, and fixed-root-wire checks
  passed in 0.95 seconds after release linking. The active checkpoint has 1,556
  VM tables, 1,664 sampled values, 629 AIR instructions, protocol identifier
  `[1812854606, 380357156, 1799778124, 326217952, 1577751674, 998653010, 10229157, 1305708380]`,
  and VM AIR digest
  `[1150624488, 1921625284, 1150277924, 591183324, 1430805914, 109481434, 173677670, 1962108186]`.
- `cargo test --release -p recursion --test air_dsl_guard -- --nocapture --test-threads=1`:
  all five roster, owner, direct-DSL, and generated-component route guards
  passed after moving the four exact owners and routes out of the manual schema.
- Guest-bin release clippy passed with warnings denied for `lt_reg_output`,
  `lt_imm_output`, `branch_eq_output`, and `branch_lt_output`.
- `cargo clippy --release -p air -p runner -p prover -p recursion --all-targets --no-deps -- -D warnings`
  passed for every affected host target.
- `prek run --all-files`: the external-directory guard and Trunk checks passed.
- Recursive-root proofs remain deferred until the final opcode roster: this
  slice changes the VM component geometry and protocol identity, but no root
  construction boundary.
- Implementation commit `9c6fb0ef` was pushed to
  `origin/chore/scratchpad-cleanups`.

### `FELT-002 shift checkpoint` — 2026-08-07

- `crates/air/src/opcodes/{shifts_reg,shifts_imm}.rs` are the sole sources for
  SLL/SRL/SRA and SLLI/SRLI/SRAI state transitions, witness rows, constraints,
  relations, and component evaluators through direct `define_air_fns!`
  invocations. Their runner functions decode only registers, immediates, and the
  one-hot opcode tuple before calling the generated fill. The obsolete
  `define_air!` blocks and manual shift-witness builder are gone.
- The shift functions authenticate the five-bit amount, byte carries, dynamic
  masks, and arithmetic sign through the existing bitwise relation, then
  range-check the four output bytes. No standalone or opcode-specific macro was
  added. The existing compiler now commits nonlinear relation arguments before
  pair-batched LogUp evaluation; two macro-level degree regressions and both
  production shift evaluators prove every constraint remains at degree three or
  below. Trusted preprocessed components retain their singleton nonlinear tail.
- `/usr/bin/time -l cargo nextest run --release -p runner -p prover ... -j 12`
  selected nine runner boundary cases, six component fixtures, three lookup
  gates, two malformed-witness checks, and two exact-guest aggregate AIR checks:
  all 22 passed concurrently in 3.35 seconds after release compilation, with
  1.46 GB maximum RSS and zero swaps.
- `/usr/bin/time -l cargo nextest run --release -p prover --test integration ... -j 1`:
  the register and immediate single-chunk guests proved and verified
  sequentially in 13.76 seconds, with 2.09 GB maximum RSS and zero swaps.
- `/usr/bin/time -l cargo test --release -p stwo-macros --test air_fns -- --test-threads=12`
  passed all 58 compiler, access, intrinsic, relation, degree, and proof tests.
  `cargo test --release -p air --lib -- --test-threads=12` passed all 46 AIR
  tests.
- `/usr/bin/time -l cargo test --release -p recursion --lib profile::tests:: -- --nocapture --test-threads=7`:
  all seven profile construction, geometry, digest, registry, and fixed-wire
  tests passed in 0.58 seconds after release compilation, with 3.17 GB maximum
  RSS and zero swaps. The active checkpoint has 1,677 VM tables, 1,785 sampled
  values, 646 AIR instructions, protocol identifier
  `[1496761093, 943642719, 1615269435, 2129355053, 368726675, 2114118801, 2126697374, 1055584304]`,
  and VM AIR digest
  `[1045320913, 590638401, 396291190, 174280959, 1757939123, 404792689, 410635700, 1286242632]`.
- `cargo test --release -p recursion --test air_dsl_guard -- --nocapture --test-threads=5`
  passed all five roster, owner, direct-DSL, and generated-component route
  guards after moving both exact shift owners and routes out of the manual
  schema.
- Host release clippy passed with warnings denied for `stwo-macros`, `air`,
  `runner`, `prover`, and `recursion`; standalone guest release clippy passed
  for both shift output fixtures. `prek run --all-files` passed.
- Implementation commit `92060bc2` was pushed to
  `origin/chore/scratchpad-cleanups`. Recursive-root proofs remain deferred
  until the final opcode roster because this slice changes VM geometry but not a
  root construction boundary.

### `FELT-002 multiplication checkpoint` — 2026-08-07

- `crates/air/src/opcodes/{mul,mulh}.rs` are the sole sources for MUL, MULH,
  MULHSU, and MULHU state transitions, witness rows, constraints, relations, and
  component evaluators through direct `define_air_fns!` invocations. The runner
  retains only opcode decoding and generated-fill adapters; the two manual
  schema blocks and the handwritten high-product witness are gone.
- The migration composes only existing DSL operations. Canonical `split_m31`
  decompositions bind every schoolbook product limb and carry. The existing
  bitwise relation authenticates signed operand extension for MULH and MULHSU.
  No DSL extension, standalone macro, or opcode-specific wrapper was added.
- The seven generated-runner boundary cases passed in release mode, covering
  low-word wrapping, signed, signed-unsigned, and unsigned high products plus
  writes aliasing either source register.
- The four MUL/MULH/MULHSU/MULHU component fixtures passed concurrently. Both
  generated evaluators have no constraint above degree three; a forged product
  limb violated component constraints and a forged sign mask left a non-zero
  relation sum.
- The MUL and MULHU single-chunk aggregate AIR checks passed concurrently in
  2.68 seconds. An equality-qualified nextest listing selected exactly the two
  intended prove/verify tests, excluding the larger `mul_output_many` fixture.
- `/usr/bin/time -l cargo nextest run --release -p prover --test integration -j 1 ...`:
  the exact MUL and MULHU single-chunk guests proved and verified sequentially
  in 14.51 seconds with 2.01 GB maximum RSS and zero swaps.
- `cargo test --release -p air --lib -- --test-threads=12`: all 46 AIR tests
  passed. Standalone guest release clippy passed with warnings denied for
  `mul_output` and `mulhu_no_alias`.
- `/usr/bin/time -l cargo test --release -p recursion --lib profile::tests:: -- --nocapture --test-threads=7`:
  all seven generated-geometry, digest, registry, and fixed-root-wire checks
  passed. The active checkpoint has 1,681 VM tables, 1,789 sampled values, 683
  AIR instructions, protocol identifier
  `[915081946, 1206305469, 307660850, 106314972, 1803682289, 1766607321, 444822829, 1292162663]`,
  and VM AIR digest
  `[30389008, 734083804, 1159035147, 924691055, 1836516683, 2044817792, 1768787824, 1059211173]`.
- `cargo test --release -p recursion --test air_dsl_guard -- --nocapture --test-threads=5`:
  all five roster, owner, direct-DSL, and generated-component route guards
  passed after moving both exact owners and routes out of the manual schema.
- Host release clippy passed with warnings denied for `air`, `runner`, `prover`,
  and `recursion`; `prek run --all-files` passed. Implementation commit
  `2e9f1fd4` was pushed to `origin/chore/scratchpad-cleanups`.
- Recursive-root proofs remain deferred until the final opcode roster because
  this slice changes VM geometry and protocol identity but not a root
  construction boundary.

### `FELT-002 load/store checkpoint` — 2026-08-07

- `crates/air/src/opcodes/load_store.rs` is the sole source for LB, LH, LBU,
  LHU, LW, SB, SH, and SW state transitions, witness rows, constraints,
  relations, and component evaluation through a direct `define_air_fns!`
  invocation. The runner retains decode-to-argument adapters only; the manual
  schema block and handwritten load/store witnesses are gone.
- The existing felt DSL now accepts `read_word` and `write_word` statements
  whose constrained boolean address-space argument selects register or aligned
  memory access. Generated register writes preserve x0, while address-zero
  memory writes remain valid. This is an extension of `define_air_fns!`, not a
  standalone or opcode-specific macro.
- Byte and half-word lane selection, sign extension, alignment, and preservation
  of untouched store bytes are relation-bound. A canonical base-address range
  check also prevents M31 modulus wraparound from mapping an out-of-range base
  into an accepted low effective address. Unaligned traced stores publish their
  aligned word address consistently with the memory relation.
- `cargo test --release -p stwo-macros --test air_fns`: all 68 compiler, access,
  relation, malformed-row, and toy prove/verify tests passed. Ten focused
  dynamic-access cases cover both address spaces, x0, address-zero memory,
  invalid selectors, and forged rows.
- `cargo test --release -p runner generated_`: all 69 generated-execution
  boundary cases passed, including every load lane, every byte and half-word
  store lane, full words, preserved bytes, and register aliases. The aligned
  byte-write trace regression also passed independently.
- Eleven exact load/store component and adversarial cases passed concurrently;
  changing a load result or an untouched store limb violated generated
  constraints. `cargo test --release -p air --lib` passed all 46 AIR tests.
- The exact single-chunk aggregate AIR check passed in 2.61 seconds.
  `/usr/bin/time -l cargo nextest run --release -p prover --test integration -j 1 -E 'test(=load_store_single_chunk_proves_and_verifies)'`
  proved and verified the proof-capable load/store guest in 6.803 seconds with
  2.03 GB maximum RSS and zero swaps.
- All seven generated-geometry, digest, registry, and fixed-root-wire profile
  tests passed. The active checkpoint has 1,726 VM tables, 1,834 sampled values,
  695 AIR instructions, protocol identifier
  `[466445823, 1367009901, 1596720998, 1043908003, 1382761831, 1599587195, 1994327166, 195567491]`,
  and VM AIR digest
  `[440386542, 1501448090, 1399437031, 1738029001, 951731387, 970859645, 942115080, 1256533305]`.
- `cargo test --release -p recursion --test air_dsl_guard -- --nocapture --test-threads=1`
  passed all five exact-roster, owner, direct-DSL, and generated-route guards.
  Host and guest release clippy passed with warnings denied; the
  dependency-inclusive host command separately reports two existing warnings in
  `external/stwo`. Repository and commit hooks passed.
- Implementation commit `273cc005` was pushed to
  `origin/chore/scratchpad-cleanups`. Recursive-root proofs remain deferred
  until division freezes the final opcode roster.

### `FELT-002 division checkpoint` — 2026-08-07

- `crates/air/src/opcodes/div.rs` is the sole source for DIV, DIVU, REM, and
  REMU state transitions, witness rows, constraints, relations, and component
  evaluation through a direct `define_air_fns!` invocation. The runner now
  supplies only the decoded one-hot tuple; the handwritten division witness, M31
  inverse helper, manual schema block, and bare component route are gone.
- The existing felt DSL gained one reusable `divrem_u32` witness intrinsic. It
  commits quotient, remainder, zero-divisor, zero-remainder, overflow, and
  inverse columns but adds no hidden soundness rule. The felt function binds
  them through canonical byte ranges, exact signed 64-bit product-plus-remainder
  equality, absolute-remainder comparison, divide-by-zero behavior, and the
  `INT_MIN / -1` overflow case. No standalone or opcode-specific macro exists.
- `cargo test --release -p stwo-macros --test air_fns -- --test-threads=12`
  passed all 75 compiler, access, intrinsic, relation, malformed-row, and toy
  proof tests. Seven focused division-intrinsic cases cover signed quotients and
  remainders, unsigned maxima, zero divisors, zero remainders, and overflow.
- The twelve direct runner boundaries passed concurrently in 0.00 seconds after
  release compilation. They cover every sign combination, divide-by-zero, signed
  overflow, unsigned maxima, and destination aliases of both sources.
- The four opcode component fixtures and the range-check fixture passed
  concurrently in 2.62 seconds. The generated evaluator has no constraint above
  degree three; separate quotient and remainder corruptions both violated its
  local constraints.
- `cargo test --release -p prover --test max_mul test_div_edge_cases_satisfy_aggregate_constraints -- --exact --test-threads=1`
  closed the aggregate relations for the exact division edge-case chunk in 5.38
  seconds after release linking.
- `/usr/bin/time -l cargo test --release -p prover --test max_mul test_full_proof_div_edge_cases -- --exact --test-threads=1`
  proved and verified that same single chunk in 6.69 seconds with 2.046 GB
  maximum RSS and zero swaps.
- `/usr/bin/time -l cargo test --release -p recursion --lib profile::tests:: -- --nocapture --test-threads=7`
  passed all seven generated-geometry, digest, registry, and fixed-root-wire
  checks. The test body took 0.36 seconds; release compilation took 332.09
  seconds with 3.18 GB maximum RSS and zero swaps. The final opcode roster has
  1,905 VM tables, 2,013 sampled values, 787 AIR instructions, protocol
  identifier
  `[1201321936, 1233882972, 279865999, 1954284523, 1154633417, 1357347584, 450458594, 1504555888]`,
  and VM AIR digest
  `[989155288, 580703196, 976117667, 521366381, 1764914922, 1795063835, 1935043607, 1312613651]`.
- `cargo test --release -p recursion --test air_dsl_guard -- --nocapture --test-threads=6`
  passed all six roster, owner, direct-DSL, component-route, and
  no-manual-runner guards. Host release clippy passed with warnings denied, and
  repository plus commit hooks passed.
- Implementation commit `04b6dc6b` was pushed to
  `origin/chore/scratchpad-cleanups`. The final manifest is frozen; recursive
  root conformance is now the active gate.

## Project finish line

The project is complete only when all tasks are `[done]`, one application
statement and one root proof verify the final execution without descendant
proofs, root proof size is constant across supported segment counts, every AIR
reachable from recursion uses an accepted macro DSL, and every current-state or
performance claim is backed by checked-in release evidence.
