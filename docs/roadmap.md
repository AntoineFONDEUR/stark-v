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
  - `crates/recursion` contains the active universal verifier design without a
    `v2` namespace or abandoned aggregation wrappers.
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
- `[active] PRO-001` Freeze the first recursive protocol profile.
- `[pending] REC-001` Adapt a real VM proof to the recursive leaf wire.
- `[pending] REC-002` Build the universal trace assembler.
- `[pending] REC-003` Close the segment-leaf branch end to end.
- `[pending] REC-004` Close the canonical empty-leaf branch.
- `[pending] REC-005` Implement the outer recursion prover and verifier.
- `[pending] REC-006` Verify a real recursion proof as a child.
- `[pending] REC-007` Prove the two-child binary branch.
- `[pending] REC-008` Build the recursive tree driver.
- `[pending] REC-009` Expose and bind the application root API.
- `[pending] REC-010` Demonstrate constant root-proof size.
- `[pending] PRE-001` Prepare the hash-precompile proof split for production.
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
2. Preserve exact native-verifier absorption order and domain separation.
3. Test changed, missing, duplicated, and reordered payloads independently.

Done when all nine components are macro-generated, native and AIR transcript
vectors agree, the manual inventory is 18, and the milestone is tested,
committed, and pushed.

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

### `[active] PRO-001` Freeze the protocol profile

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

### `[pending] REC-001` Real VM-proof adapter

Dependencies: `PRO-001`.

Required work:

1. Convert `prover::Proof<Poseidon2M31Hash>` and authenticated public data into
   the fixed segment-leaf wire.
2. Derive the exact height-zero span from the public claim, job context, segment
   index, and cycle interval.
3. Reject capacity overflow, non-canonical optional roots, and disagreement
   between runner metadata and authenticated proof data.

Done when a real proof round-trips and one focused test rejects each malformed
wire or metadata field.

### `[pending] REC-002` Universal trace assembler

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

### `[pending] REC-003` Segment-leaf closure

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

### `[pending] REC-004` Canonical empty leaf

Dependencies: `REC-003`.

Required work:

1. Emit the unique empty-span statement and minimal valid universal witness.
2. Constrain empty leaves to slots at or beyond the declared segment count and
   below the fixed tree capacity.
3. Constrain every inactive wire to zero.

Done when canonical padding verifies and executed-slot empties, out-of-capacity
slots, and non-zero inactive wires fail.

### `[pending] REC-005` Outer prover and verifier

Dependencies: `REC-004`.

Required work:

1. Preprocess the universal AIR for `PRO-001`.
2. Define one recursion proof artifact containing the protocol identity, parent
   statement, component claims, interaction claims, and STWO proof.
3. Prove and verify the complete roster with the Poseidon2-M31 channel.
4. Require callers to supply the expected protocol and expected statement.

Done when real segment and empty leaves produce valid recursion proofs and each
public claim or proof mutation is rejected.

### `[pending] REC-006` Recursion-child closure

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

### `[pending] REC-007` Binary node

Dependencies: `REC-006`.

Required work:

1. Materialize independent left and right child-verifier lanes with distinct
   verifier identifiers.
2. Prove equal heights, exact slot adjacency, common job identity, machine-state
   boundary equality, valid edge-claim placement, and the unique parent fold.
3. Feed the complete binary witness through `REC-005`.

Done when two valid adjacent child proofs produce one verified parent proof and
swapped, duplicated, gapped, overlapping, or mismatched children fail.

### `[pending] REC-008` Tree driver

Dependencies: `REC-007`.

Required work:

1. Segment a run and prove its VM leaves.
2. Append canonical empty leaves to the unique minimal power-of-two capacity.
3. Prove successive binary levels; parallelism is allowed only among independent
   nodes within one level.
4. Return one root proof and root statement without descendant proofs.

Done when runs with 1, 2, 3, 4, and 8 executed segments each produce one valid
root proof with the expected span.

### `[pending] REC-009` Application root API

Dependencies: `REC-008`.

Required work:

1. Accept the expected protocol, program, initial and final machine state,
   public input, public output, and total cycles.
2. Verify exactly one root proof and compare every complete-execution statement
   field before returning success.
3. Keep all multi-proof host APIs exclusively in `continuation`.

Done when the expected statement verifies and one focused test rejects each
independently changed statement field.

### `[pending] REC-010` Constant-size demonstration

Dependencies: `REC-009`.

Required work:

1. Serialize roots for every supported segment count under `PRO-001`.
2. Record root proof bytes and root-verifier operation shape independently from
   total tree-prover work.
3. Add a checked-in conformance test for equal serialized sizes and verifier
   shapes.

Done when every supported count yields exactly one root proof with identical
serialized size and root-verifier shape.

## Planned VM capabilities

These features remain project goals. They may not change the meaning of a
completed `PRO-001` profile silently: any changed roster, public claim, or proof
artifact receives a new manifest identity and repeats affected recursion
conformance tests.

### `[pending] PRE-001` Hash precompile

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

## Project finish line

The project is complete only when all tasks are `[done]`, one application
statement and one root proof verify the final execution without descendant
proofs, root proof size is constant across supported segment counts, every AIR
reachable from recursion uses an accepted macro DSL, and every current-state or
performance claim is backed by checked-in release evidence.
