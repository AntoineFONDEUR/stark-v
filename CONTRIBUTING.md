# Contributing to stark-v

Thanks for your interest in stark-v. This document covers the practical bits:
how to build, test, and submit a change.

## Scope

stark-v is a RISC-V (RV32IM) zkVM aimed at client-side verifiable Ethereum.
Contributions that move the project toward that goal are especially welcome:

- New RV32IM opcode AIRs or constraint improvements
- Guest-side optimizations for Ethereum state transition workloads
- Prover performance work (parallelism, memory, allocator tuning)
- Verifier ergonomics on resource-constrained targets
- Bug fixes, tests, documentation, examples

If you are unsure whether a change is in scope, open an issue first to discuss.

## Development setup

stark-v pins a specific Rust nightly via `rust-toolchain.toml`. Stwo lives as a
git submodule under `external/`.

```bash
git clone --recursive https://github.com/starkware-libs/stark-v.git
cd stark-v
cargo build --release --workspace
cargo nextest run --release --workspace --profile ci
```

The `ci` nextest profile (`.config/nextest.toml`) excludes the heavy-proofs
recursion modules, whose tests each need tens of GiB and hours of proving. Run
those only on a large host via the default profile, which serializes them:
`cargo nextest run --release --workspace --test-threads 4`.

If you cloned without `--recursive`:

```bash
git submodule update --init --recursive
```

## Pre-commit hooks

The repository ships pre-commit hooks (managed via `prek`). They run formatting,
linting, spell-check, and a guard that prevents accidental edits to `external/`.
Run them locally before pushing:

```bash
prek run --all-files
```

Pre-commit hooks are part of the contract — please do not bypass them with
`--no-verify`. If a hook complains, fix the underlying issue rather than
disabling the rule.

## Coding guidelines

- **Tests.** New code needs unit tests for the logic it introduces. For
  cross-cutting changes, add an integration test under the crate that owns the
  behavior. Use `rstest` so each data point is a named test rather than a loop
  over fixtures.
- **Comments.** Comments describe what the code _is_, not what you _did_. Don't
  narrate the edit history, the PR, or what the function "used to do" — that
  belongs in the commit message.
- **Logging.** Use the `tracing` crate (already a workspace dependency); never
  `println!` in library code.
- **Module docstrings.** Each new module should start with a `//!` doc comment
  explaining its responsibility.

## Submitting a change

1. Fork the repository and create a topic branch.
2. Make your change, with tests.
3. Run `prek run --all-files` and
   `cargo nextest run --release --workspace --profile ci` (plus the heavy
   default profile on a large host when touching recursion proving).
4. Open a pull request. In the description, explain _why_ the change is needed;
   the diff already shows the _what_.
5. CI will run the same checks on a clean machine. If it fails on something that
   passed locally, suspect environment drift (toolchain, submodule state) before
   retrying.

Small, focused PRs land faster than large ones. If a change is large by
necessity, please split out preparatory refactors into separate commits.

## Security issues

Please do not file public issues for vulnerabilities. See
[SECURITY.md](SECURITY.md) for the disclosure process.

## License

By contributing, you agree that your contributions will be dual-licensed under
the Apache-2.0 and MIT licenses, matching the rest of the repository.
