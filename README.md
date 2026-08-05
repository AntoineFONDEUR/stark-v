# stark-v

A RISC-V zkVM for client-side proving.

stark-v generates STARK proofs for the RV32IM instructions and guest ABI that
the runner and AIR currently support.

> :warning: This is a work in progress and not yet ready for production.

## Architecture

stark-v uses [stwo](https://github.com/starkware-libs/stwo) Circle STARKs and
LogUp relations to prove RV32IM execution traces. The active VM AIR schema in
`crates/air/src/schema.rs` is declared through `define_air!`; Poseidon2 is
declared through `define_air_fns!`. Those definitions generate trace columns,
constraints, witness plumbing, relations, and component metadata used by the
runner and prover.

The main workspace boundaries are:

- `air`: canonical field words, instruction decoding, VM AIR schema,
  preprocessed tables, and Poseidon2;
- `runner`: RV32IM execution, memory layout, trace filling, and segmentation;
- `prover`: preprocessing and single-segment STARK proving and verification;
- `continuation`: host-side verification of a non-empty chain containing one
  proof per segment; proof size and verification work are linear in segment
  count;
- `recursion`: the universal recursive-verifier AIR plus manifest-bound outer
  proving and verification for segment leaves, empty leaves, and two-child
  binary parents; tree construction and the application root API remain
  unfinished;
- `sdk` and `guest-lib`: host and guest interfaces.

### Memory Layout

The guest program uses a fixed memory layout defined in
`guest/guest-bin/linker.ld`:

```text
Address Range           Region          Size
─────────────────────────────────────────────────
0x00000400 - 0x000FFFFF  TEXT (rx)      ~1 MB   Program code
0x00100000 - 0x00100FFF  INPUT          4 KB    Input buffer
0x00101000              HALT_FLAG       4 B     Halt detection
0x00101004              OUTPUT_LEN      4 B     Output length
0x00101008 - 0x001FFFBF  OUTPUT         ~1 MB   Output buffer
0x001FFFC0 - 0x001FFFFF  STACK          1 KB    Stack (grows down)
0x00200000 - 0x002FFFFF  DATA (rw)      1 MB    Heap/static data
```

### Documentation status

- [RV32IM AIR architecture](docs/airs.md) describes the active system and points
  to source truth.
- [Recursive proving](docs/recursion.md) distinguishes current components from
  the remaining tree and constant-size root API work.
- [Project roadmap](docs/roadmap.md) is the dependency-ordered finish-line task
  list and classifies current versus planned documents.
- [Felt AIR compiler](docs/felt-air-compiler.md),
  [hash precompiles](docs/precompiles.md), and
  [syscalls/output journal](docs/syscalls.md) are forward designs with explicit
  implementation status.

## Usage

### Writing a Guest Program

Create a guest binary using the `guest_main!` macro:

```rust
// guest/my-program/src/main.rs
#![no_std]
#![no_main]

guest_bin::guest_main!({
    // Your computation here
    let result = 42u32;
    result
});
```

### Proving Execution

```rust
use prover::{prove_rv32im, verify_rv32im};
use runner::run_with_input;
use stwo::core::pcs::PcsConfig;

// Load and run the guest ELF
let elf_bytes = std::fs::read("path/to/guest.elf")?;
let input = 42u32.to_le_bytes();
let run_result = run_with_input(&elf_bytes, &input, 100_000_000)?;

// Generate and verify proof
let config = PcsConfig::default();
let preprocessed = prover::preprocess(config);
let proof = prove_rv32im(run_result, config, &preprocessed);
verify_rv32im(proof, config, &preprocessed)?;
```

## Benchmarks

The benchmark measures proving throughput in kHz or MHz (thousands or millions
of RISC-V cycles per second).

### Parallelization Strategy

Two approaches are used to maximize throughput:

1. **`parallel` feature** — Intra-proof Rayon parallelism. Best for individual
   proof latency.

2. **Multiple non-parallel proofs** — Run multiple single-threaded provers in
   parallel. Based on findings from
   [rookie-numbers](https://github.com/clementwalter/rookie-numbers/), this can
   achieve higher aggregate throughput for continuation segments and, once
   recursive proving exists, independent leaves or nodes at the same tree level.

### Running Benchmarks

```bash
# Clone with submodules
git clone --recursive https://github.com/starkware-libs/stark-v.git
cd stark-v

# Non-parallel prover with parallel processes (max throughput)
cargo bench --release --package prover --bench fibonacci

# Parallel prover (faster individual proofs)
cargo bench --release --package prover --bench fibonacci --features parallel
```

Results are intentionally not copied into this document: they become stale as
the AIR and protocol change. Run the checked-in benchmark against the commit and
profile being evaluated.

## Features

- `parallel` — Enable Rayon parallelism in the prover

## Contributing

Bug reports, ideas and pull requests are welcome. See
[CONTRIBUTING.md](CONTRIBUTING.md) for the development workflow and
[SECURITY.md](SECURITY.md) for responsible disclosure of security issues.

## License

Licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or
  <http://www.apache.org/licenses/LICENSE-2.0>)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or
  <http://opensource.org/licenses/MIT>)

at your option.
