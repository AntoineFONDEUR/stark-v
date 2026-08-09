//! Fibonacci proving benchmark.
//!
//! Parameterized on:
//! - `FIB_N`: Fibonacci input size (const generic)
//! - `par_iter`: Number of parallel proving iterations (args)
//!
//! The benchmark table shows throughput in cycles/sec (the "items/sec" column).
//!
//! Usage:
//! ```bash
//! cargo bench --release --package prover --bench fibonacci --features parallel
//! ```

use divan::counter::ItemsCount;
use prover::e2e::{ensure_guest_built, guest_bin_dir};
use prover::{print_enabled_features, prove_rv32im};
use rayon::iter::{IntoParallelIterator, ParallelIterator};
use runner::run_with_input;
use stwo::core::fri::FriConfig;
use stwo::core::pcs::PcsConfig;

fn main() {
    divan::main();
}

const FIB_N: &[u32] = &[500_000, 750_000, 1_000_000];

#[divan::bench(consts = FIB_N, args = [8, 10, 12], sample_count = 1)]
fn bench_fibonacci<const N: u32>(bencher: divan::Bencher, par_iter: usize) {
    print_enabled_features();

    // Setup: build guest, load ELF
    ensure_guest_built();
    let elf_path = guest_bin_dir().join("fib_input");
    let elf_bytes = std::fs::read(&elf_path).expect("Failed to read fib_input ELF");
    let input = N.to_le_bytes();

    // Run once to get cycle count
    let test_run =
        run_with_input(&elf_bytes, &input, 100_000_000).expect("Failed to run fib_input");
    let cycles = test_run.cycles;

    // Total cycles processed per benchmark iteration
    let total_cycles = cycles * par_iter as u64;

    let config = PcsConfig {
        pow_bits: 24,
        fri_config: FriConfig::new(0, 1, 70, 1),
        lifting_log_size: None,
    };
    // Preprocessing is a cached artifact shared across proofs; keep it out of
    // the timed section so the bench measures proving, not preprocessing.
    let preprocessing = prover::preprocess(config);

    bencher
        // Report cycles as throughput counter - divan will show cycles/sec
        .counter(ItemsCount::new(total_cycles as usize))
        .bench(|| {
            // Run VM and prove in parallel - each iteration gets its own RunResult
            let proofs: Vec<_> = (0..par_iter)
                .into_par_iter()
                .map(|_| {
                    let run_result = run_with_input(&elf_bytes, &input, 100_000_000)
                        .expect("Failed to run fib_input");
                    prove_rv32im(run_result, config, &preprocessing)
                })
                .collect();

            divan::black_box(proofs)
        });
}
