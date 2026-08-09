//! Tests for run_with_input.

use guest_lib::programs::ConstantResult;
use guest_lib::programs::fib::{FibResult, fib};
use prover::e2e::{ensure_guest_built, guest_bin_dir};
use runner::run_with_input;

#[test]
fn test_run_with_input_fib() {
    ensure_guest_built();

    let elf_path = guest_bin_dir().join("fib_input");
    let elf_bytes =
        std::fs::read(&elf_path).unwrap_or_else(|e| panic!("Failed to read {elf_path:?}: {e}"));

    for n in [5u32, 10u32] {
        let input = n.to_le_bytes();
        let result =
            run_with_input(&elf_bytes, &input, 10_000_000).expect("Failed to run fib_input");
        let output = result
            .output
            .unwrap_or_else(|| panic!("No output for fib_input({n})"));
        let decoded: FibResult = postcard::from_bytes(&output).expect("Failed to decode output");
        assert_eq!(decoded, fib(n));
    }
}

/// The host publishes the actual input length at `__input_len`, and the guest
/// reads it back — so `read_input_len()` reflects the bytes passed, not the
/// buffer capacity.
#[test]
fn test_input_len_is_published_to_the_guest() {
    ensure_guest_built();

    let elf_path = guest_bin_dir().join("input_len_echo");
    let elf_bytes =
        std::fs::read(&elf_path).unwrap_or_else(|e| panic!("Failed to read {elf_path:?}: {e}"));

    let input = [0u8; 13];
    let result =
        run_with_input(&elf_bytes, &input, 10_000_000).expect("Failed to run input_len_echo");
    let output = result.output.expect("no output for input_len_echo");
    let decoded: ConstantResult = postcard::from_bytes(&output).expect("Failed to decode output");
    assert_eq!(decoded.value, 13);
}
