//! CLI for benchmarking stark-v proving and verification.
//!
//! This binary provides commands for:
//! - Running guest programs and generating proofs
//! - Verifying proofs (in the same process)
//! - Measuring proof and preprocessing sizes

use clap::{Parser, Subcommand, ValueEnum};
use prover::{prove_rv32im_with_backend, verify_rv32im, BackendReport, PcsConfig, ProverBackend};
use runner::run_with_input;
use serde::{Deserialize, Serialize};
use std::fs;
use std::path::PathBuf;
use tracing::{error, info};

/// stark-v benchmark CLI
#[derive(Parser)]
#[command(name = "stark-v-bench", version, about)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Run a guest program, generate a proof, and verify it
    Prove {
        /// Path to the ELF file to execute
        #[arg(long)]
        elf: PathBuf,

        /// Path to input data file (raw bytes, optional)
        #[arg(long)]
        input: Option<PathBuf>,

        /// Maximum number of cycles before aborting
        #[arg(long, default_value_t = 100_000_000)]
        max_cycles: u64,

        /// Output path for metrics JSON
        #[arg(long)]
        metrics_out: Option<PathBuf>,

        /// Skip verification after proving
        #[arg(long)]
        skip_verify: bool,

        /// Proving backend policy
        #[arg(long, value_enum, default_value_t = BackendArg::Simd)]
        backend: BackendArg,
    },

    /// Just run the VM without proving (for timing VM execution separately)
    Run {
        /// Path to the ELF file to execute
        #[arg(long)]
        elf: PathBuf,

        /// Path to input data file (raw bytes, optional)
        #[arg(long)]
        input: Option<PathBuf>,

        /// Maximum number of cycles before aborting
        #[arg(long, default_value_t = 100_000_000)]
        max_cycles: u64,

        /// Output path for metrics JSON
        #[arg(long)]
        metrics_out: Option<PathBuf>,
    },

    /// Run guest program, prove, and verify (full benchmark)
    Bench {
        /// Path to the ELF file to execute
        #[arg(long)]
        elf: PathBuf,

        /// Path to input data file (raw bytes, optional)
        #[arg(long)]
        input: Option<PathBuf>,

        /// Maximum number of cycles before aborting
        #[arg(long, default_value_t = 100_000_000)]
        max_cycles: u64,

        /// Output path for metrics JSON
        #[arg(long)]
        metrics_out: Option<PathBuf>,

        /// Proving backend policy
        #[arg(long, value_enum, default_value_t = BackendArg::Simd)]
        backend: BackendArg,
    },

    /// Measure sizes (ELF as preprocessing size)
    Measure {
        /// Path to the ELF file (for preprocessing size)
        #[arg(long)]
        elf: PathBuf,

        /// Proof size in bytes (passed as argument since we can't serialize proofs)
        #[arg(long, default_value_t = 0)]
        proof_size: usize,

        /// Output path for sizes JSON
        #[arg(long)]
        output: PathBuf,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, ValueEnum)]
enum BackendArg {
    Simd,
    MetalPrefer,
    #[value(name = "metal-required")]
    MetalRequired,
}

impl From<BackendArg> for ProverBackend {
    fn from(backend: BackendArg) -> Self {
        match backend {
            BackendArg::Simd => Self::Simd,
            BackendArg::MetalPrefer => Self::MetalPrefer,
            BackendArg::MetalRequired => Self::MetalParticipationRequired,
        }
    }
}

/// Metrics collected during proving
#[derive(Debug, Clone, Serialize, Deserialize)]
struct ProveMetrics {
    /// Number of VM cycles executed
    cycles: u64,
    /// Exact postcard-serialized proof size in bytes
    proof_size_bytes: usize,
    /// Whether verification succeeded
    verified: bool,
    /// Requested backend and observed dispatch evidence
    backend: BackendReport,
}

/// Metrics collected during VM run only
#[derive(Debug, Clone, Serialize, Deserialize)]
struct RunMetrics {
    /// Number of VM cycles executed
    cycles: u64,
    /// Output length in bytes (if any)
    output_len: Option<usize>,
}

/// Size measurements
#[derive(Debug, Clone, Serialize, Deserialize)]
struct SizeMetrics {
    /// Proof size in bytes
    proof_size: usize,
    /// Preprocessing size in bytes (ELF size for zkVM)
    preprocessing_size: usize,
}

fn main() {
    tracing_subscriber::fmt()
        .with_env_filter(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| tracing_subscriber::EnvFilter::new("info")),
        )
        .init();

    let cli = Cli::parse();

    match cli.command {
        Command::Prove {
            elf,
            input,
            max_cycles,
            metrics_out,
            skip_verify,
            backend,
        } => {
            run_prove(
                &elf,
                input.as_ref(),
                max_cycles,
                metrics_out.as_ref(),
                skip_verify,
                backend,
            );
        }

        Command::Run {
            elf,
            input,
            max_cycles,
            metrics_out,
        } => {
            run_only(&elf, input.as_ref(), max_cycles, metrics_out.as_ref());
        }

        Command::Bench {
            elf,
            input,
            max_cycles,
            metrics_out,
            backend,
        } => {
            run_prove(
                &elf,
                input.as_ref(),
                max_cycles,
                metrics_out.as_ref(),
                false,
                backend,
            );
        }

        Command::Measure {
            elf,
            proof_size,
            output,
        } => {
            // Measure ELF size as preprocessing size
            let elf_bytes = match fs::read(&elf) {
                Ok(bytes) => bytes,
                Err(e) => {
                    error!(path = ?elf, "Failed to read ELF file: {e}");
                    std::process::exit(1);
                }
            };
            let preprocessing_size = elf_bytes.len();
            info!("ELF (preprocessing) size: {} bytes", preprocessing_size);

            let sizes = SizeMetrics {
                proof_size,
                preprocessing_size,
            };

            let json = serde_json::to_string_pretty(&sizes).expect("Failed to serialize sizes");
            fs::write(&output, json).expect("Failed to write sizes");
            info!("Sizes saved to {:?}", output);
        }
    }
}

fn run_only(
    elf: &PathBuf,
    input: Option<&PathBuf>,
    max_cycles: u64,
    metrics_out: Option<&PathBuf>,
) {
    // Load ELF
    let elf_bytes = match fs::read(elf) {
        Ok(bytes) => bytes,
        Err(e) => {
            error!(path = ?elf, "Failed to read ELF file: {e}");
            std::process::exit(1);
        }
    };

    // Load input if provided
    let input_bytes = match input {
        Some(path) => match fs::read(path) {
            Ok(bytes) => bytes,
            Err(e) => {
                error!(path = ?path, "Failed to read input file: {e}");
                std::process::exit(1);
            }
        },
        None => vec![],
    };

    // Run the guest program
    info!("Running guest program...");
    let run_result = match run_with_input(&elf_bytes, &input_bytes, max_cycles) {
        Ok(result) => result,
        Err(e) => {
            error!("Failed to run guest program: {e}");
            std::process::exit(1);
        }
    };

    let cycles = run_result.cycles;
    let output_len = run_result.output.as_ref().map(|o| o.len());
    info!("Guest program completed with {} cycles", cycles);

    let metrics = RunMetrics { cycles, output_len };

    if let Some(metrics_path) = metrics_out {
        let json = serde_json::to_string_pretty(&metrics).expect("Failed to serialize metrics");
        fs::write(metrics_path, json).expect("Failed to write metrics");
        info!("Metrics saved to {:?}", metrics_path);
    } else {
        println!("{}", serde_json::to_string_pretty(&metrics).unwrap());
    }
}

fn run_prove(
    elf: &PathBuf,
    input: Option<&PathBuf>,
    max_cycles: u64,
    metrics_out: Option<&PathBuf>,
    skip_verify: bool,
    backend: BackendArg,
) {
    // Load ELF
    let elf_bytes = match fs::read(elf) {
        Ok(bytes) => bytes,
        Err(e) => {
            error!(path = ?elf, "Failed to read ELF file: {e}");
            std::process::exit(1);
        }
    };

    // Load input if provided
    let input_bytes = match input {
        Some(path) => match fs::read(path) {
            Ok(bytes) => bytes,
            Err(e) => {
                error!(path = ?path, "Failed to read input file: {e}");
                std::process::exit(1);
            }
        },
        None => vec![],
    };

    // Run the guest program
    info!("Running guest program...");
    let run_result = match run_with_input(&elf_bytes, &input_bytes, max_cycles) {
        Ok(result) => result,
        Err(e) => {
            error!("Failed to run guest program: {e}");
            std::process::exit(1);
        }
    };

    let cycles = run_result.cycles;
    info!("Guest program completed with {} cycles", cycles);

    // Generate proof
    let config = PcsConfig::default();

    info!("Preprocessing...");
    let preprocessed = prover::preprocess(config);

    info!("Generating proof...");
    let outcome = match prove_rv32im_with_backend(run_result, config, &preprocessed, backend.into())
    {
        Ok(outcome) => outcome,
        Err(error) => {
            error!("Proof generation failed: {error}");
            std::process::exit(1);
        }
    };
    let proof_size_bytes = postcard::to_allocvec(&outcome.proof)
        .expect("postcard proof serialization must succeed")
        .len();
    let backend_report = outcome.backend_report;
    let proof = outcome.proof;

    // Verify if not skipped
    let verified = if !skip_verify {
        info!("Verifying proof...");
        match verify_rv32im(proof, config, &preprocessed) {
            Ok(()) => {
                info!("Proof verified successfully");
                true
            }
            Err(e) => {
                error!("Proof verification failed: {e}");
                false
            }
        }
    } else {
        info!("Skipping verification");
        false
    };

    // Output metrics
    let metrics = ProveMetrics {
        cycles,
        proof_size_bytes,
        verified,
        backend: backend_report,
    };

    if let Some(metrics_path) = metrics_out {
        let json = serde_json::to_string_pretty(&metrics).expect("Failed to serialize metrics");
        fs::write(metrics_path, json).expect("Failed to write metrics");
        info!("Metrics saved to {:?}", metrics_path);
    } else {
        println!("{}", serde_json::to_string_pretty(&metrics).unwrap());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn selected_backend(args: &[&str]) -> BackendArg {
        let cli = Cli::try_parse_from(args).expect("CLI should parse");
        match cli.command {
            Command::Prove { backend, .. } | Command::Bench { backend, .. } => backend,
            _ => panic!("expected proving command"),
        }
    }

    #[test]
    fn prove_backend_defaults_to_simd() {
        assert_eq!(
            selected_backend(&["stark-v-bench", "prove", "--elf", "guest.elf"]),
            BackendArg::Simd
        );
        assert_eq!(
            selected_backend(&["stark-v-bench", "bench", "--elf", "guest.elf"]),
            BackendArg::Simd
        );
    }

    #[test]
    fn prove_backend_parses_all_policies() {
        for (argument, expected) in [
            ("simd", BackendArg::Simd),
            ("metal-prefer", BackendArg::MetalPrefer),
            ("metal-required", BackendArg::MetalRequired),
        ] {
            assert_eq!(
                selected_backend(&[
                    "stark-v-bench",
                    "prove",
                    "--elf",
                    "guest.elf",
                    "--backend",
                    argument,
                ]),
                expected
            );
            assert_eq!(
                selected_backend(&[
                    "stark-v-bench",
                    "bench",
                    "--elf",
                    "guest.elf",
                    "--backend",
                    argument,
                ]),
                expected
            );
        }
    }

    #[test]
    fn backend_arguments_map_to_core_policy() {
        assert_eq!(ProverBackend::from(BackendArg::Simd), ProverBackend::Simd);
        assert_eq!(
            ProverBackend::from(BackendArg::MetalPrefer),
            ProverBackend::MetalPrefer
        );
        assert_eq!(
            ProverBackend::from(BackendArg::MetalRequired),
            ProverBackend::MetalParticipationRequired
        );
    }

    #[test]
    fn prove_metrics_serialize_exact_size_and_backend_evidence() {
        let metrics = ProveMetrics {
            cycles: 42,
            proof_size_bytes: 1234,
            verified: true,
            backend: BackendReport {
                requested: ProverBackend::MetalPrefer,
                actual: prover::ActualProverBackend::CpuHybridMetal,
                fallback_reason: None,
                device_name: Some("Test GPU".to_owned()),
                successful_submissions: 7,
                failed_submissions: 0,
            },
        };

        let json = serde_json::to_value(metrics).expect("metrics should serialize");
        assert_eq!(json["proof_size_bytes"], 1234);
        assert_eq!(json["backend"]["requested"], "MetalPrefer");
        assert_eq!(json["backend"]["actual"], "CpuHybridMetal");
        assert_eq!(json["backend"]["device_name"], "Test GPU");
        assert_eq!(json["backend"]["successful_submissions"], 7);
        assert_eq!(json["backend"]["failed_submissions"], 0);
    }
}
