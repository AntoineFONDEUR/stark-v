//! CLI for benchmarking stark-v proving and verification.
//!
//! This binary provides commands for:
//! - Running guest programs and generating proofs
//! - Verifying proofs (in the same process)
//! - Measuring proof and preprocessing sizes

use clap::{Parser, Subcommand};
use prover::{PcsConfig, prove_rv32im, verify_rv32im};
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
    },

    /// Measure sizes (ELF as preprocessing size)
    Measure {
        /// Path to the ELF file (for preprocessing size)
        #[arg(long)]
        elf: PathBuf,

        /// Proof size in bytes, as reported by `prove`'s `proof_size_estimate`
        /// metric (passed through so external harnesses can combine the two
        /// measurements without re-proving)
        #[arg(long, default_value_t = 0)]
        proof_size: usize,

        /// Output path for sizes JSON
        #[arg(long)]
        output: PathBuf,
    },
}

/// Metrics collected during proving
#[derive(Debug, Clone, Serialize, Deserialize)]
struct ProveMetrics {
    /// Number of VM cycles executed
    cycles: u64,
    /// Size of the proof in bytes (estimated)
    proof_size_estimate: usize,
    /// Whether verification succeeded
    verified: bool,
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
        } => {
            run_prove(
                &elf,
                input.as_ref(),
                max_cycles,
                metrics_out.as_ref(),
                skip_verify,
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
        } => {
            run_prove(
                &elf,
                input.as_ref(),
                max_cycles,
                metrics_out.as_ref(),
                false,
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
    let proof = prove_rv32im(run_result, config, &preprocessed);

    let proof_size_estimate =
        proof.vm.stark_proof.size_estimate() + proof.poseidon2.stark_proof.size_estimate();

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
        proof_size_estimate,
        verified,
    };

    if let Some(metrics_path) = metrics_out {
        let json = serde_json::to_string_pretty(&metrics).expect("Failed to serialize metrics");
        fs::write(metrics_path, json).expect("Failed to write metrics");
        info!("Metrics saved to {:?}", metrics_path);
    } else {
        println!("{}", serde_json::to_string_pretty(&metrics).unwrap());
    }
}
