//! Recursive-pipeline benchmark: proves one guest execution through the
//! universal 2-to-1 recursion tree and reports per-stage wall times, the
//! serialized root proof size, and root verification time as JSON metrics.
//!
//! Stage times come from the recursion crate's own tracing spans
//! (`prove_segment_leaves`, `prove_padding_leaves`, `prove_tree_level`,
//! `prove_root_node`, `verify_recursive_root`), accumulated by
//! [`SpanTimings`]; leaf throughput is executed cycles divided by the leaf
//! stage's wall time.

use std::fs;
use std::path::PathBuf;
use std::sync::{Arc, Mutex};
use std::time::Instant;

use prover::poseidon2_channel::Poseidon2M31MerkleChannel;
use serde::Serialize;
use tracing::field::{Field, Visit};
use tracing::span::{Attributes, Id};
use tracing::{error, info};
use tracing_subscriber::Layer;
use tracing_subscriber::layer::Context;
use tracing_subscriber::registry::LookupSpan;

/// One closed recursion-pipeline span with its recorded numeric fields.
#[derive(Debug, Clone, Serialize)]
pub struct StageTiming {
    pub stage: &'static str,
    pub fields: Vec<(String, u64)>,
    pub seconds: f64,
}

/// Shared sink for the recursion pipeline's stage spans, in close order.
#[derive(Clone, Default)]
pub struct SpanTimings(Arc<Mutex<Vec<StageTiming>>>);

impl SpanTimings {
    fn take(&self) -> Vec<StageTiming> {
        std::mem::take(&mut self.0.lock().expect("timing sink is never poisoned"))
    }
}

/// Numeric span fields (segment, cycle, and node counts) as key/value pairs.
#[derive(Default)]
struct NumericFields(Vec<(String, u64)>);

impl Visit for NumericFields {
    fn record_u64(&mut self, field: &Field, value: u64) {
        self.0.push((field.name().to_owned(), value));
    }

    fn record_i64(&mut self, field: &Field, value: i64) {
        if let Ok(value) = u64::try_from(value) {
            self.0.push((field.name().to_owned(), value));
        }
    }

    fn record_debug(&mut self, _field: &Field, _value: &dyn std::fmt::Debug) {}
}

/// Span data stored at creation so the close handler can emit one timing.
struct StageStart {
    at: Instant,
    fields: Vec<(String, u64)>,
}

/// Tracing layer that turns every closed span into a [`StageTiming`].
pub struct SpanTimingLayer {
    sink: SpanTimings,
}

impl SpanTimingLayer {
    pub const fn new(sink: SpanTimings) -> Self {
        Self { sink }
    }
}

impl<S> Layer<S> for SpanTimingLayer
where
    S: tracing::Subscriber + for<'a> LookupSpan<'a>,
{
    fn on_new_span(&self, attrs: &Attributes<'_>, id: &Id, ctx: Context<'_, S>) {
        let span = ctx.span(id).expect("new span is registered");
        let mut fields = NumericFields::default();
        attrs.record(&mut fields);
        span.extensions_mut().insert(StageStart {
            at: Instant::now(),
            fields: fields.0,
        });
    }

    fn on_close(&self, id: Id, ctx: Context<'_, S>) {
        let span = ctx.span(&id).expect("closed span is registered");
        let Some(start) = span.extensions_mut().remove::<StageStart>() else {
            return;
        };
        self.sink
            .0
            .lock()
            .expect("timing sink is never poisoned")
            .push(StageTiming {
                stage: span.metadata().name(),
                fields: start.fields,
                seconds: start.at.elapsed().as_secs_f64(),
            });
    }
}

/// Metrics for one complete recursive proving and verification run.
#[derive(Debug, Serialize)]
struct RecursionMetrics {
    segments: usize,
    total_cycles: u64,
    vm_preprocessing_seconds: f64,
    recursion_preprocessing_seconds: f64,
    prove_seconds: f64,
    stages: Vec<StageTiming>,
    leaf_stage_seconds: Option<f64>,
    leaf_throughput_cycles_per_second: Option<f64>,
    root_proof_bytes: usize,
    encode_seconds: f64,
    verify_seconds: f64,
    verified: bool,
}

/// Segmentation selector: fixed cycle budget, table-row capacity, or one segment.
pub struct Segmentation {
    pub segment_cycles: Option<u32>,
    pub max_rows: Option<u32>,
}

pub fn run_recursion_bench(
    elf: &PathBuf,
    input: Option<&PathBuf>,
    segmentation: &Segmentation,
    max_cycles: u64,
    metrics_out: Option<&PathBuf>,
    timings: &SpanTimings,
) {
    let elf_bytes = match fs::read(elf) {
        Ok(bytes) => bytes,
        Err(e) => {
            error!(path = ?elf, "Failed to read ELF file: {e}");
            std::process::exit(1);
        }
    };
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

    info!("Running guest program...");
    let run_results = match (segmentation.segment_cycles, segmentation.max_rows) {
        (Some(_), Some(_)) => {
            error!("--segment-cycles and --max-rows are mutually exclusive");
            std::process::exit(1);
        }
        (None, Some(max_rows)) => {
            runner::run_segments_by_capacity(&elf_bytes, &input_bytes, max_rows, max_cycles)
        }
        (segment_cycles, None) => {
            runner::run_segments_with_input(&elf_bytes, &input_bytes, segment_cycles, max_cycles)
        }
    };
    let run_results = match run_results {
        Ok(results) => results,
        Err(e) => {
            error!("Failed to run guest program: {e}");
            std::process::exit(1);
        }
    };
    let segments = run_results.len();
    let total_cycles = run_results.iter().map(|segment| segment.cycles).sum();
    info!("Guest executed {total_cycles} cycles over {segments} segment(s)");

    let profile = match recursion::profile::frozen_protocol_profile() {
        Ok(profile) => profile,
        Err(e) => {
            error!("Invalid frozen protocol profile: {e}");
            std::process::exit(1);
        }
    };
    let started = Instant::now();
    let vm_preprocessing = prover::preprocess_with_channel::<Poseidon2M31MerkleChannel>(
        profile.manifest().vm_pcs().config(),
    );
    let vm_preprocessing_seconds = started.elapsed().as_secs_f64();
    let started = Instant::now();
    let preprocessing = match recursion::recursive_proof::preprocess_recursion(&profile) {
        Ok(preprocessing) => preprocessing,
        Err(e) => {
            error!("Recursion preprocessing failed: {e}");
            std::process::exit(1);
        }
    };
    let recursion_preprocessing_seconds = started.elapsed().as_secs_f64();
    info!(
        "Preprocessed VM in {vm_preprocessing_seconds:.2}s and recursion in {recursion_preprocessing_seconds:.2}s"
    );

    let started = Instant::now();
    let tree = match recursion::tree::prove_recursive_segments(
        &profile,
        &vm_preprocessing,
        &preprocessing,
        run_results,
    ) {
        Ok(tree) => tree,
        Err(e) => {
            error!("Recursive proving failed: {e}");
            std::process::exit(1);
        }
    };
    let prove_seconds = started.elapsed().as_secs_f64();
    info!("Proved the recursive root in {prove_seconds:.2}s");

    let (root_statement, proof) = tree.into_parts();
    let started = Instant::now();
    let root_proof_bytes = match recursion::root::encode_recursive_root(&profile, &proof) {
        Ok(bytes) => bytes.as_bytes().len(),
        Err(e) => {
            error!("Root encoding failed: {e}");
            std::process::exit(1);
        }
    };
    let encode_seconds = started.elapsed().as_secs_f64();
    info!("Encoded the root proof to {root_proof_bytes} bytes in {encode_seconds:.2}s");

    let started = Instant::now();
    let verified = match recursion::root::verify_recursive_root(
        &profile,
        &preprocessing,
        root_statement.complete_execution(),
        proof,
    ) {
        Ok(()) => true,
        Err(e) => {
            error!("Root verification failed: {e}");
            false
        }
    };
    let verify_seconds = started.elapsed().as_secs_f64();
    info!("Verified the root proof in {verify_seconds:.2}s");

    let stages = timings.take();
    let leaf_stage_seconds = stages
        .iter()
        .find(|stage| stage.stage == "prove_segment_leaves")
        .map(|stage| stage.seconds);
    let metrics = RecursionMetrics {
        segments,
        total_cycles,
        vm_preprocessing_seconds,
        recursion_preprocessing_seconds,
        prove_seconds,
        stages,
        leaf_stage_seconds,
        leaf_throughput_cycles_per_second: leaf_stage_seconds
            .map(|seconds| total_cycles as f64 / seconds),
        root_proof_bytes,
        encode_seconds,
        verify_seconds,
        verified,
    };
    let json = serde_json::to_string_pretty(&metrics).expect("metrics serialize to JSON");
    match metrics_out {
        Some(path) => {
            fs::write(path, &json).expect("Failed to write metrics");
            info!("Metrics saved to {path:?}");
        }
        None => println!("{json}"),
    }
    if !verified {
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use tracing_subscriber::layer::SubscriberExt;

    use super::*;

    #[test]
    fn closed_spans_report_their_name_numeric_fields_and_duration() {
        let timings = SpanTimings::default();
        let subscriber = tracing_subscriber::registry().with(SpanTimingLayer::new(timings.clone()));
        tracing::subscriber::with_default(subscriber, || {
            let _stage = tracing::info_span!("stage_under_test", nodes = 4_usize).entered();
        });
        let stages = timings.take();
        assert_eq!(
            (
                stages.len(),
                stages[0].stage,
                stages[0].fields.as_slice(),
                stages[0].seconds >= 0.0,
            ),
            (
                1,
                "stage_under_test",
                [("nodes".to_owned(), 4_u64)].as_slice(),
                true,
            )
        );
    }
}
