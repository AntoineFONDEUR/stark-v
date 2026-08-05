//! Explicit prover-backend selection before Fiat-Shamir transcript construction.

use serde::{Deserialize, Serialize};
use stwo::core::pcs::PcsConfig;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleHasher;
use thiserror::Error;

#[cfg(all(feature = "metal", target_os = "macos"))]
use crate::prove_rv32im_cpu;
use crate::{Preprocessing, Proof, prove_rv32im};

/// Requested proving placement.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum ProverBackend {
    /// Use the existing SIMD prover path.
    Simd,
    /// Prefer an admitted Metal session, falling back to SIMD before the transcript.
    MetalPrefer,
    /// Require an admitted Metal session and at least one successful checked dispatch.
    MetalParticipationRequired,
}

/// Backend that actually produced the proof.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum ActualProverBackend {
    /// The existing SIMD backend.
    Simd,
    /// The scalar CPU backend, with no successful checked Metal dispatch.
    CpuBackend,
    /// The CPU backend with one or more successful checked Metal dispatches.
    ///
    /// This is intentionally hybrid: small and unsupported work remains on the CPU.
    CpuHybridMetal,
}

/// Backend-selection and checked-Metal telemetry for one proof.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct BackendReport {
    pub requested: ProverBackend,
    pub actual: ActualProverBackend,
    /// Why a preferred Metal request used SIMD, or why an admitted session had no
    /// successful dispatch.
    pub fallback_reason: Option<String>,
    /// Admitted Metal device, if admission succeeded.
    pub device_name: Option<String>,
    pub successful_submissions: u64,
    pub failed_submissions: u64,
}

impl BackendReport {
    fn simd(requested: ProverBackend, fallback_reason: Option<String>) -> Self {
        Self {
            requested,
            actual: ActualProverBackend::Simd,
            fallback_reason,
            device_name: None,
            successful_submissions: 0,
            failed_submissions: 0,
        }
    }

    #[cfg(all(feature = "metal", target_os = "macos"))]
    fn from_metal_session(
        requested: ProverBackend,
        session: stwo::prover::backend::metal::MetalSessionReport,
    ) -> Self {
        let participated = session.successful_submissions > 0;
        let fallback_reason = if session.failed_submissions > 0 {
            Some(format!(
                "the admitted Metal session reported {} failed checked submission(s)",
                session.failed_submissions
            ))
        } else if !participated {
            Some(
                "the admitted Metal session completed without a successful checked submission"
                    .to_owned(),
            )
        } else {
            None
        };
        Self {
            requested,
            actual: if participated {
                ActualProverBackend::CpuHybridMetal
            } else {
                ActualProverBackend::CpuBackend
            },
            fallback_reason,
            device_name: Some(session.device_name),
            successful_submissions: session.successful_submissions,
            failed_submissions: session.failed_submissions,
        }
    }
}

/// Proof plus the backend placement that actually produced it.
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct ProveOutcome {
    pub proof: Proof<Blake2sMerkleHasher>,
    pub backend_report: BackendReport,
}

/// Backend selection failed before proving, or a completed proof failed a strict
/// Metal-participation requirement and was discarded.
#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub enum BackendSelectionError {
    #[error("Metal proving is unavailable: {reason}")]
    MetalUnavailable { reason: String },
    #[error("Metal session admission failed: {reason}")]
    MetalAdmissionFailed { reason: String },
    #[error("Metal participation was required, but no checked command succeeded: {report:?}")]
    MetalParticipationMissing { report: BackendReport },
    #[error("Metal participation was required, but checked commands failed: {report:?}")]
    MetalSubmissionFailures { report: BackendReport },
}

enum SelectedBackend {
    Simd(BackendReport),
    #[cfg(all(feature = "metal", target_os = "macos"))]
    CpuMetal {
        requested: ProverBackend,
        session: stwo::prover::backend::metal::MetalSession,
    },
}

/// Proves an RV32IM execution using an explicitly selected backend policy.
///
/// Selection and Metal admission complete before this function enters either proving
/// path, and therefore before the Fiat-Shamir channel is created. `MetalPrefer`
/// falls back to SIMD at that boundary. `MetalParticipationRequired` instead rejects
/// unavailable Metal before proving and discards a completed proof unless its session
/// reports at least one checked success and no checked failures.
pub fn prove_rv32im_with_backend(
    run_result: runner::RunResult,
    config: PcsConfig,
    preprocessing: &Preprocessing,
    requested: ProverBackend,
) -> Result<ProveOutcome, BackendSelectionError> {
    match select_backend(requested)? {
        SelectedBackend::Simd(backend_report) => Ok(ProveOutcome {
            proof: prove_rv32im(run_result, config, preprocessing),
            backend_report,
        }),
        #[cfg(all(feature = "metal", target_os = "macos"))]
        SelectedBackend::CpuMetal { requested, session } => {
            let proof = prove_rv32im_cpu(run_result, config, preprocessing);
            let session_report = session.finish();
            let required_validation = (requested == ProverBackend::MetalParticipationRequired)
                .then(|| {
                    stwo::prover::backend::metal::MetalRequirement::ParticipationRequired
                        .validate(&session_report)
                });
            let backend_report = BackendReport::from_metal_session(requested, session_report);
            if let Some(validation) = required_validation {
                map_required_validation(validation, &backend_report)?;
            }
            Ok(ProveOutcome {
                proof,
                backend_report,
            })
        }
    }
}

#[cfg(all(feature = "metal", target_os = "macos"))]
fn map_required_validation(
    validation: Result<(), stwo::prover::backend::metal::MetalRequirementError>,
    report: &BackendReport,
) -> Result<(), BackendSelectionError> {
    use stwo::prover::backend::metal::MetalRequirementError;

    match validation {
        Ok(()) => Ok(()),
        Err(MetalRequirementError::NoSuccessfulSubmissions) => {
            Err(BackendSelectionError::MetalParticipationMissing {
                report: report.clone(),
            })
        }
        Err(MetalRequirementError::FailedSubmissions { .. }) => {
            Err(BackendSelectionError::MetalSubmissionFailures {
                report: report.clone(),
            })
        }
    }
}

fn select_backend(requested: ProverBackend) -> Result<SelectedBackend, BackendSelectionError> {
    match requested {
        ProverBackend::Simd => Ok(SelectedBackend::Simd(BackendReport::simd(requested, None))),
        ProverBackend::MetalPrefer | ProverBackend::MetalParticipationRequired => {
            select_metal_backend(requested)
        }
    }
}

#[cfg(all(feature = "metal", target_os = "macos"))]
fn select_metal_backend(
    requested: ProverBackend,
) -> Result<SelectedBackend, BackendSelectionError> {
    use stwo::prover::backend::metal::{MetalAdmissionError, MetalSession};

    match MetalSession::admit() {
        Ok(session) => Ok(SelectedBackend::CpuMetal { requested, session }),
        Err(error) if requested == ProverBackend::MetalPrefer => Ok(SelectedBackend::Simd(
            BackendReport::simd(requested, Some(error.to_string())),
        )),
        Err(error) => {
            let reason = error.to_string();
            match error {
                MetalAdmissionError::NoUnifiedMemoryDevice => {
                    Err(BackendSelectionError::MetalUnavailable { reason })
                }
                MetalAdmissionError::SessionMutexPoisoned
                | MetalAdmissionError::StaticPipelineUnavailable { .. } => {
                    Err(BackendSelectionError::MetalAdmissionFailed { reason })
                }
            }
        }
    }
}

#[cfg(not(all(feature = "metal", target_os = "macos")))]
fn select_metal_backend(
    requested: ProverBackend,
) -> Result<SelectedBackend, BackendSelectionError> {
    let reason = unavailable_metal_reason().to_owned();
    if requested == ProverBackend::MetalPrefer {
        Ok(SelectedBackend::Simd(BackendReport::simd(
            requested,
            Some(reason),
        )))
    } else {
        Err(BackendSelectionError::MetalUnavailable { reason })
    }
}

#[cfg(not(all(feature = "metal", target_os = "macos")))]
const fn unavailable_metal_reason() -> &'static str {
    #[cfg(not(feature = "metal"))]
    {
        "the prover crate was built without its `metal` feature"
    }
    #[cfg(all(feature = "metal", not(target_os = "macos")))]
    {
        "the Metal prover path is supported only on macOS"
    }
}

#[cfg(test)]
fn validate_required_participation(report: &BackendReport) -> Result<(), BackendSelectionError> {
    if report.failed_submissions > 0 {
        return Err(BackendSelectionError::MetalSubmissionFailures {
            report: report.clone(),
        });
    }
    if report.successful_submissions == 0 {
        return Err(BackendSelectionError::MetalParticipationMissing {
            report: report.clone(),
        });
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn admitted_report(successful_submissions: u64, failed_submissions: u64) -> BackendReport {
        BackendReport {
            requested: ProverBackend::MetalParticipationRequired,
            actual: if successful_submissions > 0 {
                ActualProverBackend::CpuHybridMetal
            } else {
                ActualProverBackend::CpuBackend
            },
            fallback_reason: None,
            device_name: Some("test device".to_owned()),
            successful_submissions,
            failed_submissions,
        }
    }

    #[test]
    fn required_participation_rejects_zero_dispatches() {
        assert!(matches!(
            validate_required_participation(&admitted_report(0, 0)),
            Err(BackendSelectionError::MetalParticipationMissing { .. })
        ));
    }

    #[test]
    fn required_participation_rejects_any_failure() {
        assert!(matches!(
            validate_required_participation(&admitted_report(3, 1)),
            Err(BackendSelectionError::MetalSubmissionFailures { .. })
        ));
    }

    #[test]
    fn required_participation_accepts_success_without_failure() {
        assert_eq!(
            validate_required_participation(&admitted_report(1, 0)),
            Ok(())
        );
    }

    #[cfg(not(feature = "metal"))]
    #[test]
    fn feature_off_prefer_selects_simd_with_a_reason() {
        let Ok(SelectedBackend::Simd(report)) = select_backend(ProverBackend::MetalPrefer) else {
            panic!("feature-off MetalPrefer must select SIMD");
        };
        assert_eq!(report.actual, ActualProverBackend::Simd);
        assert!(report.fallback_reason.is_some());
    }

    #[cfg(not(feature = "metal"))]
    #[test]
    fn feature_off_required_fails_before_proving() {
        assert!(matches!(
            select_backend(ProverBackend::MetalParticipationRequired),
            Err(BackendSelectionError::MetalUnavailable { .. })
        ));
    }
}
