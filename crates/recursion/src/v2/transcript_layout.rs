//! Trusted frame, call, and word layout for the recursion V2 transcript.
//!
//! A verifier plan fixes every transcript operation and payload width. This
//! module expands that information into deterministic hash IDs, call IDs,
//! frame boundaries, header constants, payload slots, and sponge padding.
//! AIR preprocessing consumes this layout so proof columns supply values but
//! never choose transcript structure.

use core::fmt;

use air::digest::M31Word;

use super::kernel::{VerifierControlPlan, VerifierStep};
use super::protocol::CanonicalWords;
use super::statement::SPAN_STATEMENT_CANONICAL_WORDS;
use super::transcript::{HashPurpose, TranscriptError, TranscriptTrace};
use super::transcript_program::{
    TranscriptEffect, TranscriptOperationTrace, TranscriptProgramError, operation_header,
};

const RATE: usize = 8;
const DIGEST_WORDS: usize = 8;
const DRAW_COUNTER: u16 = 0;
const DRAW_TAG: u32 = 0x4452_4157;
const POW_NONCE_WORDS: usize = 4;

/// Origin of one padded sponge input word.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TranscriptWordSource {
    Digest { limb: u32 },
    Payload { index: u32 },
    Constant(M31Word),
}

/// One trusted Poseidon call coordinate within a transcript frame.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TranscriptCallLayout {
    call_id: u32,
    hash_id: u32,
    step: u32,
    is_first: bool,
    is_last: bool,
    purpose: HashPurpose,
}

impl TranscriptCallLayout {
    pub const fn call_id(&self) -> u32 {
        self.call_id
    }

    pub const fn hash_id(&self) -> u32 {
        self.hash_id
    }

    pub const fn step(&self) -> u32 {
        self.step
    }

    pub const fn is_first(&self) -> bool {
        self.is_first
    }

    pub const fn is_last(&self) -> bool {
        self.is_last
    }

    pub const fn purpose(&self) -> HashPurpose {
        self.purpose
    }
}

/// One independent sponge session and its complete padded word ownership.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TranscriptFrameLayout {
    hash_id: u32,
    first_call_id: u32,
    call_count: u32,
    purpose: HashPurpose,
    stream_word_count: u32,
    words: Vec<TranscriptWordSource>,
}

impl TranscriptFrameLayout {
    pub const fn hash_id(&self) -> u32 {
        self.hash_id
    }

    pub const fn first_call_id(&self) -> u32 {
        self.first_call_id
    }

    pub const fn call_count(&self) -> u32 {
        self.call_count
    }

    pub const fn purpose(&self) -> HashPurpose {
        self.purpose
    }

    pub const fn stream_word_count(&self) -> u32 {
        self.stream_word_count
    }

    pub fn words(&self) -> &[TranscriptWordSource] {
        &self.words
    }
}

/// Frame range and payload width for one transcript-affecting control step.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TranscriptOperationLayout {
    ordinal: u32,
    sequence: u32,
    step: VerifierStep,
    effect: TranscriptEffect,
    first_hash_id: u32,
    hash_count: u32,
    first_call_id: u32,
    call_count: u32,
    payload_word_count: u32,
}

impl TranscriptOperationLayout {
    pub const fn ordinal(&self) -> u32 {
        self.ordinal
    }

    pub const fn sequence(&self) -> u32 {
        self.sequence
    }

    pub const fn step(&self) -> VerifierStep {
        self.step
    }

    pub const fn effect(&self) -> TranscriptEffect {
        self.effect
    }

    pub const fn first_hash_id(&self) -> u32 {
        self.first_hash_id
    }

    pub const fn hash_count(&self) -> u32 {
        self.hash_count
    }

    pub const fn first_call_id(&self) -> u32 {
        self.first_call_id
    }

    pub const fn call_count(&self) -> u32 {
        self.call_count
    }

    pub const fn payload_word_count(&self) -> u32 {
        self.payload_word_count
    }
}

/// Complete trusted transcript preprocessing for one verifier schema.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TranscriptLayout {
    operations: Vec<TranscriptOperationLayout>,
    frames: Vec<TranscriptFrameLayout>,
    calls: Vec<TranscriptCallLayout>,
}

impl TranscriptLayout {
    pub fn new(plan: &VerifierControlPlan) -> Result<Self, TranscriptLayoutError> {
        let mut layout = Self {
            operations: Vec::new(),
            frames: Vec::new(),
            calls: Vec::new(),
        };
        for (sequence, step) in plan.steps().iter().copied().enumerate() {
            let Some(effect) = step.transcript_effect() else {
                continue;
            };
            let sequence = u32::try_from(sequence)
                .map_err(|_| TranscriptLayoutError::SequenceOutOfRange { sequence })?;
            let ordinal = u32::try_from(layout.operations.len()).map_err(|_| {
                TranscriptLayoutError::OperationCountOutOfRange {
                    count: layout.operations.len(),
                }
            })?;
            let first_hash_id = next_index("hash", layout.frames.len())?;
            let first_call_id = next_index("call", layout.calls.len())?;
            let payload_word_count = payload_word_count(plan, step)?;

            layout.push_mix_frame(sequence, step, payload_word_count)?;
            if matches!(effect, TranscriptEffect::Draw | TranscriptEffect::Pow) {
                layout.push_draw_frame()?;
            }

            let hash_count = monotonic_count(first_hash_id, layout.frames.len(), "hash")?;
            let call_count = monotonic_count(first_call_id, layout.calls.len(), "call")?;
            layout.operations.push(TranscriptOperationLayout {
                ordinal,
                sequence,
                step,
                effect,
                first_hash_id,
                hash_count,
                first_call_id,
                call_count,
                payload_word_count,
            });
        }
        Ok(layout)
    }

    pub fn operations(&self) -> &[TranscriptOperationLayout] {
        &self.operations
    }

    pub fn frames(&self) -> &[TranscriptFrameLayout] {
        &self.frames
    }

    pub fn calls(&self) -> &[TranscriptCallLayout] {
        &self.calls
    }

    /// Checks a recording backend against every trusted structural coordinate.
    pub fn validate_execution(
        &self,
        operations: &[TranscriptOperationTrace],
        trace: &TranscriptTrace,
    ) -> Result<(), TranscriptLayoutError> {
        trace
            .sponge_rows()
            .map_err(TranscriptLayoutError::Transcript)?;
        require_len("operations", self.operations.len(), operations.len())?;
        require_len("frames", self.frames.len(), trace.hash_frames.len())?;
        require_len("calls", self.calls.len(), trace.poseidon_calls.len())?;

        for (expected, actual) in self.operations.iter().zip(operations) {
            let actual_tuple = (
                actual.sequence(),
                actual.step(),
                actual.first_hash_id(),
                actual.hash_count(),
                actual.first_call_id(),
                actual.call_count(),
            );
            let expected_tuple = (
                expected.sequence,
                expected.step,
                expected.first_hash_id,
                expected.hash_count,
                expected.first_call_id,
                expected.call_count,
            );
            if actual_tuple != expected_tuple {
                return Err(TranscriptLayoutError::OperationMismatch {
                    ordinal: expected.ordinal,
                });
            }
        }

        for (expected, actual) in self.frames.iter().zip(&trace.hash_frames) {
            let actual_word_count = u32::try_from(actual.words.len()).map_err(|_| {
                TranscriptLayoutError::WordCountOutOfRange {
                    count: actual.words.len(),
                }
            })?;
            if (
                actual.hash_id,
                actual.first_call_id,
                actual.call_count,
                actual.purpose,
                actual_word_count,
            ) != (
                expected.hash_id,
                expected.first_call_id,
                expected.call_count,
                expected.purpose,
                expected.stream_word_count,
            ) {
                return Err(TranscriptLayoutError::FrameMismatch {
                    hash_id: expected.hash_id,
                });
            }
            for (word, source) in actual.words.iter().zip(&expected.words) {
                if let TranscriptWordSource::Constant(expected_word) = source {
                    if word != expected_word {
                        return Err(TranscriptLayoutError::ConstantWordMismatch {
                            hash_id: expected.hash_id,
                        });
                    }
                }
            }
        }

        for (expected, actual) in self.calls.iter().zip(&trace.poseidon_calls) {
            if (actual.id.call_id, actual.id.hash_id, actual.id.step)
                != (expected.call_id, expected.hash_id, expected.step)
            {
                return Err(TranscriptLayoutError::CallMismatch {
                    call_id: expected.call_id,
                });
            }
        }
        Ok(())
    }

    fn push_mix_frame(
        &mut self,
        sequence: u32,
        step: VerifierStep,
        payload_word_count: u32,
    ) -> Result<(), TranscriptLayoutError> {
        let mut words = digest_sources();
        words.extend(
            operation_header(sequence, step)
                .map_err(TranscriptLayoutError::Program)?
                .into_iter()
                .map(TranscriptWordSource::Constant),
        );
        for index in 0..payload_word_count {
            words.push(TranscriptWordSource::Payload { index });
        }
        self.push_frame(HashPurpose::Mix, words)
    }

    fn push_draw_frame(&mut self) -> Result<(), TranscriptLayoutError> {
        let mut words = digest_sources();
        words.extend([
            TranscriptWordSource::Constant(M31Word::from(DRAW_COUNTER)),
            TranscriptWordSource::Constant(
                M31Word::try_from(DRAW_TAG).expect("draw tag is canonical M31"),
            ),
        ]);
        self.push_frame(HashPurpose::Draw, words)
    }

    fn push_frame(
        &mut self,
        purpose: HashPurpose,
        mut words: Vec<TranscriptWordSource>,
    ) -> Result<(), TranscriptLayoutError> {
        let hash_id = next_index("hash", self.frames.len())?;
        let first_call_id = next_index("call", self.calls.len())?;
        let stream_word_count = u32::try_from(words.len())
            .map_err(|_| TranscriptLayoutError::WordCountOutOfRange { count: words.len() })?;
        words.push(TranscriptWordSource::Constant(M31Word::from(1_u16)));
        while !words.len().is_multiple_of(RATE) {
            words.push(TranscriptWordSource::Constant(M31Word::ZERO));
        }
        let call_count = words.len() / RATE;
        let call_count_u32 = u32::try_from(call_count)
            .map_err(|_| TranscriptLayoutError::CallCountOutOfRange { count: call_count })?;
        for step in 0..call_count {
            let call_id = next_index("call", self.calls.len())?;
            let step = u32::try_from(step)
                .map_err(|_| TranscriptLayoutError::CallCountOutOfRange { count: call_count })?;
            self.calls.push(TranscriptCallLayout {
                call_id,
                hash_id,
                step,
                is_first: step == 0,
                is_last: step + 1 == call_count_u32,
                purpose,
            });
        }
        self.frames.push(TranscriptFrameLayout {
            hash_id,
            first_call_id,
            call_count: call_count_u32,
            purpose,
            stream_word_count,
            words,
        });
        Ok(())
    }
}

fn digest_sources() -> Vec<TranscriptWordSource> {
    (0..DIGEST_WORDS)
        .map(|limb| TranscriptWordSource::Digest { limb: limb as u32 })
        .collect()
}

fn payload_word_count(
    plan: &VerifierControlPlan,
    step: VerifierStep,
) -> Result<u32, TranscriptLayoutError> {
    let count = match step {
        VerifierStep::BindProtocol => DIGEST_WORDS,
        VerifierStep::BindStatement => SPAN_STATEMENT_CANONICAL_WORDS,
        VerifierStep::BindPcsParameters => plan.pcs_parameters().canonical_words().len(),
        VerifierStep::AbsorbTraceCommitment { .. } | VerifierStep::AbsorbFriCommitment { .. } => {
            DIGEST_WORDS
        }
        VerifierStep::AbsorbPublicClaim
        | VerifierStep::DrawRelationChallenge { .. }
        | VerifierStep::DrawCompositionRandomness
        | VerifierStep::DrawOodsPoint
        | VerifierStep::DrawDeepRandomness
        | VerifierStep::DrawFriAlpha { .. }
        | VerifierStep::DrawQueryBlock { .. } => 0,
        VerifierStep::VerifyAndAbsorbInteractionPow { .. }
        | VerifierStep::VerifyAndAbsorbPcsPow { .. } => POW_NONCE_WORDS,
        VerifierStep::AbsorbClaimedSums { count }
        | VerifierStep::AbsorbSampledValues { count }
        | VerifierStep::AbsorbLastLayerCoefficients { count } => {
            return count
                .checked_mul(4)
                .ok_or(TranscriptLayoutError::PayloadWordCountOverflow { count });
        }
        VerifierStep::AccumulatePublicLogupTerm { .. }
        | VerifierStep::AssertGlobalLogupZero
        | VerifierStep::EvaluateAirInstruction { .. }
        | VerifierStep::AssertComposition { .. }
        | VerifierStep::VerifyTraceMerklePath { .. }
        | VerifierStep::EvaluateDeepQuotient { .. }
        | VerifierStep::VerifyFriMerklePath { .. }
        | VerifierStep::FoldFri { .. }
        | VerifierStep::VerifyLastLayer { .. }
        | VerifierStep::CloseRelation { .. }
        | VerifierStep::Complete => {
            return Err(TranscriptLayoutError::NonTranscriptStep { step });
        }
    };
    u32::try_from(count).map_err(|_| TranscriptLayoutError::WordCountOutOfRange { count })
}

fn next_index(field: &'static str, value: usize) -> Result<u32, TranscriptLayoutError> {
    u32::try_from(value).map_err(|_| TranscriptLayoutError::IndexOutOfRange { field, value })
}

fn monotonic_count(
    first: u32,
    current: usize,
    field: &'static str,
) -> Result<u32, TranscriptLayoutError> {
    next_index(field, current)?
        .checked_sub(first)
        .ok_or(TranscriptLayoutError::IndexRegression { field })
}

fn require_len(
    field: &'static str,
    expected: usize,
    actual: usize,
) -> Result<(), TranscriptLayoutError> {
    if expected != actual {
        return Err(TranscriptLayoutError::LengthMismatch {
            field,
            expected,
            actual,
        });
    }
    Ok(())
}

/// Invalid trusted layout or disagreement with a recording backend.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TranscriptLayoutError {
    Program(TranscriptProgramError),
    Transcript(TranscriptError),
    SequenceOutOfRange {
        sequence: usize,
    },
    OperationCountOutOfRange {
        count: usize,
    },
    WordCountOutOfRange {
        count: usize,
    },
    CallCountOutOfRange {
        count: usize,
    },
    PayloadWordCountOverflow {
        count: u32,
    },
    IndexOutOfRange {
        field: &'static str,
        value: usize,
    },
    IndexRegression {
        field: &'static str,
    },
    NonTranscriptStep {
        step: VerifierStep,
    },
    LengthMismatch {
        field: &'static str,
        expected: usize,
        actual: usize,
    },
    OperationMismatch {
        ordinal: u32,
    },
    FrameMismatch {
        hash_id: u32,
    },
    ConstantWordMismatch {
        hash_id: u32,
    },
    CallMismatch {
        call_id: u32,
    },
}

impl fmt::Display for TranscriptLayoutError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Program(error) => write!(formatter, "invalid transcript program: {error}"),
            Self::Transcript(error) => write!(formatter, "invalid transcript trace: {error}"),
            Self::SequenceOutOfRange { sequence } => {
                write!(formatter, "transcript sequence {sequence} does not fit u32")
            }
            Self::OperationCountOutOfRange { count } => {
                write!(
                    formatter,
                    "transcript operation count {count} does not fit u32"
                )
            }
            Self::WordCountOutOfRange { count } => {
                write!(formatter, "transcript word count {count} does not fit u32")
            }
            Self::CallCountOutOfRange { count } => {
                write!(formatter, "transcript call count {count} does not fit u32")
            }
            Self::PayloadWordCountOverflow { count } => {
                write!(
                    formatter,
                    "{count} QM31 payload values overflow the word count"
                )
            }
            Self::IndexOutOfRange { field, value } => {
                write!(
                    formatter,
                    "transcript {field} index {value} does not fit u32"
                )
            }
            Self::IndexRegression { field } => {
                write!(formatter, "transcript {field} index regressed")
            }
            Self::NonTranscriptStep { step } => {
                write!(
                    formatter,
                    "verifier step {step:?} has no transcript payload"
                )
            }
            Self::LengthMismatch {
                field,
                expected,
                actual,
            } => write!(
                formatter,
                "transcript has {actual} {field}, trusted layout requires {expected}"
            ),
            Self::OperationMismatch { ordinal } => {
                write!(
                    formatter,
                    "transcript operation {ordinal} disagrees with its layout"
                )
            }
            Self::FrameMismatch { hash_id } => {
                write!(
                    formatter,
                    "transcript hash frame {hash_id} disagrees with its layout"
                )
            }
            Self::ConstantWordMismatch { hash_id } => write!(
                formatter,
                "transcript hash frame {hash_id} changed a trusted constant word"
            ),
            Self::CallMismatch { call_id } => {
                write!(
                    formatter,
                    "transcript call {call_id} disagrees with its layout"
                )
            }
        }
    }
}

impl std::error::Error for TranscriptLayoutError {}
