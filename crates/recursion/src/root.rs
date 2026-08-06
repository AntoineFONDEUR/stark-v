//! Application verification for one complete recursive execution root.
//!
//! The caller supplies a segmentation-free complete execution statement. The
//! verifier first requires the proof statement to be the canonical root, then
//! compares every application-owned field before verifying the single
//! manifest-bound recursion proof. Root encoding uses the exact wire and
//! verifier schedule fixed by the protocol profile.

use core::fmt;

use air::digest::Digest8;

use crate::profile::{FrozenProtocolProfile, ROOT_PROOF_BYTE_SIZE, RootProofBytes};
use crate::recursion_child::{RecursionChildError, adapt_recursion_child};
use crate::recursive_proof::{
    RecursionPreprocessing, RecursionProof, RecursionProofError, verify_recursion_proof,
};
use crate::statement::{CompleteExecutionStatement, RootStatement, StatementError};
use crate::wire::WireError;

const ROOT_ENCODING_STACK_SIZE: usize = 64 * 1024 * 1024;

/// One application-owned field in a complete execution claim.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CompleteExecutionField {
    Protocol,
    Program,
    InitialState,
    FinalState,
    PublicInput,
    PublicOutput,
    TotalCycles,
}

impl fmt::Display for CompleteExecutionField {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            Self::Protocol => "protocol",
            Self::Program => "program",
            Self::InitialState => "initial machine state",
            Self::FinalState => "final machine state",
            Self::PublicInput => "public input",
            Self::PublicOutput => "public output",
            Self::TotalCycles => "total cycles",
        };
        formatter.write_str(name)
    }
}

/// Failure while binding and verifying one application root proof.
#[derive(Debug)]
pub enum RootVerificationError {
    InvalidRoot(StatementError),
    ExpectedExecutionMismatch(CompleteExecutionField),
    Proof(RecursionProofError),
}

/// Profile-owned operation shape for one application root verification.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RootVerifierShape {
    step_count: usize,
    plan_digest: Digest8,
}

impl RootVerifierShape {
    pub const fn step_count(self) -> usize {
        self.step_count
    }

    pub const fn plan_digest(self) -> Digest8 {
        self.plan_digest
    }
}

/// Measured fixed proof bytes and profile-owned verifier shape.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RecursiveRootConformance {
    proof_byte_size: usize,
    verifier_shape: RootVerifierShape,
}

impl RecursiveRootConformance {
    pub const fn proof_byte_size(self) -> usize {
        self.proof_byte_size
    }

    pub const fn verifier_shape(self) -> RootVerifierShape {
        self.verifier_shape
    }
}

/// Failure while checking or encoding one fixed root artifact.
#[derive(Debug)]
pub enum RootEncodingError {
    InvalidRoot(StatementError),
    Proof(RecursionChildError),
    Wire(WireError),
    ThreadSpawn(std::io::Error),
    ThreadPanic,
}

impl fmt::Display for RootVerificationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidRoot(error) => write!(formatter, "invalid root statement: {error}"),
            Self::ExpectedExecutionMismatch(field) => {
                write!(
                    formatter,
                    "root {field} does not match the expected execution"
                )
            }
            Self::Proof(error) => write!(formatter, "invalid root proof: {error}"),
        }
    }
}

impl std::error::Error for RootVerificationError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::InvalidRoot(error) => Some(error),
            Self::Proof(error) => Some(error),
            Self::ExpectedExecutionMismatch(_) => None,
        }
    }
}

impl fmt::Display for RootEncodingError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidRoot(error) => write!(formatter, "invalid root statement: {error}"),
            Self::Proof(error) => write!(formatter, "invalid root proof: {error}"),
            Self::Wire(error) => write!(formatter, "invalid root encoding: {error}"),
            Self::ThreadSpawn(error) => write!(formatter, "root encoder thread failed: {error}"),
            Self::ThreadPanic => formatter.write_str("root encoder thread panicked"),
        }
    }
}

impl std::error::Error for RootEncodingError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::InvalidRoot(error) => Some(error),
            Self::Proof(error) => Some(error),
            Self::Wire(error) => Some(error),
            Self::ThreadSpawn(error) => Some(error),
            Self::ThreadPanic => None,
        }
    }
}

/// Returns the exact trusted operation schedule for every root under a profile.
pub fn root_verifier_shape(profile: &FrozenProtocolProfile) -> RootVerifierShape {
    RootVerifierShape {
        step_count: profile.recursion_plan().steps().len(),
        plan_digest: profile.recursion_plan().digest(),
    }
}

/// Encodes one canonical root through the protocol's existing fixed proof wire.
pub fn encode_recursive_root(
    profile: &FrozenProtocolProfile,
    proof: &RecursionProof,
) -> Result<Box<RootProofBytes>, RootEncodingError> {
    RootStatement::new(proof.statement).map_err(RootEncodingError::InvalidRoot)?;
    let wire = adapt_recursion_child(profile, proof).map_err(RootEncodingError::Proof)?;
    // The fixed byte array is larger than a default test-thread stack.
    std::thread::Builder::new()
        .name("recursive-root-encoder".into())
        .stack_size(ROOT_ENCODING_STACK_SIZE)
        .spawn(move || {
            wire.encode::<ROOT_PROOF_BYTE_SIZE>()
                .map(Box::new)
                .map_err(RootEncodingError::Wire)
        })
        .map_err(RootEncodingError::ThreadSpawn)?
        .join()
        .map_err(|_| RootEncodingError::ThreadPanic)?
}

/// Measures proof bytes and verifier shape without retaining tree descendants.
pub fn recursive_root_conformance(
    profile: &FrozenProtocolProfile,
    proof: &RecursionProof,
) -> Result<RecursiveRootConformance, RootEncodingError> {
    let bytes = encode_recursive_root(profile, proof)?;
    Ok(RecursiveRootConformance {
        proof_byte_size: bytes.as_bytes().len(),
        verifier_shape: root_verifier_shape(profile),
    })
}

/// Verifies exactly one recursive root against an application-owned execution.
pub fn verify_recursive_root(
    profile: &FrozenProtocolProfile,
    preprocessing: &RecursionPreprocessing,
    expected: &CompleteExecutionStatement,
    proof: RecursionProof,
) -> Result<(), RootVerificationError> {
    let root = RootStatement::new(proof.statement).map_err(RootVerificationError::InvalidRoot)?;
    validate_expected_execution(expected, root.complete_execution())?;
    verify_recursion_proof(
        profile,
        preprocessing,
        expected.protocol(),
        root.statement(),
        proof,
    )
    .map_err(RootVerificationError::Proof)
}

fn validate_expected_execution(
    expected: &CompleteExecutionStatement,
    actual: &CompleteExecutionStatement,
) -> Result<(), RootVerificationError> {
    let mismatch = if expected.protocol() != actual.protocol() {
        Some(CompleteExecutionField::Protocol)
    } else if expected.program() != actual.program() {
        Some(CompleteExecutionField::Program)
    } else if expected.initial_state() != actual.initial_state() {
        Some(CompleteExecutionField::InitialState)
    } else if expected.final_state() != actual.final_state() {
        Some(CompleteExecutionField::FinalState)
    } else if expected.public_input() != actual.public_input() {
        Some(CompleteExecutionField::PublicInput)
    } else if expected.public_output() != actual.public_output() {
        Some(CompleteExecutionField::PublicOutput)
    } else if expected.total_cycles() != actual.total_cycles() {
        Some(CompleteExecutionField::TotalCycles)
    } else {
        None
    };
    mismatch.map_or(Ok(()), |field| {
        Err(RootVerificationError::ExpectedExecutionMismatch(field))
    })
}

#[cfg(test)]
pub(crate) mod tests {
    use air::digest::{IoDigest, ProgramDigest, ProtocolId};
    use rstest::rstest;

    use super::*;
    use crate::test_fixtures::{digest, state, two_executed};

    #[derive(Clone, Copy)]
    enum ChangedField {
        Protocol,
        Program,
        InitialState,
        FinalState,
        PublicInput,
        PublicOutput,
        TotalCycles,
    }

    #[rstest]
    #[case::protocol(ChangedField::Protocol, CompleteExecutionField::Protocol)]
    #[case::program(ChangedField::Program, CompleteExecutionField::Program)]
    #[case::initial_state(ChangedField::InitialState, CompleteExecutionField::InitialState)]
    #[case::final_state(ChangedField::FinalState, CompleteExecutionField::FinalState)]
    #[case::public_input(ChangedField::PublicInput, CompleteExecutionField::PublicInput)]
    #[case::public_output(ChangedField::PublicOutput, CompleteExecutionField::PublicOutput)]
    #[case::total_cycles(ChangedField::TotalCycles, CompleteExecutionField::TotalCycles)]
    fn every_changed_application_field_is_rejected(
        #[case] changed: ChangedField,
        #[case] expected_field: CompleteExecutionField,
    ) {
        let (_, _, statement) = two_executed();
        let root = RootStatement::new(statement).expect("the fixture spans its complete job");
        let expected = changed_execution(*root.complete_execution(), changed);
        assert!(matches!(
            validate_expected_execution(&expected, root.complete_execution()),
            Err(RootVerificationError::ExpectedExecutionMismatch(field))
                if field == expected_field
        ));
    }

    #[test]
    fn unchanged_application_execution_is_accepted() {
        let (_, _, statement) = two_executed();
        let root = RootStatement::new(statement).expect("the fixture spans its complete job");
        assert!(
            validate_expected_execution(root.complete_execution(), root.complete_execution())
                .is_ok()
        );
    }

    #[test]
    fn frozen_root_verifier_shape_matches_the_conformance_vector() {
        let profile = crate::profile::frozen_protocol_profile().expect("frozen profile is valid");
        assert_eq!(root_verifier_shape(&profile), frozen_root_verifier_shape());
    }

    pub(crate) fn matches_frozen_root_conformance(conformance: RecursiveRootConformance) -> bool {
        conformance.proof_byte_size() == ROOT_PROOF_BYTE_SIZE
            && conformance.verifier_shape() == frozen_root_verifier_shape()
    }

    fn frozen_root_verifier_shape() -> RootVerifierShape {
        RootVerifierShape {
            step_count: 4_937,
            plan_digest: Digest8::try_from([
                1_257_248_829,
                1_216_201_935,
                354_922_115,
                2_062_314_934,
                1_132_069_174,
                1_088_399_207,
                325_143_630,
                1_511_814_991,
            ])
            .expect("the checked verifier-plan digest is canonical"),
        }
    }

    fn changed_execution(
        execution: CompleteExecutionStatement,
        changed: ChangedField,
    ) -> CompleteExecutionStatement {
        CompleteExecutionStatement::new(
            if matches!(changed, ChangedField::Protocol) {
                ProtocolId::from(digest(50))
            } else {
                execution.protocol()
            },
            if matches!(changed, ChangedField::Program) {
                ProgramDigest::from(digest(51))
            } else {
                execution.program()
            },
            if matches!(changed, ChangedField::InitialState) {
                state(52)
            } else {
                execution.initial_state()
            },
            if matches!(changed, ChangedField::FinalState) {
                state(53)
            } else {
                execution.final_state()
            },
            if matches!(changed, ChangedField::PublicInput) {
                IoDigest::from(digest(54))
            } else {
                execution.public_input()
            },
            if matches!(changed, ChangedField::PublicOutput) {
                IoDigest::from(digest(55))
            } else {
                execution.public_output()
            },
            if matches!(changed, ChangedField::TotalCycles) {
                execution.total_cycles() + 1
            } else {
                execution.total_cycles()
            },
        )
        .expect("the changed execution remains structurally valid")
    }
}
