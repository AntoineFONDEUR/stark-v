//! Application verification for one complete recursive execution root.
//!
//! The caller supplies a segmentation-free complete execution statement. The
//! verifier first requires the proof statement to be the canonical root, then
//! compares every application-owned field before verifying the single
//! manifest-bound recursion proof.

use core::fmt;

use crate::profile::FrozenProtocolProfile;
use crate::recursive_proof::{
    RecursionPreprocessing, RecursionProof, RecursionProofError, verify_recursion_proof,
};
use crate::statement::{CompleteExecutionStatement, RootStatement, StatementError};

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
mod tests {
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
