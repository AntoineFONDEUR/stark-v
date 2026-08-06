use stwo::core::verifier::VerificationError as StwoVerificationError;
use thiserror::Error;

#[derive(Clone, Debug, Error)]
pub enum VerificationError {
    #[error("Proof has no preprocessing commitment.")]
    MissingProofPreprocessingCommitment,
    #[error("Verifier preprocessing has no commitment root.")]
    MissingVerifierPreprocessingCommitment,
    #[error("Proof preprocessing commitment does not match verifier preprocessing.")]
    PreprocessingCommitmentMismatch,
    #[error("Invalid logup sum.")]
    InvalidLogupSum,
    #[error("VM shared-relation claim does not match its committed interactions.")]
    InvalidSharedRelationClaim,
    #[error("VM and Poseidon2 shared-relation claims do not cancel.")]
    SharedRelationMismatch,
    #[error("Interaction proof of work failed.")]
    InteractionProofOfWork,
    #[error(transparent)]
    Stwo(#[from] StwoVerificationError),
}
