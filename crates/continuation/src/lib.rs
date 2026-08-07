//! Host-side continuation across independently proven execution segments.
//!
//! A continuation contains one STARK proof per segment. Verification checks
//! every proof independently and checks equality at adjacent machine-state
//! boundaries. It is useful before recursive proving is complete, but it is
//! not recursive or succinct: proof count, proof bytes, and verification work
//! all grow linearly with the number of segments.

use core::fmt;

use rayon::iter::{IntoParallelIterator, ParallelIterator};
use stwo::core::channel::MerkleChannel;
use stwo::core::pcs::PcsConfig;
use stwo::core::vcs_lifted::blake2_merkle::{Blake2sMerkleChannel, Blake2sMerkleHasher};
use stwo::core::vcs_lifted::merkle_hasher::MerkleHasherLifted;
use stwo::prover::backend::simd::SimdBackend;
use thiserror::Error;

use prover::{
    Preprocessing, PublicData, SegmentProof, prove_rv32im_with_channel, verify_rv32im_with_channel,
};

/// A public field that must agree at an adjacent segment boundary.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BoundaryField {
    ProgramCounter,
    Registers,
    ReadWriteMemoryRoot,
    PublicIoState,
    ProgramRoot,
}

impl fmt::Display for BoundaryField {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            Self::ProgramCounter => "final_pc != initial_pc",
            Self::Registers => "final_regs != initial_regs",
            Self::ReadWriteMemoryRoot => "final_rw_root != initial_rw_root",
            Self::PublicIoState => "final_public_io_state != initial_public_io_state",
            Self::ProgramRoot => "program_root differs",
        };
        formatter.write_str(name)
    }
}

/// Failures from host-side continuation verification.
#[derive(Debug, Error)]
pub enum ContinuationError {
    #[error("a continuation must contain at least one proof")]
    EmptyProofChain,
    #[error("segment boundary mismatch between segments {previous} and {next}: {field}")]
    BoundaryMismatch {
        previous: usize,
        next: usize,
        field: BoundaryField,
    },
    #[error(transparent)]
    Proof(#[from] prover::VerificationError),
}

/// Proves every segment independently with the Blake2s channel.
pub fn prove_segments(
    run_results: Vec<runner::RunResult>,
    config: PcsConfig,
    preprocessing: &Preprocessing,
) -> Vec<SegmentProof<Blake2sMerkleHasher>> {
    prove_segments_with_channel::<Blake2sMerkleChannel>(run_results, config, preprocessing)
}

/// Proves every segment independently with the selected Merkle channel.
///
/// Segment proofs are produced in parallel because no proof depends on
/// another segment's witness. This parallelism changes throughput, not the
/// linear proof count of a continuation.
pub fn prove_segments_with_channel<MC: MerkleChannel>(
    run_results: Vec<runner::RunResult>,
    config: PcsConfig,
    preprocessing: &Preprocessing<MC::H>,
) -> Vec<SegmentProof<MC::H>>
where
    SimdBackend: stwo::prover::backend::BackendForChannel<MC>
        + stwo::prover::backend::ColumnOps<
            <MC::H as MerkleHasherLifted>::Hash,
            Column = Vec<<MC::H as MerkleHasherLifted>::Hash>,
        >,
    MC::H: Sync,
    <MC::H as MerkleHasherLifted>::Hash: Send + Sync,
{
    run_results
        .into_par_iter()
        .map(|run_result| prove_rv32im_with_channel::<MC>(run_result, config, preprocessing))
        .collect()
}

/// Checks that a non-empty sequence of public segment claims forms one chain.
pub fn validate_segment_chain(public_data: &[PublicData]) -> Result<(), ContinuationError> {
    if public_data.is_empty() {
        return Err(ContinuationError::EmptyProofChain);
    }

    for (index, pair) in public_data.windows(2).enumerate() {
        let (previous, next) = (&pair[0], &pair[1]);
        let mismatch = |field| ContinuationError::BoundaryMismatch {
            previous: index,
            next: index + 1,
            field,
        };
        if previous.final_pc != next.initial_pc {
            return Err(mismatch(BoundaryField::ProgramCounter));
        }
        if previous.final_regs != next.initial_regs {
            return Err(mismatch(BoundaryField::Registers));
        }
        if previous.final_rw_root != next.initial_rw_root {
            return Err(mismatch(BoundaryField::ReadWriteMemoryRoot));
        }
        if previous.final_public_io_state != next.initial_public_io_state {
            return Err(mismatch(BoundaryField::PublicIoState));
        }
        if previous.program_root != next.program_root {
            return Err(mismatch(BoundaryField::ProgramRoot));
        }
    }
    Ok(())
}

/// Verifies a non-empty continuation with the Blake2s channel.
pub fn verify_segments(
    proofs: Vec<SegmentProof<Blake2sMerkleHasher>>,
    config: PcsConfig,
    preprocessing: &Preprocessing,
) -> Result<(), ContinuationError> {
    verify_segments_with_channel::<Blake2sMerkleChannel>(proofs, config, preprocessing)
}

/// Verifies each proof and every adjacent public boundary on the host.
pub fn verify_segments_with_channel<MC: MerkleChannel>(
    proofs: Vec<SegmentProof<MC::H>>,
    config: PcsConfig,
    preprocessing: &Preprocessing<MC::H>,
) -> Result<(), ContinuationError> {
    let public_data = proofs
        .iter()
        .map(|proof| proof.vm.public_data.clone())
        .collect::<Vec<_>>();
    validate_segment_chain(&public_data)?;

    for proof in proofs {
        verify_rv32im_with_channel::<MC>(proof, config, preprocessing)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use prover::public_data::{IoEntries, PublicData};

    use super::*;

    fn public_data(initial_pc: u32, final_pc: u32) -> PublicData {
        PublicData {
            initial_pc,
            final_pc,
            clock: 0,
            initial_regs: [0; 32],
            final_regs: [0; 32],
            initial_public_io_state: [0; 8],
            final_public_io_state: [0; 8],
            journal_count: 0,
            journal_last_clock: 0,
            reg_last_clock: [0; 32],
            program_root: None,
            initial_rw_root: None,
            final_rw_root: None,
            io_entries: IoEntries {
                input_start: 0,
                input_len: 0,
                input_words: Vec::new(),
                output_len: 0,
                output_len_addr: 0,
                output_data_addr: 0,
                output_words: Vec::new(),
            },
        }
    }

    fn digest(seed: u32) -> [u32; 8] {
        core::array::from_fn(|index| seed + index as u32)
    }

    #[test]
    fn empty_chain_is_rejected() {
        assert!(matches!(
            validate_segment_chain(&[]),
            Err(ContinuationError::EmptyProofChain)
        ));
    }

    #[test]
    fn matching_boundary_is_accepted() {
        assert!(validate_segment_chain(&[public_data(1, 2), public_data(2, 3)]).is_ok());
    }

    #[test]
    fn program_counter_mismatch_is_rejected() {
        assert!(matches!(
            validate_segment_chain(&[public_data(1, 2), public_data(3, 4)]),
            Err(ContinuationError::BoundaryMismatch {
                field: BoundaryField::ProgramCounter,
                ..
            })
        ));
    }

    #[test]
    fn register_mismatch_is_rejected() {
        let mut previous = public_data(1, 2);
        previous.final_regs[1] = 7;
        assert!(matches!(
            validate_segment_chain(&[previous, public_data(2, 3)]),
            Err(ContinuationError::BoundaryMismatch {
                field: BoundaryField::Registers,
                ..
            })
        ));
    }

    #[test]
    fn memory_root_mismatch_is_rejected() {
        let mut previous = public_data(1, 2);
        previous.final_rw_root = Some(digest(1));
        assert!(matches!(
            validate_segment_chain(&[previous, public_data(2, 3)]),
            Err(ContinuationError::BoundaryMismatch {
                field: BoundaryField::ReadWriteMemoryRoot,
                ..
            })
        ));
    }

    #[test]
    fn public_io_state_mismatch_is_rejected() {
        let mut previous = public_data(1, 2);
        previous.final_public_io_state = digest(1);
        assert!(matches!(
            validate_segment_chain(&[previous, public_data(2, 3)]),
            Err(ContinuationError::BoundaryMismatch {
                field: BoundaryField::PublicIoState,
                ..
            })
        ));
    }

    #[test]
    fn program_root_mismatch_is_rejected() {
        let mut previous = public_data(1, 2);
        previous.program_root = Some(digest(1));
        assert!(matches!(
            validate_segment_chain(&[previous, public_data(2, 3)]),
            Err(ContinuationError::BoundaryMismatch {
                field: BoundaryField::ProgramRoot,
                ..
            })
        ));
    }
}
