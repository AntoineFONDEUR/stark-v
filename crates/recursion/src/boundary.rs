//! Execution boundary: the public interface of a segment proof or an
//! aggregate node at every level of the recursion tree.
//!
//! A boundary states *which* slice of an execution a proof attests: the
//! entry/exit program counter and register file, the read-write memory
//! commitment at both ends, and the program commitment. Chaining two
//! boundaries checks the left exit state equals the right entry state, so the
//! root of an aggregation tree exposes one boundary spanning the entire
//! execution regardless of its length.

use prover::Proof;
use stwo::core::vcs_lifted::merkle_hasher::MerkleHasherLifted;

/// Execution boundary exposed by a segment proof or an aggregate node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Boundary {
    pub entry_pc: u32,
    pub exit_pc: u32,
    pub entry_regs: [u32; 32],
    pub exit_regs: [u32; 32],
    pub entry_rw_root: Option<u32>,
    pub exit_rw_root: Option<u32>,
    pub program_root: Option<u32>,
}

impl Boundary {
    /// The boundary a segment proof exposes through its public data.
    pub fn of_segment<H: MerkleHasherLifted>(proof: &Proof<H>) -> Self {
        let public_data = &proof.public_data;
        Self {
            entry_pc: public_data.initial_pc,
            exit_pc: public_data.final_pc,
            entry_regs: public_data.initial_regs,
            exit_regs: public_data.final_regs,
            entry_rw_root: public_data.initial_rw_root,
            exit_rw_root: public_data.final_rw_root,
            program_root: public_data.program_root,
        }
    }

    /// Chain two boundaries: the left exit must equal the right entry, and
    /// both must run the same program.
    pub fn chain(&self, right: &Self) -> Result<Self, &'static str> {
        if self.exit_pc != right.entry_pc {
            return Err("exit_pc != entry_pc");
        }
        if self.exit_regs != right.entry_regs {
            return Err("exit_regs != entry_regs");
        }
        if self.exit_rw_root != right.entry_rw_root {
            return Err("exit_rw_root != entry_rw_root");
        }
        if self.program_root != right.program_root {
            return Err("program_root differs");
        }
        Ok(Self {
            entry_pc: self.entry_pc,
            exit_pc: right.exit_pc,
            entry_regs: self.entry_regs,
            exit_regs: right.exit_regs,
            entry_rw_root: self.entry_rw_root,
            exit_rw_root: right.exit_rw_root,
            program_root: self.program_root,
        })
    }
}

/// Fold an ordered sequence of boundaries into the single span they cover,
/// checking every adjacent pair chains. `None` for an empty sequence.
pub fn fold_boundaries(
    boundaries: impl IntoIterator<Item = Boundary>,
) -> Result<Option<Boundary>, &'static str> {
    let mut folded: Option<Boundary> = None;
    for boundary in boundaries {
        folded = Some(match folded {
            None => boundary,
            Some(prev) => prev.chain(&boundary)?,
        });
    }
    Ok(folded)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn boundary(entry_pc: u32, exit_pc: u32) -> Boundary {
        Boundary {
            entry_pc,
            exit_pc,
            entry_regs: [0; 32],
            exit_regs: [0; 32],
            entry_rw_root: Some(7),
            exit_rw_root: Some(7),
            program_root: Some(42),
        }
    }

    #[test]
    fn test_chain_combines_outer_boundary() {
        let combined = boundary(0, 4).chain(&boundary(4, 8)).expect("chains");
        assert_eq!((combined.entry_pc, combined.exit_pc), (0, 8));
    }

    #[test]
    fn test_chain_rejects_pc_gap() {
        assert!(boundary(0, 4).chain(&boundary(8, 12)).is_err());
    }

    #[test]
    fn test_chain_rejects_program_mismatch() {
        let mut right = boundary(4, 8);
        right.program_root = Some(43);
        assert!(boundary(0, 4).chain(&right).is_err());
    }

    #[test]
    fn test_fold_spans_the_whole_sequence() {
        let folded = fold_boundaries([boundary(0, 4), boundary(4, 8), boundary(8, 16)])
            .expect("chains")
            .expect("non-empty");
        assert_eq!((folded.entry_pc, folded.exit_pc), (0, 16));
    }

    #[test]
    fn test_fold_of_nothing_is_none() {
        assert_eq!(fold_boundaries([]).expect("trivially chains"), None);
    }

    #[test]
    fn test_fold_rejects_out_of_order_segments() {
        assert!(fold_boundaries([boundary(4, 8), boundary(0, 4)]).is_err());
    }
}
