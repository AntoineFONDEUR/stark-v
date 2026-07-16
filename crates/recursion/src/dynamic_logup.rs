//! LogUp finalization shared by native and circuit-valued claimed sums.
//!
//! The recursive verifier receives a child's claimed sum as a circuit wire,
//! while the existing recorder embeds a native secure-field value. The proxy
//! preserves STWO's fraction batching and constraint order for both forms.

use stwo::core::Fraction;

use crate::recorder::Rec;

/// LogUp state whose cumulative-sum shift is a circuit value.
pub(crate) struct CircuitLogup {
    pub(crate) interaction: usize,
    pub(crate) cumsum_shift: Rec,
    pub(crate) fracs: Vec<Fraction<Rec, Rec>>,
    pub(crate) is_finalized: bool,
}

impl CircuitLogup {
    pub(crate) fn new(interaction: usize, cumsum_shift: Rec) -> Self {
        Self {
            interaction,
            cumsum_shift,
            fracs: Vec::new(),
            is_finalized: true,
        }
    }
}

impl Drop for CircuitLogup {
    fn drop(&mut self) {
        assert!(self.is_finalized, "CircuitLogup was not finalized");
    }
}

macro_rules! recursion_logup_proxy {
    () => {
        fn write_logup_frac(
            &mut self,
            fraction: stwo::core::Fraction<Self::EF, Self::EF>,
        ) {
            if self.logup.fracs.is_empty() {
                self.logup.is_finalized = false;
            }
            self.logup.fracs.push(fraction);
        }

        fn finalize_logup_batched(&mut self, batching: &Vec<usize>) {
            assert!(!self.logup.is_finalized, "LogUp was already finalized");
            let fracs = core::mem::take(&mut self.logup.fracs);
            assert_eq!(
                batching.len(),
                fracs.len(),
                "batching must have one entry per LogUp fraction"
            );
            let last_batch = *batching.iter().max().expect("LogUp requires a fraction");
            let interaction = self.logup.interaction;
            let cumsum_shift = self.logup.cumsum_shift.clone();

            let mut fracs_by_batch: Vec<
                Vec<stwo::core::Fraction<Self::EF, Self::EF>>,
            > = vec![Vec::new(); last_batch + 1];
            for (&batch, fraction) in batching.iter().zip(fracs) {
                fracs_by_batch[batch].push(fraction);
            }
            assert!(
                fracs_by_batch.iter().all(|batch| !batch.is_empty()),
                "batching must contain every consecutive batch"
            );

            let mut previous_column_sum = <Self::EF as num_traits::Zero>::zero();
            for batch in &fracs_by_batch[..last_batch] {
                let fraction: stwo::core::Fraction<Self::EF, Self::EF> =
                    batch.iter().cloned().sum();
                let [current_sum] = self.next_extension_interaction_mask(interaction, [0]);
                let difference = current_sum.clone() - previous_column_sum.clone();
                previous_column_sum = current_sum;
                self.add_constraint(
                    difference * fraction.denominator - fraction.numerator,
                );
            }

            let fraction: stwo::core::Fraction<Self::EF, Self::EF> =
                fracs_by_batch[last_batch].iter().cloned().sum();
            let [previous_row_sum, current_sum] =
                self.next_extension_interaction_mask(interaction, [-1, 0]);
            let difference = current_sum - previous_row_sum - previous_column_sum;
            self.add_constraint(
                (difference + cumsum_shift) * fraction.denominator - fraction.numerator,
            );
            self.logup.is_finalized = true;
        }

        fn finalize_logup(&mut self) {
            let batches = (0..self.logup.fracs.len()).collect();
            self.finalize_logup_batched(&batches)
        }

        fn finalize_logup_in_pairs(&mut self) {
            let batches = (0..self.logup.fracs.len()).map(|index| index / 2).collect();
            self.finalize_logup_batched(&batches)
        }
    };
}

pub(crate) use recursion_logup_proxy;
