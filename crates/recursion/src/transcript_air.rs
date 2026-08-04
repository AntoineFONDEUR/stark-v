//! Atomic transcript hash-call AIR for recursion.
//!
//! Every enabled row consumes one fixed control tuple and one exact rate
//! chunk, proves the complete Poseidon2 input/output tuple, chains internal
//! sponge states, and emits the final rate block of each hash frame. Separate
//! relations make the remaining ownership explicit: the verifier program
//! supplies control and data, while frame semantics consume final outputs.

use air::digest::M31Word;
use air::poseidon2::poseidon2_traced_state;
use air::trace::Poseidon2Table;
use prover::relations::Relations;
use stwo::core::ColumnVec;
use stwo::core::channel::Channel;
use stwo::core::fields::m31::{BaseField, P};
use stwo::core::fields::qm31::QM31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo_constraint_framework::relation;

use super::transcript::{HashPurpose, TranscriptError, TranscriptTrace};

// State tuple: verifier, hash session, step, and the complete 16-word state.
relation!(HashStateRelation, 19);
// Data tuple: verifier, hash session, step, and the exact eight-word rate chunk.
relation!(HashDataRelation, 11);
// Output tuple: verifier, hash session, final call, purpose bit, and rate output.
relation!(HashOutputRelation, 12);
// Control tuple fixes every call coordinate and frame-boundary selector.
relation!(HashCallControlRelation, 7);

/// Relations connecting hash calls to the fixed verifier program.
#[derive(Clone)]
pub struct TranscriptAirRelations {
    pub state: HashStateRelation,
    pub data: HashDataRelation,
    pub output: HashOutputRelation,
    pub control: HashCallControlRelation,
}

impl TranscriptAirRelations {
    pub fn dummy() -> Self {
        Self {
            state: HashStateRelation::dummy(),
            data: HashDataRelation::dummy(),
            output: HashOutputRelation::dummy(),
            control: HashCallControlRelation::dummy(),
        }
    }

    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            state: HashStateRelation::draw(channel),
            data: HashDataRelation::draw(channel),
            output: HashOutputRelation::draw(channel),
            control: HashCallControlRelation::draw(channel),
        }
    }
}

/// Relation instances used by the macro-generated hash-call component.
#[derive(Clone)]
pub struct TranscriptHashCallRelations {
    pub poseidon2_io: air::relations::relation_types::poseidon2_io,
    pub state: HashStateRelation,
    pub data: HashDataRelation,
    pub output: HashOutputRelation,
    pub control: HashCallControlRelation,
}

impl TranscriptHashCallRelations {
    /// Combine the universal VM Poseidon2 relation with transcript-local relations.
    pub fn new(vm: &Relations, transcript: &TranscriptAirRelations) -> Self {
        Self {
            poseidon2_io: vm.poseidon2_io.clone(),
            state: transcript.state.clone(),
            data: transcript.data.clone(),
            output: transcript.output.clone(),
            control: transcript.control.clone(),
        }
    }
}

stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [],
    embedded_component: true,
    embedded_relations: crate::transcript_air::TranscriptHashCallRelations,
    logup_batch: 2,

    relation poseidon2_io(32);
    relation control(7);
    relation data(11);
    relation state(19);
    relation output(12);

    fn transcript_hash_call(
        verifier_id, call_id, hash_id, step, is_first, is_last, is_draw,
        previous_0, previous_1, previous_2, previous_3,
        previous_4, previous_5, previous_6, previous_7,
        previous_8, previous_9, previous_10, previous_11,
        previous_12, previous_13, previous_14, previous_15,
        chunk_0, chunk_1, chunk_2, chunk_3,
        chunk_4, chunk_5, chunk_6, chunk_7,
        output_0, output_1, output_2, output_3,
        output_4, output_5, output_6, output_7,
        output_8, output_9, output_10, output_11,
        output_12, output_13, output_14, output_15,
    ) {
        constrain is_first * (1 - is_first);
        constrain is_last * (1 - is_last);
        constrain is_draw * (1 - is_draw);
        constrain is_first * (1 - enabler);
        constrain is_last * (1 - enabler);
        constrain is_draw * (1 - enabler);
        constrain is_first * step;
        constrain is_first * previous_0;
        constrain is_first * previous_1;
        constrain is_first * previous_2;
        constrain is_first * previous_3;
        constrain is_first * previous_4;
        constrain is_first * previous_5;
        constrain is_first * previous_6;
        constrain is_first * previous_7;
        constrain is_first * previous_8;
        constrain is_first * previous_9;
        constrain is_first * previous_10;
        constrain is_first * previous_11;
        constrain is_first * previous_12;
        constrain is_first * previous_13;
        constrain is_first * previous_14;
        constrain is_first * previous_15;

        consume poseidon2_io(
            previous_0 + chunk_0,
            previous_1 + chunk_1,
            previous_2 + chunk_2,
            previous_3 + chunk_3,
            previous_4 + chunk_4,
            previous_5 + chunk_5,
            previous_6 + chunk_6,
            previous_7 + chunk_7,
            previous_8, previous_9, previous_10, previous_11,
            previous_12, previous_13, previous_14, previous_15,
            output_0, output_1, output_2, output_3,
            output_4, output_5, output_6, output_7,
            output_8, output_9, output_10, output_11,
            output_12, output_13, output_14, output_15,
        );
        consume control(
            verifier_id, call_id, hash_id, step, is_first, is_last, is_draw,
        );
        consume data(
            verifier_id, hash_id, step,
            chunk_0, chunk_1, chunk_2, chunk_3,
            chunk_4, chunk_5, chunk_6, chunk_7,
        );
        consume(enabler - is_first) state(
            verifier_id, hash_id, step,
            previous_0, previous_1, previous_2, previous_3,
            previous_4, previous_5, previous_6, previous_7,
            previous_8, previous_9, previous_10, previous_11,
            previous_12, previous_13, previous_14, previous_15,
        );
        emit(enabler - is_last) state(
            verifier_id, hash_id, step + 1,
            output_0, output_1, output_2, output_3,
            output_4, output_5, output_6, output_7,
            output_8, output_9, output_10, output_11,
            output_12, output_13, output_14, output_15,
        );
        emit(is_last) output(
            verifier_id, hash_id, call_id, is_draw,
            output_0, output_1, output_2, output_3,
            output_4, output_5, output_6, output_7,
        );

        return (
            output_0, output_1, output_2, output_3,
            output_4, output_5, output_6, output_7,
        );
    }
}

pub use component::air::{Component, Eval};

/// Generate all six interaction entries from the macro-defined frame.
pub fn gen_interaction_trace(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    relations: &Relations,
    transcript_relations: &TranscriptAirRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    component::witness::gen_interaction_trace(
        trace,
        &TranscriptHashCallRelations::new(relations, transcript_relations),
    )
}

/// Materializes validated transcript calls and matching Poseidon2 rows.
pub fn push_transcript_calls(
    table: &mut TranscriptHashCallTable,
    poseidon2: &mut Poseidon2Table,
    verifier_id: u32,
    trace: &TranscriptTrace,
) -> Result<(), TranscriptError> {
    for row in trace.sponge_rows()? {
        let frame = &trace.hash_frames[row.id.hash_id as usize];
        let final_call_id = frame
            .final_call_id()
            .expect("validated frame call range is nonempty and fits u32");
        let is_first = u32::from(row.id.step == 0);
        let is_last = u32::from(row.id.call_id == final_call_id);
        let is_draw = u32::from(frame.purpose == HashPurpose::Draw);
        let mut input = row.previous.map(M31Word::as_u32);
        for (slot, word) in input.iter_mut().zip(row.chunk) {
            *slot = add_m31(*slot, word.as_u32());
        }
        let output = poseidon2_traced_state(poseidon2, input, false, true);
        if output != row.output.map(M31Word::as_u32) {
            return Err(TranscriptError::RecordedPoseidonOutputMismatch {
                call_id: row.id.call_id,
            });
        }

        let mut values = vec![
            verifier_id,
            row.id.call_id,
            row.id.hash_id,
            row.id.step,
            is_first,
            is_last,
            is_draw,
        ];
        values.extend(row.previous.map(M31Word::as_u32));
        values.extend(row.chunk.map(M31Word::as_u32));
        values.extend(row.output.map(M31Word::as_u32));
        let mut table_row = Vec::with_capacity(values.len() + 1);
        table_row.push(1);
        table_row.extend(values);
        table.push_row(&table_row);
    }
    Ok(())
}

fn add_m31(left: u32, right: u32) -> u32 {
    ((u64::from(left) + u64::from(right)) % u64::from(P)) as u32
}

#[cfg(test)]
mod tests {
    use rstest::rstest;
    use stwo::core::pcs::TreeVec;
    use stwo::core::poly::circle::CanonicCoset;
    use stwo_constraint_framework::{FrameworkEval, assert_constraints_on_polys};

    use super::*;
    use crate::transcript::{RecordingTranscriptBackend, TranscriptKernel};

    fn fixture_trace() -> TranscriptTrace {
        let mut kernel = TranscriptKernel::<RecordingTranscriptBackend>::default();
        kernel
            .absorb_u32s(&[1, 2, 3])
            .expect("fixture words are accepted");
        kernel.draw_block().expect("fixture draw succeeds");
        kernel.into_backend().into_trace()
    }

    fn assert_table_satisfies_constraints(table: TranscriptHashCallTable) {
        let relations = Relations::dummy();
        let transcript_relations = TranscriptAirRelations::dummy();
        let trace = table.into_witness();
        let log_size = trace
            .first()
            .map(|column| column.domain.log_size())
            .expect("generated table has columns");
        let (interaction, claimed_sum) =
            gen_interaction_trace(&trace, &relations, &transcript_relations);
        let traces = TreeVec::new(vec![vec![], trace, interaction]);
        let trace_polys = traces.map_cols(|column| column.interpolate());
        let eval = Eval {
            log_size,
            relations: TranscriptHashCallRelations::new(&relations, &transcript_relations),
        };
        assert_constraints_on_polys(
            &trace_polys,
            CanonicCoset::new(log_size),
            |row| {
                eval.evaluate(row);
            },
            claimed_sum,
        );
    }

    #[rstest]
    fn recorded_transcript_calls_satisfy_the_hash_call_air() {
        let mut table = TranscriptHashCallTable::new();
        push_transcript_calls(&mut table, &mut Poseidon2Table::new(), 1, &fixture_trace())
            .expect("validated transcript materializes");
        assert_table_satisfies_constraints(table);
    }

    #[rstest]
    #[should_panic]
    fn first_hash_call_requires_the_zero_initial_state() {
        let mut table = TranscriptHashCallTable::new();
        push_transcript_calls(&mut table, &mut Poseidon2Table::new(), 0, &fixture_trace())
            .expect("validated transcript materializes");
        table.previous_0[0] = 1;
        assert_table_satisfies_constraints(table);
    }

    #[rstest]
    #[should_panic]
    fn frame_boundary_selectors_are_boolean() {
        let mut table = TranscriptHashCallTable::new();
        push_transcript_calls(&mut table, &mut Poseidon2Table::new(), 0, &fixture_trace())
            .expect("validated transcript materializes");
        table.is_last[0] = 2;
        assert_table_satisfies_constraints(table);
    }

    #[rstest]
    fn forged_recorded_poseidon_output_is_rejected_during_materialization() {
        let mut trace = fixture_trace();
        let last_call = trace.poseidon_calls.len() - 1;
        let forged = M31Word::try_from(add_m31(
            trace.poseidon_calls[last_call].output[0].as_u32(),
            1,
        ))
        .expect("modular addition is canonical M31");
        trace.poseidon_calls[last_call].output[0] = forged;
        let last_frame = trace.hash_frames.len() - 1;
        trace.hash_frames[last_frame].output[0] = forged;
        let result = push_transcript_calls(
            &mut TranscriptHashCallTable::new(),
            &mut Poseidon2Table::new(),
            0,
            &trace,
        );
        assert_eq!(
            result,
            Err(TranscriptError::RecordedPoseidonOutputMismatch {
                call_id: last_call as u32,
            })
        );
    }

    #[rstest]
    fn hash_call_constraint_profile_stays_cubic() {
        use stwo_constraint_framework::expr::ExprEvaluator;

        let eval = Eval {
            log_size: 4,
            relations: TranscriptHashCallRelations::new(
                &Relations::dummy(),
                &TranscriptAirRelations::dummy(),
            ),
        };
        let degrees = eval
            .evaluate(ExprEvaluator::new())
            .constraint_degree_bounds();
        assert_eq!((degrees.len(), degrees.into_iter().max()), (27, Some(3)));
    }
}
