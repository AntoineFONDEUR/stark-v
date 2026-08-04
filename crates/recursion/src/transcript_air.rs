//! Atomic transcript hash-call AIR for recursion.
//!
//! Every enabled row consumes one fixed control tuple and one exact rate
//! chunk, proves the complete Poseidon2 input/output tuple, chains internal
//! sponge states, and emits the final rate block of each hash frame. Separate
//! relations make the remaining ownership explicit: the verifier program
//! supplies control and data, while frame semantics consume final outputs.

use air::digest::M31Word;
use air::poseidon2::{T, poseidon2_traced_state};
use air::trace::Poseidon2Table;
use prover::relations::Relations;
use stwo::core::ColumnVec;
use stwo::core::channel::Channel;
use stwo::core::fields::m31::{BaseField, P};
use stwo::core::fields::qm31::QM31;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, RelationEntry, relation,
};
use stwo_macros::define_component_tables;

use super::transcript::{HashPurpose, TranscriptError, TranscriptTrace};

const RATE: usize = T / 2;

define_component_tables! {
    transcript_hash_call: {
        committed: {
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
        },
        constraints: {
            is_first * (1 - is_first),
            is_last * (1 - is_last),
            is_draw * (1 - is_draw),
            is_first * (1 - enabler),
            is_last * (1 - enabler),
            is_draw * (1 - enabler),
            is_first * step,
            is_first * previous_0,
            is_first * previous_1,
            is_first * previous_2,
            is_first * previous_3,
            is_first * previous_4,
            is_first * previous_5,
            is_first * previous_6,
            is_first * previous_7,
            is_first * previous_8,
            is_first * previous_9,
            is_first * previous_10,
            is_first * previous_11,
            is_first * previous_12,
            is_first * previous_13,
            is_first * previous_14,
            is_first * previous_15,
        },
    },
}

use prover_columns::TranscriptHashCallColumns;

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

pub type Component = FrameworkComponent<Eval>;

#[derive(Clone)]
pub struct Eval {
    pub log_size: u32,
    pub relations: Relations,
    pub transcript_relations: TranscriptAirRelations,
}

impl FrameworkEval for Eval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let cols = TranscriptHashCallColumns::from_eval(&mut eval);
        for constraint in cols.constraints() {
            eval.add_constraint(constraint);
        }

        let one = E::F::from(BaseField::from(1));
        let previous = [
            cols.previous_0.clone(),
            cols.previous_1.clone(),
            cols.previous_2.clone(),
            cols.previous_3.clone(),
            cols.previous_4.clone(),
            cols.previous_5.clone(),
            cols.previous_6.clone(),
            cols.previous_7.clone(),
            cols.previous_8.clone(),
            cols.previous_9.clone(),
            cols.previous_10.clone(),
            cols.previous_11.clone(),
            cols.previous_12.clone(),
            cols.previous_13.clone(),
            cols.previous_14.clone(),
            cols.previous_15.clone(),
        ];
        let chunk = [
            cols.chunk_0.clone(),
            cols.chunk_1.clone(),
            cols.chunk_2.clone(),
            cols.chunk_3.clone(),
            cols.chunk_4.clone(),
            cols.chunk_5.clone(),
            cols.chunk_6.clone(),
            cols.chunk_7.clone(),
        ];
        let output = [
            cols.output_0.clone(),
            cols.output_1.clone(),
            cols.output_2.clone(),
            cols.output_3.clone(),
            cols.output_4.clone(),
            cols.output_5.clone(),
            cols.output_6.clone(),
            cols.output_7.clone(),
            cols.output_8.clone(),
            cols.output_9.clone(),
            cols.output_10.clone(),
            cols.output_11.clone(),
            cols.output_12.clone(),
            cols.output_13.clone(),
            cols.output_14.clone(),
            cols.output_15.clone(),
        ];

        let mut poseidon_tuple = Vec::with_capacity(2 * T);
        for (word, previous_word) in previous.iter().enumerate() {
            poseidon_tuple.push(if word < RATE {
                previous_word.clone() + chunk[word].clone()
            } else {
                previous_word.clone()
            });
        }
        poseidon_tuple.extend(output.iter().cloned());
        eval.add_to_relation(RelationEntry::new(
            &self.relations.poseidon2_io,
            -E::EF::from(cols.enabler.clone()),
            &poseidon_tuple,
        ));

        eval.add_to_relation(RelationEntry::new(
            &self.transcript_relations.control,
            -E::EF::from(cols.enabler.clone()),
            &[
                cols.verifier_id.clone(),
                cols.call_id.clone(),
                cols.hash_id.clone(),
                cols.step.clone(),
                cols.is_first.clone(),
                cols.is_last.clone(),
                cols.is_draw.clone(),
            ],
        ));

        let mut data_tuple = vec![
            cols.verifier_id.clone(),
            cols.hash_id.clone(),
            cols.step.clone(),
        ];
        data_tuple.extend(chunk.iter().cloned());
        eval.add_to_relation(RelationEntry::new(
            &self.transcript_relations.data,
            -E::EF::from(cols.enabler.clone()),
            &data_tuple,
        ));

        let mut previous_tuple = vec![
            cols.verifier_id.clone(),
            cols.hash_id.clone(),
            cols.step.clone(),
        ];
        previous_tuple.extend(previous.iter().cloned());
        eval.add_to_relation(RelationEntry::new(
            &self.transcript_relations.state,
            -E::EF::from(cols.enabler.clone() - cols.is_first.clone()),
            &previous_tuple,
        ));
        let mut next_tuple = vec![
            cols.verifier_id.clone(),
            cols.hash_id.clone(),
            cols.step.clone() + one,
        ];
        next_tuple.extend(output.iter().cloned());
        eval.add_to_relation(RelationEntry::new(
            &self.transcript_relations.state,
            E::EF::from(cols.enabler.clone() - cols.is_last.clone()),
            &next_tuple,
        ));

        let mut output_tuple = vec![
            cols.verifier_id.clone(),
            cols.hash_id.clone(),
            cols.call_id.clone(),
            cols.is_draw.clone(),
        ];
        output_tuple.extend(output[..RATE].iter().cloned());
        eval.add_to_relation(RelationEntry::new(
            &self.transcript_relations.output,
            E::EF::from(cols.is_last.clone()),
            &output_tuple,
        ));

        eval.finalize_logup_in_pairs();
        eval
    }
}

/// Generates the interaction trace for all six hash-call relation entries.
pub fn gen_interaction_trace(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    relations: &Relations,
    transcript_relations: &TranscriptAirRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    let cols = TranscriptHashCallColumns::from_iter(trace.iter().map(|eval| &eval.values.data));
    let simd_size = cols.enabler.len();
    let log_size = trace[0].domain.log_size();
    let enabled: Vec<PackedQM31> = cols
        .enabler
        .iter()
        .map(|&value| PackedQM31::from(value))
        .collect();
    let neg_enabled: Vec<PackedQM31> = enabled.iter().map(|&value| -value).collect();
    let neg_non_first: Vec<PackedQM31> = (0..simd_size)
        .map(|row| -PackedQM31::from(cols.enabler[row] - cols.is_first[row]))
        .collect();
    let non_last: Vec<PackedQM31> = (0..simd_size)
        .map(|row| PackedQM31::from(cols.enabler[row] - cols.is_last[row]))
        .collect();
    let last: Vec<PackedQM31> = cols
        .is_last
        .iter()
        .map(|&value| PackedQM31::from(value))
        .collect();

    let in_rate: Vec<Vec<_>> = [
        (cols.previous_0, cols.chunk_0),
        (cols.previous_1, cols.chunk_1),
        (cols.previous_2, cols.chunk_2),
        (cols.previous_3, cols.chunk_3),
        (cols.previous_4, cols.chunk_4),
        (cols.previous_5, cols.chunk_5),
        (cols.previous_6, cols.chunk_6),
        (cols.previous_7, cols.chunk_7),
    ]
    .into_iter()
    .map(|(previous, chunk)| {
        (0..simd_size)
            .map(|row| previous[row] + chunk[row])
            .collect()
    })
    .collect();
    let one = stwo::prover::backend::simd::m31::PackedM31::broadcast(BaseField::from(1));
    let next_step: Vec<_> = (0..simd_size).map(|row| cols.step[row] + one).collect();

    let poseidon_denom = combine!(
        relations.poseidon2_io,
        [
            &in_rate[0],
            &in_rate[1],
            &in_rate[2],
            &in_rate[3],
            &in_rate[4],
            &in_rate[5],
            &in_rate[6],
            &in_rate[7],
            cols.previous_8,
            cols.previous_9,
            cols.previous_10,
            cols.previous_11,
            cols.previous_12,
            cols.previous_13,
            cols.previous_14,
            cols.previous_15,
            cols.output_0,
            cols.output_1,
            cols.output_2,
            cols.output_3,
            cols.output_4,
            cols.output_5,
            cols.output_6,
            cols.output_7,
            cols.output_8,
            cols.output_9,
            cols.output_10,
            cols.output_11,
            cols.output_12,
            cols.output_13,
            cols.output_14,
            cols.output_15
        ]
    );
    let control_denom = combine!(
        transcript_relations.control,
        [
            cols.verifier_id,
            cols.call_id,
            cols.hash_id,
            cols.step,
            cols.is_first,
            cols.is_last,
            cols.is_draw
        ]
    );
    let data_denom = combine!(
        transcript_relations.data,
        [
            cols.verifier_id,
            cols.hash_id,
            cols.step,
            cols.chunk_0,
            cols.chunk_1,
            cols.chunk_2,
            cols.chunk_3,
            cols.chunk_4,
            cols.chunk_5,
            cols.chunk_6,
            cols.chunk_7
        ]
    );
    let previous_denom = combine!(
        transcript_relations.state,
        [
            cols.verifier_id,
            cols.hash_id,
            cols.step,
            cols.previous_0,
            cols.previous_1,
            cols.previous_2,
            cols.previous_3,
            cols.previous_4,
            cols.previous_5,
            cols.previous_6,
            cols.previous_7,
            cols.previous_8,
            cols.previous_9,
            cols.previous_10,
            cols.previous_11,
            cols.previous_12,
            cols.previous_13,
            cols.previous_14,
            cols.previous_15
        ]
    );
    let next_denom = combine!(
        transcript_relations.state,
        [
            cols.verifier_id,
            cols.hash_id,
            &next_step,
            cols.output_0,
            cols.output_1,
            cols.output_2,
            cols.output_3,
            cols.output_4,
            cols.output_5,
            cols.output_6,
            cols.output_7,
            cols.output_8,
            cols.output_9,
            cols.output_10,
            cols.output_11,
            cols.output_12,
            cols.output_13,
            cols.output_14,
            cols.output_15
        ]
    );
    let output_denom = combine!(
        transcript_relations.output,
        [
            cols.verifier_id,
            cols.hash_id,
            cols.call_id,
            cols.is_draw,
            cols.output_0,
            cols.output_1,
            cols.output_2,
            cols.output_3,
            cols.output_4,
            cols.output_5,
            cols.output_6,
            cols.output_7
        ]
    );

    let mut logup_gen = LogupTraceGenerator::new(log_size);
    write_pair!(
        &neg_enabled,
        &poseidon_denom,
        &neg_enabled,
        &control_denom,
        logup_gen
    );
    write_pair!(
        &neg_enabled,
        &data_denom,
        &neg_non_first,
        &previous_denom,
        logup_gen
    );
    write_pair!(&non_last, &next_denom, &last, &output_denom, logup_gen);
    logup_gen.finalize_last()
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
    use stwo_constraint_framework::assert_constraints_on_polys;

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
            relations,
            transcript_relations,
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
            relations: Relations::dummy(),
            transcript_relations: TranscriptAirRelations::dummy(),
        };
        let degrees = eval
            .evaluate(ExprEvaluator::new())
            .constraint_degree_bounds();
        assert_eq!((degrees.len(), degrees.into_iter().max()), (27, Some(3)));
    }
}
