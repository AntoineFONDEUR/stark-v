//! Pins the hand-written [`air::clock::ClockGapTable::into_columns`] order to
//! the macro-generated `ClockUpdateColumns` layout: the two must agree for the
//! clock catch-up witness to land in the committed columns the AIR constrains.

use air::trace::prover_columns::ClockUpdateColumns;

#[test]
fn test_clock_gap_columns_match_generated_layout() {
    // into_columns() order: enabler, addr_space, addr, clock_prev, value_0..3.
    assert_eq!(
        ClockUpdateColumns::<()>::NAMES,
        [
            "enabler",
            "addr_space",
            "addr",
            "clock_prev",
            "value_0",
            "value_1",
            "value_2",
            "value_3",
        ]
    );
}
