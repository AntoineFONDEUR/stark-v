//! Re-export trace tables and the `trace_op!` macro from the shared air crate.

pub use air::trace::*;

/// Forward `trace_op!` invocations to the macro generated in [`air::trace`].
macro_rules! trace_op {
    ($($tt:tt)*) => {
        air::trace_op!($($tt)*)
    };
}
