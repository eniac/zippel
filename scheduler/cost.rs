use crate::lang::{AExp, BExp, Exp};

/// Cost represents the runtime and memory cost of running
/// a zippel expression.
pub trait Cost {
    fn runtime(&self, num_thread: usize) -> f64;
    fn memory(&self, num_thread: usize) -> f64;
}
