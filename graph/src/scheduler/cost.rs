use backend::ArkConfig;
use crate::Op;
use std::fmt;

use share::{Pretty, BoxAllocator, DocAllocator, DocBuilder};

/// Measures the cost of a zippel operation
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Cost(pub f64);

impl<'a, D, A> Pretty<'a, D, A> for Cost
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.text(format!("{:.2}", self.0))
    }

    fn is_nil(&self) -> bool {
        false
    }
}

impl fmt::Display for Cost {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:.2}", self.0)
    }
}

impl From<f64> for Cost {
    fn from(cost: f64) -> Self {
        Cost(cost)
    }
}

/// Implement this trait to give costs to operations in the DAG.
pub trait CostModel<C: ArkConfig> {
    fn cost(&self, op: &Op<C>, nthreads: usize) -> Cost;
}

