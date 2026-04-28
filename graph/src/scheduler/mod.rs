mod asymptotic_cost;
mod cost;
pub mod local_scheduler;

use crate::{Dag, UDag};
pub use asymptotic_cost::AsymptoticCost;
use backend::ArkConfig;
pub use cost::{Cost, CostModel};
use std::fmt;

/// Thread identifiers
pub type ThreadId = usize;

/// Allocation of threads to each graph node
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct ThreadAlloc(usize);

impl ThreadAlloc {
    pub fn new(threads: usize) -> Self {
        ThreadAlloc(threads)
    }

    pub fn get(&self) -> usize {
        self.0
    }
}

/// A DAG with thread allocations
pub type TDag<C> = Dag<C, ThreadAlloc>;

impl fmt::Display for ThreadAlloc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
/// This trait implements a scheduling algorithm for the DAG.
pub trait Scheduler {
    fn schedule<C: ArkConfig>(self, dag: UDag<C>) -> TDag<C>;
}
