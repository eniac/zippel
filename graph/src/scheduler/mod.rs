pub mod local_scheduler;
mod cost;
mod asymptotic_cost;

pub use cost::{Cost, CostModel};
pub use asymptotic_cost::AsymptoticCost;
use std::fmt;
use crate::{Dag, UDag};
use backend::ArkConfig;

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
