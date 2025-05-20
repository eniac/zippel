pub mod ilp;
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
pub struct ThreadAlloc(Vec<ThreadId>);

impl ThreadAlloc {
    pub fn new(threads: Vec<ThreadId>) -> Self {
        ThreadAlloc(threads)
    }
}

/// A DAG with thread allocations
pub type TDag<C> = Dag<C, ThreadAlloc>;

impl fmt::Display for ThreadAlloc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Threads [{}]",
            self.0.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(", "))
    }
}

impl ThreadAlloc {
    pub fn size(&self) -> usize {
        self.0.len()
    }
}

/// This trait implements a scheduling algorithm for the DAG.
pub trait Scheduler {
    fn schedule<C: ArkConfig>(self, dag: UDag<C>, miip_gap: f64) -> TDag<C>;
}
