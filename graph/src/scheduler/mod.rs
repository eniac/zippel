pub mod ilp;
mod asymptotic_cost;

pub use asymptotic_cost::{CDag, AsymptoticCost};
use std::fmt;
use backend::ArkConfig;
use good_lp::{
    constraint, default_solver, variable, Expression, ResolutionError, Solver, SolverModel,
    Variable,
};
use crate::{graph::Dag, lang::types::Nothing};
use crate::scheduler::CDag;
use share::{Pretty, DocAllocator, DocBuilder, BoxAllocator};
use log::{debug, info};
use petgraph::graph::NodeIndex;
use std::collections::{BTreeMap, HashMap};

/// Thread identifiers
pub type ThreadId = usize;

/// Allocation of threads to each graph node
pub struct ThreadAlloc(Vec<ThreadId>);

/// A DAG with thread allocations
pub type TDag<C> = Dag<C, ThreadAlloc>;

impl fmt::Display for ThreadAlloc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Threads [{}]",
            self.0.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(", "))
    }
}

/// Scheduler trait, takes in a DAG with costs (CDag) and outputs a scheduled Dag (TDag)
pub trait Scheduler {
    fn schedule<C: ArkConfig>(&self, dag: CDag<C>) -> TDag<C>;
}
