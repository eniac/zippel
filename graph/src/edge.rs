use crate::scope::ScopedVar;
use std::fmt;
use lang::id::{Tid, TidTraversal};

/// Represents edges of graphs in the Zippel language
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Dependency {
    Data,       // Data dependency
    Transcript, // Transcript dependency
    Implicit    // Implicit dependency
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Edge {
    pub var: Option<ScopedVar>,
    pub dep: Dependency,
}

impl fmt::Display for Dependency {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Dependency::Data => write!(f, "Data"),
            Dependency::Transcript => write!(f, "Transcript"),
            Dependency::Implicit => write!(f, "Implicit"),
        }
    }
}

impl fmt::Display for Edge {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.var {
            Some(var) => write!(f, "{}: {}", var, self.dep),
            None => write!(f, "{}", self.dep),
        }
    }
}

impl TidTraversal for Edge {
    fn tid_traverse<E>(&self, f: &mut dyn FnMut(Tid) -> Result<Tid, E>) -> Result<Self, E> {
        match &self.var {
            Some(var) => Ok(Edge { var: Some(var.tid_traverse(f)?), dep: self.dep.clone() }),
            None => Ok(Edge { var: None, dep: self.dep.clone() }),
        }
    }
}
