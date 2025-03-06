use crate::scope::ScopedVar;
use std::fmt;
use lang::id::Tid;

/// Represents edges of graphs in the Zippel language
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Dependency {
    Data,       // Data dependency
    Transcript, // Transcript dependency
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
