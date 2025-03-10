use std::fmt;
use lang::id::Vid;

/// Represents edges of graphs in the Zippel language
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Dependency {
    Data,       // Data dependency
    Transcript, // Transcript dependency
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Edge {
    pub var: Option<Vid>,
    pub dep: Dependency,
}

impl Edge {
    pub fn new(var: Option<Vid>, dep: Dependency) -> Edge {
        Edge { var, dep }
    }

    pub fn data() -> Edge {
        Edge::new(None, Dependency::Data)
    }

    pub fn data_var(v: &Vid) -> Edge {
        Edge::new(Some(v.clone()), Dependency::Data)
    }

    pub fn transcript() -> Edge {
        Edge::new(None, Dependency::Transcript)
    }

    pub fn transcript_var(v: &Vid) -> Edge {
        Edge::new(Some(v.clone()), Dependency::Transcript)
    }

    pub fn is_data(&self) -> bool {
        self.dep == Dependency::Data
    }

    pub fn is_transcript(&self) -> bool {
        self.dep == Dependency::Transcript
    }
}

impl fmt::Display for Dependency {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Dependency::Data => write!(f, "Data"),
            Dependency::Transcript => write!(f, "Transcript"),
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

