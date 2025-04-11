use std::fmt;
use lang::id::Vid;

/// Represents edges of graphs in the Zippel language
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Edge {
    Var(Vid),
    Data,
    Transcript
}

impl Edge {
    pub fn var(var: Vid) -> Edge {
        Edge::Var(var)
    }

    pub fn transcript() -> Edge {
        Edge::Transcript
    }

    pub fn data() -> Edge {
        Edge::Data
    }
}

impl fmt::Display for Edge {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Edge::Var(v) => write!(f, "{}", v),
            Edge::Data => write!(f, "data"),
            Edge::Transcript => write!(f, "transcript"),
        }
    }
}

