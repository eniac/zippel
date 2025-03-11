use std::fmt;
use lang::id::Vid;

/// Represents edges of graphs in the Zippel language

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Edge {
    Var(Vid),
    Data,
    Transcript(Vid)
}

impl Edge {
    pub fn var(var: Vid) -> Edge {
        Edge::Var(var)
    }

    pub fn transcript(v: Vid) -> Edge {
        Edge::Transcript(v)
    }
}

impl fmt::Display for Edge {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Edge::Var(v) => write!(f, "{}", v),
            Edge::Data => Ok(()),
            Edge::Transcript(v) => write!(f, "{}", v),
        }
    }
}

