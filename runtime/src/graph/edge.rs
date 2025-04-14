use std::fmt;
use lang::id::Vid;

#[derive(Debug, Copy, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum EdgeType {
    Data,
    Transcript,
    Implicit,
}

/// Represents edges of graphs in the Zippel language
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Edge(pub EdgeType, pub Option<Vid>);

impl Edge {
    pub fn new(edge_type: EdgeType, var: Option<Vid>) -> Edge {
        Edge(edge_type, var)
    }
    pub fn var(var: Vid) -> Edge {
        Edge(EdgeType::Data, Some(var))
    }

    pub fn transcript() -> Edge {
        Edge(EdgeType::Transcript, None)
    }

    pub fn transcript_var(var: Vid) -> Edge {
        Edge(EdgeType::Transcript, Some(var))
    }

    pub fn data() -> Edge {
        Edge(EdgeType::Data, None)
    }

    pub fn implicit() -> Edge {
        Edge(EdgeType::Implicit, None)
    }
}

impl fmt::Display for EdgeType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            EdgeType::Data => write!(f, "data"),
            EdgeType::Transcript => write!(f, "transcript"),
            EdgeType::Implicit => write!(f, "implicit"),
        }
    }
}

impl fmt::Display for Edge {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.1 {
            Some(ref v) => write!(f, "{} {}", self.0, v),
            None => write!(f, "{}", self.0),
        }
    }
}

