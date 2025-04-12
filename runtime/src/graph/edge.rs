use std::fmt;
use lang::id::Vid;

/// Represents edges of graphs in the Zippel language
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Edge {
    Data(Option<Vid>),
    Transcript,
    Implicit(Option<Vid>),
}

impl Edge {
    pub fn var(var: Vid) -> Edge {
        Edge::Data(Some(var))
    }

    pub fn transcript() -> Edge {
        Edge::Transcript
    }

    pub fn data() -> Edge {
        Edge::Data(None)
    }
    pub fn into_implicit(&self) -> Self {
        match self {
            Edge::Data(v) => Edge::Implicit(v.clone()),
            e => e.clone(),
        }
    }
}

impl fmt::Display for Edge {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Edge::Data(Some(v)) => write!(f, "{}", v),
            Edge::Data(None) => write!(f, ""),
            Edge::Transcript => write!(f, ""),
            Edge::Implicit(Some(v)) => write!(f, "{}", v),
            Edge::Implicit(None) => write!(f, ""),
        }
    }
}

