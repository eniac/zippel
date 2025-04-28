use std::fmt;
use lang::id::Vid;

#[derive(Debug, Copy, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum DepType {
    Data,
    Transcript,
}

/// Represents edges of graphs in the Zippel language
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Dep(pub DepType, pub Option<Vid>);

impl Dep {
    pub fn new(edge_type: DepType, var: Option<Vid>) -> Dep {
        Dep(edge_type, var)
    }
    pub fn var(var: Vid) -> Dep {
        Dep(DepType::Data, Some(var))
    }

    pub fn transcript() -> Dep {
        Dep(DepType::Transcript, None)
    }

    pub fn transcript_var(var: Vid) -> Dep {
        Dep(DepType::Transcript, Some(var))
    }

    pub fn data() -> Dep {
        Dep(DepType::Data, None)
    }

    pub fn is_data(&self) -> bool {
        self.0 == DepType::Data
    }
    pub fn is_transcript(&self) -> bool {
        self.0 == DepType::Transcript
    }
    pub fn edge_type(&self) -> DepType {
        self.0
    }
    pub fn has_var(&self, var: &Vid) -> bool {
        match &self.1 {
            Some(v) => v == var,
            None => false,
        }
    }
    pub fn get_var(&self) -> Option<Vid> {
        let Dep(_, v) = self;
        v.clone()
    }
}

impl fmt::Display for DepType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            DepType::Data => write!(f, "data"),
            DepType::Transcript => write!(f, "transcript"),
        }
    }
}

impl fmt::Display for Dep {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.1 {
            Some(ref v) => write!(f, "{} {}", self.0, v),
            None => write!(f, "{}", self.0),
        }
    }
}
