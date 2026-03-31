use std::fmt;

#[derive(Debug, Copy, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum DepType {
    Data,
    Transcript,
}

/// Represents edges of graphs in the Zippel language.
/// Edges are either data dependencies or transcript dependencies.
#[derive(Debug, Copy, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Dep(pub DepType);

impl Dep {
    pub fn new(edge_type: DepType) -> Dep {
        Dep(edge_type)
    }

    pub fn transcript() -> Dep {
        Dep(DepType::Transcript)
    }

    pub fn data() -> Dep {
        Dep(DepType::Data)
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
        write!(f, "{}", self.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dep_data() {
        let dep = Dep::data();
        assert!(dep.is_data());
        assert!(!dep.is_transcript());
    }

    #[test]
    fn test_dep_transcript() {
        let dep = Dep::transcript();
        assert!(dep.is_transcript());
        assert!(!dep.is_data());
    }

    #[test]
    fn test_dep_ord() {
        assert!(Dep::data() < Dep::transcript());
    }

    #[test]
    fn test_dep_copy() {
        let d1 = Dep::data();
        let d2 = d1;
        assert_eq!(d1, d2);
    }
}
