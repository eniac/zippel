use std::fmt;

/// The kind of dependency an edge in a [`Dag`](crate::Dag) represents.
///
/// The ordering is significant: `Data < Transcript`, which is relied on when
/// edge weights are sorted or compared.
#[derive(Debug, Copy, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum DepType {
    /// The sink consumes the value produced by the source node.
    Data,
    /// The sink follows the source in the Fiat-Shamir transcript chain.
    ///
    /// Transcript edges form a single chain through all proof and challenge
    /// nodes, which is what makes `Dag::transcript_nodes` a linear walk.
    Transcript,
}

/// Represents edges of graphs in the Zippel language.
/// Edges are either data dependencies or transcript dependencies.
#[derive(Debug, Copy, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Dep(pub DepType);

impl Dep {
    /// Builds a dependency edge of the given kind.
    pub fn new(edge_type: DepType) -> Dep {
        Dep(edge_type)
    }

    /// Builds a transcript-ordering edge.
    pub fn transcript() -> Dep {
        Dep(DepType::Transcript)
    }

    /// Builds a data-dependency edge.
    pub fn data() -> Dep {
        Dep(DepType::Data)
    }

    /// Returns `true` for data-dependency edges.
    pub fn is_data(&self) -> bool {
        self.0 == DepType::Data
    }
    /// Returns `true` for transcript-ordering edges.
    pub fn is_transcript(&self) -> bool {
        self.0 == DepType::Transcript
    }
    /// Returns the underlying [`DepType`] of this edge.
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
