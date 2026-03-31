use std::fmt;

#[derive(Debug, Copy, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum DepType {
    Data,
    Transcript,
}

/// Represents edges of graphs in the Zippel language
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
    fn test_dep_new_data() {
        let dep = Dep::new(DepType::Data);
        assert_eq!(dep.0, DepType::Data);
    }

    #[test]
    fn test_dep_new_transcript() {
        let dep = Dep::new(DepType::Transcript);
        assert_eq!(dep.0, DepType::Transcript);
    }

    #[test]
    fn test_dep_transcript_constructor() {
        let dep = Dep::transcript();
        assert_eq!(dep.0, DepType::Transcript);
    }

    #[test]
    fn test_dep_data_constructor() {
        let dep = Dep::data();
        assert_eq!(dep.0, DepType::Data);
    }

    #[test]
    fn test_dep_is_data_true() {
        let dep = Dep::data();
        assert!(dep.is_data());
    }

    #[test]
    fn test_dep_is_data_false() {
        let dep = Dep::transcript();
        assert!(!dep.is_data());
    }

    #[test]
    fn test_dep_is_transcript_true() {
        let dep = Dep::transcript();
        assert!(dep.is_transcript());
    }

    #[test]
    fn test_dep_is_transcript_false() {
        let dep = Dep::data();
        assert!(!dep.is_transcript());
    }

    #[test]
    fn test_dep_edge_type() {
        let dep = Dep::data();
        assert_eq!(dep.edge_type(), DepType::Data);
        let dep2 = Dep::transcript();
        assert_eq!(dep2.edge_type(), DepType::Transcript);
    }

    #[test]
    fn test_deptype_display_data() {
        let dt = DepType::Data;
        assert_eq!(format!("{}", dt), "data");
    }

    #[test]
    fn test_deptype_display_transcript() {
        let dt = DepType::Transcript;
        assert_eq!(format!("{}", dt), "transcript");
    }

    #[test]
    fn test_dep_display() {
        let dep = Dep::data();
        assert_eq!(format!("{}", dep), "data");
    }

    #[test]
    fn test_dep_clone() {
        let dep1 = Dep::data();
        let dep2 = dep1.clone();
        assert_eq!(dep1, dep2);
    }

    #[test]
    fn test_dep_eq() {
        let dep1 = Dep::data();
        let dep2 = Dep::data();
        assert_eq!(dep1, dep2);
    }

    #[test]
    fn test_dep_ord() {
        let dep1 = Dep::data();
        let dep2 = Dep::transcript();
        assert!(dep1 < dep2);
    }

    #[test]
    fn test_deptype_copy() {
        let dt1 = DepType::Data;
        let dt2 = dt1;
        assert_eq!(dt1, dt2);
    }

    #[test]
    fn test_dep_copy() {
        let dep1 = Dep::data();
        let dep2 = dep1;
        assert_eq!(dep1, dep2);
    }
}
