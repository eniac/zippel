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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dep_new_data() {
        let dep = Dep::new(DepType::Data, None);
        assert_eq!(dep.0, DepType::Data);
        assert_eq!(dep.1, None);
    }

    #[test]
    fn test_dep_new_transcript() {
        let dep = Dep::new(DepType::Transcript, None);
        assert_eq!(dep.0, DepType::Transcript);
        assert_eq!(dep.1, None);
    }

    #[test]
    fn test_dep_var() {
        let vid = Vid::new("x");
        let dep = Dep::var(vid.clone());
        assert_eq!(dep.0, DepType::Data);
        assert_eq!(dep.1, Some(vid));
    }

    #[test]
    fn test_dep_transcript_constructor() {
        let dep = Dep::transcript();
        assert_eq!(dep.0, DepType::Transcript);
        assert_eq!(dep.1, None);
    }

    #[test]
    fn test_dep_transcript_var() {
        let vid = Vid::new("t");
        let dep = Dep::transcript_var(vid.clone());
        assert_eq!(dep.0, DepType::Transcript);
        assert_eq!(dep.1, Some(vid));
    }

    #[test]
    fn test_dep_data_constructor() {
        let dep = Dep::data();
        assert_eq!(dep.0, DepType::Data);
        assert_eq!(dep.1, None);
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
    fn test_dep_has_var_true() {
        let vid = Vid::new("x");
        let dep = Dep::var(vid.clone());
        assert!(dep.has_var(&vid));
    }

    #[test]
    fn test_dep_has_var_false() {
        let vid = Vid::new("x");
        let dep = Dep::data();
        assert!(!dep.has_var(&vid));
    }

    #[test]
    fn test_dep_has_var_wrong_var() {
        let vid1 = Vid::new("x");
        let vid2 = Vid::new("y");
        let dep = Dep::var(vid1);
        assert!(!dep.has_var(&vid2));
    }

    #[test]
    fn test_dep_get_var_some() {
        let vid = Vid::new("x");
        let dep = Dep::var(vid.clone());
        assert_eq!(dep.get_var(), Some(vid));
    }

    #[test]
    fn test_dep_get_var_none() {
        let dep = Dep::data();
        assert_eq!(dep.get_var(), None);
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
    fn test_dep_display_no_var() {
        let dep = Dep::data();
        assert_eq!(format!("{}", dep), "data");
    }

    #[test]
    fn test_dep_display_with_var() {
        let vid = Vid::new("x");
        let dep = Dep::var(vid);
        let s = format!("{}", dep);
        assert!(s.contains("data"));
        assert!(s.contains("x"));
    }

    #[test]
    fn test_dep_clone() {
        let vid = Vid::new("x");
        let dep1 = Dep::var(vid);
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
}
