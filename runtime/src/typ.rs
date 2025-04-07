use std::fmt;

/// Base types for the Zippel language
#[derive(Clone, Copy, PartialEq, Eq, Ord, PartialOrd)]
pub enum RBase {
    Index,
    Scalar,
    G1,
    G2,
    GT,
}

/// Runtime types for the Zippel language
#[derive(Clone, Copy, PartialEq, Eq, Ord, PartialOrd)]
pub enum RTyp {
    Base(RBase),
    Vec(RBase, usize),
}

impl fmt::Display for RBase {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RBase::Index => write!(f, "Index"),
            RBase::Scalar => write!(f, "Scalar"),
            RBase::G1 => write!(f, "G1"),
            RBase::G2 => write!(f, "G2"),
            RBase::GT => write!(f, "GT"),
        }
    }
}

impl fmt::Display for RTyp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RTyp::Base(base) => write!(f, "{}", base),
            RTyp::Vec(base, n) => write!(f, "[{}; {}]", base, n),
        }
    }
}
