use std::fmt;

#[derive(Clone, Copy, PartialEq, Eq, Ord, PartialOrd)]
pub enum RTyp {
    Index,
    Scalar,
    G1,
    G2,
    GT,
    VecG1(usize),
    VecG2(usize),
    VecGT(usize)
}

impl fmt::Display for RTyp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RTyp::Index => write!(f, "Index"),
            RTyp::Scalar => write!(f, "Scalar"),
            RTyp::G1 => write!(f, "G1"),
            RTyp::G2 => write!(f, "G2"),
            RTyp::GT => write!(f, "GT"),
            RTyp::VecG1(n) => write!(f, "[G1; {}]", n),
            RTyp::VecG2(n) => write!(f, "[G2; {}]", n),
            RTyp::VecGT(n) => write!(f, "[GT; {}]", n),
        }
    }
}
