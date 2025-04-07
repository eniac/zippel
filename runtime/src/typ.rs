use std::fmt;

/// Runtime types for the Zippel language
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd)]
pub enum RTyp {
    Bool,
    Index,
    Scalar,
    G1,
    G2,
    G1Affine,
    G2Affine,
    GT,
    Vec(Box<RTyp>, usize),
}

impl RTyp {
    pub fn vec_scalar(n: usize) -> Self {
        RTyp::Vec(Box::new(RTyp::Scalar), n)
    }
    pub fn vec_g1(n: usize) -> Self {
        RTyp::Vec(Box::new(RTyp::G1), n)
    }
    pub fn vec_g2(n: usize) -> Self {
        RTyp::Vec(Box::new(RTyp::G2), n)
    }
    pub fn vec_g1_affine(n: usize) -> Self {
        RTyp::Vec(Box::new(RTyp::G1Affine), n)
    }
    pub fn vec_g2_affine(n: usize) -> Self {
        RTyp::Vec(Box::new(RTyp::G2Affine), n)
    }
    pub fn vec_gt(n: usize) -> Self {
        RTyp::Vec(Box::new(RTyp::GT), n)
    }
    pub fn vec_bool(n: usize) -> Self {
        RTyp::Vec(Box::new(RTyp::Bool), n)
    }
    pub fn vec_index(n: usize) -> Self {
        RTyp::Vec(Box::new(RTyp::Index), n)
    }
    pub fn vec(base: RTyp, n: usize) -> Self {
        RTyp::Vec(Box::new(base), n)
    }
}

impl fmt::Display for RTyp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RTyp::Bool => write!(f, "Bool"),
            RTyp::Index => write!(f, "Index"),
            RTyp::Scalar => write!(f, "Scalar"),
            RTyp::G1 => write!(f, "G1"),
            RTyp::G2 => write!(f, "G2"),
            RTyp::G1Affine => write!(f, "G1Affine"),
            RTyp::G2Affine => write!(f, "G2Affine"),
            RTyp::GT => write!(f, "GT"),
            RTyp::Vec(base, n) => write!(f, "[{}; {}]", base, n),
        }
    }
}

#[cfg(test)] use arbitrary::{Arbitrary, Unstructured};
#[cfg(test)]
impl<'a> Arbitrary<'a> for RTyp {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        match u.int_in_range(0..=8)? {
            0 => Ok(RTyp::Index),
            1 => Ok(RTyp::Scalar),
            2 => Ok(RTyp::G1),
            3 => Ok(RTyp::G2),
            4 => Ok(RTyp::G1Affine),
            5 => Ok(RTyp::G2Affine),
            6 => Ok(RTyp::GT),
            7 => Ok(RTyp::Bool),
            _ => {
                let base = RTyp::arbitrary(u)?;
                let n = u.int_in_range(1..=10)?;
                Ok(RTyp::Vec(Box::new(base), n))
            }
        }
    }
}

