use lang::typ::{CTyp, Kind};
use lang::typ::range::CRange;
use lang::id::Tid;
use share::Ctx;
use std::fmt;
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]

pub enum ATyp {
    Bool,
    Fin(CRange),
    Vec(Box<ATyp>, usize),
    Scalar,
    G1Affine,
    G2Affine,
    G1,
    G2,
    GT,
}

impl ATyp {
    pub fn vec_scalar(n: usize) -> Self {
        ATyp::Vec(Box::new(ATyp::Scalar), n)
    }

    pub fn vec(t: ATyp, n: usize) -> Self {
        ATyp::Vec(Box::new(t), n)
    }

    pub fn into_vec(self) -> Option<(ATyp, usize)> {
        match self {
            ATyp::Vec(box b, n) => Some((b, n)),
            _ => None
        }
    }

    // Convert from Generic types to arkworks types
    pub fn from_ctyp(typ: &CTyp, kctx: &Ctx<Tid, Kind>) -> Option<Self> {
        match typ {
            CTyp::Base(b) => {
                let k = kctx.get(b).unwrap();
                match k {
                    Kind::Field => Some(ATyp::Scalar),
                    Kind::Group => {
                        // For all other groups that form a pairing
                        for (og, _) in kctx.iter().filter(|(t, k)| k.is_group() && *t != b) {
                            if let Some((_, Kind::Pairing(x, y))) = kctx.find_one(|t, k| k.is_pairing(&og, t)) {
                                if &x == b {
                                    return Some(ATyp::G1);
                                } else if &y == b {
                                    return Some(ATyp::G2);
                                }
                            }
                        }
                        None
                    },
                    Kind::Pairing(_, _) => Some(ATyp::GT),
                    Kind::Scalar(_) => Some(ATyp::Scalar),
                    // CTyp have no Range kinds
                    Kind::Range(_) => unreachable!()
                }
            },
            CTyp::Vec(box t, n) =>
                Some(ATyp::vec(ATyp::from_ctyp(&t, kctx)?, *n)),
            CTyp::Fin(r) => Some(ATyp::Fin(*r)),
            CTyp::Bool => Some(ATyp::Bool),
            CTyp::Uni(_, n) => Some(ATyp::vec_scalar(*n)),
            CTyp::Mle(_, n) => Some(ATyp::vec_scalar(1 << n))
        }
    }
}

impl fmt::Display for ATyp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ATyp::Bool => write!(f, "bool"),
            ATyp::Fin(r) => write!(f, "fin({})", r),
            ATyp::Vec(t, n) => write!(f, "{}[{}]", t, n),
            ATyp::Scalar => write!(f, "scalar"),
            ATyp::G1Affine => write!(f, "G1Affine"),
            ATyp::G2Affine => write!(f, "G2Affine"),
            ATyp::G1 => write!(f, "G1"),
            ATyp::G2 => write!(f, "G2"),
            ATyp::GT => write!(f, "GT")
        }
    }
}
