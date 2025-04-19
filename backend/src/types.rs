use lang::typ::{Nothing, CTyp, Kind};
pub use lang::typ::lub::{Lub, LubError};
use lang::typ::range::CRange;
use lang::id::Tid;
use share::{Ctx, Pretty, DocAllocator, DocBuilder};
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

    pub fn vec(t: &ATyp, n: usize) -> Self {
        ATyp::Vec(Box::new(t.clone()), n)
    }

    pub fn fin(r: &CRange) -> Self {
        ATyp::Fin(r.clone())
    }

    pub fn into_vec(self) -> (ATyp, usize) {
        match self {
            ATyp::Vec(box b, n) => (b, n),
            _ => unreachable!()
        }
    }

    pub fn is_scalar(&self) -> bool {
        matches!(self, ATyp::Scalar)
    }

    pub fn is_vec(&self) -> bool {
        matches!(self, ATyp::Vec(_, _))
    }

    pub fn is_fin(&self) -> bool {
        matches!(self, ATyp::Fin(_))
    }

    pub fn is_bool(&self) -> bool {
        matches!(self, ATyp::Bool)
    }

    pub fn is_group(&self) -> bool {
        matches!(self, ATyp::G1 | ATyp::G2 | ATyp::G1Affine | ATyp::G2Affine | ATyp::GT)
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
                    // ATyp have no Range kinds
                    Kind::Range(_) => unreachable!()
                }
            },
            CTyp::Vec(box t, n) =>
                Some(ATyp::Vec(Box::new(ATyp::from_ctyp(&t, kctx)?), *n)),
            CTyp::Fin(r) => Some(ATyp::Fin(*r)),
            CTyp::Bool => Some(ATyp::Bool),
            CTyp::Uni(_, n) => Some(ATyp::vec_scalar(*n)),
            CTyp::Mle(_, n) => Some(ATyp::vec_scalar(1 << n))
        }
    }
}

/// Least-upper bounds for [Range] overapproximate sets of integers
impl Lub for ATyp {
    type Context = Nothing;
    fn lub_equ(a: &Self, b: &Self, _: &Nothing) -> Result<Self, LubError> {
        match (a, b) {
            (ATyp::Fin(r1), ATyp::Fin(r2)) =>
                Ok(ATyp::Fin(CRange::lub_equ(r1, r2, &Nothing)
                        .map_err(|e| LubError::next(LubError::equ(&a, &b), e))?)),
            (ATyp::Vec(box t1, n1), ATyp::Vec(box t2, n2)) if n1 == n2 => {
                let t = ATyp::lub_equ(t1, t2, &Nothing)
                    .map_err(|e| LubError::next(LubError::equ(&a, &b), e))?;
                Ok(ATyp::vec(&t, *n1))
            },
            (ATyp::Scalar, ATyp::Fin(_)) | (ATyp::Fin(_), ATyp::Scalar) => Ok(ATyp::Scalar),
            (ATyp::G1Affine, ATyp::G1) | (ATyp::G1, ATyp::G1Affine) => Ok(ATyp::G1),
            (ATyp::G2Affine, ATyp::G2) | (ATyp::G2, ATyp::G2Affine) => Ok(ATyp::G2),
            (a, b) if a == b => Ok(a.clone()),
            (a, b) => Err(LubError::equ(&a, &b))
        }
    }
    fn lub_add(a: &Self, b: &Self, ctx: &Self::Context) -> Result<Self, LubError> {
        match (a, b) {
            (ATyp::Fin(r1), ATyp::Fin(r2)) =>
                Ok(ATyp::Fin(CRange::lub_add(r1, r2, ctx)
                    .map_err(|e| LubError::next(LubError::add(&a, &b), e))?)),
            (ATyp::Vec(box t1, n1), ATyp::Vec(box t2, n2)) if n1 == n2 => {
                let t = ATyp::lub_add(t1, t2, ctx)
                    .map_err(|e| LubError::next(LubError::add(&a, &b), e))?;
                Ok(ATyp::vec(&t, *n1))
            },
            (ATyp::Scalar, ATyp::Fin(_)) | (ATyp::Fin(_), ATyp::Scalar) => Ok(ATyp::Scalar),
            (ATyp::G1Affine, ATyp::G1) | (ATyp::G1, ATyp::G1Affine) => Ok(ATyp::G1),
            (ATyp::G2Affine, ATyp::G2) | (ATyp::G2, ATyp::G2Affine) => Ok(ATyp::G2),
            (a, b) if a == b => Ok(a.clone()),
            (a, b) => Err(LubError::add(&a, &b))
        }
    }

    fn lub_sub(a: &Self, b: &Self, ctx: &Self::Context) -> Result<Self, LubError> {
        match (a, b) {
            (ATyp::Fin(r1), ATyp::Fin(r2)) =>
                Ok(ATyp::Fin(CRange::lub_sub(r1, r2, ctx)
                    .map_err(|e| LubError::next(LubError::sub(&a, &b), e))?)),
            (ATyp::Vec(box t1, n1), ATyp::Vec(box t2, n2)) if n1 == n2 => {
                let t = ATyp::lub_sub(t1, t2, ctx)
                    .map_err(|e| LubError::next(LubError::sub(&a, &b), e))?;
                Ok(ATyp::vec(&t, *n1))
            },
            (ATyp::Scalar, ATyp::Fin(_)) | (ATyp::Fin(_), ATyp::Scalar) => Ok(ATyp::Scalar),
            (ATyp::G1Affine, ATyp::G1) | (ATyp::G1, ATyp::G1Affine) => Ok(ATyp::G1),
            (ATyp::G2Affine, ATyp::G2) | (ATyp::G2, ATyp::G2Affine) => Ok(ATyp::G2),
            (a, b) if a == b => Ok(a.clone()),
            (a, b) => Err(LubError::sub(&a, &b))
        }
    }
    fn lub_mul(a: &Self, b: &Self, ctx: &Self::Context) -> Result<Self, LubError> {
        match (a, b) {
            (ATyp::Fin(r1), ATyp::Fin(r2)) =>
                Ok(ATyp::Fin(CRange::lub_mul(r1, r2, ctx)
                    .map_err(|e| LubError::next(LubError::mul(&a, &a), e))?)),
            (ATyp::Vec(box t1, n1), ATyp::Vec(box t2, n2)) if n1 == n2 => {
                let t = ATyp::lub_mul(t1, t2, ctx)
                    .map_err(|e| LubError::next(LubError::mul(&a, &a), e))?;
                Ok(ATyp::vec(&t, *n1))
            },
            (ATyp::Scalar, ATyp::Scalar) => Ok(ATyp::Scalar),
            (ATyp::Scalar, ATyp::Fin(_)) | (ATyp::Fin(_), ATyp::Scalar) => Ok(ATyp::Scalar),
            // Scalar mul
            (ATyp::G1Affine, ATyp::Scalar)
            | (ATyp::Scalar, ATyp::G1Affine) => Ok(ATyp::G1Affine),
            (ATyp::G2Affine, ATyp::Scalar)
            | (ATyp::Scalar, ATyp::G2Affine) => Ok(ATyp::G2Affine),
            (ATyp::G1, ATyp::Scalar)
            | (ATyp::Scalar, ATyp::G1) => Ok(ATyp::G1),
            (ATyp::G2, ATyp::Scalar)
            | (ATyp::Scalar, ATyp::G2) => Ok(ATyp::G2),
            (ATyp::GT, ATyp::Scalar)
            | (ATyp::Scalar, ATyp::GT) => Ok(ATyp::GT),
            // GT billinear map
            (ATyp::G1, ATyp::G2)
            | (ATyp::G2, ATyp::G1)
            | (ATyp::G1, ATyp::G2Affine)
            | (ATyp::G1Affine, ATyp::G2)
            | (ATyp::G1Affine, ATyp::G2Affine)
            | (ATyp::G2Affine, ATyp::G1)
            | (ATyp::G2, ATyp::G1Affine) => Ok(ATyp::GT),
            (a, b) if a == b => Ok(a.clone()),
            (a, b) => Err(LubError::mul(&a, &b))
        }
    }

    fn lub_div(x: &Self, y: &Self, ctx: &Self::Context) -> Result<Self, LubError> {
        match (x, y) {
            (ATyp::Fin(r1), ATyp::Fin(r2)) =>
                Ok(ATyp::Fin(CRange::lub_div(r1, r2, ctx)
                    .map_err(|e| LubError::next(LubError::div(&x, &y), e))?)),
            (ATyp::Vec(box t1, n1), ATyp::Vec(box t2, n2)) if n1 == n2 => {
                let t = ATyp::lub_div(t1, t2, ctx)
                    .map_err(|e| LubError::next(LubError::div(&x, &y), e))?;
                Ok(ATyp::vec(&t, *n1))
            },
            (ATyp::Scalar, ATyp::Scalar) => Ok(ATyp::Scalar),
            (ATyp::Scalar, ATyp::Fin(_)) | (ATyp::Fin(_), ATyp::Scalar) => Ok(ATyp::Scalar),
            (ATyp::G1, ATyp::Scalar) => Ok(ATyp::G1),
            (ATyp::G2, ATyp::Scalar) => Ok(ATyp::G2),
            (ATyp::G1Affine, ATyp::Scalar) => Ok(ATyp::G1Affine),
            (ATyp::G2Affine, ATyp::Scalar) => Ok(ATyp::G2Affine),
            (ATyp::GT, ATyp::Scalar) => Ok(ATyp::GT),
            (a, b) => Err(LubError::div(&a, &b))
        }
    }

    fn lub_rem(x: &Self, y: &Self, ctx: &Self::Context) -> Result<Self, LubError> {
        match (x, y) {
            (ATyp::Scalar, ATyp::Scalar) => Ok(ATyp::Scalar),
            (ATyp::Scalar, ATyp::Fin(_)) | (ATyp::Fin(_), ATyp::Scalar) => Ok(ATyp::Scalar),
            (ATyp::Fin(a), ATyp::Fin(b)) =>
                Ok(ATyp::Fin(CRange::lub_rem(a, b, &Nothing)
                    .map_err(|e| LubError::next(LubError::rem(&x, &y), e))?)),
            // Vec<A> % Vec<B> = Vec<C> where C = A = B
            (ATyp::Vec(box a, n), ATyp::Vec(box b, m)) if n == m =>
                Ok(ATyp::vec(&ATyp::lub_rem(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::rem(&x, &y), e))?, *n)),
            // Vec<A> / c = Vec<A>
            (ATyp::Vec(box b, n), a) =>
                Ok(ATyp::vec(&ATyp::lub_rem(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::rem(&x, &y), e))?, *n)),

            (_, _) => Err(LubError::rem(&x, &y))
        }
    }

    fn lub_pow(x: &Self, y: &Self, ctx: &Self::Context) -> Result<Self, LubError> {
        match (x, y) {
            (ATyp::Fin(a), ATyp::Fin(b)) =>
                Ok(ATyp::Fin(CRange::lub_pow(a, b, &Nothing)
                    .map_err(|e| LubError::next(LubError::pow(&x, &y), e))?)),
            (ATyp::Scalar, ATyp::Fin(_)) => Ok(ATyp::Scalar),
            // Vec<A> ^ Vec<B> = Vec<C>
            (ATyp::Vec(box a, n), ATyp::Vec(box b, m)) if n == m =>
                Ok(ATyp::vec(&ATyp::lub_pow(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::pow(&x, &y), e))?, *n)),
            // Vec<B> ^ A = Vec<A^B>
            (ATyp::Vec(box a, n), b) =>
                Ok(ATyp::vec(&ATyp::lub_pow(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::pow(&x, &y), e))?, *n)),

            (_, _) => Err(LubError::pow(&x, &y))
        }
    }

    fn lub_dot(x: &Self, y: &Self, ctx: &Self::Context) -> Result<Self, LubError> {
        match (x, y) {
            (ATyp::Fin(r1), ATyp::Fin(r2)) =>
                Ok(ATyp::Fin(CRange::lub_dot(r1, r2, ctx)
                    .map_err(|e| LubError::next(LubError::dot(&x, &y), e))?)),
            (ATyp::Vec(box t1, n1), ATyp::Vec(box t2, n2)) if n1 == n2 => {
                let t = ATyp::lub_mul(t1, t2, ctx)
                    .map_err(|e| LubError::next(LubError::dot(&x, &y), e))?;
                Ok(t)
            },
            (a, b) => ATyp::lub_mul(a, b, ctx)
                .map_err(|e| LubError::next(LubError::dot(&x, &y), e))
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

impl<'a, D, A> Pretty<'a, D, A> for ATyp
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.text(format!("{}", self))
    }

    fn is_nil(&self) -> bool {
        false
    }
}
