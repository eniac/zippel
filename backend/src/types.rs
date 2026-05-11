use lang::id::Tid;
pub use lang::typ::lub::{Lub, LubError};
use lang::typ::range::CRange;
use lang::typ::{CKind, CTyp, Nothing};
use share::{Ctx, DocAllocator, DocBuilder, Pretty};
use std::fmt;

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Hash)]
pub enum ABase {
    G1,
    G2,
    GT,
    Scalar,
    Bool,
    Fin(CRange),
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Hash)]
pub enum ATyp {
    /// Base type
    Base(ABase),
    /// Vector
    Vec(Box<ATyp>, usize),
    /// Record type with named fields
    Record(Ctx<String, ATyp>),
    /// Univariate polynomial in coefficient form (max degree)
    Uni(usize),
    /// Multilinear extension (num variables)
    Mle(usize),
    /// Virtual polynomial - product of polynomials (num_vars, max_degree)
    VPoly(usize, usize),
}

impl ATyp {
    pub fn scalar() -> Self {
        ATyp::Base(ABase::Scalar)
    }
    pub fn g1() -> Self {
        ATyp::Base(ABase::G1)
    }
    pub fn g2() -> Self {
        ATyp::Base(ABase::G2)
    }
    pub fn gt() -> Self {
        ATyp::Base(ABase::GT)
    }
    pub fn bool() -> Self {
        ATyp::Base(ABase::Bool)
    }
    pub fn fin(r: CRange) -> Self {
        ATyp::Base(ABase::Fin(r))
    }
    pub fn uni(n: usize) -> Self {
        ATyp::Uni(n)
    }
    pub fn vec_scalar(n: usize) -> Self {
        ATyp::Vec(Box::new(ATyp::scalar()), n)
    }
    pub fn vec_bool(n: usize) -> Self {
        ATyp::Vec(Box::new(ATyp::bool()), n)
    }
    pub fn vec_g1(n: usize) -> Self {
        ATyp::Vec(Box::new(ATyp::g1()), n)
    }
    pub fn vec_g2(n: usize) -> Self {
        ATyp::Vec(Box::new(ATyp::g2()), n)
    }
    pub fn vec_gt(n: usize) -> Self {
        ATyp::Vec(Box::new(ATyp::gt()), n)
    }
    pub fn vec_fin(r: CRange, n: usize) -> Self {
        ATyp::Vec(Box::new(ATyp::fin(r)), n)
    }
    pub fn vec(t: &ATyp, n: usize) -> Self {
        ATyp::Vec(Box::new(t.clone()), n)
    }
    pub fn mle(n: usize) -> Self {
        ATyp::Mle(n)
    }
    pub fn vpoly(num_vars: usize, max_degree: usize) -> Self {
        ATyp::VPoly(num_vars, max_degree)
    }
    pub fn into_vec(self) -> (ATyp, usize) {
        match self {
            ATyp::Vec(box b, n) => (b, n),
            ATyp::Uni(n) => (ATyp::scalar(), n),
            _ => unreachable!(),
        }
    }

    pub fn is_scalar(&self) -> bool {
        matches!(self, ATyp::Base(ABase::Scalar))
    }

    pub fn is_vec(&self) -> bool {
        matches!(self, ATyp::Vec(_, _))
    }

    pub fn is_uni(&self) -> bool {
        matches!(self, ATyp::Uni(_))
    }

    pub fn is_mle(&self) -> bool {
        matches!(self, ATyp::Mle(_))
    }

    pub fn is_vpoly(&self) -> bool {
        matches!(self, ATyp::VPoly(_, _))
    }

    pub fn is_fin(&self) -> bool {
        matches!(self, ATyp::Base(ABase::Fin(_)))
    }

    pub fn is_bool(&self) -> bool {
        matches!(self, ATyp::Base(ABase::Bool))
    }

    pub fn is_group(&self) -> bool {
        matches!(self, ATyp::Base(ABase::G1 | ABase::G2 | ABase::GT))
    }

    pub fn into_inner(&self) -> ATyp {
        match self {
            ATyp::Vec(box t, _) => t.into_inner(),
            ATyp::Uni(_) => ATyp::scalar(),
            base => base.clone(),
        }
    }

    pub fn size(&self) -> usize {
        match self {
            ATyp::Vec(t, n) => t.size() * n,
            ATyp::Base(_) => 1,
            ATyp::Record(fields) => fields.iter().map(|(_, t)| t.size()).sum(),
            ATyp::Uni(n) => *n,
            ATyp::Mle(n) => *n,
            ATyp::VPoly(m, n) => m * n,
        }
    }

    // Convert from Generic types to arkworks types
    pub fn from_ctyp(typ: &CTyp, kctx: &Ctx<Tid, CKind>) -> Option<Self> {
        match typ {
            CTyp::Base(b) => {
                let k = kctx.get(b)?;
                match k {
                    CKind::Field => Some(ATyp::scalar()),
                    CKind::Group => {
                        if let Some((x, _y)) = kctx.find_map(|_t, k| k.get_pairing_of(b)) {
                            // If this is a pairing assign the right pairing types
                            if &x == b {
                                Some(ATyp::g1())
                            } else {
                                Some(ATyp::g2())
                            }
                        } else {
                            // Otherwise, return the group type
                            Some(ATyp::g1())
                        }
                    }
                    CKind::Pairing(_, _) => Some(ATyp::gt()),
                    CKind::Scalar(_) => Some(ATyp::scalar()),
                    // ATyp have no Range kinds, post [concretize]
                    CKind::Range(_) | CKind::SizeVar => unreachable!(),
                }
            }
            CTyp::Vec(box t, n) => Some(ATyp::Vec(Box::new(ATyp::from_ctyp(&t, kctx)?), *n)),
            CTyp::Poly(_, m, n) => Some(ATyp::vpoly(*m, *n)),
            CTyp::Fin(r) => Some(ATyp::fin(r.clone())),
            CTyp::Bool => Some(ATyp::bool()),
            CTyp::Record(fields) => {
                let mut atyp_fields = Ctx::new();
                for (name, field_typ) in fields.iter() {
                    if let Some(atyp) = ATyp::from_ctyp(field_typ, kctx) {
                        atyp_fields.insert(name, &atyp);
                    } else {
                        return None;
                    }
                }
                Some(ATyp::Record(atyp_fields))
            }
        }
    }
}

impl Lub for ABase {
    type Context = Nothing;
    fn lub_equ(a: &Self, b: &Self, _: &Nothing) -> Result<Self, LubError> {
        match (a, b) {
            (ABase::Fin(r1), ABase::Fin(r2)) => Ok(ABase::Fin(
                CRange::lub_equ(r1, r2, &Nothing)
                    .map_err(|e| LubError::next(LubError::equ(&a, &b), e))?,
            )),
            (ABase::Scalar, ABase::Fin(_)) | (ABase::Fin(_), ABase::Scalar) => Ok(ABase::Scalar),
            (ABase::G1, ABase::G1) => Ok(ABase::G1),
            (ABase::G2, ABase::G2) => Ok(ABase::G2),
            (ABase::GT, ABase::GT) => Ok(ABase::GT),
            (ABase::Scalar, ABase::Scalar) => Ok(ABase::Scalar),
            (a, b) => Err(LubError::equ(&a, &b)),
        }
    }

    fn lub_add(a: &Self, b: &Self, ctx: &Self::Context) -> Result<Self, LubError> {
        match (a, b) {
            (ABase::Fin(r1), ABase::Fin(r2)) => Ok(ABase::Fin(
                CRange::lub_add(r1, r2, ctx)
                    .map_err(|e| LubError::next(LubError::add(&a, &b), e))?,
            )),
            (ABase::Scalar, ABase::Fin(_)) | (ABase::Fin(_), ABase::Scalar) => Ok(ABase::Scalar),
            (ABase::G1, ABase::G1) => Ok(ABase::G1),
            (ABase::G2, ABase::G2) => Ok(ABase::G2),
            (ABase::GT, ABase::GT) => Ok(ABase::GT),
            (ABase::Scalar, ABase::Scalar) => Ok(ABase::Scalar),
            (a, b) => Err(LubError::add(&a, &b)),
        }
    }

    fn lub_sub(a: &Self, b: &Self, ctx: &Self::Context) -> Result<Self, LubError> {
        match (a, b) {
            (ABase::Fin(r1), ABase::Fin(r2)) => Ok(ABase::Fin(
                CRange::lub_sub(r1, r2, ctx)
                    .map_err(|e| LubError::next(LubError::sub(&a, &b), e))?,
            )),
            (ABase::Scalar, ABase::Fin(_)) | (ABase::Fin(_), ABase::Scalar) => Ok(ABase::Scalar),
            (ABase::G1, ABase::G1) => Ok(ABase::G1),
            (ABase::G2, ABase::G2) => Ok(ABase::G2),
            (ABase::GT, ABase::GT) => Ok(ABase::GT),
            (ABase::Scalar, ABase::Scalar) => Ok(ABase::Scalar),
            (a, b) => Err(LubError::sub(&a, &b)),
        }
    }

    fn lub_mul(a: &Self, b: &Self, ctx: &Self::Context) -> Result<Self, LubError> {
        match (a, b) {
            (ABase::Fin(r1), ABase::Fin(r2)) => Ok(ABase::Fin(
                CRange::lub_mul(r1, r2, ctx)
                    .map_err(|e| LubError::next(LubError::mul(&a, &b), e))?,
            )),
            (ABase::Scalar, ABase::Scalar) => Ok(ABase::Scalar),
            (ABase::Scalar, ABase::Fin(_)) | (ABase::Fin(_), ABase::Scalar) => Ok(ABase::Scalar),
            (ABase::G1, ABase::Scalar) | (ABase::Scalar, ABase::G1) => Ok(ABase::G1),
            (ABase::G2, ABase::Scalar) | (ABase::Scalar, ABase::G2) => Ok(ABase::G2),
            (ABase::GT, ABase::Scalar) | (ABase::Scalar, ABase::GT) => Ok(ABase::GT),
            (a, b) => Err(LubError::mul(&a, &b)),
        }
    }

    fn lub_pair(a: &Self, b: &Self, _ctx: &Self::Context) -> Result<Self, LubError> {
        match (a, b) {
            (ABase::G1, ABase::G2) | (ABase::G2, ABase::G1) => Ok(ABase::GT),
            (a, b) => Err(LubError::pair(&a, &b)),
        }
    }

    fn lub_div(a: &Self, b: &Self, ctx: &Self::Context) -> Result<Self, LubError> {
        match (a, b) {
            (ABase::Fin(r1), ABase::Fin(r2)) => Ok(ABase::Fin(
                CRange::lub_div(r1, r2, ctx)
                    .map_err(|e| LubError::next(LubError::div(&a, &b), e))?,
            )),
            (a, ABase::Fin(_)) => Ok(a.clone()),
            (ABase::Scalar, ABase::Scalar) => Ok(ABase::Scalar),
            (ABase::Fin(_), ABase::Scalar) => Ok(ABase::Scalar),
            (ABase::G1, ABase::Scalar) => Ok(ABase::G1),
            (ABase::G2, ABase::Scalar) => Ok(ABase::G2),
            (ABase::GT, ABase::Scalar) => Ok(ABase::GT),
            (a, b) => Err(LubError::div(&a, &b)),
        }
    }

    fn lub_pow(a: &Self, b: &Self, ctx: &Self::Context) -> Result<Self, LubError> {
        match (a, b) {
            (ABase::Fin(r1), ABase::Fin(r2)) => Ok(ABase::Fin(
                CRange::lub_pow(r1, r2, ctx)
                    .map_err(|e| LubError::next(LubError::pow(&a, &b), e))?,
            )),
            (ABase::Scalar, ABase::Fin(_)) => Ok(ABase::Scalar),
            (a, b) => Err(LubError::pow(&a, &b)),
        }
    }

    fn lub_dot(a: &Self, b: &Self, ctx: &Self::Context) -> Result<Self, LubError> {
        match (a, b) {
            (ABase::Fin(r1), ABase::Fin(r2)) => Ok(ABase::Fin(
                CRange::lub_dot(r1, r2, ctx)
                    .map_err(|e| LubError::next(LubError::dot(&a, &b), e))?,
            )),
            (ABase::Scalar, ABase::Scalar) => Ok(ABase::Scalar),
            (ABase::Scalar, ABase::Fin(_)) | (ABase::Fin(_), ABase::Scalar) => Ok(ABase::Scalar),
            (ABase::G1, ABase::Scalar) | (ABase::Scalar, ABase::G1) => Ok(ABase::G1),
            (ABase::G2, ABase::Scalar) | (ABase::Scalar, ABase::G2) => Ok(ABase::G2),
            (ABase::GT, ABase::Scalar) | (ABase::Scalar, ABase::GT) => Ok(ABase::GT),
            (ABase::G1, ABase::G2) | (ABase::G2, ABase::G1) => Ok(ABase::GT),
            (a, b) => Err(LubError::dot(&a, &b)),
        }
    }

    fn lub_rem(a: &Self, b: &Self, ctx: &Self::Context) -> Result<Self, LubError> {
        match (a, b) {
            (ABase::Fin(r1), ABase::Fin(r2)) => Ok(ABase::Fin(
                CRange::lub_rem(r1, r2, ctx)
                    .map_err(|e| LubError::next(LubError::rem(&a, &b), e))?,
            )),
            (ABase::Scalar, ABase::Fin(r)) => Ok(ABase::Fin(r.clone())),
            (a, b) => Err(LubError::rem(&a, &b)),
        }
    }

    fn lub_and(a: &Self, b: &Self, _: &Self::Context) -> Result<Self, LubError> {
        match (a, b) {
            (ABase::Bool, ABase::Bool) => Ok(ABase::Bool),
            (a, b) => Err(LubError::and(&a, &b)),
        }
    }

    fn lub_concat(a: &Self, b: &Self, _: &Self::Context) -> Result<Self, LubError> {
        Err(LubError::concat(&a, &b))
    }
}

/// Least-upper bounds for [Range] overapproximate sets of integers
impl Lub for ATyp {
    type Context = Nothing;
    fn lub_equ(a: &Self, b: &Self, _: &Nothing) -> Result<Self, LubError> {
        match (a, b) {
            (ATyp::Base(a), ATyp::Base(b)) => ABase::lub_equ(a, b, &Nothing)
                .map(ATyp::Base)
                .map_err(|e| LubError::next(LubError::equ(&a, &b), e)),
            (ATyp::Vec(box t1, n1), ATyp::Vec(box t2, n2)) if n1 == n2 => {
                let t = ATyp::lub_equ(t1, t2, &Nothing)
                    .map_err(|e| LubError::next(LubError::equ(&a, &b), e))?;
                Ok(ATyp::vec(&t, *n1))
            }
            (ATyp::Uni(n1), ATyp::Uni(n2)) if n1 == n2 => Ok(ATyp::uni(*n1)),
            (ATyp::Mle(n1), ATyp::Mle(n2)) if n1 == n2 => Ok(ATyp::mle(*n1)),
            (ATyp::VPoly(m1, n1), ATyp::VPoly(m2, n2)) if m1 == m2 && n1 == n2 => {
                Ok(ATyp::vpoly(*m1, *n1))
            }
            (a, b) => Err(LubError::equ(&a, &b)),
        }
    }

    fn lub_add(a: &Self, b: &Self, ctx: &Self::Context) -> Result<Self, LubError> {
        match (a, b) {
            (ATyp::Base(a), ATyp::Base(b)) => ABase::lub_add(a, b, ctx)
                .map(ATyp::Base)
                .map_err(|e| LubError::next(LubError::add(&a, &b), e)),

            (ATyp::Vec(box t1, n1), ATyp::Vec(box t2, n2)) if n1 == n2 => {
                let t = ATyp::lub_add(t1, t2, ctx)
                    .map_err(|e| LubError::next(LubError::add(&a, &b), e))?;
                Ok(ATyp::vec(&t, *n1))
            }

            (ATyp::Uni(n1), ATyp::Uni(n2)) => Ok(ATyp::uni(*n1.max(n2))),
            (ATyp::Mle(n1), ATyp::Mle(n2)) => Ok(if n1 == n2 {
                ATyp::mle(*n1)
            } else {
                ATyp::vpoly(*n1.max(n2), 1)
            }),
            (ATyp::Uni(n), ATyp::Mle(m)) | (ATyp::Mle(m), ATyp::Uni(n)) => Ok(ATyp::vpoly(*m, *n)),
            (ATyp::VPoly(m1, n1), ATyp::VPoly(m2, n2)) => Ok(ATyp::vpoly(*m1.max(m2), *n1.max(n2))),
            (ATyp::VPoly(m, n), ATyp::Uni(d)) | (ATyp::Uni(d), ATyp::VPoly(m, n)) => {
                Ok(ATyp::vpoly(*m, *n.max(d)))
            }
            (ATyp::VPoly(m, n), ATyp::Mle(v)) | (ATyp::Mle(v), ATyp::VPoly(m, n)) => {
                Ok(ATyp::vpoly(*m.max(v), *n))
            }
            (a, b) => Err(LubError::add(&a, &b)),
        }
    }

    fn lub_sub(a: &Self, b: &Self, ctx: &Self::Context) -> Result<Self, LubError> {
        match (a, b) {
            (ATyp::Base(a), ATyp::Base(b)) => ABase::lub_sub(a, b, ctx)
                .map(ATyp::Base)
                .map_err(|e| LubError::next(LubError::sub(&a, &b), e)),
            (ATyp::Vec(box t1, n1), ATyp::Vec(box t2, n2)) if n1 == n2 => {
                let t = ATyp::lub_sub(t1, t2, ctx)
                    .map_err(|e| LubError::next(LubError::sub(&a, &b), e))?;
                Ok(ATyp::vec(&t, *n1))
            }
            (ATyp::Uni(n1), ATyp::Uni(n2)) => Ok(ATyp::uni(*n1.max(n2))),
            (ATyp::Mle(n1), ATyp::Mle(n2)) => Ok(if n1 == n2 {
                ATyp::mle(*n1)
            } else {
                ATyp::vpoly(*n1.max(n2), 1)
            }),
            (ATyp::Uni(n), ATyp::Mle(m)) | (ATyp::Mle(m), ATyp::Uni(n)) => Ok(ATyp::vpoly(*m, *n)),
            (ATyp::VPoly(m1, n1), ATyp::VPoly(m2, n2)) => Ok(ATyp::vpoly(*m1.max(m2), *n1.max(n2))),
            (ATyp::VPoly(m, n), ATyp::Uni(d)) | (ATyp::Uni(d), ATyp::VPoly(m, n)) => {
                Ok(ATyp::vpoly(*m, *n.max(d)))
            }
            (ATyp::VPoly(m, n), ATyp::Mle(v)) | (ATyp::Mle(v), ATyp::VPoly(m, n)) => {
                Ok(ATyp::vpoly(*m.max(v), *n))
            }
            (a, b) => Err(LubError::sub(&a, &b)),
        }
    }
    fn lub_mul(a: &Self, b: &Self, ctx: &Self::Context) -> Result<Self, LubError> {
        match (a, b) {
            (ATyp::Base(a), ATyp::Base(b)) => ABase::lub_mul(a, b, ctx)
                .map(ATyp::Base)
                .map_err(|e| LubError::next(LubError::mul(&a, &b), e)),
            // Uni * Uni -> Uni (product of univariates stays univariate, degrees add)
            (ATyp::Uni(n1), ATyp::Uni(n2)) => Ok(ATyp::uni(*n1 + *n2)),
            // Mle * Mle -> VPoly (product of multilinears becomes degree 2)
            (ATyp::Mle(m1), ATyp::Mle(m2)) => Ok(ATyp::vpoly(*m1.max(m2), 2)),
            // Uni * Mle -> VPoly (mixed product)
            (ATyp::Uni(n), ATyp::Mle(m)) | (ATyp::Mle(m), ATyp::Uni(n)) => {
                Ok(ATyp::vpoly(*m, *n + 1))
            }
            // VPoly * anything -> VPoly with summed degrees
            (ATyp::VPoly(m1, n1), ATyp::VPoly(m2, n2)) => Ok(ATyp::vpoly(*m1.max(m2), *n1 + *n2)),
            (ATyp::VPoly(m, n), ATyp::Uni(d)) | (ATyp::Uni(d), ATyp::VPoly(m, n)) => {
                Ok(ATyp::vpoly(*m, *n + *d))
            }
            (ATyp::VPoly(m1, n), ATyp::Mle(m2)) | (ATyp::Mle(m2), ATyp::VPoly(m1, n)) => {
                Ok(ATyp::vpoly(*m1.max(m2), *n + 1))
            }
            // Scalar * polynomial -> same polynomial type
            (ATyp::Uni(n1), ATyp::Base(ABase::Scalar))
            | (ATyp::Base(ABase::Scalar), ATyp::Uni(n1)) => Ok(ATyp::uni(*n1)),
            (ATyp::Mle(n1), ATyp::Base(ABase::Scalar))
            | (ATyp::Base(ABase::Scalar), ATyp::Mle(n1)) => Ok(ATyp::mle(*n1)),
            (ATyp::VPoly(m, n), ATyp::Base(ABase::Scalar))
            | (ATyp::Base(ABase::Scalar), ATyp::VPoly(m, n)) => Ok(ATyp::vpoly(*m, *n)),
            (ATyp::Vec(box t1, n1), ATyp::Vec(box t2, n2)) if n1 == n2 => {
                let t = ATyp::lub_mul(t1, t2, ctx)
                    .map_err(|e| LubError::next(LubError::mul(&a, &a), e))?;
                Ok(ATyp::vec(&t, *n1))
            }
            (ATyp::Vec(box t1, n1), b) | (b, ATyp::Vec(box t1, n1)) => {
                let t = ATyp::lub_mul(t1, b, ctx)
                    .map_err(|e| LubError::next(LubError::mul(&a, &b), e))?;
                Ok(ATyp::vec(&t, *n1))
            }
            (a, b) => Err(LubError::mul(&a, &b)),
        }
    }

    fn lub_pair(a: &Self, b: &Self, ctx: &Self::Context) -> Result<Self, LubError> {
        match (a, b) {
            // e(G1, G2) * e(G2, G1) = GT
            (ATyp::Base(a), ATyp::Base(b)) => ABase::lub_pair(a, b, ctx)
                .map(ATyp::Base)
                .map_err(|e| LubError::next(LubError::pair(&a, &b), e)),
            // e(Vec<G1>, Vec<G2>) * e(Vec<G2>, Vec<G1>) = Vec<GT>
            (ATyp::Vec(box t1, n1), ATyp::Vec(box t2, n2)) if n1 == n2 => {
                let t = ATyp::lub_pair(t1, t2, ctx)
                    .map_err(|e| LubError::next(LubError::pair(&a, &b), e))?;
                Ok(ATyp::vec(&t, *n1))
            }
            (a, b) => Err(LubError::pair(&a, &b)),
        }
    }

    fn lub_div(x: &Self, y: &Self, ctx: &Self::Context) -> Result<Self, LubError> {
        match (x, y) {
            (ATyp::Base(a), ATyp::Base(b)) => ABase::lub_div(a, b, ctx)
                .map(ATyp::Base)
                .map_err(|e| LubError::next(LubError::div(&x, &y), e)),
            (ATyp::Uni(n1), ATyp::Uni(n2)) => Ok(ATyp::uni(n1.saturating_sub(*n2))),
            (ATyp::Vec(box t1, n1), ATyp::Vec(box t2, n2)) if n1 == n2 => {
                let t = ATyp::lub_div(t1, t2, ctx)
                    .map_err(|e| LubError::next(LubError::div(&x, &y), e))?;
                Ok(ATyp::vec(&t, *n1))
            }
            (ATyp::Vec(box t1, n1), b) | (b, ATyp::Vec(box t1, n1)) => {
                let t = ATyp::lub_div(t1, b, ctx)
                    .map_err(|e| LubError::next(LubError::div(&x, &y), e))?;
                Ok(ATyp::vec(&t, *n1))
            }
            (a, b) => Err(LubError::div(&a, &b)),
        }
    }

    fn lub_rem(x: &Self, y: &Self, ctx: &Self::Context) -> Result<Self, LubError> {
        match (x, y) {
            (ATyp::Base(a), ATyp::Base(b)) => ABase::lub_rem(a, b, ctx)
                .map(ATyp::Base)
                .map_err(|e| LubError::next(LubError::rem(&x, &y), e)),
            // Vec<A> % Vec<B> = Vec<C> where C = A = B
            (ATyp::Vec(box a, n), ATyp::Vec(box b, m)) if n == m => Ok(ATyp::vec(
                &ATyp::lub_rem(a, b, ctx).map_err(|e| LubError::next(LubError::rem(&x, &y), e))?,
                *n,
            )),
            // Uni<A> % Uni<B> = Uni<B-1>
            (ATyp::Uni(_), ATyp::Uni(n2)) => Ok(ATyp::uni(n2.saturating_sub(1))),
            // Vec<A> % C = Vec<A>
            (ATyp::Vec(box t1, n1), b) | (b, ATyp::Vec(box t1, n1)) => {
                let t = ATyp::lub_rem(t1, b, ctx)
                    .map_err(|e| LubError::next(LubError::rem(&x, &y), e))?;
                Ok(ATyp::vec(&t, *n1))
            }
            (_, _) => Err(LubError::rem(&x, &y)),
        }
    }

    fn lub_pow(x: &Self, y: &Self, ctx: &Self::Context) -> Result<Self, LubError> {
        match (x, y) {
            (ATyp::Base(a), ATyp::Base(b)) => ABase::lub_pow(a, b, ctx)
                .map(ATyp::Base)
                .map_err(|e| LubError::next(LubError::pow(&x, &y), e)),
            // Vec<A> ^ Vec<B> = Vec<C>
            (ATyp::Vec(box a, n), ATyp::Vec(box b, m)) if n == m => Ok(ATyp::vec(
                &ATyp::lub_pow(a, b, ctx).map_err(|e| LubError::next(LubError::pow(&x, &y), e))?,
                *n,
            )),

            // Uni<A> ^ Fin<B> = Uni<A*B>
            (ATyp::Uni(n1), ATyp::Base(ABase::Fin(r))) => Ok(ATyp::uni(n1 * r.len())),
            // Vec<C> ^ C
            (ATyp::Vec(box t1, n1), b) | (b, ATyp::Vec(box t1, n1)) => {
                let t = ATyp::lub_pow(t1, b, ctx)
                    .map_err(|e| LubError::next(LubError::pow(&x, &y), e))?;
                Ok(ATyp::vec(&t, *n1))
            }
            (_, _) => Err(LubError::pow(&x, &y)),
        }
    }

    fn lub_dot(x: &Self, y: &Self, ctx: &Self::Context) -> Result<Self, LubError> {
        match (x, y) {
            (ATyp::Base(a), ATyp::Base(b)) => ABase::lub_dot(a, b, ctx)
                .map(ATyp::Base)
                .map_err(|e| LubError::next(LubError::dot(&x, &y), e)),
            (ATyp::Vec(box t1, n1), ATyp::Vec(box t2, n2)) if n1 == n2 => {
                let t = ATyp::lub_mul(t1, t2, ctx)
                    .map_err(|e| LubError::next(LubError::dot(&x, &y), e))?;
                Ok(t)
            }
            (ATyp::Uni(n1), ATyp::Uni(n2)) if n1 == n2 => Ok(ATyp::scalar()),
            (_, _) => Err(LubError::dot(&x, &y)),
        }
    }

    fn lub_concat(x: &Self, y: &Self, _: &Self::Context) -> Result<Self, LubError> {
        match (x, y) {
            (ATyp::Vec(box t1, n1), ATyp::Vec(box t2, n2)) => {
                let t = ATyp::lub_equ(t1, t2, &Nothing)
                    .map_err(|e| LubError::next(LubError::concat(&x, &y), e))?;
                Ok(ATyp::vec(&t, *n1 + *n2))
            }
            (ATyp::Vec(box t, n), ATyp::Uni(n2)) | (ATyp::Uni(n2), ATyp::Vec(box t, n)) => {
                ATyp::lub_equ(t, &ATyp::scalar(), &Nothing)
                    .map_err(|e| LubError::next(LubError::concat(&x, &y), e))?;
                Ok(ATyp::uni(*n + *n2))
            }
            (a, b) => Err(LubError::concat(&a, &b)),
        }
    }

    fn lub_and(a: &Self, b: &Self, ctx: &Self::Context) -> Result<Self, LubError> {
        match (a, b) {
            (ATyp::Base(a), ATyp::Base(b)) => ABase::lub_and(a, b, ctx)
                .map(ATyp::Base)
                .map_err(|e| LubError::next(LubError::and(&a, &b), e)),
            (ATyp::Vec(box t1, n1), ATyp::Vec(box t2, n2)) if n1 == n2 => {
                let t = ATyp::lub_and(t1, t2, ctx)
                    .map_err(|e| LubError::next(LubError::and(&a, &b), e))?;
                Ok(ATyp::vec(&t, *n1))
            }
            (ATyp::Vec(box t1, _), b) | (b, ATyp::Vec(box t1, _)) => {
                ATyp::lub_and(t1, b, ctx).map_err(|e| LubError::next(LubError::and(&a, &b), e))
            }
            (a, b) => Err(LubError::and(&a, &b)),
        }
    }
}

impl fmt::Display for ABase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ABase::Bool => write!(f, "Bool"),
            ABase::Fin(r) => write!(f, "Fin<{}>", r),
            ABase::Scalar => write!(f, "Scalar"),
            ABase::G1 => write!(f, "G1"),
            ABase::G2 => write!(f, "G2"),
            ABase::GT => write!(f, "GT"),
        }
    }
}
impl fmt::Display for ATyp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ATyp::Base(b) => write!(f, "{}", b),
            ATyp::Vec(t, n) => write!(f, "[{}; {}]", t, n),
            ATyp::Record(fields) => {
                write!(f, "{{|")?;
                for (i, (name, typ)) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {}", name, typ)?;
                }
                write!(f, "|}}")
            }
            ATyp::Uni(n) => write!(f, "Uni<{}>", n),
            ATyp::Mle(n) => write!(f, "Mle<{}>", n),
            ATyp::VPoly(m, n) => write!(f, "VPoly<{}, {}>", m, n),
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

#[cfg(test)]
mod tests {
    use super::*;
    use lang::typ::Nothing;
    use lang::typ::lub::Lub;

    /// `Uni(d) * Mle(n) == VPoly(n, d+1)` (and reverse) — mixed univariate × multilinear product.
    #[test]
    fn lub_mul_uni_mle_pins_vpoly() {
        for (d, n) in &[(0usize, 1usize), (1, 2), (2, 3), (4, 1), (5, 3)] {
            let left = ATyp::lub_mul(&ATyp::uni(*d), &ATyp::mle(*n), &Nothing).unwrap();
            let right = ATyp::lub_mul(&ATyp::mle(*n), &ATyp::uni(*d), &Nothing).unwrap();
            let expected = ATyp::vpoly(*n, d + 1);
            assert_eq!(
                left,
                expected,
                "Uni({d}) * Mle({n}) should equal VPoly({n}, {})",
                d + 1,
            );
            assert_eq!(
                right,
                expected,
                "Mle({n}) * Uni({d}) should equal VPoly({n}, {})",
                d + 1,
            );
        }
    }

    #[test]
    fn vpoly_add_uni() {
        let result = ATyp::lub_add(&ATyp::vpoly(2, 3), &ATyp::uni(5), &Nothing).unwrap();
        assert_eq!(result, ATyp::vpoly(2, 5));
    }

    #[test]
    fn vpoly_sub_mle() {
        let result = ATyp::lub_sub(&ATyp::vpoly(2, 3), &ATyp::mle(5), &Nothing).unwrap();
        assert_eq!(result, ATyp::vpoly(5, 3));
    }

    #[test]
    fn vpoly_equ_same() {
        let result = ATyp::lub_equ(&ATyp::vpoly(2, 3), &ATyp::vpoly(2, 3), &Nothing).unwrap();
        assert_eq!(result, ATyp::vpoly(2, 3));
    }

    #[test]
    fn vpoly_equ_different_fails() {
        let result = ATyp::lub_equ(&ATyp::vpoly(2, 3), &ATyp::vpoly(4, 5), &Nothing);
        assert!(result.is_err());
    }

    #[test]
    fn from_ctyp_preserves_poly_params() {
        use lang::id::Tid;
        use lang::typ::{CKind, CTyp};

        let mut kctx = Ctx::new();
        kctx.insert(&Tid::from("F"), &CKind::Field);

        let ctyp = CTyp::Poly(Tid::from("F"), 3, 5);
        let atyp = ATyp::from_ctyp(&ctyp, &kctx).unwrap();
        assert_eq!(atyp, ATyp::vpoly(3, 5));
    }

    // ========================================================================
    // Property-based tests for algebraic laws
    // ========================================================================

    use arbitrary::{Arbitrary, Unstructured};

    /// Newtype for generating random polynomial ATyp variants
    #[derive(Debug, Clone, PartialEq, Eq)]
    struct PolyATyp(ATyp);

    impl<'a> Arbitrary<'a> for PolyATyp {
        fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
            let variant: u8 = u.int_in_range(0..=2)?;
            Ok(PolyATyp(match variant {
                0 => ATyp::uni(u.int_in_range(1..=10)?),
                1 => ATyp::mle(u.int_in_range(1..=10)?),
                _ => ATyp::vpoly(u.int_in_range(1..=10)?, u.int_in_range(1..=10)?),
            }))
        }
    }

    #[test]
    fn pbt_mul_commutativity() {
        arbtest::arbtest(|u| {
            let a: PolyATyp = u.arbitrary()?;
            let b: PolyATyp = u.arbitrary()?;
            let ab = ATyp::lub_mul(&a.0, &b.0, &Nothing);
            let ba = ATyp::lub_mul(&b.0, &a.0, &Nothing);
            assert_eq!(ab, ba, "mul not commutative: {:?} * {:?}", a.0, b.0);
            Ok(())
        });
    }

    #[test]
    fn pbt_mul_associativity() {
        arbtest::arbtest(|u| {
            let a: PolyATyp = u.arbitrary()?;
            let b: PolyATyp = u.arbitrary()?;
            let c: PolyATyp = u.arbitrary()?;
            let ab = ATyp::lub_mul(&a.0, &b.0, &Nothing).unwrap();
            let ab_c = ATyp::lub_mul(&ab, &c.0, &Nothing);
            let bc = ATyp::lub_mul(&b.0, &c.0, &Nothing).unwrap();
            let a_bc = ATyp::lub_mul(&a.0, &bc, &Nothing);
            assert_eq!(
                ab_c, a_bc,
                "(a*b)*c != a*(b*c) for a={:?}, b={:?}, c={:?}",
                a.0, b.0, c.0
            );
            Ok(())
        });
    }

    #[test]
    fn pbt_add_commutativity() {
        arbtest::arbtest(|u| {
            let a: PolyATyp = u.arbitrary()?;
            let b: PolyATyp = u.arbitrary()?;
            let ab = ATyp::lub_add(&a.0, &b.0, &Nothing);
            let ba = ATyp::lub_add(&b.0, &a.0, &Nothing);
            assert_eq!(ab, ba, "add not commutative: {:?} + {:?}", a.0, b.0);
            Ok(())
        });
    }

    #[test]
    fn pbt_add_associativity() {
        arbtest::arbtest(|u| {
            let a: PolyATyp = u.arbitrary()?;
            let b: PolyATyp = u.arbitrary()?;
            let c: PolyATyp = u.arbitrary()?;
            // add may fail for incompatible types; only test when all succeed
            if let (Ok(ab), Ok(bc)) = (
                ATyp::lub_add(&a.0, &b.0, &Nothing),
                ATyp::lub_add(&b.0, &c.0, &Nothing),
            ) && let (Ok(ab_c), Ok(a_bc)) = (
                ATyp::lub_add(&ab, &c.0, &Nothing),
                ATyp::lub_add(&a.0, &bc, &Nothing),
            ) {
                assert_eq!(
                    ab_c, a_bc,
                    "(a+b)+c != a+(b+c) for a={:?}, b={:?}, c={:?}",
                    a.0, b.0, c.0
                );
            }
            Ok(())
        });
    }

    #[test]
    fn pbt_scalar_mul_identity() {
        arbtest::arbtest(|u| {
            let a: PolyATyp = u.arbitrary()?;
            let sa = ATyp::lub_mul(&ATyp::scalar(), &a.0, &Nothing).unwrap();
            let as_ = ATyp::lub_mul(&a.0, &ATyp::scalar(), &Nothing).unwrap();
            assert_eq!(sa, a.0, "Scalar * a != a for a={:?}", a.0);
            assert_eq!(as_, a.0, "a * Scalar != a for a={:?}", a.0);
            Ok(())
        });
    }

    // ========================================================================
    // Pinning tests for polynomial-shape lub_mul / lub_add / lub_concat / lub_dot
    //
    // These tests fix the current ATyp lub semantics for polynomial shapes so
    // that any accidental change to the degree/num_vars arithmetic gets caught
    // by regressions.  They mirror the Phase-14 m+1 convention documented in
    // `docs/poly-encoding.md` — `Uni(m)` holds a polynomial of max degree `m`
    // (so `m+1` coefficients), `Mle(n)` is the multilinear extension over `n`
    // variables (so `2^n` evaluations), and `VPoly(n, m)` is multivariate with
    // `n` variables and max total degree `m`.
    // ========================================================================

    // ---------- lub_mul ----------

    /// `Uni(m1) * Uni(m2) == Uni(m1 + m2)` — degrees add for univariate product.
    #[test]
    fn lub_mul_uni_uni_pins_degree_sum() {
        for (m1, m2) in &[(0, 0), (0, 1), (1, 2), (2, 3), (3, 4)] {
            let result = ATyp::lub_mul(&ATyp::uni(*m1), &ATyp::uni(*m2), &Nothing).unwrap();
            assert_eq!(
                result,
                ATyp::uni(m1 + m2),
                "Uni({}) * Uni({}) should equal Uni({})",
                m1,
                m2,
                m1 + m2,
            );
        }
    }

    /// `Mle(n) * Mle(n) == VPoly(n, 2)` — product of multilinears is degree 2.
    #[test]
    fn lub_mul_mle_same_vars_is_vpoly_deg_2() {
        for n in 1..=4 {
            let result = ATyp::lub_mul(&ATyp::mle(n), &ATyp::mle(n), &Nothing).unwrap();
            assert_eq!(
                result,
                ATyp::vpoly(n, 2),
                "Mle({n}) * Mle({n}) should equal VPoly({n}, 2)",
            );
        }
    }

    /// `Mle(n1) * Mle(n2)` with `n1 != n2` — current arm uses `max(n1,n2)` for
    /// the num_vars and 2 for the degree.  Pins that behaviour.
    #[test]
    fn lub_mul_mle_distinct_vars_pins_max_and_deg_2() {
        for (n1, n2) in &[(1usize, 2usize), (2, 1), (1, 4), (4, 2), (2, 3), (3, 5)] {
            let result = ATyp::lub_mul(&ATyp::mle(*n1), &ATyp::mle(*n2), &Nothing).unwrap();
            assert_eq!(
                result,
                ATyp::vpoly(*n1.max(n2), 2),
                "Mle({n1}) * Mle({n2}) should equal VPoly(max, 2)",
            );
        }
    }

    /// `VPoly(n1,m1) * VPoly(n2,m2) == VPoly(max(n1,n2), m1+m2)`.
    #[test]
    fn lub_mul_vpoly_vpoly_pins_max_vars_and_sum_degree() {
        for (n1, m1, n2, m2) in &[
            (1, 1, 1, 1),
            (2, 1, 2, 2),
            (2, 2, 3, 1),
            (3, 2, 1, 1),
            (3, 4, 5, 2),
        ] {
            let result =
                ATyp::lub_mul(&ATyp::vpoly(*n1, *m1), &ATyp::vpoly(*n2, *m2), &Nothing).unwrap();
            assert_eq!(
                result,
                ATyp::vpoly(*n1.max(n2), m1 + m2),
                "VPoly({n1},{m1}) * VPoly({n2},{m2}) should equal VPoly(max,sum)",
            );
        }
    }

    /// `VPoly(n,m) * Uni(d) == VPoly(n, m+d)` (in both orders).
    #[test]
    fn lub_mul_vpoly_uni_pins_degree_sum() {
        for (n, m, d) in &[
            (1usize, 1usize, 0usize),
            (2, 2, 1),
            (3, 0, 4),
            (4, 5, 2),
            (2, 3, 4),
        ] {
            let left = ATyp::lub_mul(&ATyp::vpoly(*n, *m), &ATyp::uni(*d), &Nothing).unwrap();
            let right = ATyp::lub_mul(&ATyp::uni(*d), &ATyp::vpoly(*n, *m), &Nothing).unwrap();
            let expected = ATyp::vpoly(*n, m + d);
            assert_eq!(
                left,
                expected,
                "VPoly({n},{m}) * Uni({d}) should equal VPoly({n},{})",
                m + d
            );
            assert_eq!(
                right,
                expected,
                "Uni({d}) * VPoly({n},{m}) should equal VPoly({n},{})",
                m + d
            );
        }
    }

    /// `VPoly(n,m) * Mle(n')` — the arm uses `max(n, n')` for num_vars and
    /// `m + 1` for the degree (multilinear contributes +1 to degree).
    #[test]
    fn lub_mul_vpoly_mle_pins_degree_plus_one() {
        for (n, m, n_mle) in &[
            (1usize, 1usize, 1usize),
            (2, 2, 3),
            (3, 0, 1),
            (4, 5, 4),
            (2, 3, 5),
        ] {
            let left = ATyp::lub_mul(&ATyp::vpoly(*n, *m), &ATyp::mle(*n_mle), &Nothing).unwrap();
            let right = ATyp::lub_mul(&ATyp::mle(*n_mle), &ATyp::vpoly(*n, *m), &Nothing).unwrap();
            let expected = ATyp::vpoly(*n.max(n_mle), m + 1);
            assert_eq!(
                left, expected,
                "VPoly({n},{m}) * Mle({n_mle}) should pin to VPoly(max, m+1)",
            );
            assert_eq!(
                right, expected,
                "Mle({n_mle}) * VPoly({n},{m}) should pin to VPoly(max, m+1)",
            );
        }
    }

    // ---------- lub_add ----------

    /// `Uni(m1) + Uni(m2) == Uni(max(m1, m2))` — sum cannot exceed the larger degree.
    #[test]
    fn lub_add_uni_uni_pins_max_degree() {
        for (m1, m2) in &[(0, 0), (0, 1), (1, 2), (2, 3), (3, 4), (3, 5)] {
            let result = ATyp::lub_add(&ATyp::uni(*m1), &ATyp::uni(*m2), &Nothing).unwrap();
            assert_eq!(
                result,
                ATyp::uni(*m1.max(m2)),
                "Uni({m1}) + Uni({m2}) should equal Uni(max)",
            );
        }
    }

    /// `Mle(n) + Mle(n) == Mle(n)` — sum of multilinears with same num_vars
    /// stays multilinear.
    #[test]
    fn lub_add_mle_same_vars_is_mle() {
        for n in 1..=4 {
            let result = ATyp::lub_add(&ATyp::mle(n), &ATyp::mle(n), &Nothing).unwrap();
            assert_eq!(
                result,
                ATyp::mle(n),
                "Mle({n}) + Mle({n}) should equal Mle({n})"
            );
        }
    }

    /// `Mle(n1) + Mle(n2)` with `n1 != n2` — current arm pins to
    /// `VPoly(max(n1, n2), 1)` (degree-1 multivariate).
    #[test]
    fn lub_add_mle_distinct_vars_pins_vpoly_deg_1() {
        for (n1, n2) in &[(1usize, 2usize), (3, 1), (2, 4), (4, 3)] {
            let result = ATyp::lub_add(&ATyp::mle(*n1), &ATyp::mle(*n2), &Nothing).unwrap();
            assert_eq!(
                result,
                ATyp::vpoly(*n1.max(n2), 1),
                "Mle({n1}) + Mle({n2}) should pin to VPoly(max, 1)",
            );
        }
    }

    /// `VPoly(n1,m1) + VPoly(n2,m2) == VPoly(max(n1,n2), max(m1,m2))`.
    #[test]
    fn lub_add_vpoly_vpoly_pins_max_max() {
        for (n1, m1, n2, m2) in &[
            (1, 1, 1, 1),
            (2, 1, 2, 2),
            (2, 2, 3, 1),
            (3, 2, 1, 1),
            (2, 3, 4, 5),
        ] {
            let result =
                ATyp::lub_add(&ATyp::vpoly(*n1, *m1), &ATyp::vpoly(*n2, *m2), &Nothing).unwrap();
            assert_eq!(
                result,
                ATyp::vpoly(*n1.max(n2), *m1.max(m2)),
                "VPoly({n1},{m1}) + VPoly({n2},{m2}) should equal VPoly(max,max)",
            );
        }
    }

    // ---------- lub_concat ----------

    /// `concat(Vec<Scalar, k>, Uni(m)) == Uni(k + m)` (and reverse).
    /// A vector of k scalar coefficients concatenated with a poly of degree m
    /// yields a poly of degree k+m.
    #[test]
    fn lub_concat_vec_scalar_uni_pins_degree_sum() {
        for (k, m) in &[(1usize, 0usize), (1, 1), (2, 3), (4, 2), (5, 5)] {
            let left = ATyp::lub_concat(&ATyp::vec_scalar(*k), &ATyp::uni(*m), &Nothing).unwrap();
            let right = ATyp::lub_concat(&ATyp::uni(*m), &ATyp::vec_scalar(*k), &Nothing).unwrap();
            let expected = ATyp::uni(k + m);
            assert_eq!(
                left,
                expected,
                "concat(Vec<Scalar,{k}>, Uni({m})) should equal Uni({})",
                k + m,
            );
            assert_eq!(
                right,
                expected,
                "concat(Uni({m}), Vec<Scalar,{k}>) should equal Uni({})",
                k + m,
            );
        }
    }

    /// `concat(Vec<Scalar, k>, Mle(n))` — no arm covers this combination, so
    /// the call returns an error.  Pin the error so anybody adding a future
    /// arm has to update this test consciously.
    #[test]
    fn lub_concat_vec_scalar_mle_pins_error() {
        let result = ATyp::lub_concat(&ATyp::vec_scalar(4), &ATyp::mle(2), &Nothing);
        assert!(
            result.is_err(),
            "concat(Vec<Scalar,4>, Mle(2)) currently has no arm and should error, got {result:?}",
        );
        let result = ATyp::lub_concat(&ATyp::mle(2), &ATyp::vec_scalar(4), &Nothing);
        assert!(
            result.is_err(),
            "concat(Mle(2), Vec<Scalar,4>) currently has no arm and should error, got {result:?}",
        );
    }

    /// `concat(Vec<T,n1>, Vec<T,n2>) == Vec<T,n1+n2>` — sanity pin for the
    /// vector–vector arm used as the comparison baseline for the spec above.
    #[test]
    fn lub_concat_vec_vec_pins_length_sum() {
        let result =
            ATyp::lub_concat(&ATyp::vec_scalar(3), &ATyp::vec_scalar(5), &Nothing).unwrap();
        assert_eq!(result, ATyp::vec_scalar(8));
    }

    // ---------- lub_dot ----------

    /// `dot(Vec<G1, n>, Vec<Scalar, n>) == G1` — MSM type rule (group of the
    /// non-scalar side).
    #[test]
    fn lub_dot_vec_g1_vec_scalar_is_g1() {
        for n in 1..=4 {
            let left = ATyp::lub_dot(&ATyp::vec_g1(n), &ATyp::vec_scalar(n), &Nothing).unwrap();
            let right = ATyp::lub_dot(&ATyp::vec_scalar(n), &ATyp::vec_g1(n), &Nothing).unwrap();
            assert_eq!(
                left,
                ATyp::g1(),
                "dot(Vec<G1,{n}>, Vec<Scalar,{n}>) should be G1"
            );
            assert_eq!(
                right,
                ATyp::g1(),
                "dot(Vec<Scalar,{n}>, Vec<G1,{n}>) should be G1"
            );
        }
    }

    /// `dot(Vec<G2, n>, Vec<Scalar, n>) == G2` — same rule for G2.
    #[test]
    fn lub_dot_vec_g2_vec_scalar_is_g2() {
        for n in 1..=4 {
            let result = ATyp::lub_dot(&ATyp::vec_g2(n), &ATyp::vec_scalar(n), &Nothing).unwrap();
            assert_eq!(
                result,
                ATyp::g2(),
                "dot(Vec<G2,{n}>, Vec<Scalar,{n}>) should be G2"
            );
        }
    }

    /// `dot(Vec<Scalar, n>, Vec<Scalar, n>) == Scalar`.
    #[test]
    fn lub_dot_vec_scalar_vec_scalar_is_scalar() {
        for n in 1..=4 {
            let result =
                ATyp::lub_dot(&ATyp::vec_scalar(n), &ATyp::vec_scalar(n), &Nothing).unwrap();
            assert_eq!(
                result,
                ATyp::scalar(),
                "dot(Vec<Scalar,{n}>, Vec<Scalar,{n}>) should be Scalar"
            );
        }
    }

    /// `dot(Vec<G1, n>, Vec<G2, n>)` — the pairing-style inner product
    /// (Tate/Weil pairing on each component, summed in GT) is **not** wired
    /// up.  The `ATyp::lub_dot` Vec arm delegates to `ATyp::lub_mul` on the
    /// inner types, and `ABase::lub_mul` rejects `G1 * G2`.  Pin the error
    /// so any future implementation of a `dot` -> `pair` rule has to update
    /// this test deliberately.
    #[test]
    fn lub_dot_vec_g1_vec_g2_pins_error() {
        for n in 1..=4 {
            let left = ATyp::lub_dot(&ATyp::vec_g1(n), &ATyp::vec_g2(n), &Nothing);
            let right = ATyp::lub_dot(&ATyp::vec_g2(n), &ATyp::vec_g1(n), &Nothing);
            assert!(
                left.is_err(),
                "dot(Vec<G1,{n}>, Vec<G2,{n}>) currently has no pairing arm and should error, got {left:?}",
            );
            assert!(
                right.is_err(),
                "dot(Vec<G2,{n}>, Vec<G1,{n}>) currently has no pairing arm and should error, got {right:?}",
            );
        }
    }

    /// `dot(Uni(n), Uni(n)) == Scalar` — explicit Uni–Uni arm.
    #[test]
    fn lub_dot_uni_uni_is_scalar() {
        for n in 0..=4 {
            let result = ATyp::lub_dot(&ATyp::uni(n), &ATyp::uni(n), &Nothing).unwrap();
            assert_eq!(
                result,
                ATyp::scalar(),
                "dot(Uni({n}), Uni({n})) should be Scalar"
            );
        }
    }

    /// `dot(Vec<T, n>, Vec<T, m>)` with `n != m` has no covering arm, so it
    /// must error.
    #[test]
    fn lub_dot_mismatched_vec_lengths_errors() {
        let result = ATyp::lub_dot(&ATyp::vec_scalar(3), &ATyp::vec_scalar(4), &Nothing);
        assert!(
            result.is_err(),
            "dot of mismatched Vec lengths should error, got {result:?}",
        );
    }
}
