use lang::ast::range::CRange;
use lang::id::Tid;
pub use lang::typ::lub::{Lub, LubError};
use lang::typ::{CKind, CTyp, Nothing};
use share::Ctx;
use std::fmt;

/// Binomial coefficient `C(n, k)`.
///
/// Used by `ATyp::physical_len` to count coefficients of `VPoly(n, m)` — the
/// number of multi-indices `(i₁, …, iₙ) ∈ ℕⁿ` with `i₁ + ⋯ + iₙ ≤ m`
/// equals `C(m + n, n)`. See `docs/poly-encoding.md`.
///
/// Panics on overflow — this indicates a type whose physical layout
/// exceeds `usize`, which is a genuine error, not a silent clamp.
pub fn binomial(n: usize, k: usize) -> usize {
    if k > n {
        return 0;
    }
    let k = k.min(n - k);
    let mut result: usize = 1;
    for i in 0..k {
        result = result
            .checked_mul(n - i)
            .expect("binomial: intermediate overflow")
            / (i + 1);
    }
    result
}

/// Atomic (non-aggregate) arkworks-level type.
///
/// `ABase` is the leaf of [`ATyp`]: it names a concrete runtime element kind
/// that a `Value<C>` can hold for a given `ArkConfig`. Source-level base types
/// (`Typ::Base(Tid)`) are collapsed onto these variants by
/// [`ATyp::from_ctyp`], which consults the kind context to decide which
/// arkworks type a bare `Tid` stands for.
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Hash)]
pub enum ABase {
    /// First pairing source group, and the default group when the config
    /// declares no pairing at all.
    G1,
    /// Second pairing source group; only reachable when `kctx` contains a
    /// `Pairing(..)` kind naming this `Tid` as its right component.
    G2,
    /// Pairing target group, the codomain of `e: G1 × G2 → GT`.
    GT,
    /// Element of the scalar field of the configured curve.
    Scalar,
    /// Empty type, occupying zero physical slots; used for operations
    /// evaluated only for effect.
    Unit,
    /// Boolean, the result type of comparisons and of verifier checks.
    Bool,
    /// Machine integer constrained to a concrete range, carried over from the
    /// source-level `Typ::Fin` after concretization.
    Fin(CRange),
}

/// Arkworks-level (IR and runtime) type.
///
/// `ATyp` is the second of Zippel's two type levels: source types
/// (`lang::typ::Typ`) are converted here by [`ATyp::from_ctyp`] once sizes are
/// concrete and kinds are known. The essential difference from the source
/// level is that the single source constructor `Typ::Poly(_, num_vars,
/// max_degree)` is split into the three distinct polynomial encodings
/// [`ATyp::Uni`], [`ATyp::Mle`] and [`ATyp::VPoly`], each with its own
/// coefficient layout (see [`ATyp::physical_len`]). Every `Op<C, R>` in the
/// graph IR reports its result as an `ATyp`.
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Hash)]
pub enum ATyp {
    /// Base type
    Base(ABase),
    /// Vector
    Vec(Box<ATyp>, usize),
    /// Record type with named fields
    Record(Ctx<String, ATyp>),
    /// Univariate polynomial in coefficient form. The parameter is the
    /// **max polynomial degree** (not the coefficient count); coefficient
    /// count is `m + 1`. See `docs/poly-encoding.md`.
    Uni(usize),
    /// Multilinear extension over `n` boolean variables. Coefficient /
    /// evaluation count is `2^n`. See `docs/poly-encoding.md`.
    Mle(usize),
    /// Virtual (multivariate) polynomial `VPoly(n, m)`: `n` variables and
    /// **max total degree** `m`. Coefficient count is `C(m + n, n)`.
    /// See `docs/poly-encoding.md`.
    VPoly(usize, usize),
}

impl ATyp {
    /// The scalar-field type of the configured curve.
    pub fn scalar() -> Self {
        ATyp::Base(ABase::Scalar)
    }
    /// The first pairing source group (also the plain group type).
    pub fn g1() -> Self {
        ATyp::Base(ABase::G1)
    }
    /// The second pairing source group.
    pub fn g2() -> Self {
        ATyp::Base(ABase::G2)
    }
    /// The pairing target group.
    pub fn gt() -> Self {
        ATyp::Base(ABase::GT)
    }
    /// The unit type, which occupies no physical slots.
    pub fn unit() -> Self {
        ATyp::Base(ABase::Unit)
    }
    /// The boolean type.
    pub fn bool() -> Self {
        ATyp::Base(ABase::Bool)
    }
    /// A bounded integer type over the concrete range `r`.
    pub fn fin(r: CRange) -> Self {
        ATyp::Base(ABase::Fin(r))
    }
    /// A univariate polynomial of max degree `n`, i.e. `n + 1` coefficients.
    pub fn uni(n: usize) -> Self {
        ATyp::Uni(n)
    }
    /// A length-`n` vector of scalars.
    pub fn vec_scalar(n: usize) -> Self {
        ATyp::Vec(Box::new(ATyp::scalar()), n)
    }
    /// A length-`n` vector of `G1` elements.
    pub fn vec_g1(n: usize) -> Self {
        ATyp::Vec(Box::new(ATyp::g1()), n)
    }
    /// A length-`n` vector of `G2` elements.
    pub fn vec_g2(n: usize) -> Self {
        ATyp::Vec(Box::new(ATyp::g2()), n)
    }
    /// A length-`n` vector of `GT` elements.
    pub fn vec_gt(n: usize) -> Self {
        ATyp::Vec(Box::new(ATyp::gt()), n)
    }
    /// A length-`n` vector of bounded integers over the range `r`.
    pub fn vec_fin(r: CRange, n: usize) -> Self {
        ATyp::Vec(Box::new(ATyp::fin(r)), n)
    }
    /// A length-`n` vector whose elements have type `t`.
    pub fn vec(t: &ATyp, n: usize) -> Self {
        ATyp::Vec(Box::new(t.clone()), n)
    }
    /// A multilinear extension over `n` boolean variables, i.e. `2^n` slots.
    pub fn mle(n: usize) -> Self {
        ATyp::Mle(n)
    }
    /// A virtual polynomial in `num_vars` variables of max total degree
    /// `max_degree`.
    pub fn vpoly(num_vars: usize, max_degree: usize) -> Self {
        ATyp::VPoly(num_vars, max_degree)
    }
    /// View this type as `(element, length)`. For `Uni(m)`, the length
    /// is the coefficient count `m + 1` (not the degree). This matches
    /// `size()` and the `Vec<F, m + 1>` ↔ `Poly<F, 1, m>` consistency
    /// rule in `docs/poly-encoding.md`.
    ///
    /// # Panics
    /// Panics if `self` is neither a `Vec` nor a `Uni`, or if the `Uni`
    /// coefficient count `m + 1` overflows `usize`.
    pub fn into_vec(self) -> (ATyp, usize) {
        match self {
            ATyp::Vec(deref!(b), n) => (b, n),
            ATyp::Uni(m) => (
                ATyp::scalar(),
                m.checked_add(1).expect("into_vec: m + 1 overflow"),
            ),
            _ => unreachable!(),
        }
    }

    /// Whether this is the scalar-field base type.
    pub fn is_scalar(&self) -> bool {
        matches!(self, ATyp::Base(ABase::Scalar))
    }

    /// Whether this is a vector type; note that polynomial types are *not*
    /// vectors, even though `Uni` shares a flat layout with one.
    pub fn is_vec(&self) -> bool {
        matches!(self, ATyp::Vec(_, _))
    }

    /// Whether this is a univariate polynomial in coefficient form.
    pub fn is_uni(&self) -> bool {
        matches!(self, ATyp::Uni(_))
    }

    /// Whether this is a multilinear extension.
    pub fn is_mle(&self) -> bool {
        matches!(self, ATyp::Mle(_))
    }

    /// Whether this is a general virtual (multivariate) polynomial.
    pub fn is_vpoly(&self) -> bool {
        matches!(self, ATyp::VPoly(_, _))
    }

    /// Whether this is a range-bounded integer type.
    pub fn is_fin(&self) -> bool {
        matches!(self, ATyp::Base(ABase::Fin(_)))
    }

    /// Whether this is the unit type.
    pub fn is_unit(&self) -> bool {
        matches!(self, ATyp::Base(ABase::Unit))
    }

    /// Whether this is the boolean type.
    pub fn is_bool(&self) -> bool {
        matches!(self, ATyp::Base(ABase::Bool))
    }

    /// Whether this is any of the three group types `G1`, `G2` or `GT`.
    pub fn is_group(&self) -> bool {
        matches!(self, ATyp::Base(ABase::G1 | ABase::G2 | ABase::GT))
    }

    /// Whether this is the first pairing source group.
    pub fn is_g1(&self) -> bool {
        matches!(self, ATyp::Base(ABase::G1))
    }

    /// Whether this is the second pairing source group.
    pub fn is_g2(&self) -> bool {
        matches!(self, ATyp::Base(ABase::G2))
    }

    /// Whether this is the pairing target group.
    pub fn is_gt(&self) -> bool {
        matches!(self, ATyp::Base(ABase::GT))
    }

    /// The scalar-level element type obtained by stripping every layer of
    /// aggregation: nested `Vec`s are peeled recursively and any `Uni`
    /// resolves to [`ATyp::scalar`]. Base types, `Mle`, `VPoly` and `Record`
    /// are returned unchanged.
    pub fn into_inner(&self) -> ATyp {
        match self {
            ATyp::Vec(deref!(t), _) => t.into_inner(),
            ATyp::Uni(_) => ATyp::scalar(),
            base => base.clone(),
        }
    }

    /// Number of flattened scalar slots needed to represent a value of
    /// this type — i.e. the **coefficient count** under the canonical
    /// polynomial encoding (see `docs/poly-encoding.md`).
    ///
    /// - `Uni(m)` has `m + 1` coefficients.
    /// - `Mle(n)` has `2^n` evaluations over the boolean hypercube.
    /// - `VPoly(n, m)` has `C(m + n, n)` multi-indices with total
    ///   degree `≤ m`.
    ///
    /// # Panics
    /// Panics if the slot count is not representable: a `Vec` whose
    /// element count times length overflows, a `Uni`/`VPoly` whose degree
    /// arithmetic overflows, or an `Mle` whose variable count does not fit
    /// in a `u32` or makes `1 << n` overflow.
    pub fn physical_len(&self) -> usize {
        match self {
            ATyp::Vec(t, n) => t
                .physical_len()
                .checked_mul(*n)
                .expect("physical_len: Vec element count * length overflow"),
            ATyp::Base(ABase::Unit) => 0,
            ATyp::Base(_) => 1,
            ATyp::Record(fields) => fields.iter().map(|(_, t)| t.physical_len()).sum(),
            ATyp::Uni(m) => m.checked_add(1).expect("physical_len: Uni m + 1 overflow"),
            ATyp::Mle(n) => 1usize
                .checked_shl((*n).try_into().expect("physical_len: Mle n exceeds u32"))
                .expect("physical_len: Mle 1 << n overflow"),
            ATyp::VPoly(n, m) => binomial(
                m.checked_add(*n)
                    .expect("physical_len: VPoly m + n overflow"),
                *n,
            ),
        }
    }

    // Convert from Generic types to arkworks types
    /// Lowers a concrete source type to its arkworks-level counterpart.
    ///
    /// Base types are resolved through the kind context `kctx`: a `Field` or
    /// `Scalar` kind becomes [`ABase::Scalar`], a `Pairing` kind becomes
    /// [`ABase::GT`], and a `Group` kind is routed to `G1` or `G2` by looking
    /// for a `Pairing` kind in `kctx` that mentions it (defaulting to `G1`
    /// when the config declares no pairing). `CTyp::Poly` is split into the
    /// three arkworks polynomial encodings by convention: `Poly(_, 1, m)` is
    /// `Uni(m)`, `Poly(_, n, 1)` with `n >= 2` is `Mle(n)`, and anything else
    /// is `VPoly(m, m * n)`. Arm order matters — `Poly(_, 1, 1)` is a
    /// degree-1 univariate, not a one-variable multilinear.
    ///
    /// Returns `None` if a base type is absent from `kctx`, if a nested field
    /// or element type fails to convert, or if the `VPoly` total-degree bound
    /// `m * n` overflows.
    ///
    /// # Panics
    /// Panics on a `Range` or `SizeVar` kind: those are eliminated by
    /// concretization, so reaching one here means the pipeline was run out of
    /// order.
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
            CTyp::Vec(deref!(t), n) => Some(ATyp::Vec(Box::new(ATyp::from_ctyp(t, kctx)?), n.node)),
            // CTyp::Poly(F, num_vars, max_degree) maps by convention:
            //   (1, m)  → Uni(m)   — univariate, m = max degree
            //   (n, 1)  → Mle(n)   — multilinear, n = num variables (n≥2)
            //   (m, n)  → VPoly(m, m*n) — general, total degree bound m*n
            // Order matters: Poly(F,1,1) hits the Uni arm (degree-1 univariate
            // = linear), not the Mle arm (which requires n≥2).
            CTyp::Poly(_, m_vars, m) if m_vars.node == 1 => Some(ATyp::Uni(m.node)),
            CTyp::Poly(_, n, d) if d.node == 1 && n.node >= 2 => Some(ATyp::Mle(n.node)),
            CTyp::Poly(_, m, n) => Some(ATyp::VPoly(m.node, m.node.checked_mul(n.node)?)),
            CTyp::Fin(r) => Some(ATyp::fin(r.clone())),
            CTyp::Unit => Some(ATyp::unit()),
            CTyp::Bool => Some(ATyp::bool()),
            CTyp::Record(fields) => {
                let mut atyp_fields = Ctx::new();
                for (name, field_typ) in fields.iter() {
                    let atyp = ATyp::from_ctyp(field_typ, kctx)?;
                    atyp_fields.insert(&name.node, &atyp);
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
            (ABase::Unit, ABase::Unit) => Ok(ABase::Unit),
            (ABase::Bool, ABase::Bool) => Ok(ABase::Bool),
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
            (ABase::G1, ABase::G2) | (ABase::G2, ABase::G1) => Ok(ABase::GT),
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

    fn lub_concat(a: &Self, b: &Self, _: &Self::Context) -> Result<Self, LubError> {
        Err(LubError::concat(&a, &b))
    }

    fn lub_and(a: &Self, b: &Self, _: &Self::Context) -> Result<Self, LubError> {
        Err(LubError::and(&a, &b))
    }
}

/// Least-upper bounds for `Range` overapproximate sets of integers
impl Lub for ATyp {
    type Context = Nothing;
    fn lub_equ(a: &Self, b: &Self, _: &Nothing) -> Result<Self, LubError> {
        match (a, b) {
            (ATyp::Base(a), ATyp::Base(b)) => ABase::lub_equ(a, b, &Nothing)
                .map(ATyp::Base)
                .map_err(|e| LubError::next(LubError::equ(&a, &b), e)),
            (ATyp::Vec(deref!(t1), n1), ATyp::Vec(deref!(t2), n2)) if n1 == n2 => {
                let t = ATyp::lub_equ(t1, t2, &Nothing)
                    .map_err(|e| LubError::next(LubError::equ(&a, &b), e))?;
                Ok(ATyp::vec(&t, *n1))
            }
            (ATyp::Uni(n1), ATyp::Uni(n2)) => Ok(ATyp::uni(*n1.max(n2))),
            (ATyp::Mle(n1), ATyp::Mle(n2)) => Ok(ATyp::mle(*n1.max(n2))),
            (ATyp::VPoly(m1, n1), ATyp::VPoly(m2, n2)) => Ok(ATyp::vpoly(*m1.max(m2), *n1.max(n2))),
            (ATyp::Record(fields_a), ATyp::Record(fields_b)) => {
                let mut result_fields = Ctx::new();
                for (name, typ_a) in fields_a.iter() {
                    if let Some(typ_b) = fields_b.get(name) {
                        let lub_typ = ATyp::lub_equ(typ_a, typ_b, &Nothing)
                            .map_err(|e| LubError::next(LubError::equ(&a, &b), e))?;
                        result_fields.insert(name, &lub_typ);
                    }
                }
                Ok(ATyp::Record(result_fields))
            }
            (a, b) => Err(LubError::equ(&a, &b)),
        }
    }

    fn lub_add(a: &Self, b: &Self, ctx: &Self::Context) -> Result<Self, LubError> {
        match (a, b) {
            (ATyp::Base(a), ATyp::Base(b)) => ABase::lub_add(a, b, ctx)
                .map(ATyp::Base)
                .map_err(|e| LubError::next(LubError::add(&a, &b), e)),

            (ATyp::Vec(deref!(t1), n1), ATyp::Vec(deref!(t2), n2)) if n1 == n2 => {
                let t = ATyp::lub_add(t1, t2, ctx)
                    .map_err(|e| LubError::next(LubError::add(&a, &b), e))?;
                Ok(ATyp::vec(&t, *n1))
            }
            // Vec<A> + c = Vec<lub_add(A, c)> — scalar/poly broadcast.
            (ATyp::Vec(deref!(t1), n), b) | (b, ATyp::Vec(deref!(t1), n))
                if !matches!(b, ATyp::Vec(_, _)) =>
            {
                let t = ATyp::lub_add(t1, b, ctx)
                    .map_err(|e| LubError::next(LubError::add(&a, &b), e))?;
                Ok(ATyp::vec(&t, *n))
            }

            (ATyp::Uni(n1), ATyp::Uni(n2)) => Ok(ATyp::uni(*n1.max(n2))),
            (ATyp::Mle(n1), ATyp::Mle(n2)) => Ok(if n1 == n2 {
                ATyp::mle(*n1)
            } else {
                let v = *n1.max(n2);
                ATyp::vpoly(v, v)
            }),
            (ATyp::Uni(n), ATyp::Mle(m)) | (ATyp::Mle(m), ATyp::Uni(n)) => {
                Ok(ATyp::vpoly(*m, (*n).max(*m)))
            }
            (ATyp::VPoly(m1, n1), ATyp::VPoly(m2, n2)) => Ok(ATyp::vpoly(*m1.max(m2), *n1.max(n2))),
            (ATyp::VPoly(m, n), ATyp::Uni(d)) | (ATyp::Uni(d), ATyp::VPoly(m, n)) => {
                Ok(ATyp::vpoly(*m, *n.max(d)))
            }
            (ATyp::VPoly(m, n), ATyp::Mle(v)) | (ATyp::Mle(v), ATyp::VPoly(m, n)) => {
                Ok(ATyp::vpoly(*m.max(v), (*n).max(*v)))
            }
            (ATyp::Uni(n1), ATyp::Base(ABase::Scalar))
            | (ATyp::Base(ABase::Scalar), ATyp::Uni(n1)) => Ok(ATyp::uni(*n1)),
            (ATyp::Mle(n1), ATyp::Base(ABase::Scalar))
            | (ATyp::Base(ABase::Scalar), ATyp::Mle(n1)) => Ok(ATyp::mle(*n1)),
            (ATyp::VPoly(m, n), ATyp::Base(ABase::Scalar))
            | (ATyp::Base(ABase::Scalar), ATyp::VPoly(m, n)) => Ok(ATyp::vpoly(*m, *n)),
            (a, b) => Err(LubError::add(&a, &b)),
        }
    }

    fn lub_sub(a: &Self, b: &Self, ctx: &Self::Context) -> Result<Self, LubError> {
        match (a, b) {
            (ATyp::Base(a), ATyp::Base(b)) => ABase::lub_sub(a, b, ctx)
                .map(ATyp::Base)
                .map_err(|e| LubError::next(LubError::sub(&a, &b), e)),
            (ATyp::Vec(deref!(t1), n1), ATyp::Vec(deref!(t2), n2)) if n1 == n2 => {
                let t = ATyp::lub_sub(t1, t2, ctx)
                    .map_err(|e| LubError::next(LubError::sub(&a, &b), e))?;
                Ok(ATyp::vec(&t, *n1))
            }
            // Vec<A> - c = Vec<lub_sub(A, c)> — broadcast.
            (ATyp::Vec(deref!(t1), n), b) if !matches!(b, ATyp::Vec(_, _)) => {
                let t = ATyp::lub_sub(t1, b, ctx)
                    .map_err(|e| LubError::next(LubError::sub(&a, &b), e))?;
                Ok(ATyp::vec(&t, *n))
            }
            // c - Vec<A> = Vec<lub_sub(c, A)> — broadcast.
            (a, ATyp::Vec(deref!(t2), n)) if !matches!(a, ATyp::Vec(_, _)) => {
                let t = ATyp::lub_sub(a, t2, ctx)
                    .map_err(|e| LubError::next(LubError::sub(&a, &b), e))?;
                Ok(ATyp::vec(&t, *n))
            }
            (ATyp::Uni(n1), ATyp::Uni(n2)) => Ok(ATyp::uni(*n1.max(n2))),
            (ATyp::Mle(n1), ATyp::Mle(n2)) => Ok(if n1 == n2 {
                ATyp::mle(*n1)
            } else {
                let v = *n1.max(n2);
                ATyp::vpoly(v, v)
            }),
            (ATyp::Uni(n), ATyp::Mle(m)) | (ATyp::Mle(m), ATyp::Uni(n)) => {
                Ok(ATyp::vpoly(*m, (*n).max(*m)))
            }
            (ATyp::VPoly(m1, n1), ATyp::VPoly(m2, n2)) => Ok(ATyp::vpoly(*m1.max(m2), *n1.max(n2))),
            (ATyp::VPoly(m, n), ATyp::Uni(d)) | (ATyp::Uni(d), ATyp::VPoly(m, n)) => {
                Ok(ATyp::vpoly(*m, *n.max(d)))
            }
            (ATyp::VPoly(m, n), ATyp::Mle(v)) | (ATyp::Mle(v), ATyp::VPoly(m, n)) => {
                Ok(ATyp::vpoly(*m.max(v), (*n).max(*v)))
            }
            (ATyp::Uni(n1), ATyp::Base(ABase::Scalar))
            | (ATyp::Base(ABase::Scalar), ATyp::Uni(n1)) => Ok(ATyp::uni(*n1)),
            (ATyp::Mle(n1), ATyp::Base(ABase::Scalar))
            | (ATyp::Base(ABase::Scalar), ATyp::Mle(n1)) => Ok(ATyp::mle(*n1)),
            (ATyp::VPoly(m, n), ATyp::Base(ABase::Scalar))
            | (ATyp::Base(ABase::Scalar), ATyp::VPoly(m, n)) => Ok(ATyp::vpoly(*m, *n)),
            (a, b) => Err(LubError::sub(&a, &b)),
        }
    }
    fn lub_mul(a: &Self, b: &Self, ctx: &Self::Context) -> Result<Self, LubError> {
        match (a, b) {
            (ATyp::Base(a), ATyp::Base(b)) => ABase::lub_mul(a, b, ctx)
                .map(ATyp::Base)
                .map_err(|e| LubError::next(LubError::mul(&a, &b), e)),
            // Uni * Uni -> Uni (product of univariates stays univariate, degrees add)
            (ATyp::Uni(n1), ATyp::Uni(n2)) => Ok(ATyp::uni(
                n1.checked_add(*n2).ok_or_else(|| LubError::mul(&a, &b))?,
            )),
            // Mle * Mle -> VPoly (total degrees add: Mle(n) has total degree n)
            (ATyp::Mle(m1), ATyp::Mle(m2)) => Ok(ATyp::vpoly(
                *m1.max(m2),
                m1.checked_add(*m2).ok_or_else(|| LubError::mul(&a, &b))?,
            )),
            // Uni * Mle -> VPoly (Uni(n) has total degree n, Mle(m) has total degree m)
            (ATyp::Uni(n), ATyp::Mle(m)) | (ATyp::Mle(m), ATyp::Uni(n)) => Ok(ATyp::vpoly(
                *m,
                n.checked_add(*m).ok_or_else(|| LubError::mul(&a, &b))?,
            )),
            // VPoly * anything -> VPoly with summed degrees
            (ATyp::VPoly(m1, n1), ATyp::VPoly(m2, n2)) => Ok(ATyp::vpoly(
                *m1.max(m2),
                n1.checked_add(*n2).ok_or_else(|| LubError::mul(&a, &b))?,
            )),
            (ATyp::VPoly(m, n), ATyp::Uni(d)) | (ATyp::Uni(d), ATyp::VPoly(m, n)) => Ok(
                ATyp::vpoly(*m, n.checked_add(*d).ok_or_else(|| LubError::mul(&a, &b))?),
            ),
            (ATyp::VPoly(m1, n), ATyp::Mle(m2)) | (ATyp::Mle(m2), ATyp::VPoly(m1, n)) => {
                Ok(ATyp::vpoly(
                    *m1.max(m2),
                    n.checked_add(*m2).ok_or_else(|| LubError::mul(&a, &b))?,
                ))
            }
            // Scalar * polynomial -> same polynomial type
            (ATyp::Uni(n1), ATyp::Base(ABase::Scalar))
            | (ATyp::Base(ABase::Scalar), ATyp::Uni(n1)) => Ok(ATyp::uni(*n1)),
            (ATyp::Mle(n1), ATyp::Base(ABase::Scalar))
            | (ATyp::Base(ABase::Scalar), ATyp::Mle(n1)) => Ok(ATyp::mle(*n1)),
            (ATyp::VPoly(m, n), ATyp::Base(ABase::Scalar))
            | (ATyp::Base(ABase::Scalar), ATyp::VPoly(m, n)) => Ok(ATyp::vpoly(*m, *n)),
            (ATyp::Vec(deref!(t1), n1), ATyp::Vec(deref!(t2), n2)) if n1 == n2 => {
                let t = ATyp::lub_mul(t1, t2, ctx)
                    .map_err(|e| LubError::next(LubError::mul(&a, &a), e))?;
                Ok(ATyp::vec(&t, *n1))
            }
            (ATyp::Vec(deref!(t1), n1), b) | (b, ATyp::Vec(deref!(t1), n1)) => {
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
            (ATyp::Vec(deref!(t1), n1), ATyp::Vec(deref!(t2), n2)) if n1 == n2 => {
                let t = ATyp::lub_pair(t1, t2, ctx)
                    .map_err(|e| LubError::next(LubError::pair(&a, &b), e))?;
                Ok(ATyp::vec(&t, *n1))
            }
            // Vec<A> * c = Vec<lub_pair(A, c)> — scalar broadcast, matching
            // CTyp::lub_pair.
            (ATyp::Vec(deref!(t1), n), b) | (b, ATyp::Vec(deref!(t1), n))
                if !matches!(b, ATyp::Vec(_, _)) =>
            {
                let t = ATyp::lub_pair(t1, b, ctx)
                    .map_err(|e| LubError::next(LubError::pair(&a, &b), e))?;
                Ok(ATyp::vec(&t, *n))
            }
            (a, b) => Err(LubError::pair(&a, &b)),
        }
    }

    fn lub_div(x: &Self, y: &Self, ctx: &Self::Context) -> Result<Self, LubError> {
        match (x, y) {
            (ATyp::Base(a), ATyp::Base(b)) => ABase::lub_div(a, b, ctx)
                .map(ATyp::Base)
                .map_err(|e| LubError::next(LubError::div(&x, &y), e)),
            // Both `Uni` indices are degree *upper bounds*, not exact degrees.
            // A degree-≤ n1 dividend divided by any nonzero divisor still has
            // degree ≤ n1, so the quotient keeps the dividend's bound; the old
            // `n1 - n2` rule was unsound whenever the divisor's actual degree
            // fell below its declared bound.
            (ATyp::Uni(n1), ATyp::Uni(_)) => Ok(ATyp::uni(*n1)),
            (ATyp::Uni(n1), ATyp::Base(ABase::Scalar | ABase::Fin(_))) => Ok(ATyp::uni(*n1)),
            (ATyp::Mle(n1), ATyp::Base(ABase::Scalar | ABase::Fin(_))) => Ok(ATyp::mle(*n1)),
            (ATyp::VPoly(m, n), ATyp::Base(ABase::Scalar | ABase::Fin(_))) => {
                Ok(ATyp::vpoly(*m, *n))
            }
            (ATyp::Vec(deref!(t1), n1), ATyp::Vec(deref!(t2), n2)) if n1 == n2 => {
                let t = ATyp::lub_div(t1, t2, ctx)
                    .map_err(|e| LubError::next(LubError::div(&x, &y), e))?;
                Ok(ATyp::vec(&t, *n1))
            }
            (ATyp::Vec(deref!(t1), n1), b) => {
                let t = ATyp::lub_div(t1, b, ctx)
                    .map_err(|e| LubError::next(LubError::div(&x, &y), e))?;
                Ok(ATyp::vec(&t, *n1))
            }
            (ATyp::Base(ABase::Fin(_)), ATyp::Vec(ATyp::Base(ABase::Fin(_)), _)) => {
                Err(LubError::div(&x, &y))
            }
            (a, ATyp::Vec(deref!(t2), n2)) => {
                let t = ATyp::lub_div(a, t2, ctx)
                    .map_err(|e| LubError::next(LubError::div(&x, &y), e))?;
                Ok(ATyp::vec(&t, *n2))
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
            (ATyp::Vec(deref!(a), n), ATyp::Vec(deref!(b), m)) if n == m => Ok(ATyp::vec(
                &ATyp::lub_rem(a, b, ctx).map_err(|e| LubError::next(LubError::rem(&x, &y), e))?,
                *n,
            )),
            // Uni<A> % Uni<B> = Uni<B-1> (requires B > 0)
            (ATyp::Uni(_), ATyp::Uni(n2)) if *n2 > 0 => Ok(ATyp::uni(
                n2.checked_sub(1).ok_or_else(|| LubError::rem(&x, &y))?,
            )),
            // Vec<A> % C = Vec<lub_rem(A, C)>; scalar-left vector remainder
            // is not Groebner-lowerable and falls through to an error.
            (ATyp::Vec(deref!(t1), n1), b) => {
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
            // Uni<A> ^ Fin<B> = Uni<A*B>
            (ATyp::Uni(n1), ATyp::Base(ABase::Fin(r))) => Ok(ATyp::uni(
                n1.checked_mul(r.len())
                    .ok_or_else(|| LubError::pow(&x, &y))?,
            )),
            // Vec<C> ^ C. Vector exponents and scalar-left vector
            // exponentiation are not runtime-supported.
            (ATyp::Vec(deref!(t1), n1), b) => {
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
            (ATyp::Vec(ATyp::Base(ABase::G1), n1), ATyp::Vec(ATyp::Base(ABase::G2), n2))
            | (ATyp::Vec(ATyp::Base(ABase::G2), n1), ATyp::Vec(ATyp::Base(ABase::G1), n2))
                if n1 == n2 =>
            {
                Ok(ATyp::gt())
            }
            (ATyp::Vec(deref!(t1), n1), ATyp::Vec(deref!(t2), n2)) if n1 == n2 => {
                let t = ATyp::lub_mul(t1, t2, ctx)
                    .map_err(|e| LubError::next(LubError::dot(&x, &y), e))?;
                Ok(t)
            }
            (_, _) => Err(LubError::dot(&x, &y)),
        }
    }

    fn lub_concat(x: &Self, y: &Self, _: &Self::Context) -> Result<Self, LubError> {
        match (x, y) {
            (ATyp::Vec(deref!(t1), n1), ATyp::Vec(deref!(t2), n2)) => {
                let t = ATyp::lub_equ(t1, t2, &Nothing)
                    .map_err(|e| LubError::next(LubError::concat(&x, &y), e))?;
                Ok(ATyp::vec(
                    &t,
                    n1.checked_add(*n2)
                        .ok_or_else(|| LubError::concat(&x, &y))?,
                ))
            }
            (ATyp::Vec(deref!(t1), n1), b) => {
                let t = ATyp::lub_equ(t1, b, &Nothing)
                    .map_err(|e| LubError::next(LubError::concat(&x, &y), e))?;
                Ok(ATyp::vec(
                    &t,
                    n1.checked_add(1).ok_or_else(|| LubError::concat(&x, &y))?,
                ))
            }
            (a, ATyp::Vec(deref!(t2), n2)) => {
                let t = ATyp::lub_equ(a, t2, &Nothing)
                    .map_err(|e| LubError::next(LubError::concat(&x, &y), e))?;
                Ok(ATyp::vec(
                    &t,
                    n2.checked_add(1).ok_or_else(|| LubError::concat(&x, &y))?,
                ))
            }
            (a, b) => Err(LubError::concat(&a, &b)),
        }
    }

    fn lub_and(x: &Self, y: &Self, _: &Self::Context) -> Result<Self, LubError> {
        match (x, y) {
            (ATyp::Base(ABase::Bool), ATyp::Base(ABase::Bool)) => Ok(ATyp::Base(ABase::Bool)),
            (_, _) => Err(LubError::and(&x, &y)),
        }
    }
}

impl fmt::Display for ABase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ABase::Unit => write!(f, "Unit"),
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

#[cfg(test)]
mod tests {
    use super::*;
    use lang::ast::spanned::Spanned;
    use lang::typ::Nothing;
    use lang::typ::lub::Lub;

    #[test]
    fn vpoly_add_uni() {
        let result = ATyp::lub_add(&ATyp::vpoly(2, 3), &ATyp::uni(5), &Nothing).unwrap();
        assert_eq!(result, ATyp::vpoly(2, 5));
    }

    #[test]
    fn vpoly_sub_mle() {
        let result = ATyp::lub_sub(&ATyp::vpoly(2, 3), &ATyp::mle(5), &Nothing).unwrap();
        assert_eq!(result, ATyp::vpoly(5, 5));
    }

    #[test]
    fn vpoly_equ_same() {
        let result = ATyp::lub_equ(&ATyp::vpoly(2, 3), &ATyp::vpoly(2, 3), &Nothing).unwrap();
        assert_eq!(result, ATyp::vpoly(2, 3));
    }

    #[test]
    fn record_lub_equ_intersects_widths() {
        let mut a = Ctx::new();
        a.insert(&"x".to_string(), &ATyp::scalar());
        let mut b = Ctx::new();
        b.insert(&"x".to_string(), &ATyp::scalar());
        b.insert(&"y".to_string(), &ATyp::uni(3));
        let ra = ATyp::Record(a);
        let rb = ATyp::Record(b);

        let mut expected_fields = Ctx::new();
        expected_fields.insert(&"x".to_string(), &ATyp::scalar());
        let expected = ATyp::Record(expected_fields);

        assert_eq!(ATyp::lub_equ(&ra, &rb, &Nothing), Ok(expected.clone()));
        assert_eq!(ATyp::lub_equ(&rb, &ra, &Nothing), Ok(expected));
    }

    #[test]
    fn vpoly_equ_different_coerces_to_wider() {
        let result = ATyp::lub_equ(&ATyp::vpoly(2, 3), &ATyp::vpoly(4, 5), &Nothing);
        assert_eq!(result.unwrap(), ATyp::vpoly(4, 5));
    }

    #[test]
    fn from_ctyp_preserves_poly_params() {
        use lang::id::Tid;
        use lang::typ::{CKind, CTyp};

        let mut kctx = Ctx::new();
        kctx.insert(&Tid::from("F"), &CKind::Field);

        let ctyp = CTyp::Poly(Tid::from("F"), Spanned::dummy(3), Spanned::dummy(5));
        let atyp = ATyp::from_ctyp(&ctyp, &kctx).unwrap();
        assert_eq!(atyp, ATyp::VPoly(3, 15));
    }

    /// Phase 7 regression: `lub_mul` on `CTyp::Poly` and on the lowered
    /// `ATyp::VPoly` must produce compatible ATyps. The CTyp path is always
    /// at least as conservative (VPoly degree ≥ ATyp path) because CTyp's
    /// per-variable degree → total degree via `n*d` is a worst-case bound.
    #[test]
    fn pbt_lub_mul_ctyp_atyp_cross_consistency() {
        use lang::id::Tid;
        use lang::typ::lub::Lub as _;
        use lang::typ::{CKind, CTyp};

        arbtest::arbtest(|u| {
            let f = Tid::from("F");
            let mut kctx = Ctx::new();
            kctx.insert(&f, &CKind::Field);

            let m1: usize = u.int_in_range(1..=6)?;
            let n1: usize = u.int_in_range(1..=6)?;
            let m2: usize = u.int_in_range(1..=6)?;
            let n2: usize = u.int_in_range(1..=6)?;

            let c1 = CTyp::Poly(f.clone(), Spanned::dummy(m1), Spanned::dummy(n1));
            let c2 = CTyp::Poly(f.clone(), Spanned::dummy(m2), Spanned::dummy(n2));
            let c_mul = CTyp::lub_mul(&c1, &c2, &kctx).unwrap();
            let c_mul_lowered = ATyp::from_ctyp(&c_mul, &kctx).unwrap();

            let a1 = ATyp::from_ctyp(&c1, &kctx).unwrap();
            let a2 = ATyp::from_ctyp(&c2, &kctx).unwrap();
            let a_mul = ATyp::lub_mul(&a1, &a2, &Nothing).unwrap();

            if matches!(c_mul_lowered, ATyp::Uni(_) | ATyp::Mle(_)) {
                assert_eq!(
                    c_mul_lowered, a_mul,
                    "CTyp and ATyp lub_mul disagree on Uni/Mle path"
                );
            } else {
                let (ATyp::VPoly(cn, cd), ATyp::VPoly(an, ad)) = (&c_mul_lowered, &a_mul) else {
                    panic!("expected VPoly for general case, got {c_mul_lowered} vs {a_mul}");
                };
                assert_eq!(cn, an, "VPoly num_vars mismatch");
                assert!(
                    cd >= ad,
                    "CTyp-lowered degree should be >= ATyp-lubbed: {cd} < {ad}"
                );
            }
            Ok(())
        });
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
    fn pbt_lub_mul_uni_uni_pins_degree_sum() {
        arbtest::arbtest(|u| {
            let m1: usize = u.int_in_range(0..=8)?;
            let m2: usize = u.int_in_range(0..=8)?;
            let result = ATyp::lub_mul(&ATyp::uni(m1), &ATyp::uni(m2), &Nothing).unwrap();
            assert_eq!(
                result,
                ATyp::uni(m1 + m2),
                "Uni({m1}) * Uni({m2}) should equal Uni({})",
                m1 + m2,
            );
            Ok(())
        });
    }

    /// `Uni(d) * Mle(n) == VPoly(n, d+n)` (and reverse).
    #[test]
    fn pbt_lub_mul_uni_mle_pins_vpoly() {
        arbtest::arbtest(|u| {
            let d: usize = u.int_in_range(0..=8)?;
            let n: usize = u.int_in_range(1..=8)?;
            let left = ATyp::lub_mul(&ATyp::uni(d), &ATyp::mle(n), &Nothing).unwrap();
            let right = ATyp::lub_mul(&ATyp::mle(n), &ATyp::uni(d), &Nothing).unwrap();
            let expected = ATyp::vpoly(n, d + n);
            assert_eq!(
                left, expected,
                "Uni({d}) * Mle({n}) should equal {expected}"
            );
            assert_eq!(
                right, expected,
                "Mle({n}) * Uni({d}) should equal {expected}"
            );
            Ok(())
        });
    }

    /// `Mle(n1) * Mle(n2)` always pins to `VPoly(max(n1,n2), n1+n2)` — total
    /// degrees add (Mle(n) has total degree n).
    #[test]
    fn pbt_lub_mul_mle_mle_pins_max_and_sum_total_degree() {
        arbtest::arbtest(|u| {
            let n1: usize = u.int_in_range(1..=8)?;
            let n2: usize = u.int_in_range(1..=8)?;
            let result = ATyp::lub_mul(&ATyp::mle(n1), &ATyp::mle(n2), &Nothing).unwrap();
            assert_eq!(
                result,
                ATyp::vpoly(n1.max(n2), n1 + n2),
                "Mle({n1}) * Mle({n2}) should equal VPoly(max, n1+n2)",
            );
            Ok(())
        });
    }

    /// `VPoly(n1,m1) * VPoly(n2,m2) == VPoly(max(n1,n2), m1+m2)`.
    #[test]
    fn pbt_lub_mul_vpoly_vpoly_pins_max_vars_and_sum_degree() {
        arbtest::arbtest(|u| {
            let n1: usize = u.int_in_range(1..=8)?;
            let m1: usize = u.int_in_range(1..=8)?;
            let n2: usize = u.int_in_range(1..=8)?;
            let m2: usize = u.int_in_range(1..=8)?;
            let result =
                ATyp::lub_mul(&ATyp::vpoly(n1, m1), &ATyp::vpoly(n2, m2), &Nothing).unwrap();
            assert_eq!(
                result,
                ATyp::vpoly(n1.max(n2), m1 + m2),
                "VPoly({n1},{m1}) * VPoly({n2},{m2}) should equal VPoly(max, sum)",
            );
            Ok(())
        });
    }

    /// `VPoly(n,m) * Uni(d) == VPoly(n, m+d)` (in both orders).
    #[test]
    fn pbt_lub_mul_vpoly_uni_pins_degree_sum() {
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(1..=8)?;
            let m: usize = u.int_in_range(0..=8)?;
            let d: usize = u.int_in_range(0..=8)?;
            let left = ATyp::lub_mul(&ATyp::vpoly(n, m), &ATyp::uni(d), &Nothing).unwrap();
            let right = ATyp::lub_mul(&ATyp::uni(d), &ATyp::vpoly(n, m), &Nothing).unwrap();
            let expected = ATyp::vpoly(n, m + d);
            assert_eq!(
                left, expected,
                "VPoly({n},{m}) * Uni({d}) should equal {expected}"
            );
            assert_eq!(
                right, expected,
                "Uni({d}) * VPoly({n},{m}) should equal {expected}"
            );
            Ok(())
        });
    }

    /// `VPoly(n,m) * Mle(n')` pins to `VPoly(max(n,n'), m+n')` — the
    /// multilinear has total degree n', which adds to the VPoly degree.
    #[test]
    fn pbt_lub_mul_vpoly_mle_pins_degree_plus_mle_total() {
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(1..=8)?;
            let m: usize = u.int_in_range(0..=8)?;
            let n_mle: usize = u.int_in_range(1..=8)?;
            let left = ATyp::lub_mul(&ATyp::vpoly(n, m), &ATyp::mle(n_mle), &Nothing).unwrap();
            let right = ATyp::lub_mul(&ATyp::mle(n_mle), &ATyp::vpoly(n, m), &Nothing).unwrap();
            let expected = ATyp::vpoly(n.max(n_mle), m + n_mle);
            assert_eq!(
                left, expected,
                "VPoly({n},{m}) * Mle({n_mle}) should equal {expected}"
            );
            assert_eq!(
                right, expected,
                "Mle({n_mle}) * VPoly({n},{m}) should equal {expected}"
            );
            Ok(())
        });
    }

    // ---------- lub_mul: pairing and group broadcast ----------

    /// `G1 * G2 == GT` and `G2 * G1 == GT` — pairing promoted to mul.
    #[test]
    fn pbt_lub_mul_g1_g2_is_gt() {
        assert_eq!(
            ABase::lub_mul(&ABase::G1, &ABase::G2, &Nothing).unwrap(),
            ABase::GT
        );
        assert_eq!(
            ABase::lub_mul(&ABase::G2, &ABase::G1, &Nothing).unwrap(),
            ABase::GT
        );
    }

    /// `VecG1 * G2 == VecGT` — broadcast pairing through lub_mul.
    #[test]
    fn pbt_lub_mul_vec_g1_g2_is_vec_gt() {
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(1..=8)?;
            assert_eq!(
                ATyp::lub_mul(&ATyp::vec_g1(n), &ATyp::g2(), &Nothing).unwrap(),
                ATyp::vec(&ATyp::gt(), n),
                "VecG1({n}) * G2 should be VecGT({n})"
            );
            assert_eq!(
                ATyp::lub_mul(&ATyp::g2(), &ATyp::vec_g1(n), &Nothing).unwrap(),
                ATyp::vec(&ATyp::gt(), n),
                "G2 * VecG1({n}) should be VecGT({n})"
            );
            Ok(())
        });
    }

    /// `VecG2 * G1 == VecGT` — broadcast pairing in reverse order.
    #[test]
    fn pbt_lub_mul_vec_g2_g1_is_vec_gt() {
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(1..=8)?;
            assert_eq!(
                ATyp::lub_mul(&ATyp::vec_g2(n), &ATyp::g1(), &Nothing).unwrap(),
                ATyp::vec(&ATyp::gt(), n),
                "VecG2({n}) * G1 should be VecGT({n})"
            );
            assert_eq!(
                ATyp::lub_mul(&ATyp::g1(), &ATyp::vec_g2(n), &Nothing).unwrap(),
                ATyp::vec(&ATyp::gt(), n),
                "G1 * VecG2({n}) should be VecGT({n})"
            );
            Ok(())
        });
    }

    /// `VecG1 * VecG2 == VecGT` — element-wise pairing via lub_mul.
    #[test]
    fn pbt_lub_mul_vec_g1_vec_g2_is_vec_gt() {
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(1..=8)?;
            assert_eq!(
                ATyp::lub_mul(&ATyp::vec_g1(n), &ATyp::vec_g2(n), &Nothing).unwrap(),
                ATyp::vec(&ATyp::gt(), n),
                "VecG1({n}) * VecG2({n}) should be VecGT({n})"
            );
            assert_eq!(
                ATyp::lub_mul(&ATyp::vec_g2(n), &ATyp::vec_g1(n), &Nothing).unwrap(),
                ATyp::vec(&ATyp::gt(), n),
                "VecG2({n}) * VecG1({n}) should be VecGT({n})"
            );
            Ok(())
        });
    }

    /// `VecG1 * VecG1` errors — group element multiplication is not valid
    /// even with pairing in lub_mul (G1*G1 has no pairing).
    #[test]
    fn pbt_lub_mul_vec_g1_vec_g1_pins_error() {
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(1..=8)?;
            assert!(
                ATyp::lub_mul(&ATyp::vec_g1(n), &ATyp::vec_g1(n), &Nothing).is_err(),
                "VecG1({n}) * VecG1({n}) should error (no self-pairing)"
            );
            Ok(())
        });
    }

    // ---------- lub_add ----------

    /// `Uni(m1) + Uni(m2) == Uni(max(m1, m2))`.
    #[test]
    fn pbt_lub_add_uni_uni_pins_max_degree() {
        arbtest::arbtest(|u| {
            let m1: usize = u.int_in_range(0..=8)?;
            let m2: usize = u.int_in_range(0..=8)?;
            let result = ATyp::lub_add(&ATyp::uni(m1), &ATyp::uni(m2), &Nothing).unwrap();
            assert_eq!(
                result,
                ATyp::uni(m1.max(m2)),
                "Uni({m1}) + Uni({m2}) should equal Uni(max)",
            );
            Ok(())
        });
    }

    /// `Mle(n1) + Mle(n2)` pins to `Mle(n)` if `n1 == n2`, else to
    /// `VPoly(max(n1,n2), max(n1,n2))` — Mle(n) has total degree n.
    #[test]
    fn pbt_lub_add_mle_mle_pins() {
        arbtest::arbtest(|u| {
            let n1: usize = u.int_in_range(1..=8)?;
            let n2: usize = u.int_in_range(1..=8)?;
            let result = ATyp::lub_add(&ATyp::mle(n1), &ATyp::mle(n2), &Nothing).unwrap();
            let expected = if n1 == n2 {
                ATyp::mle(n1)
            } else {
                let v = n1.max(n2);
                ATyp::vpoly(v, v)
            };
            assert_eq!(
                result, expected,
                "Mle({n1}) + Mle({n2}) should equal {expected}",
            );
            Ok(())
        });
    }

    /// `VPoly(n1,m1) + VPoly(n2,m2) == VPoly(max(n1,n2), max(m1,m2))`.
    #[test]
    fn pbt_lub_add_vpoly_vpoly_pins_max_max() {
        arbtest::arbtest(|u| {
            let n1: usize = u.int_in_range(1..=8)?;
            let m1: usize = u.int_in_range(1..=8)?;
            let n2: usize = u.int_in_range(1..=8)?;
            let m2: usize = u.int_in_range(1..=8)?;
            let result =
                ATyp::lub_add(&ATyp::vpoly(n1, m1), &ATyp::vpoly(n2, m2), &Nothing).unwrap();
            assert_eq!(
                result,
                ATyp::vpoly(n1.max(n2), m1.max(m2)),
                "VPoly({n1},{m1}) + VPoly({n2},{m2}) should equal VPoly(max, max)",
            );
            Ok(())
        });
    }

    // ---------- lub_concat ----------

    /// Phase B: `concat(Vec<Scalar, k>, Uni(m))` is now a type error in
    /// both directions. The pre-Phase-B arm returned `Uni(k + m)` by
    /// reinterpreting the Vec as a coefficient list; that implicit
    /// coercion was removed in PR #135 to match the CTyp-level rule. Use
    /// `poly([...])` / `coef(...)` to bridge between Vec and polynomial.
    #[test]
    fn pbt_lub_concat_vec_scalar_uni_pins_error() {
        arbtest::arbtest(|u| {
            let k: usize = u.int_in_range(1..=8)?;
            let m: usize = u.int_in_range(0..=8)?;
            assert!(
                ATyp::lub_concat(&ATyp::vec_scalar(k), &ATyp::uni(m), &Nothing).is_err(),
                "concat(Vec<Scalar,{k}>, Uni({m})) is a type error after Phase B",
            );
            assert!(
                ATyp::lub_concat(&ATyp::uni(m), &ATyp::vec_scalar(k), &Nothing).is_err(),
                "concat(Uni({m}), Vec<Scalar,{k}>) is a type error after Phase B",
            );
            Ok(())
        });
    }

    /// `concat(Vec<Scalar, k>, Mle(n))` (and reverse) — no arm covers this
    /// combination, so the call must error.  Pin the error so any future arm
    /// has to update this test consciously.
    #[test]
    fn pbt_lub_concat_vec_scalar_mle_pins_error() {
        arbtest::arbtest(|u| {
            let k: usize = u.int_in_range(1..=8)?;
            let n: usize = u.int_in_range(1..=8)?;
            assert!(
                ATyp::lub_concat(&ATyp::vec_scalar(k), &ATyp::mle(n), &Nothing).is_err(),
                "concat(Vec<Scalar,{k}>, Mle({n})) currently has no arm and should error",
            );
            assert!(
                ATyp::lub_concat(&ATyp::mle(n), &ATyp::vec_scalar(k), &Nothing).is_err(),
                "concat(Mle({n}), Vec<Scalar,{k}>) currently has no arm and should error",
            );
            Ok(())
        });
    }

    /// `concat(Vec<Scalar,n1>, Vec<Scalar,n2>) == Vec<Scalar, n1+n2>` —
    /// sanity pin for the vector–vector arm used as the comparison baseline.
    #[test]
    fn pbt_lub_concat_vec_vec_pins_length_sum() {
        arbtest::arbtest(|u| {
            let n1: usize = u.int_in_range(1..=8)?;
            let n2: usize = u.int_in_range(1..=8)?;
            let result =
                ATyp::lub_concat(&ATyp::vec_scalar(n1), &ATyp::vec_scalar(n2), &Nothing).unwrap();
            assert_eq!(
                result,
                ATyp::vec_scalar(n1 + n2),
                "concat(Vec<Scalar,{n1}>, Vec<Scalar,{n2}>) should equal Vec<Scalar, {}>",
                n1 + n2,
            );
            Ok(())
        });
    }

    // ---------- lub_dot ----------

    /// `dot(Vec<G1, n>, Vec<Scalar, n>) == G1` — MSM type rule (in both orders).
    #[test]
    fn pbt_lub_dot_vec_g1_vec_scalar_is_g1() {
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(1..=8)?;
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
            Ok(())
        });
    }

    /// `dot(Vec<G2, n>, Vec<Scalar, n>) == G2`.
    #[test]
    fn pbt_lub_dot_vec_g2_vec_scalar_is_g2() {
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(1..=8)?;
            let result = ATyp::lub_dot(&ATyp::vec_g2(n), &ATyp::vec_scalar(n), &Nothing).unwrap();
            assert_eq!(
                result,
                ATyp::g2(),
                "dot(Vec<G2,{n}>, Vec<Scalar,{n}>) should be G2"
            );
            Ok(())
        });
    }

    /// `dot(Vec<Scalar, n>, Vec<Scalar, n>) == Scalar`.
    #[test]
    fn pbt_lub_dot_vec_scalar_vec_scalar_is_scalar() {
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(1..=8)?;
            let result =
                ATyp::lub_dot(&ATyp::vec_scalar(n), &ATyp::vec_scalar(n), &Nothing).unwrap();
            assert_eq!(
                result,
                ATyp::scalar(),
                "dot(Vec<Scalar,{n}>, Vec<Scalar,{n}>) should be Scalar",
            );
            Ok(())
        });
    }

    /// `dot(Vec<G1, n>, Vec<G2, n>) == GT` (and reverse) — aggregate pairing dot.
    /// The Vec arm delegates element types through the pairing rule.
    #[test]
    fn pbt_lub_dot_vec_g1_vec_g2_is_gt() {
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(1..=8)?;
            let left = ATyp::lub_dot(&ATyp::vec_g1(n), &ATyp::vec_g2(n), &Nothing).unwrap();
            let right = ATyp::lub_dot(&ATyp::vec_g2(n), &ATyp::vec_g1(n), &Nothing).unwrap();
            assert_eq!(
                left,
                ATyp::gt(),
                "dot(Vec<G1,{n}>, Vec<G2,{n}>) should be GT"
            );
            assert_eq!(
                right,
                ATyp::gt(),
                "dot(Vec<G2,{n}>, Vec<G1,{n}>) should be GT"
            );
            Ok(())
        });
    }

    /// `dot(Vec<GT, n>, Vec<Scalar, n>) == GT` — GT is a target group,
    /// and `GT · Scalar → GT` under `lub_dot`.
    #[test]
    fn pbt_lub_dot_vec_gt_vec_scalar_is_gt() {
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(1..=8)?;
            assert_eq!(
                ATyp::lub_dot(&ATyp::vec(&ATyp::gt(), n), &ATyp::vec_scalar(n), &Nothing).unwrap(),
                ATyp::gt(),
                "dot(Vec<GT,{n}>, Vec<Scalar,{n}>) should be GT"
            );
            Ok(())
        });
    }

    /// Division preserves vector operand order.
    #[test]
    fn lub_div_vector_operand_order() {
        assert_eq!(
            ATyp::lub_div(&ATyp::scalar(), &ATyp::vec_scalar(2), &Nothing),
            Ok(ATyp::vec_scalar(2))
        );
        assert_eq!(
            ATyp::lub_div(&ATyp::g1(), &ATyp::vec_scalar(2), &Nothing),
            Ok(ATyp::vec_g1(2))
        );
        assert!(ATyp::lub_div(&ATyp::scalar(), &ATyp::vec_g1(2), &Nothing).is_err());
        assert_eq!(
            ATyp::lub_div(&ATyp::vec_g1(2), &ATyp::scalar(), &Nothing),
            Ok(ATyp::vec_g1(2))
        );

        let fin = ATyp::fin(CRange::singleton(3));
        assert!(ATyp::lub_div(&fin, &ATyp::vec(&fin, 2), &Nothing).is_err());
    }

    #[test]
    fn lub_rem_rejects_scalar_left_vector() {
        let fin = ATyp::fin(CRange::singleton(3));
        assert!(ATyp::lub_rem(&ATyp::vec(&fin, 2), &fin, &Nothing).is_ok());
        assert!(ATyp::lub_rem(&fin, &ATyp::vec(&fin, 2), &Nothing).is_err());
    }

    #[test]
    fn lub_pow_rejects_scalar_left_vector_and_vec_exponents() {
        let fin = ATyp::fin(CRange::singleton(3));
        assert!(ATyp::lub_pow(&ATyp::vec(&fin, 2), &fin, &Nothing).is_ok());
        assert!(ATyp::lub_pow(&fin, &ATyp::vec(&fin, 2), &Nothing).is_err());
        assert!(ATyp::lub_pow(&ATyp::scalar(), &ATyp::vec(&fin, 2), &Nothing).is_err());
        assert!(ATyp::lub_pow(&ATyp::vec(&fin, 2), &ATyp::vec(&fin, 2), &Nothing).is_err());
    }

    #[test]
    fn lub_div_poly_groebner_supported_shapes() {
        // Both indices are upper bounds: the quotient keeps the dividend's
        // bound for every relative ordering of the two declared bounds.
        assert_eq!(
            ATyp::lub_div(&ATyp::uni(3), &ATyp::uni(1), &Nothing),
            Ok(ATyp::uni(3))
        );
        assert_eq!(
            ATyp::lub_div(&ATyp::uni(3), &ATyp::uni(3), &Nothing),
            Ok(ATyp::uni(3))
        );
        assert_eq!(
            ATyp::lub_div(&ATyp::uni(1), &ATyp::uni(3), &Nothing),
            Ok(ATyp::uni(1))
        );
        assert!(ATyp::lub_div(&ATyp::vpoly(2, 3), &ATyp::vpoly(2, 1), &Nothing).is_err());
        assert!(ATyp::lub_div(&ATyp::vpoly(1, 3), &ATyp::uni(1), &Nothing).is_err());
        assert!(ATyp::lub_div(&ATyp::uni(3), &ATyp::vpoly(1, 1), &Nothing).is_err());

        assert!(ATyp::lub_div(&ATyp::vpoly(2, 3), &ATyp::vpoly(3, 1), &Nothing).is_err());
        assert!(ATyp::lub_div(&ATyp::vpoly(2, 3), &ATyp::uni(1), &Nothing).is_err());
        assert!(ATyp::lub_div(&ATyp::uni(3), &ATyp::vpoly(2, 1), &Nothing).is_err());
        assert!(ATyp::lub_div(&ATyp::mle(2), &ATyp::uni(1), &Nothing).is_err());
        assert!(ATyp::lub_div(&ATyp::uni(2), &ATyp::mle(2), &Nothing).is_err());
        assert!(ATyp::lub_div(&ATyp::mle(2), &ATyp::vpoly(2, 2), &Nothing).is_err());
        assert!(ATyp::lub_div(&ATyp::vpoly(2, 2), &ATyp::mle(2), &Nothing).is_err());
        assert!(ATyp::lub_div(&ATyp::mle(2), &ATyp::mle(2), &Nothing).is_err());
    }

    #[test]
    fn lub_rem_poly_groebner_supported_shapes() {
        assert_eq!(
            ATyp::lub_rem(&ATyp::uni(3), &ATyp::uni(1), &Nothing),
            Ok(ATyp::uni(0))
        );
        assert!(ATyp::lub_rem(&ATyp::vpoly(2, 3), &ATyp::vpoly(2, 1), &Nothing).is_err());
        assert!(ATyp::lub_rem(&ATyp::vpoly(1, 3), &ATyp::uni(1), &Nothing).is_err());
        assert!(ATyp::lub_rem(&ATyp::uni(3), &ATyp::vpoly(1, 1), &Nothing).is_err());

        assert!(ATyp::lub_rem(&ATyp::vpoly(2, 3), &ATyp::vpoly(3, 1), &Nothing).is_err());
        assert!(ATyp::lub_rem(&ATyp::vpoly(2, 3), &ATyp::uni(1), &Nothing).is_err());
        assert!(ATyp::lub_rem(&ATyp::uni(3), &ATyp::vpoly(2, 1), &Nothing).is_err());
        assert!(ATyp::lub_rem(&ATyp::mle(2), &ATyp::uni(1), &Nothing).is_err());
        assert!(ATyp::lub_rem(&ATyp::uni(2), &ATyp::mle(2), &Nothing).is_err());
        assert!(ATyp::lub_rem(&ATyp::mle(2), &ATyp::vpoly(2, 2), &Nothing).is_err());
        assert!(ATyp::lub_rem(&ATyp::vpoly(2, 2), &ATyp::mle(2), &Nothing).is_err());
        assert!(ATyp::lub_rem(&ATyp::mle(2), &ATyp::mle(2), &Nothing).is_err());
        assert!(ATyp::lub_rem(&ATyp::vpoly(1, 2), &ATyp::scalar(), &Nothing).is_err());
    }

    /// Polynomial/scalar division requires the polynomial-like operand on the left.
    #[test]
    fn lub_div_poly_scalar_requires_poly_left() {
        assert!(ATyp::lub_div(&ATyp::scalar(), &ATyp::uni(2), &Nothing).is_err());
        assert!(ATyp::lub_div(&ATyp::scalar(), &ATyp::mle(2), &Nothing).is_err());
        assert!(ATyp::lub_div(&ATyp::scalar(), &ATyp::vpoly(1, 2), &Nothing).is_err());

        let fin = ATyp::Base(ABase::Fin(CRange::singleton(3)));
        for (poly, expected) in [
            (ATyp::uni(2), ATyp::uni(2)),
            (ATyp::mle(2), ATyp::mle(2)),
            (ATyp::vpoly(1, 2), ATyp::vpoly(1, 2)),
        ] {
            assert_eq!(
                ATyp::lub_div(&poly, &ATyp::scalar(), &Nothing),
                Ok(expected.clone())
            );
            assert_eq!(ATyp::lub_div(&poly, &fin, &Nothing), Ok(expected));
        }
    }

    /// `dot(Vec<Scalar, n>, Vec<Scalar, m>)` with `n != m` has no covering arm,
    /// so it must error.
    #[test]
    fn pbt_lub_dot_mismatched_vec_lengths_pins_error() {
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(1..=8)?;
            let delta: usize = u.int_in_range(1..=8)?;
            let m = n + delta; // ensure m != n
            let result = ATyp::lub_dot(&ATyp::vec_scalar(n), &ATyp::vec_scalar(m), &Nothing);
            assert!(
                result.is_err(),
                "dot(Vec<Scalar,{n}>, Vec<Scalar,{m}>) of mismatched lengths should error, got {result:?}",
            );
            Ok(())
        });
    }

    // --- Type-layout API tests ---

    // --- Overflow tests: checked arithmetic in ATyp::lub_* ---

    #[test]
    fn atyp_lub_mul_uni_degree_overflow() {
        let a = ATyp::uni(usize::MAX);
        let b = ATyp::uni(1);
        assert!(ATyp::lub_mul(&a, &b, &Nothing).is_err());
    }

    #[test]
    fn atyp_lub_mul_vpoly_degree_overflow() {
        let a = ATyp::vpoly(1, usize::MAX);
        let b = ATyp::vpoly(1, 1);
        assert!(ATyp::lub_mul(&a, &b, &Nothing).is_err());
    }

    #[test]
    fn atyp_lub_concat_vec_overflow() {
        let a = ATyp::vec_scalar(usize::MAX);
        let b = ATyp::vec_scalar(1);
        assert!(ATyp::lub_concat(&a, &b, &Nothing).is_err());
    }

    #[test]
    fn atyp_lub_concat_vec_element_overflow() {
        let a = ATyp::vec_scalar(usize::MAX);
        assert!(ATyp::lub_concat(&a, &ATyp::scalar(), &Nothing).is_err());
    }

    #[test]
    fn atyp_lub_pow_uni_fin_overflow() {
        let a = ATyp::uni(usize::MAX);
        let r = CRange::from_raw(0, 1, 2); // len = 2
        let b = ATyp::fin(r);
        assert!(ATyp::lub_pow(&a, &b, &Nothing).is_err());
    }

    #[test]
    fn atyp_from_ctyp_poly_degree_overflow() {
        let f = Tid::from("F");
        let kctx: Ctx<Tid, CKind> = Ctx::from([(f.clone(), CKind::Field)]);
        // Poly(F, m, n) where m * n overflows
        let ctyp = CTyp::Poly(f, Spanned::dummy(usize::MAX), Spanned::dummy(2));
        assert_eq!(ATyp::from_ctyp(&ctyp, &kctx), None);
    }

    #[test]
    #[should_panic(expected = "physical_len: Uni m + 1 overflow")]
    fn atyp_physical_len_uni_overflow() {
        let t = ATyp::uni(usize::MAX);
        t.physical_len();
    }

    #[test]
    #[should_panic(expected = "physical_len: Mle 1 << n overflow")]
    fn atyp_physical_len_mle_overflow() {
        let t = ATyp::mle(usize::BITS as usize);
        t.physical_len();
    }
}
