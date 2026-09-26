//! The `lang`-level type system: source types, kinds, qualifiers, and type inference.
//!
//! Source types are [`Typ`](crate::typ::Typ), where `T` is the base-type tag (normally
//! [`Tid`](crate::id::Tid)) and `N` is the size representation — [`Size`](crate::ast::size::Size)
//! before concretization ([`UTyp`](crate::typ::UTyp)) and `usize` afterwards
//! ([`CTyp`](crate::typ::CTyp)). The IR-level counterpart is `backend::ATyp`.

/// Bridge from source types to the `arkworks`-flavoured base types.
pub mod ark;
mod distribution;
/// Kind-directed type inference (`Typeable`, `TypeError`).
pub mod infer;
mod kind;
/// Least-upper bounds joining operand types of binary operations.
pub mod lub;
mod nothing;
mod qualifier;
/// Substitutions for type aliases and symbolic sizes.
pub mod subst;
mod typevar;
/// Kind-aware unification of source types.
pub mod unify;

pub use crate::ast::range::{CRange, Range, RangeError, RangeTraversal};
use crate::ast::spanned::Spanned;
use crate::ast::Size;
use crate::id::{Tid, TidSubst};

pub use ark::Ark;
pub use distribution::Distribution;
pub use infer::{TypeError, Typeable};
pub use kind::{CKind, Kind, UKind};
pub use lub::LubError;
pub use nothing::Nothing;
pub use qualifier::Qualifier;
pub use subst::{AliasSubsts, SizeSubsts};
pub use typevar::{CTypeVar, CTypeVars, TypeVar, TypeVars, UTypeVar, UTypeVars};

use share::traversal::{ToTraversal1, ToTraversal2};
use share::Ctx;
use std::fmt;

/// The types of expressions, `N` is the size parameter
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Typ<T, N> {
    /// Polynomial with M variables and degree N over base type T
    /// Poly(F, 1, N) represents univariate polynomials of degree N
    /// Poly(F, M, 1) represents multilinear polynomials of M variables
    Poly(T, Spanned<N>, Spanned<N>),
    /// Vector of size `N` and base type [Typ]
    Vec(Box<Spanned<Typ<T, N>>>, Spanned<N>),
    /// Tid type [Tid]
    Base(T),
    /// Fin within range
    Fin(Range<N>),
    /// Unit type (assert/verify/protocol return)
    Unit,
    /// Boolean type (result of `==`)
    Bool,
    /// Record type with named fields
    Record(Ctx<Spanned<String>, Spanned<Typ<T, N>>>),
}

/// Many types
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Typs<T, N>(pub Vec<Spanned<Typ<T, N>>>);

/// Generic type [Tid]
pub type GTyp<N> = Typ<Tid, N>;
/// Several generic types over [`Tid`] base tags.
pub type GTyps<N> = Typs<Tid, N>;

/// Symbolically sized type
pub type UTyp = Typ<Tid, Size>;
/// Alias intended for several symbolically sized types; note it currently expands to a single
/// `Typ<Tid, Size>`, i.e. it is identical to [`UTyp`].
pub type UTyps = Typ<Tid, Size>;

/// Concrete size type
pub type CTyp = Typ<Tid, usize>;
/// Several concretely sized types.
pub type CTyps = Typs<Tid, usize>;

impl<N: Clone> TidSubst for GTyp<N> {
    fn tid_subst(&mut self, from: &Tid, to: &Tid) {
        match self {
            Typ::Poly(b, _, _) | Typ::Base(b) if b == from => *b = to.clone(),
            Typ::Vec(b, _) => b.node.tid_subst(from, to),
            Typ::Record(fields) => {
                fields.modify(|_, field_typ| {
                    field_typ.node.tid_subst(from, to);
                });
            }
            Typ::Fin(_) | Typ::Unit | Typ::Bool | Typ::Base(_) | Typ::Poly(_, _, _) => {}
        }
    }
}

impl<T, N> IntoIterator for Typs<T, N> {
    type Item = Spanned<Typ<T, N>>;
    type IntoIter = std::vec::IntoIter<Spanned<Typ<T, N>>>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<T, N> FromIterator<Spanned<Typ<T, N>>> for Typs<T, N> {
    fn from_iter<I: IntoIterator<Item = Spanned<Typ<T, N>>>>(iter: I) -> Self {
        Typs(iter.into_iter().collect())
    }
}

impl<N: Clone> TidSubst for GTyps<N> {
    fn tid_subst(&mut self, from: &Tid, to: &Tid) {
        self.0.iter_mut().for_each(|t| t.node.tid_subst(from, to))
    }
}

impl<T, N> Typ<T, N> {
    /// Wraps a base-type tag as a [`Typ::Base`].
    pub fn base(b: &T) -> Self
    where
        T: Clone,
    {
        Typ::Base(b.clone())
    }
    /// Builds the type of a length-`n` vector whose elements have type `b`, with dummy spans.
    pub fn vec(b: &Typ<T, N>, n: N) -> Self
    where
        T: Clone,
        N: Clone,
    {
        Typ::Vec(Box::new(Spanned::dummy(b.clone())), Spanned::dummy(n))
    }
    /// Builds a [`Typ::Fin`] constrained to the integer `range`.
    pub fn fin(range: Range<N>) -> Self {
        Typ::Fin(range)
    }
    /// The unit type, returned by `assert` / `verify` / protocol bodies.
    pub fn unit() -> Self {
        Typ::Unit
    }
    /// The boolean type, produced by `==`.
    pub fn bool() -> Self {
        Typ::Bool
    }
    /// Splits a vector type into its element type and length.
    ///
    /// # Panics
    /// Panics if `self` is not a [`Typ::Vec`]; callers must have established the shape already.
    pub fn into_vec(self) -> (Spanned<Self>, Spanned<N>) {
        match self {
            Typ::Vec(deref!(t), n) => (t, n),
            _ => unreachable!(),
        }
    }
}

impl<N> GTyp<N> {
    /// The univariate encoding `Poly(b, 1, n)`: a degree-`n` polynomial over base type `b`.
    pub fn uni(b: &Tid, n: N) -> Self
    where
        N: From<usize>,
    {
        Typ::Poly(b.clone(), Spanned::dummy(N::from(1)), Spanned::dummy(n))
    }
    /// The multilinear encoding `Poly(b, m, 1)`: a polynomial in `m` variables over base type `b`.
    pub fn mle(b: &Tid, m: N) -> Self
    where
        N: From<usize>,
    {
        Typ::Poly(b.clone(), Spanned::dummy(m), Spanned::dummy(N::from(1)))
    }

    /// Resolves this type to the scalar-kinded [`Tid`] it can be treated as, if any.
    ///
    /// A [`Typ::Base`] resolves to itself when its kind in `ctx` is scalar-shaped. An integer
    /// [`Typ::Fin`] has no base tag of its own, so it resolves to the unique `Field` in `ctx`, or
    /// — when no field is present — to the unique `Scalar` kind. Ambiguity (several candidates) and
    /// any other type shape yield `None`.
    pub fn to_scalar<M>(&self, ctx: &Ctx<Tid, Kind<M>>) -> Option<Tid> {
        match self {
            Typ::Base(b) => {
                let k = ctx.get(b)?;
                if k.is_scalar() {
                    Some(b.clone())
                } else {
                    None
                }
            }
            Typ::Fin(_) => {
                let fields: Vec<_> = ctx
                    .iter()
                    .filter(|(_, k)| matches!(k, Kind::Field))
                    .map(|(b, _)| b.clone())
                    .collect();
                if fields.len() == 1 {
                    Some(fields[0].clone())
                } else if fields.is_empty() {
                    let scalars: Vec<_> = ctx
                        .iter()
                        .filter(|(_, k)| matches!(k, Kind::Scalar(_)))
                        .map(|(b, _)| b.clone())
                        .collect();
                    if scalars.len() == 1 {
                        Some(scalars[0].clone())
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

impl<T, N> Typs<T, N> {
    /// Number of types in the sequence.
    pub fn len(&self) -> usize {
        self.0.len()
    }
    /// Iterates over the spanned types in declaration order.
    pub fn iter(&self) -> std::slice::Iter<'_, Spanned<Typ<T, N>>> {
        self.0.iter()
    }
    /// Whether the sequence is empty.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl<T: Clone, N: Clone> ToTraversal1<T> for Typ<T, N> {
    type Output<Z> = Typ<Z, N>;
    fn traverse1<Z: Clone, E>(
        self,
        f: &mut dyn FnMut(T) -> Result<Z, E>,
    ) -> Result<Self::Output<Z>, E> {
        match self {
            Typ::Poly(b, m, n) => Ok(Typ::Poly(f(b)?, m, n)),
            Typ::Base(b) => Ok(Typ::Base(f(b)?)),
            Typ::Vec(deref!(b), n) => Ok(Typ::Vec(Box::new(b.traverse1(f)?), n)),
            Typ::Fin(r) => Ok(Typ::Fin(r)),
            Typ::Unit => Ok(Typ::Unit),
            Typ::Bool => Ok(Typ::Bool),
            Typ::Record(fields) => {
                let pairs: Vec<_> = fields
                    .into_iter()
                    .map(|(name, typ)| typ.traverse1(f).map(|new_typ| (name, new_typ)))
                    .collect::<Result<_, _>>()?;
                Ok(Typ::Record(Ctx::from_iter(pairs)))
            }
        }
    }
}

impl<T: Clone, N: Clone> ToTraversal2<N> for Typ<T, N> {
    type Output<Z> = Typ<T, Z>;
    fn traverse2<Z: Clone, E>(
        self,
        f: &mut dyn FnMut(N) -> Result<Z, E>,
    ) -> Result<Self::Output<Z>, E> {
        match self {
            Typ::Poly(b, m, n) => Ok(Typ::Poly(
                b,
                Spanned::new(f(m.node)?, m.span),
                Spanned::new(f(n.node)?, n.span),
            )),
            Typ::Base(b) => Ok(Typ::Base(b)),
            Typ::Vec(b, n) => Ok(Typ::Vec(
                Box::new(b.traverse2(f)?),
                Spanned::new(f(n.node)?, n.span),
            )),
            Typ::Fin(r) => Ok(Typ::Fin(r.traverse1(f)?)),
            Typ::Unit => Ok(Typ::Unit),
            Typ::Bool => Ok(Typ::Bool),
            Typ::Record(fields) => {
                let pairs: Vec<_> = fields
                    .into_iter()
                    .map(|(name, typ)| typ.traverse2(f).map(|new_typ| (name, new_typ)))
                    .collect::<Result<_, _>>()?;
                Ok(Typ::Record(Ctx::from_iter(pairs)))
            }
        }
    }
}

impl<T: Clone, N: Clone> RangeTraversal<N> for Typ<T, N> {
    fn range_traverse<E>(
        self,
        f: &mut dyn FnMut(Range<N>) -> Result<Range<N>, E>,
    ) -> Result<Self, E> {
        match self {
            Typ::Fin(r) => Ok(Typ::Fin(f(r)?)),
            Typ::Vec(t, n) => Ok(Typ::Vec(Box::new(t.range_traverse(f)?), n)),
            Typ::Record(fields) => {
                let pairs: Vec<_> = fields
                    .into_iter()
                    .map(|(name, typ)| typ.range_traverse(f).map(|new_typ| (name, new_typ)))
                    .collect::<Result<_, _>>()?;
                Ok(Typ::Record(Ctx::from_iter(pairs)))
            }
            _ => Ok(self),
        }
    }
}

impl<T: Clone, N: Clone> ToTraversal1<T> for Typs<T, N> {
    type Output<Z> = Typs<Z, N>;
    fn traverse1<Z: Clone, E>(
        self,
        f: &mut dyn FnMut(T) -> Result<Z, E>,
    ) -> Result<Self::Output<Z>, E> {
        Ok(Typs(
            self.0
                .into_iter()
                .map(|t| t.traverse1(f))
                .collect::<Result<Vec<_>, _>>()?,
        ))
    }
}

impl<T: Clone, N: Clone> ToTraversal2<N> for Typs<T, N> {
    type Output<Z> = Typs<T, Z>;
    fn traverse2<Z: Clone, E>(
        self,
        f: &mut dyn FnMut(N) -> Result<Z, E>,
    ) -> Result<Self::Output<Z>, E> {
        Ok(Typs(
            self.0
                .into_iter()
                .map(|t| t.traverse2(f))
                .collect::<Result<Vec<_>, _>>()?,
        ))
    }
}

impl<T: Clone, N: Clone> RangeTraversal<N> for Typs<T, N> {
    fn range_traverse<E>(
        self,
        f: &mut dyn FnMut(Range<N>) -> Result<Range<N>, E>,
    ) -> Result<Self, E> {
        Ok(Typs(
            self.0
                .into_iter()
                .map(|t| t.range_traverse(f))
                .collect::<Result<Vec<_>, _>>()?,
        ))
    }
}

/// Trait for inlining type aliases. Replaces `Typ::Base(name)` with the
/// expanded type when `name` is a key in the type alias context.
pub trait TypeInline<N>: Sized {
    /// Expands every alias occurring in `self` using the alias context `ctx`.
    fn type_inline(self, ctx: &Ctx<Tid, GTyp<N>>) -> Self;
}

impl<N: Clone> TypeInline<N> for GTyp<N> {
    fn type_inline(self, ctx: &Ctx<Tid, GTyp<N>>) -> Self {
        match self {
            Typ::Base(ref b) => {
                if let Some(expanded) = ctx.get(b) {
                    expanded.clone().type_inline(ctx)
                } else {
                    self
                }
            }
            Typ::Vec(t, n) => Typ::Vec(Box::new(t.type_inline(ctx)), n),
            Typ::Poly(b, m, n) => Typ::Poly(b, m, n),
            Typ::Fin(r) => Typ::Fin(r),
            Typ::Unit => Typ::Unit,
            Typ::Bool => Typ::Bool,
            Typ::Record(fields) => Typ::Record(Ctx::from_iter(
                fields.into_iter().map(|(k, v)| (k, v.type_inline(ctx))),
            )),
        }
    }
}

impl<N: Clone> TypeInline<N> for GTyps<N> {
    fn type_inline(self, ctx: &Ctx<Tid, GTyp<N>>) -> Self {
        Typs(self.0.into_iter().map(|t| t.type_inline(ctx)).collect())
    }
}

/// Zippel type syntax, e.g. `Poly<F, 1, 3>`, `[F; 4]`, `{a: F, b: G}`.
impl<T: fmt::Display, N: fmt::Display> fmt::Display for Typ<T, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Typ::Poly(b, m, n) => write!(f, "Poly<{b}, {}, {}>", m.node, n.node),
            Typ::Base(base) => write!(f, "{base}"),
            Typ::Vec(t, n) => write!(f, "[{t}; {}]", n.node),
            Typ::Fin(r) => write!(f, "Fin<{r}>"),
            Typ::Unit => f.write_str("Unit"),
            Typ::Bool => f.write_str("Bool"),
            Typ::Record(fields) => {
                f.write_str("{")?;
                for (i, (name, typ)) in fields.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{}: {typ}", name.node)?;
                }
                f.write_str("}")
            }
        }
    }
}

impl<T: fmt::Display, N: fmt::Display> fmt::Display for Typs<T, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        crate::display::sep(f, &self.0, ", ")
    }
}
