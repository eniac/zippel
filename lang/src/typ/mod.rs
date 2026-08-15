pub mod ark;
mod distribution;
pub mod infer;
mod kind;
pub mod lub;
mod nothing;
mod qualifier;
pub mod subst;
mod typevar;
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
use share::{BoxAllocator, Ctx, DocAllocator, DocBuilder, Pretty};
use std::fmt;

/// The types of expressions, [N] is the size parameter
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Typ<T, N> {
    /// Polynomial with M variables and degree N over base type T
    /// Poly(F, 1, N) represents univariate polynomials of degree N
    /// Poly(F, M, 1) represents multilinear polynomials of M variables
    Poly(T, Spanned<N>, Spanned<N>),
    /// Vector of size [N] and base type [Typ]
    Vec(Box<Spanned<Typ<T, N>>>, Spanned<N>),
    /// Tid type [Tid]
    Base(T),
    /// Fin within range
    Fin(Range<N>),
    /// Unit type (assert/verify/protocol return)
    Unit,
    /// Record type with named fields
    Record(Ctx<Spanned<String>, Spanned<Typ<T, N>>>),
}

/// Many types
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Typs<T, N>(pub Vec<Spanned<Typ<T, N>>>);

/// Generic type [Tid]
pub type GTyp<N> = Typ<Tid, N>;
pub type GTyps<N> = Typs<Tid, N>;

/// Symbolically sized type
pub type UTyp = Typ<Tid, Size>;
pub type UTyps = Typ<Tid, Size>;

/// Concrete size type
pub type CTyp = Typ<Tid, usize>;
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
            Typ::Fin(_) | Typ::Unit | Typ::Base(_) | Typ::Poly(_, _, _) => {}
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
    pub fn base(b: &T) -> Self
    where
        T: Clone,
    {
        Typ::Base(b.clone())
    }
    pub fn vec(b: &Typ<T, N>, n: N) -> Self
    where
        T: Clone,
        N: Clone,
    {
        Typ::Vec(Box::new(Spanned::dummy(b.clone())), Spanned::dummy(n))
    }
    pub fn fin(range: Range<N>) -> Self {
        Typ::Fin(range)
    }
    pub fn unit() -> Self {
        Typ::Unit
    }
    pub fn into_vec(self) -> (Spanned<Self>, Spanned<N>) {
        match self {
            Typ::Vec(box t, n) => (t, n),
            _ => unreachable!(),
        }
    }
}

impl<N> GTyp<N> {
    pub fn uni(b: &Tid, n: N) -> Self
    where
        N: From<usize>,
    {
        Typ::Poly(b.clone(), Spanned::dummy(N::from(1)), Spanned::dummy(n))
    }
    pub fn mle(b: &Tid, m: N) -> Self
    where
        N: From<usize>,
    {
        Typ::Poly(b.clone(), Spanned::dummy(m), Spanned::dummy(N::from(1)))
    }

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
    pub fn len(&self) -> usize {
        self.0.len()
    }
    pub fn iter(&self) -> std::slice::Iter<'_, Spanned<Typ<T, N>>> {
        self.0.iter()
    }
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
            Typ::Vec(box b, n) => Ok(Typ::Vec(Box::new(b.traverse1(f)?), n)),
            Typ::Fin(r) => Ok(Typ::Fin(r)),
            Typ::Unit => Ok(Typ::Unit),
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
            Typ::Vec(box b, n) => Ok(Typ::Vec(
                Box::new(b.traverse2(f)?),
                Spanned::new(f(n.node)?, n.span),
            )),
            Typ::Fin(r) => Ok(Typ::Fin(r.traverse1(f)?)),
            Typ::Unit => Ok(Typ::Unit),
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
            Typ::Vec(box t, n) => Ok(Typ::Vec(Box::new(t.range_traverse(f)?), n)),
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
            Typ::Vec(box t, n) => Typ::Vec(Box::new(t.type_inline(ctx)), n),
            Typ::Poly(b, m, n) => Typ::Poly(b, m, n),
            Typ::Fin(r) => Typ::Fin(r),
            Typ::Unit => Typ::Unit,
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

/// Pretty-printer for zippel types.
impl<'a, D, A, T, N> Pretty<'a, D, A> for Typ<T, N>
where
    D: DocAllocator<'a, A>,
    T: Pretty<'a, D, A> + Clone,
    N: Pretty<'a, D, A> + Clone,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        match self {
            Typ::Poly(b, m, n) => allocator.concat([
                allocator.text("Poly<"),
                b.pretty(allocator),
                allocator.text(", "),
                m.node.pretty(allocator),
                allocator.text(", "),
                n.node.pretty(allocator),
                allocator.text(">"),
            ]),
            Typ::Base(base) => base.pretty(allocator),
            Typ::Vec(box t, n) => allocator.concat([
                allocator.text("["),
                t.pretty(allocator),
                allocator.text("; "),
                n.node.pretty(allocator),
                allocator.text("]"),
            ]),
            Typ::Fin(r) => allocator.concat([
                allocator.text("Fin<"),
                r.pretty(allocator),
                allocator.text(">"),
            ]),
            Typ::Unit => allocator.text("Unit"),
            Typ::Record(fields) => {
                let mut docs = Vec::new();
                docs.push(allocator.text("{"));
                let field_docs: Vec<_> = fields
                    .into_iter()
                    .map(|(name, typ)| {
                        allocator.concat([
                            allocator.text(name.node),
                            allocator.text(": "),
                            typ.pretty(allocator),
                        ])
                    })
                    .collect();
                docs.push(allocator.intersperse(field_docs, ", "));
                docs.push(allocator.text("}"));
                allocator.concat(docs)
            }
        }
    }

    fn is_nil(&self) -> bool {
        false
    }
}

impl<'a, D, A, T, N> Pretty<'a, D, A> for Typs<T, N>
where
    D: DocAllocator<'a, A>,
    T: Pretty<'a, D, A> + Clone,
    N: Pretty<'a, D, A> + Clone,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.intersperse(self.0.into_iter().map(|t| t.pretty(allocator)), ", ")
    }

    fn is_nil(&self) -> bool {
        self.0.is_empty()
    }
}

impl<'a, N: Pretty<'a, BoxAllocator, ()> + Clone, T: Pretty<'a, BoxAllocator, ()> + Clone>
    fmt::Display for Typ<T, N>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Typ<T, N> as Pretty<'a, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

impl<'a, N: Pretty<'a, BoxAllocator, ()> + Clone, T: Pretty<'a, BoxAllocator, ()> + Clone>
    fmt::Display for Typs<T, N>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Typs<T, N> as Pretty<'a, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}
