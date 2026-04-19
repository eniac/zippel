mod kind;
mod typevar;
mod size;
mod qualifier;
mod distribution;
mod nothing;
pub mod ark;
pub mod infer;
pub mod unify;
pub mod lub;
pub mod range;
pub mod subst;

use crate::id::{Tid, TidSubst, Vid};

pub use kind::{Kind, UKind, CKind};
pub use size::{Size, EvalError};
pub use qualifier::Qualifier;
pub use distribution::Distribution;
pub use typevar::{TypeVar, TypeVars, UTypeVar, CTypeVar, UTypeVars, CTypeVars};
pub use nothing::Nothing;
pub use subst::{SizeSubsts, AliasSubsts};
pub use range::{Range, CRange, RangeError, RangeTraversal};
pub use ark::Ark;
pub use infer::{Typeable, TypeError};

use share::{Ctx, Pretty, BoxAllocator, DocAllocator, DocBuilder};
use share::traversal::{ToTraversal1, ToTraversal2};
use crate::parser::*;
use from_pest::{ConversionError, FromPest};
use pest::iterators::Pairs;
use std::fmt;

/// The types of expressions, [N] is the size parameter
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub enum Typ<T, N> {
    /// Polynomial with M variables and degree N over base type T
    /// Poly(F, 1, N) represents univariate polynomials of degree N
    /// Poly(F, M, 1) represents multilinear polynomials of M variables
    Poly(T, N, N),
    /// Vector of size [N] and base type [Typ]
    Vec(Box<Typ<T, N>>, N),
    /// Tid type [Tid]
    Base(T),
    /// Fin within range
    Fin(Range<N>),
    /// Boolean (BExp)
    Bool,
    /// Record type with named fields
    Record(Ctx<String, Typ<T, N>>)
}

/// Many types
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub struct Typs<T, N>(pub Vec<Typ<T, N>>);

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
            Typ::Poly(b, _, _)
            | Typ::Base(b) if b == from => *b = to.clone(),
            Typ::Vec(b, _) => b.tid_subst(from, to),
            Typ::Record(fields) => {
                fields.modify(|_, field_typ| {
                    field_typ.tid_subst(from, to);
                });
            },
            Typ::Fin(_) | Typ::Bool | Typ::Base(_)
            | Typ::Poly(_, _, _) => {}
        }
    }
}

impl<T, N> IntoIterator for Typs<T, N> {
    type Item = Typ<T, N>;
    type IntoIter = std::vec::IntoIter<Typ<T, N>>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<T, N> FromIterator<Typ<T, N>> for Typs<T, N> {
    fn from_iter<I: IntoIterator<Item=Typ<T, N>>>(iter: I) -> Self {
        Typs(iter.into_iter().collect())
    }
}

impl<N: Clone> TidSubst for GTyps<N> {
    fn tid_subst(&mut self, from: &Tid, to: &Tid) {
        self.0.iter_mut().for_each(|t| t.tid_subst(from, to))
    }
}

impl<T, N> Typ<T, N> {
    pub fn base(b: &T) -> Self where T: Clone {
        Typ::Base(b.clone())
    }
    pub fn vec(b: &Typ<T, N>, n: N) -> Self where T: Clone, N: Clone {
        Typ::Vec(Box::new(b.clone()), n)
    }
    pub fn fin(range: Range<N>) -> Self {
        Typ::Fin(range)
    }
    pub fn bool() -> Self {
        Typ::Bool
    }
    pub fn record(fields: Ctx<String, Typ<T, N>>) -> Self {
        Typ::Record(fields)
    }
    pub fn into_vec(self) -> (Self, N) {
        match self {
            Typ::Vec(box t, n) => (t, n),
            _ => unreachable!()
        }
    }
}

impl<N> GTyp<N> {
    pub fn varstr<'a>(b: &'a str) -> Self {
        Typ::Base(Tid::new(b))
    }
    pub fn var(b: &Tid) -> Self {
        Typ::Base(b.clone())
    }
    pub fn uni(b: &Tid, n: N) -> Self where N: From<usize> {
        Typ::Poly(b.clone(), N::from(1), n)
    }
    pub fn mle(b: &Tid, m: N) -> Self where N: From<usize> {
        Typ::Poly(b.clone(), m, N::from(1))
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
            },
            Typ::Fin(_) =>
                // Find the first field and return It
                ctx.iter().find(|(_, k)| k.is_scalar())
                    .map(|(b, _)| b.clone()),
            _ => None
        }
    }

    pub fn to_scalar_vec<M>(&self, ctx: &Ctx<Tid, Kind<M>>) -> Option<(Tid, N)> where N: Clone {
        match self {
            Typ::Vec(box t, n) => {
                let s = t.to_scalar(ctx)?;
                Some((s, n.clone()))
            },
            _ => None
        }
    }

}

impl CTyp {
    /// Helper to check if this is a univariate polynomial and extract (base_type, degree)
    pub fn as_uni(&self) -> Option<(&Tid, usize)> {
        match self {
            Typ::Poly(tid, 1, n) => Some((tid, *n)),
            _ => None
        }
    }

    /// Helper to check if this is a multilinear extension and extract (base_type, num_vars)
    pub fn as_mle(&self) -> Option<(&Tid, usize)> {
        match self {
            Typ::Poly(tid, m, 1) => Some((tid, *m)),
            _ => None
        }
    }
}

impl<T, N> Typs<T, N> {
    pub fn len(&self) -> usize {
        self.0.len()
    }
    pub fn iter(&self) -> std::slice::Iter<'_, Typ<T, N>> {
        self.0.iter()
    }
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    pub fn last(&self) -> Option<&Typ<T, N>> {
        self.0.last()
    }
}

impl<T: Clone, N: Clone> ToTraversal1<T> for Typ<T, N> {
    type Output<Z> = Typ<Z, N>;
    fn traverse1<Z: Clone, E>(self, f: &mut dyn FnMut(T) -> Result<Z, E>) -> Result<Self::Output<Z>, E> {
        match self {
            Typ::Poly(b, m, n) => Ok(Typ::Poly(f(b)?, m, n)),
            Typ::Base(b) => Ok(Typ::Base(f(b)?)),
            Typ::Vec(box b, n) =>
                Ok(Typ::Vec(Box::new(b.traverse1(f)?), n)),
            Typ::Fin(r) => Ok(Typ::Fin(r)),
            Typ::Bool => Ok(Typ::Bool),
            Typ::Record(fields) => {
                let pairs: Vec<_> = fields.into_iter()
                    .map(|(name, typ)| typ.traverse1(f).map(|new_typ| (name, new_typ)))
                    .collect::<Result<_, _>>()?;
                Ok(Typ::Record(Ctx::from_iter(pairs)))
            }
        }
    }
}

impl<T: Clone, N: Clone> ToTraversal2<N> for Typ<T, N> {
    type Output<Z> = Typ<T, Z>;
    fn traverse2<Z: Clone, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Self::Output<Z>, E> {
        match self {
            Typ::Poly(b, m, n) => Ok(Typ::Poly(b, f(m)?, f(n)?)),
            Typ::Base(b) => Ok(Typ::Base(b)),
            Typ::Vec(box b, n) =>
                Ok(Typ::Vec(Box::new(b.traverse2(f)?), f(n)?)),
            Typ::Fin(r) => Ok(Typ::Fin(r.traverse1(f)?)),
            Typ::Bool => Ok(Typ::Bool),
            Typ::Record(fields) => {
                let pairs: Vec<_> = fields.into_iter()
                    .map(|(name, typ)| typ.traverse2(f).map(|new_typ| (name, new_typ)))
                    .collect::<Result<_, _>>()?;
                Ok(Typ::Record(Ctx::from_iter(pairs)))
            }
        }
    }
}

impl<T: Clone, N: Clone> RangeTraversal<N> for Typ<T, N> {
    fn range_traverse<E>(self, f: &mut dyn FnMut(Range<N>) -> Result<Range<N>, E>) -> Result<Self, E> {
        match self {
            Typ::Fin(r) => Ok(Typ::Fin(f(r)?)),
            Typ::Vec(box t, n) => Ok(Typ::Vec(Box::new(t.range_traverse(f)?), n)),
            Typ::Record(fields) => {
                let pairs: Vec<_> = fields.into_iter()
                    .map(|(name, typ)| typ.range_traverse(f).map(|new_typ| (name, new_typ)))
                    .collect::<Result<_, _>>()?;
                Ok(Typ::Record(Ctx::from_iter(pairs)))
            },
            _ => Ok(self)
        }
    }
}

impl<T: Clone, N: Clone> ToTraversal1<T> for Typs<T, N> {
    type Output<Z> = Typs<Z, N>;
    fn traverse1<Z: Clone, E>(self, f: &mut dyn FnMut(T) -> Result<Z, E>) -> Result<Self::Output<Z>, E> {
        Ok(Typs(self.0.into_iter().map(|t| t.traverse1(f)).collect::<Result<Vec<_>, _>>()?))
    }
}

impl<T: Clone, N: Clone> ToTraversal2<N> for Typs<T, N> {
    type Output<Z> = Typs<T, Z>;
    fn traverse2<Z: Clone, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Self::Output<Z>, E> {
        Ok(Typs(self.0.into_iter().map(|t| t.traverse2(f)).collect::<Result<Vec<_>, _>>()?))
    }
}

impl<T: Clone, N: Clone> RangeTraversal<N> for Typs<T, N> {
    fn range_traverse<E>(self, f: &mut dyn FnMut(Range<N>) -> Result<Range<N>, E>) -> Result<Self, E> {
        Ok(Typs(self.0.into_iter().map(|t| t.range_traverse(f)).collect::<Result<Vec<_>, _>>()?))
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
            },
            Typ::Vec(box t, n) => Typ::Vec(Box::new(t.type_inline(ctx)), n),
            Typ::Poly(b, m, n) => Typ::Poly(b, m, n),
            Typ::Fin(r) => Typ::Fin(r),
            Typ::Bool => Typ::Bool,
            Typ::Record(fields) => Typ::Record(
                Ctx::from_iter(fields.into_iter().map(|(k, v)| (k, v.type_inline(ctx))))
            ),
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
                m.pretty(allocator),
                allocator.text(", "),
                n.pretty(allocator),
                allocator.text(">")
            ]),
            Typ::Base(base) => base.pretty(allocator),
            Typ::Vec(box t, n) => allocator.concat([
                allocator.text("["),
                t.pretty(allocator),
                allocator.text("; "),
                n.pretty(allocator),
                allocator.text("]")
            ]),
            Typ::Fin(r) => allocator.concat([
                allocator.text("Fin<"),
                r.pretty(allocator),
                allocator.text(">")
            ]),
            Typ::Bool => allocator.text("Bool"),
            Typ::Record(fields) => {
                let mut docs = Vec::new();
                docs.push(allocator.text("{"));
                let field_docs: Vec<_> = fields.into_iter().map(|(name, typ)| {
                    allocator.concat([
                        allocator.text(name),
                        allocator.text(": "),
                        typ.pretty(allocator)
                    ])
                }).collect();
                docs.push(allocator.intersperse(field_docs.into_iter(), ", "));
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

impl<'a, N: Pretty<'a, BoxAllocator, ()> + Clone, T: Pretty<'a, BoxAllocator, ()> + Clone> fmt::Display for Typ<T, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Typ<T, N> as Pretty<'a, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

impl<'a, N: Pretty<'a, BoxAllocator, ()> + Clone, T: Pretty<'a, BoxAllocator, ()> + Clone> fmt::Display for Typs<T, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Typs<T, N> as Pretty<'a, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

/// Parser for zippel types.
impl<'pest> FromPest<'pest> for UTyp {
    type Rule = Rule;
    type FatalError = InputError<'pest>;

    fn from_pest(
        pest: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        let pair = pest.next().ok_or(ConversionError::NoMatch)?;
        match pair.as_rule() {
            Rule::typ => Typ::from_pest(&mut pair.into_inner()), // Go into typ here
            Rule::base_ty => Ok(Typ::Base(Tid::from_pest(&mut pair.into_inner())?)),
            Rule::uni_ty => {
                let mut inner = pair.into_inner();
                let id = Tid::from_pest(&mut inner)?;
                let size = Size::from_pest(&mut inner)?;
                Ok(Typ::Poly(id, Size::one(), size))
            }
            Rule::mle_ty => {
                let mut inner = pair.into_inner();
                let id = Tid::from_pest(&mut inner)?;
                let size = Size::from_pest(&mut inner)?;
                Ok(Typ::Poly(id, size, Size::one()))
            }
            Rule::poly_ty => {
                let mut inner = pair.into_inner();
                let id = Tid::from_pest(&mut inner)?;
                // Each size_ty is a complete subtree, get its inner pairs
                let m_pair = inner.next().ok_or(ConversionError::NoMatch)?;
                let m = Size::from_pest(&mut m_pair.into_inner())?;
                let n_pair = inner.next().ok_or(ConversionError::NoMatch)?;
                let n = Size::from_pest(&mut n_pair.into_inner())?;
                Ok(Typ::Poly(id, m, n))
            }
            Rule::fin_ty =>
                Ok(Typ::fin(Range::from_pest(&mut pair.into_inner())?)),
            Rule::bool_ty => Ok(Typ::Bool),
            Rule::vec_ty => {
                let mut inner = pair.into_inner();
                let id = Typ::from_pest(&mut inner)?;
                let size = Size::from_pest(&mut inner)?;
                Ok(Typ::vec(&id, size))
            }
            Rule::record_ty => {
                let mut inner = pair.into_inner();
                let mut fields = Ctx::new();
                while let Some(field_pair) = inner.next() {
                    if field_pair.as_rule() == Rule::record_field {
                        let mut field_inner = field_pair.into_inner();
                        let field_name = Vid::from_pest(&mut field_inner)?.0;
                        let field_typ = Typ::from_pest(&mut field_inner)?;
                        fields.insert(&field_name, &field_typ);
                    }
                }
                Ok(Typ::Record(fields))
            }
            _ => unreachable!(),
        }
    }
}

#[cfg(test)] use pest::Parser;

#[test]
fn typ_parser() {
    let mut pairs = ZippelParser::parse(Rule::typ, "A").unwrap();
    assert_eq!(Typ::from_pest(&mut pairs).unwrap(), GTyp::varstr("A"));

    pairs = ZippelParser::parse(Rule::typ, "Uni<X, N>").unwrap();
    assert_eq!(Typ::from_pest(&mut pairs).unwrap(), GTyp::Poly(Tid::from("X"), Size::from(1), Size::from("N")));

    pairs = ZippelParser::parse(Rule::typ, "Mle<X, 2>").unwrap();
    assert_eq!(Typ::from_pest(&mut pairs).unwrap(), GTyp::Poly(Tid::from("X"), Size::from(2), Size::from(1)));

    pairs = ZippelParser::parse(Rule::typ, "Poly<X, 1, 2>").unwrap();
    assert_eq!(Typ::from_pest(&mut pairs).unwrap(), GTyp::Poly(Tid::from("X"), Size::from(1), Size::from(2)));

    pairs = ZippelParser::parse(Rule::typ, "[A; N]").unwrap();
    assert_eq!(Typ::from_pest(&mut pairs).unwrap(), GTyp::vec(&Typ::varstr("A"), Size::from("N")));

    pairs = ZippelParser::parse(Rule::typ, "Fin<0..N>").unwrap();
    assert_eq!(Typ::from_pest(&mut pairs).unwrap(), GTyp::fin(Range { start: Size::zero(), step: Size::one(), end: Size::from("N") }));

    pairs = ZippelParser::parse(Rule::typ, "Fin<10>").unwrap();
    assert_eq!(Typ::from_pest(&mut pairs).unwrap(), GTyp::fin(Range { start: Size::zero(), step: Size::one(), end: Size::from(10) }));

    pairs = ZippelParser::parse(Rule::typ, "Bool").unwrap();
    assert_eq!(Typ::from_pest(&mut pairs).unwrap(), GTyp::Bool);
}
