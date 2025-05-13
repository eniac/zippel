use from_pest::{ConversionError, FromPest};
use pest::iterators::Pairs;
use std::fmt;

use share::{Pretty, DocAllocator, DocBuilder, BoxAllocator, Ctx};
use share::traversal::{ToTraversal1, ToTraversal2};
use crate::id::{Tid, Vid, TidSubst};
use crate::typ::{Size, Typ, Qualifier, Distribution, Range, RangeTraversal};
use crate::parser::*;

/// `Arg` represents an argument in the Zippel language, including its identifier, type, and principals.
///
///     **Zippel Code:**
///     ```zippel
///     fn foo<Verifier>(a: F  & Verifier) { ... }
///     ```
///
///     In this example, `a` is the identifier of the argument, `F` is the type and `Verifier` is
///     the principal.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Arg<T, N> {
    pub qualifier: Qualifier,
    pub distribution: Distribution,
    pub id: Vid,
    pub typ: Typ<T, N>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Args<T, N>(pub Vec<Arg<T, N>>);

/// Generic typed argument
pub type GArg<N> = Arg<Tid, N>;
pub type GArgs<N> = Args<Tid, N>;

/// Symbolically sized arg
pub type UArg = Arg<Tid, Size>;
pub type UArgs = Args<Tid, Size>;

/// Concrete sized arg
pub type CArg = Arg<Tid, usize>;
pub type CArgs = Args<Tid, usize>;

impl<T, N> Arg<T, N> {
    pub fn new<'a>(qualifier: Qualifier, distribution: Distribution, id: &'a str, typ: Typ<T, N>) -> Self {
        Arg { qualifier, distribution, id: Vid::new(id), typ }
    }
    pub fn public<'a>(id : &'a str, typ: Typ<T, N>) -> Self {
        Arg { qualifier: Qualifier::Public, distribution: Distribution::Nonuniform, id: Vid::new(id), typ }
    }
    pub fn private<'a>(id: &'a str, typ: Typ<T, N>) -> Self {
        Arg { qualifier: Qualifier::Private, distribution: Distribution::Nonuniform, id : Vid::new(id), typ }
    }
    pub fn uniform<'a>(qualifier: Qualifier, id: &'a str, typ: Typ<T, N>) -> Self {
        Arg { qualifier, distribution: Distribution::Uniform,  id : Vid::new(id), typ }
    }
    pub fn public_uniform<'a>(id: &'a str, typ: Typ<T, N>) -> Self {
        Arg { qualifier: Qualifier::Public, distribution: Distribution::Uniform, id : Vid::new(id), typ }
    }
    pub fn private_uniform<'a>(id: &'a str, typ: Typ<T, N>) -> Self {
        Arg { qualifier: Qualifier::Private, distribution: Distribution::Uniform, id : Vid::new(id), typ }
    }
    pub fn public_uniform_nz<'a>(id: &'a str, typ: Typ<T, N>) -> Self {
        Arg { qualifier: Qualifier::Public, distribution: Distribution::UniformNonZero, id : Vid::new(id), typ }
    }
    pub fn private_uniform_nz<'a>(id: &'a str, typ: Typ<T, N>) -> Self {
        Arg { qualifier: Qualifier::Private, distribution: Distribution::UniformNonZero, id : Vid::new(id), typ }
    }
    pub fn is_private(&self) -> bool {
        self.qualifier.is_private()
    }
    pub fn is_public(&self) -> bool {
        self.qualifier.is_public()
    }
}

impl<T, N> Args<T, N> {
    pub fn iter(&self) -> std::slice::Iter<Arg<T, N>> {
        self.0.iter()
    }
    pub fn len(&self) -> usize {
        self.0.len()
    }
    pub fn to_ctx(&self) -> Ctx<Vid, Typ<T, N>> where T: Clone, N: Clone {
        self.0.iter().map(|arg| (arg.id.clone(), arg.typ.clone())).collect()
    }
}

impl<T, N> IntoIterator for Args<T, N> {
    type Item = Arg<T, N>;
    type IntoIter = std::vec::IntoIter<Arg<T, N>>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<T, N> FromIterator<Arg<T, N>> for Args<T, N> {
    fn from_iter<I: IntoIterator<Item=Arg<T, N>>>(iter: I) -> Self {
        Args(iter.into_iter().collect())
    }
}

impl<N> TidSubst for GArg<N> {
    fn tid_subst(&mut self, from: &Tid, to: &Tid) {
        self.typ.tid_subst(from, to)
    }
}

impl<N> TidSubst for GArgs<N> {
    fn tid_subst(&mut self, from: &Tid, to: &Tid) {
        self.0.iter_mut().for_each(|arg| arg.tid_subst(from, to))
    }
}

/// How to traverse the first type parameter [T] of [Arg<T, N>]
impl<T, N> ToTraversal1<T> for Arg<T, N> {
    type Output<Z> = Arg<Z, N>;
    fn traverse1<Z, E>(self, f: &mut dyn FnMut(T) -> Result<Z, E>) -> Result<Self::Output<Z>, E> {
        let Arg { qualifier, distribution, id, typ } = self;
        Ok(Arg { qualifier, distribution, id, typ: typ.traverse1(f)? })
    }
}

/// How to traverse the second type parameter [N] of [Arg<T, N>]
impl<T, N> ToTraversal2<N> for Arg<T, N> {
    type Output<Z> = Arg<T, Z>;
    fn traverse2<Z, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Self::Output<Z>, E> {
        let Arg { qualifier, distribution, id, typ } = self;
        Ok(Arg { qualifier, distribution, id, typ: typ.traverse2(f)? })
    }
}

/// How to traverse the second type parameter [N] of [Args<T, N>]
impl<T, N> ToTraversal1<T> for Args<T, N> {
    type Output<Z> = Args<Z, N>;
    fn traverse1<Z, E>(self, f: &mut dyn FnMut(T) -> Result<Z, E>) -> Result<Self::Output<Z>, E> {
        Ok(Args(self.0.traverse1(&mut |x| x.traverse1(f))?))
    }
}

/// How to traverse the second type parameter [N] of [Args<T, N>]
impl<T, N> ToTraversal2<N> for Args<T, N> {
    type Output<Z> = Args<T, Z>;
    fn traverse2<Z, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Self::Output<Z>, E> {
        Ok(Args(self.0.traverse1(&mut |x| x.traverse2(f))?))
    }
}

impl<T, N> RangeTraversal<N> for Arg<T, N> {
    fn range_traverse<E>(self, f: &mut dyn FnMut(Range<N>) -> Result<Range<N>, E>) -> Result<Self, E> {
        Ok(Arg { qualifier: self.qualifier, distribution: self.distribution, id: self.id, typ: self.typ.range_traverse(f)? })
    }
}

impl<T, N> RangeTraversal<N> for Args<T, N> {
    fn range_traverse<E>(self, f: &mut dyn FnMut(Range<N>) -> Result<Range<N>, E>) -> Result<Self, E> {
        Ok(Args(self.0.into_iter().map(|arg| arg.range_traverse(f)).collect::<Result<_, _>>()?))
    }
}

impl<const L: usize, N, T> From<[Arg<T, N>; L]> for Args<T, N> {
    fn from(args: [Arg<T, N>; L]) -> Self {
        Args(args.into_iter().collect())
    }
}

/// Pretty printer instance
impl<'a, D, T, N, A> Pretty<'a, D, A> for Arg<T, N>
where
    D: DocAllocator<'a, A>,
    N: 'a + Clone + Pretty<'a, D, A>,
    T: 'a + Clone + Pretty<'a, D, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        let Arg { qualifier, distribution, id, typ } = self;
        allocator.concat([
            qualifier.pretty(allocator),
            distribution.pretty(allocator),
            id.pretty(allocator),
            allocator.text(": "),
            typ.pretty(allocator),
        ])
    }

    fn is_nil(&self) -> bool {
        false
    }
}

/// Display instance calls the pretty printer
impl<'a, T, N> fmt::Display for Arg<T, N>
where
    T: Clone + Pretty<'a, BoxAllocator, ()> + 'a,
    N: Clone + Pretty<'a, BoxAllocator, ()> + 'a
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Arg<T, N> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(60, f)
    }
}

/// Pretty printer instance
impl<'a, D, T, N, A> Pretty<'a, D, A> for Args<T, N>
where
    D: DocAllocator<'a, A>,
    N: 'a + Clone + Pretty<'a, D, A>,
    T: 'a + Clone + Pretty<'a, D, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.intersperse(
            self.0.into_iter().map(|arg| arg.pretty(allocator)), ", ")
    }

    fn is_nil(&self) -> bool {
        self.0.is_empty()
    }
}

/// Display instance calls the pretty printer
impl<'a, T, N> fmt::Display for Args<T, N>
where
    T: Clone + Pretty<'a, BoxAllocator, ()> + 'a,
    N: Clone + Pretty<'a, BoxAllocator, ()> + 'a
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Args<T, N> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(140, f)
    }
}

/// Parser instances
impl<'pest> FromPest<'pest> for GArg<Size> {
    type Rule = Rule;
    type FatalError = InputError<'pest>;

    fn from_pest(
        pest: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        let pair = pest.next().ok_or(ConversionError::NoMatch)?;
        match pair.as_rule() {
            Rule::arg => {
                let mut inner = pair.into_inner();
                let mut qualifier = Qualifier::Public;
                let mut distribution = Distribution::Nonuniform;

                // Check for optional qualifier
                if let Some(qualifier_pair) = inner.peek() {
                    if qualifier_pair.as_rule() == Rule::qualifier {
                        qualifier = Qualifier::from_pest(&mut inner)?;
                    }
                }
                // Check for optional Distribution
                if let Some(distr_pair) = inner.peek() {
                    if distr_pair.as_rule() == Rule::distribution {
                        distribution = Distribution::from_pest(&mut inner)?;
                    }
                }

                let id = Vid::from_pest(&mut inner)?;
                let typ = Typ::from_pest(&mut inner)?;
                Ok(Arg { qualifier, distribution, id, typ })
            },
            _ => Err(ConversionError::Malformed(InputError::UnexpectedExp(pair))),
        }
    }
}

impl<'pest> FromPest<'pest> for GArgs<Size> {
    type Rule = Rule;
    type FatalError = InputError<'pest>;

    fn from_pest(
        pest: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        let pair = pest.next().ok_or(ConversionError::NoMatch)?;
        match pair.as_rule() {
            Rule::args => {
                let mut args = Vec::new();
                for pair in pair.into_inner() {
                    let mut p = Pairs::single(pair);
                    args.push(Arg::from_pest(&mut p)?);
                }
                Ok(Args(args))
            },
            _ => Err(ConversionError::Malformed(InputError::UnexpectedExp(pair))),
        }
    }
}

#[cfg(test)] use pest::Parser;
#[test]
fn arg_parser() {
    let ex = "public a: F, private uniform foo: X";
    let mut pairs = ZippelParser::parse(Rule::args, ex).unwrap();
    assert_eq!(
        Args::from_pest(&mut pairs),
        Ok(Args(vec![
            Arg::new(Qualifier::Public, Distribution::Nonuniform, "a", Typ::varstr("F")),
            Arg::new(Qualifier::Private, Distribution::Uniform, "foo", Typ::varstr("X"))
        ]))
    );

    let ex = "public uniform* a: F";
    let mut pairs = ZippelParser::parse(Rule::arg, ex).unwrap();
    assert_eq!(Arg::from_pest(&mut pairs), Ok(Arg::public_uniform_nz("a", Typ::varstr("F"))));

    let ex = "a: F";
    let mut pairs = ZippelParser::parse(Rule::arg, ex).unwrap();
    assert_eq!(Arg::from_pest(&mut pairs), Ok(Arg::public("a", Typ::varstr("F"))));
}

#[test]
fn arg_traversal() {
    let arg = GArg::new(Qualifier::Public, Distribution::Uniform, "a",
        Typ::fin(Range { start: Size::varstr("N") / 2, step: Size::one(), end: Size::varstr("N")*2 }));
    assert_eq!(arg.traverse2(&mut |x| x.eval(&Ctx::singleton("N".into(), 2))).unwrap(),
       Arg::new(Qualifier::Public, Distribution::Uniform, "a", Typ::fin(Range { start: 1, step: 1, end: 4 })));
}
