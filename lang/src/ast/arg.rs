use std::fmt;

use crate::ast::spanned::Spanned;
use crate::ast::Size;
use crate::id::{Tid, TidSubst, Vid};
use crate::typ::{Distribution, GTyp, Qualifier, Range, RangeTraversal, Typ, TypeInline};
use share::traversal::{ToTraversal1, ToTraversal2};
use share::{BoxAllocator, Ctx, DocAllocator, DocBuilder, Pretty};

/// `Arg` represents an argument in the Zippel language, including its identifier, type, and principals.
///
/// **Zippel Code:**
/// ```zippel
/// fn foo<Verifier>(a: F  & Verifier) { ... }
/// ```
///
/// In this example, `a` is the identifier of the argument, `F` is the type and `Verifier` is
/// the principal.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Arg<T, N> {
    /// Visibility of the argument (`witness`, `local`, `extra`, `instance`);
    /// the seed value for qualifier propagation over the DAG.
    pub qualifier: Spanned<Qualifier>,
    /// Whether the argument is assumed uniformly distributed; the seed value
    /// for uniformity propagation.
    pub distribution: Spanned<Distribution>,
    /// The bound value variable.
    pub id: Spanned<Vid>,
    /// Declared type of the argument, with size repr `N` and base-type tag `T`.
    pub typ: Spanned<Typ<T, N>>,
}

/// The argument list of a signature, in declaration order.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Args<T, N>(pub Vec<Spanned<Arg<T, N>>>);

/// Generic typed argument
pub type GArg<N> = Arg<Tid, N>;
/// Argument list whose base types are `Tid` tags.
pub type GArgs<N> = Args<Tid, N>;

/// Symbolically sized arg
pub type UArg = Arg<Tid, Size>;
/// Argument list of a freshly parsed declaration, with symbolic sizes.
pub type UArgs = Args<Tid, Size>;

/// Concrete sized arg
pub type CArg = Arg<Tid, usize>;
/// Argument list after concretization, with `usize` sizes.
pub type CArgs = Args<Tid, usize>;

impl<T, N> Arg<T, N> {
    /// Builds an argument with explicit visibility and distribution and
    /// dummy (non-source) spans.
    pub fn new(qualifier: Qualifier, distribution: Distribution, id: &str, typ: Typ<T, N>) -> Self {
        Arg {
            qualifier: Spanned::dummy(qualifier),
            distribution: Spanned::dummy(distribution),
            id: Spanned::dummy(Vid::new(id)),
            typ: Spanned::dummy(typ),
        }
    }
    /// Builds a public (`Instance`, nonuniform) argument with dummy spans;
    /// the shorthand used when constructing signatures programmatically.
    pub fn instance(id: &str, typ: Typ<T, N>) -> Self {
        Arg {
            qualifier: Spanned::dummy(Qualifier::Instance),
            distribution: Spanned::dummy(Distribution::Nonuniform),
            id: Spanned::dummy(Vid::new(id)),
            typ: Spanned::dummy(typ),
        }
    }
}

impl<T, N> Args<T, N> {
    /// Iterates over the arguments in declaration order.
    pub fn iter(&self) -> std::slice::Iter<'_, Spanned<Arg<T, N>>> {
        self.0.iter()
    }
    /// Number of arguments.
    pub fn len(&self) -> usize {
        self.0.len()
    }
    /// Whether the signature takes no arguments.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    /// Collects the arguments into the variable context used by type
    /// inference, mapping each identifier to its declared type.
    pub fn to_ctx(&self) -> Ctx<Vid, Typ<T, N>>
    where
        T: Clone,
        N: Clone,
    {
        self.0
            .iter()
            .map(|arg| (arg.node.id.node.clone(), arg.node.typ.node.clone()))
            .collect()
    }
}

impl<T, N> IntoIterator for Args<T, N> {
    type Item = Spanned<Arg<T, N>>;
    type IntoIter = std::vec::IntoIter<Spanned<Arg<T, N>>>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<T, N> FromIterator<Spanned<Arg<T, N>>> for Args<T, N> {
    fn from_iter<I: IntoIterator<Item = Spanned<Arg<T, N>>>>(iter: I) -> Self {
        Args(iter.into_iter().collect())
    }
}

impl<N: Clone> TidSubst for GArg<N> {
    fn tid_subst(&mut self, from: &Tid, to: &Tid) {
        self.typ.node.tid_subst(from, to)
    }
}

impl<N: Clone> TidSubst for GArgs<N> {
    fn tid_subst(&mut self, from: &Tid, to: &Tid) {
        self.0
            .iter_mut()
            .for_each(|arg| arg.node.tid_subst(from, to))
    }
}

/// How to traverse the first type parameter `T` of [Arg<T, N>]
impl<T: Clone, N: Clone> ToTraversal1<T> for Arg<T, N> {
    type Output<Z> = Arg<Z, N>;
    fn traverse1<Z: Clone, E>(
        self,
        f: &mut dyn FnMut(T) -> Result<Z, E>,
    ) -> Result<Self::Output<Z>, E> {
        let Arg {
            qualifier,
            distribution,
            id,
            typ,
        } = self;
        Ok(Arg {
            qualifier,
            distribution,
            id,
            typ: typ.traverse1(f)?,
        })
    }
}

/// How to traverse the second type parameter `N` of [Arg<T, N>]
impl<T: Clone, N: Clone> ToTraversal2<N> for Arg<T, N> {
    type Output<Z> = Arg<T, Z>;
    fn traverse2<Z: Clone, E>(
        self,
        f: &mut dyn FnMut(N) -> Result<Z, E>,
    ) -> Result<Self::Output<Z>, E> {
        let Arg {
            qualifier,
            distribution,
            id,
            typ,
        } = self;
        Ok(Arg {
            qualifier,
            distribution,
            id,
            typ: typ.traverse2(f)?,
        })
    }
}

/// How to traverse the first type parameter `T` of [Args<T, N>]
impl<T: Clone, N: Clone> ToTraversal1<T> for Args<T, N> {
    type Output<Z> = Args<Z, N>;
    fn traverse1<Z: Clone, E>(
        self,
        f: &mut dyn FnMut(T) -> Result<Z, E>,
    ) -> Result<Self::Output<Z>, E> {
        let mapped: Result<Vec<_>, E> = self
            .0
            .into_iter()
            .map(|s| {
                let node = s.node.traverse1(f)?;
                Ok(Spanned::new(node, s.span))
            })
            .collect();
        Ok(Args(mapped?))
    }
}

/// How to traverse the second type parameter `N` of [Args<T, N>]
impl<T: Clone, N: Clone> ToTraversal2<N> for Args<T, N> {
    type Output<Z> = Args<T, Z>;
    fn traverse2<Z: Clone, E>(
        self,
        f: &mut dyn FnMut(N) -> Result<Z, E>,
    ) -> Result<Self::Output<Z>, E> {
        let mapped: Result<Vec<_>, E> = self
            .0
            .into_iter()
            .map(|s| {
                let node = s.node.traverse2(f)?;
                Ok(Spanned::new(node, s.span))
            })
            .collect();
        Ok(Args(mapped?))
    }
}

impl<T: Clone, N: Clone> RangeTraversal<N> for Arg<T, N> {
    fn range_traverse<E>(
        self,
        f: &mut dyn FnMut(Range<N>) -> Result<Range<N>, E>,
    ) -> Result<Self, E> {
        Ok(Arg {
            qualifier: self.qualifier,
            distribution: self.distribution,
            id: self.id,
            typ: Spanned::new(self.typ.node.range_traverse(f)?, self.typ.span),
        })
    }
}

impl<T: Clone, N: Clone> RangeTraversal<N> for Args<T, N> {
    fn range_traverse<E>(
        self,
        f: &mut dyn FnMut(Range<N>) -> Result<Range<N>, E>,
    ) -> Result<Self, E> {
        let mapped: Result<Vec<_>, E> = self
            .0
            .into_iter()
            .map(|s| {
                let node = s.node.range_traverse(f)?;
                Ok(Spanned::new(node, s.span))
            })
            .collect();
        Ok(Args(mapped?))
    }
}

impl<N: Clone> TypeInline<N> for GArg<N> {
    fn type_inline(self, ctx: &Ctx<Tid, GTyp<N>>) -> Self {
        Arg {
            typ: Spanned::new(self.typ.node.type_inline(ctx), self.typ.span),
            ..self
        }
    }
}

impl<N: Clone> TypeInline<N> for GArgs<N> {
    fn type_inline(self, ctx: &Ctx<Tid, GTyp<N>>) -> Self {
        let mapped = self
            .0
            .into_iter()
            .map(|s| Spanned::new(s.node.type_inline(ctx), s.span))
            .collect();
        Args(mapped)
    }
}

impl<const L: usize, N, T> From<[Spanned<Arg<T, N>>; L]> for Args<T, N> {
    fn from(args: [Spanned<Arg<T, N>>; L]) -> Self {
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
        let Arg {
            qualifier,
            distribution,
            id,
            typ,
        } = self;
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
    N: Clone + Pretty<'a, BoxAllocator, ()> + 'a,
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
        allocator.intersperse(self.0.into_iter().map(|arg| arg.pretty(allocator)), ", ")
    }

    fn is_nil(&self) -> bool {
        self.0.is_empty()
    }
}

/// Display instance calls the pretty printer
impl<'a, T, N> fmt::Display for Args<T, N>
where
    T: Clone + Pretty<'a, BoxAllocator, ()> + 'a,
    N: Clone + Pretty<'a, BoxAllocator, ()> + 'a,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Args<T, N> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(140, f)
    }
}

#[test]
fn arg_traversal() {
    let arg = GArg::new(
        Qualifier::Instance,
        Distribution::Uniform,
        "a",
        Typ::fin(Range {
            start: Spanned::dummy(Size::Div(
                Box::new(Spanned::dummy(Size::Var(Tid::from("N")))),
                Box::new(Spanned::dummy(Size::Lit(2))),
            )),
            step: None,
            end: Some(Spanned::dummy(Size::Mul(
                Box::new(Spanned::dummy(Size::Var(Tid::from("N")))),
                Box::new(Spanned::dummy(Size::Lit(2))),
            ))),
        }),
    );
    let result = arg
        .traverse2(&mut |x| x.eval(&Ctx::singleton("N".into(), 2)))
        .unwrap();
    let expected = Arg::<Tid, usize>::new(
        Qualifier::Instance,
        Distribution::Uniform,
        "a",
        Typ::fin(Range {
            start: Spanned::dummy(1),
            step: None,
            end: Some(Spanned::dummy(4)),
        }),
    );
    assert_eq!(result.qualifier, expected.qualifier);
    assert_eq!(result.distribution, expected.distribution);
    assert_eq!(result.id, expected.id);
    assert_eq!(
        format!("{}", result.typ.node),
        format!("{}", expected.typ.node)
    );
}
