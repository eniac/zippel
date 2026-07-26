use crate::id::{Tid, TidSubst};
use crate::typ::kind::Kind;
use crate::typ::range::{Range, RangeTraversal};
use crate::typ::Size;
use share::traversal::ToTraversal1;
use share::{BoxAllocator, Ctx, DocAllocator, DocBuilder, Pretty};
use std::fmt;

/// A type variable with an associated kind, parameterized by size type N
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub struct TypeVar<N> {
    pub id: Tid,
    pub kind: Kind<N>,
}

/// Symbolically-sized type variable
pub type UTypeVar = TypeVar<Size>;
/// Concretely-sized type variable
pub type CTypeVar = TypeVar<usize>;

impl<N> TypeVar<N> {
    pub fn new(id: &Tid, kind: &Kind<N>) -> Self
    where
        N: Clone,
    {
        TypeVar {
            id: id.clone(),
            kind: kind.clone(),
        }
    }
    pub fn new_str(id: &str, kind: Kind<N>) -> Self {
        TypeVar {
            id: Tid::new(id),
            kind,
        }
    }
}

/// A collection of type variables, parameterized by size type N
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub struct TypeVars<N>(pub Vec<TypeVar<N>>);

/// Symbolically-sized type variables
pub type UTypeVars = TypeVars<Size>;
/// Concretely-sized type variables
pub type CTypeVars = TypeVars<usize>;

impl<N> TypeVars<N> {
    pub fn remove(&mut self, id: &Tid) {
        self.0.retain(|tvar| &tvar.id != id);
    }

    pub fn iter(&self) -> std::slice::Iter<'_, TypeVar<N>> {
        self.0.iter()
    }

    pub fn ids(&self) -> Vec<Tid> {
        self.0.iter().map(|tvar| tvar.id.clone()).collect()
    }

    pub fn contains(&self, id: &Tid) -> bool {
        self.0.iter().any(|tvar| &tvar.id == id)
    }
    pub fn to_ctx(&self) -> Ctx<Tid, Kind<N>>
    where
        N: Clone,
    {
        self.0
            .iter()
            .map(|tvar| (tvar.id.clone(), tvar.kind.clone()))
            .collect()
    }
}

impl<N> IntoIterator for TypeVars<N> {
    type Item = TypeVar<N>;
    type IntoIter = std::vec::IntoIter<TypeVar<N>>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<N> FromIterator<TypeVar<N>> for TypeVars<N> {
    fn from_iter<I: IntoIterator<Item = TypeVar<N>>>(iter: I) -> Self {
        TypeVars(iter.into_iter().collect())
    }
}

impl<N, const L: usize> From<[TypeVar<N>; L]> for TypeVars<N> {
    fn from(arr: [TypeVar<N>; L]) -> Self {
        TypeVars(arr.into_iter().collect())
    }
}

impl<N> TidSubst for TypeVar<N> {
    fn tid_subst(&mut self, from: &Tid, to: &Tid) {
        if &self.id == from {
            self.id = to.clone();
        }
    }
}

impl<N> TidSubst for TypeVars<N> {
    fn tid_subst(&mut self, from: &Tid, to: &Tid) {
        self.0.iter_mut().for_each(|tvar| tvar.tid_subst(from, to));
    }
}

/// Traversal over the size parameter N
impl<N> ToTraversal1<N> for TypeVar<N> {
    type Output<Z> = TypeVar<Z>;
    fn traverse1<Z: Clone, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<TypeVar<Z>, E> {
        Ok(TypeVar {
            id: self.id,
            kind: self.kind.traverse1(f)?,
        })
    }
}

/// Traversal over the size parameter N
impl<N> ToTraversal1<N> for TypeVars<N> {
    type Output<Z> = TypeVars<Z>;
    fn traverse1<Z: Clone, E>(
        self,
        f: &mut dyn FnMut(N) -> Result<Z, E>,
    ) -> Result<TypeVars<Z>, E> {
        Ok(TypeVars(
            self.0
                .into_iter()
                .map(|tv| tv.traverse1(f))
                .collect::<Result<_, _>>()?,
        ))
    }
}

/// Range traversal for TypeVar
impl<N: Clone> RangeTraversal<N> for TypeVar<N> {
    fn range_traverse<E>(
        self,
        f: &mut dyn FnMut(Range<N>) -> Result<Range<N>, E>,
    ) -> Result<Self, E> {
        Ok(TypeVar {
            id: self.id,
            kind: self.kind.range_traverse(f)?,
        })
    }
}

/// Range traversal for TypeVars
impl<N: Clone> RangeTraversal<N> for TypeVars<N> {
    fn range_traverse<E>(
        self,
        f: &mut dyn FnMut(Range<N>) -> Result<Range<N>, E>,
    ) -> Result<Self, E> {
        Ok(TypeVars(
            self.0
                .into_iter()
                .map(|tv| tv.range_traverse(f))
                .collect::<Result<_, _>>()?,
        ))
    }
}

/// Pretty printer instance
impl<'a, D, A, N> Pretty<'a, D, A> for TypeVar<N>
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    N: Pretty<'a, D, A> + Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.concat([
            self.id.pretty(allocator),
            allocator.text(": "),
            self.kind.pretty(allocator),
        ])
    }

    fn is_nil(&self) -> bool {
        false
    }
}

impl<'a, N: Pretty<'a, BoxAllocator, ()> + Clone + 'a> fmt::Display for TypeVar<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <TypeVar<N> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

impl<'a, D, A, N> Pretty<'a, D, A> for TypeVars<N>
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    N: Pretty<'a, D, A> + Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.intersperse(self.0.into_iter().map(|tvar| tvar.pretty(allocator)), ", ")
    }

    fn is_nil(&self) -> bool {
        self.0.is_empty()
    }
}

impl<'a, N: Pretty<'a, BoxAllocator, ()> + Clone + 'a> fmt::Display for TypeVars<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <TypeVars<N> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}
