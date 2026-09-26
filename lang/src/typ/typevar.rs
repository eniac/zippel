use crate::ast::range::{Range, RangeTraversal};
use crate::ast::spanned::Spanned;
use crate::ast::Size;
use crate::id::{Tid, TidSubst};
use crate::typ::kind::Kind;
use share::traversal::ToTraversal1;
use share::Ctx;
use std::fmt;

/// A type variable with an associated kind, parameterized by size type N.
/// The `id` carries its own source span so error reports can point at the
/// typevar name without needing a separate span parameter.
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub struct TypeVar<N> {
    /// The type variable's name, together with the source span it was declared at.
    pub id: Spanned<Tid>,
    /// The kind constraining what this variable may be instantiated with.
    pub kind: Kind<N>,
}

/// Symbolically-sized type variable
pub type UTypeVar = TypeVar<Size>;
/// Concretely-sized type variable
pub type CTypeVar = TypeVar<usize>;

impl<N> TypeVar<N> {
    /// Builds a type variable from a name and a kind, attaching a dummy span.
    ///
    /// Use this for typevars synthesized by the compiler; parsed typevars keep the real span
    /// recorded by the parser.
    pub fn new(id: &Tid, kind: &Kind<N>) -> Self
    where
        N: Clone,
    {
        TypeVar {
            id: Spanned::dummy(id.clone()),
            kind: kind.clone(),
        }
    }
}

/// A collection of type variables, parameterized by size type N
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub struct TypeVars<N>(pub Vec<Spanned<TypeVar<N>>>);

/// Symbolically-sized type variables
pub type UTypeVars = TypeVars<Size>;
/// Concretely-sized type variables
pub type CTypeVars = TypeVars<usize>;

impl<N> TypeVars<N> {
    /// Drops the type variable named `id`, if present.
    ///
    /// Used when a size or base type variable becomes bound and must no longer be
    /// quantified over.
    pub fn remove(&mut self, id: &Tid) {
        self.0.retain(|tvar| &tvar.node.id.node != id);
    }

    /// Iterates over the type variables, discarding their spans.
    pub fn iter(&self) -> impl Iterator<Item = &TypeVar<N>> {
        self.0.iter().map(|s| &s.node)
    }

    /// Collects the names of the type variables, in declaration order.
    pub fn ids(&self) -> Vec<Tid> {
        self.0
            .iter()
            .map(|tvar| tvar.node.id.node.clone())
            .collect()
    }

    /// Returns `true` if a type variable named `id` is declared here.
    pub fn contains(&self, id: &Tid) -> bool {
        self.0.iter().any(|tvar| &tvar.node.id.node == id)
    }
    /// Builds the kind context `kctx` for these type variables.
    ///
    /// This is how a declaration's quantifier list becomes the `Ctx<Tid, Kind<N>>` threaded
    /// through inference and through `ATyp::from_ctyp`.
    pub fn to_ctx(&self) -> Ctx<Tid, Kind<N>>
    where
        N: Clone,
    {
        self.0
            .iter()
            .map(|tvar| (tvar.node.id.node.clone(), tvar.node.kind.clone()))
            .collect()
    }
}

impl<N> IntoIterator for TypeVars<N> {
    type Item = Spanned<TypeVar<N>>;
    type IntoIter = std::vec::IntoIter<Spanned<TypeVar<N>>>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<N> FromIterator<Spanned<TypeVar<N>>> for TypeVars<N> {
    fn from_iter<I: IntoIterator<Item = Spanned<TypeVar<N>>>>(iter: I) -> Self {
        TypeVars(iter.into_iter().collect())
    }
}

impl<N, const L: usize> From<[Spanned<TypeVar<N>>; L]> for TypeVars<N> {
    fn from(arr: [Spanned<TypeVar<N>>; L]) -> Self {
        TypeVars(arr.into_iter().collect())
    }
}

impl<N> TidSubst for TypeVar<N> {
    fn tid_subst(&mut self, from: &Tid, to: &Tid) {
        if &self.id.node == from {
            self.id.node = to.clone();
        }
    }
}

impl<N> TidSubst for TypeVars<N> {
    fn tid_subst(&mut self, from: &Tid, to: &Tid) {
        self.0
            .iter_mut()
            .for_each(|tvar| tvar.node.tid_subst(from, to));
    }
}

/// Traversal over the size parameter N
impl<N: Clone> ToTraversal1<N> for TypeVar<N> {
    type Output<Z> = TypeVar<Z>;
    fn traverse1<Z: Clone, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<TypeVar<Z>, E> {
        Ok(TypeVar {
            id: self.id,
            kind: self.kind.traverse1(f)?,
        })
    }
}

/// Traversal over the size parameter N
impl<N: Clone> ToTraversal1<N> for TypeVars<N> {
    type Output<Z> = TypeVars<Z>;
    fn traverse1<Z: Clone, E>(
        self,
        f: &mut dyn FnMut(N) -> Result<Z, E>,
    ) -> Result<TypeVars<Z>, E> {
        let mapped: Result<Vec<_>, E> = self
            .0
            .into_iter()
            .map(|s| {
                let node = s.node.traverse1(f)?;
                Ok(Spanned::new(node, s.span))
            })
            .collect();
        Ok(TypeVars(mapped?))
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
        let mapped: Result<Vec<_>, E> = self
            .0
            .into_iter()
            .map(|s| {
                let node = s.node.range_traverse(f)?;
                Ok(Spanned::new(node, s.span))
            })
            .collect();
        Ok(TypeVars(mapped?))
    }
}

/// `id: kind`
impl<N: fmt::Display> fmt::Display for TypeVar<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.id.node, self.kind)
    }
}

impl<N: fmt::Display> fmt::Display for TypeVars<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        crate::display::sep(f, &self.0, ", ")
    }
}
