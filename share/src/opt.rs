use std::fmt;

use crate::pretty::{Pretty, DocAllocator, DocBuilder};
use crate::traversal::ToTraversal1;

/// Wrapper around options
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Opt<T>(Option<T>);

/// Pretty printer instance for Opt
impl<'a, D, A, T> Pretty<'a, D, A> for Opt<T>
where
    T: Clone + Pretty<'a, D, A>,
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        match self.0 {
            Some(v) => v.pretty(allocator),
            None => allocator.text("-"),
        }
    }

    fn is_nil(&self) -> bool {
        self.is_none()
    }
}

/// Display instance for Opt
impl<'a, T> fmt::Display for Opt<T>
where
    T: fmt::Display
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            Some(ref v) => write!(f, "{}", v),
            None => write!(f, "-"),
        }
    }
}

impl<T> ToTraversal1<T> for Opt<T> {
    type Output<Z> = Opt<Z>;
    fn traverse1<V, E>(self, f: &mut dyn FnMut(T) -> Result<V, E>) -> Result<Self::Output<V>, E> {
        match self.0 {
            Some(v) => f(v).map(Opt::some),
            None => Ok(Opt::none())
        }
    }
}

/// Special and wrapper methods for Ctx
impl<T> Opt<T> {
    pub fn none() -> Self {
        Opt(None)
    }

    pub fn some(t: T) -> Self {
        Opt(Some(t))
    }

    pub fn is_some(&self) -> bool {
        self.0.is_some()
    }

    pub fn is_none(&self) -> bool {
        self.0.is_none()
    }
}

/// From instance
impl<T> From<Option<T>> for Opt<T> {
    fn from(v: Option<T>) -> Self {
        Opt(v)
    }
}

impl<T> From<Opt<T>> for Option<T> {
    fn from(v: Opt<T>) -> Self {
        v.0
    }
}
