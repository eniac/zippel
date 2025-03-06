use lang::exp::{CExp, BinOp};
use lang::typ::CTyp;
use lang::module::CSig;
use lang::id::{Fid, Vid, Tid, TidTraversal};
use lang::typ::range::{CRange, RangeTraversal};
use share::{Traversal, BoxAllocator, Pretty, DocAllocator, DocBuilder};
use share::traversal::ToTraversal1;

use crate::principal::Principal;
use std::fmt;

/// Represents a scope, either by function call or iteration
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Scope {
    Sig(CSig),
    Iter(usize)
}

/// Represents a series of Scopes
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Scopes(pub Vec<Scope>);

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct ScopedVar(pub Scopes, pub Vid);

impl Scope {
    pub fn sig(sig: &CSig) -> Self {
        Scope::Sig(sig.clone())
    }

    pub fn iter(i: usize) -> Self {
        Scope::Iter(i)
    }
}

impl Scopes {
    pub fn new() -> Self {
        Scopes(Vec::new())
    }

    pub fn var(&self, v: &Vid) -> ScopedVar {
        ScopedVar(self.clone(), v.clone())
    }
    pub fn push(&mut self, scope: Scope) {
        self.0.push(scope)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    pub fn iter(&self) -> std::slice::Iter<Scope> {
        self.0.iter()
    }
}

impl ScopedVar {
    pub fn new(scopes: Scopes, vid: Vid) -> Self {
        ScopedVar(scopes, vid)
    }

    pub fn singleton(sig: CSig, vid: Vid) -> Self {
        ScopedVar(Scopes::from([Scope::Sig(sig)]), vid)
    }
}
impl IntoIterator for Scopes {
    type Item = Scope;
    type IntoIter = std::vec::IntoIter<Scope>;

    fn into_iter(self) -> Self::IntoIter {
        let Scopes(scopes) = self;
        scopes.into_iter()
    }
}

impl FromIterator<Scope> for Scopes {
    fn from_iter<I: IntoIterator<Item = Scope>>(iter: I) -> Self {
        Scopes(iter.into_iter().collect())
    }
}

impl<const N: usize> From<[Scope; N]> for Scopes {
    fn from(scopes: [Scope; N]) -> Self {
        Scopes(scopes.to_vec())
    }
}

impl TidTraversal for Scope {
    fn tid_traverse<E>(self, f: &mut dyn FnMut(Tid) -> Result<Tid, E>) -> Result<Self, E> {
        match self {
            Scope::Sig(sig) => Ok(Scope::Sig(sig.tid_traverse(f)?)),
            Scope::Iter(i) => Ok(Scope::Iter(i))
        }
    }
}

impl TidTraversal for Scopes {
    fn tid_traverse<E>(self, f: &mut dyn FnMut(Tid) -> Result<Tid, E>) -> Result<Self, E> {
        self.into_iter().map(|scope| scope.tid_traverse(f)).collect::<Result<Vec<Scope>, E>>().map(Scopes)
    }
}

impl RangeTraversal<usize> for Scope {
    fn range_traverse<E>(self, f: &mut dyn FnMut(CRange) -> Result<CRange, E>) -> Result<Self, E> {
        match self {
            Scope::Sig(sig) => Ok(Scope::Sig(sig.range_traverse(f)?)),
            Scope::Iter(i) => Ok(Scope::Iter(i))
        }
    }
}

impl RangeTraversal<usize> for Scopes {
    fn range_traverse<E>(self, f: &mut dyn FnMut(CRange) -> Result<CRange, E>) -> Result<Self, E> {
        self.into_iter().map(|scope| scope.range_traverse(f)).collect::<Result<Vec<Scope>, E>>().map(Scopes)
    }
}

impl fmt::Display for Scope {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Scope::Sig(sig) => write!(f, "{}", sig),
            Scope::Iter(i) => write!(f, "{}", i)
        }
    }
}

impl fmt::Display for Scopes {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut iter = self.0.iter();
        if let Some(scope) = iter.next() {
            write!(f, "{}", scope)?;
            for scope in iter {
                write!(f, "::{}", scope)?;
            }
        }
        Ok(())
    }
}

impl fmt::Display for ScopedVar {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let ScopedVar(scopes, vid) = self;
        write!(f, "{}::{}", scopes, vid)
    }
}
