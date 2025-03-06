use lang::exp::{CExp, BinOp};
use lang::typ::CTyp;
use lang::module::CSig;
use lang::id::{Fid, Vid, Tid, TidSubst};
use lang::typ::range::{CRange, RangeTraversal};
use share::{Traversal, BoxAllocator, Pretty, DocAllocator, DocBuilder};
use share::traversal::ToTraversal1;

use crate::principal::Principal;
use std::fmt;

/// Represents a scope by calling a function with signature [CSig].
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Scope(pub Vec<CSig>);

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct ScopedVar {
    pub scope: Scope,
    pub var: Vid
}

impl Scope {
    pub fn new() -> Self {
        Scopes(Vec::new())
    }

    pub fn singleton(sig: CSig) -> Self {
        Scopes(vec![sig])
    }

    pub fn push(&mut self, sig: CSig) {
        self.0.push(sig)
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
    pub fn new(scope: Scope, vid: &Vid) -> Self {
        ScopedVar { scope, var: vid.clone() }
    }

    pub fn singleton(sig: CSig, vid: &Vid) -> Self {
        ScopedVar::new(Scope::singleton(sig), vid)
    }
}

impl IntoIterator for Scope {
    type Item = CSig;
    type IntoIter = std::vec::IntoIter<CSig>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl FromIterator<CSig> for Scope {
    fn from_iter<I: IntoIterator<Item=CSig>>(iter: I) -> Self {
        Scope(iter.into_iter().collect())
    }
}

impl<const N: usize> From<[CSig; N]> for Scope {
    fn from(scopes: [CSig; N]) -> Self {
        Scope(scopes.to_vec())
    }
}

impl TidSubst for Scope {
    fn tid_subst(&mut self, from: Tid, to: Tid) {
        self.0.iter_mut().for_each(|sig| sig.tid_subst(from, to))
    }
}

impl RangeTraversal<usize> for Scope {
    fn range_traverse<E>(self, f: &mut dyn FnMut(CRange) -> Result<CRange, E>) -> Result<Self, E> {
        self.into_iter().map(|sig| sig.range_traverse(f)).collect::<Result<Vec<CSig>, E>>().map(Scopes)
    }
}

impl fmt::Display for Scope {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut iter = self.0.iter();
        if let Some(sig) = iter.next() {
            write!(f, "{}", sig)?;
            for sig in iter {
                write!(f, "::{}", sig)?;
            }
        }
        Ok(())
    }
}

impl fmt::Display for ScopedVar {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}::{}", self.scope, scope.var)
    }
}
