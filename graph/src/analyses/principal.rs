use crate::{Op, Node, Dag, UDag, Dep};
use petgraph::{
    graph::{EdgeReference, NodeIndex},
    visit::EdgeRef,
    Graph,
    Direction,
};
use lang::id::Vid;
use lang::typ::Qualifier;
use lang::ast::{BinOp, CArg};
use share::{Ctx, Pretty, BoxAllocator, DocAllocator, DocBuilder};
use backend::ArkConfig;
use std::fmt;

/// Assign a principal to graph nodes
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash)]
pub enum Principal {
    Verifier,
    Prover,
    Any
}

impl fmt::Display for Principal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Principal::Verifier => write!(f, "Verifier"),
            Principal::Prover => write!(f, "Prover"),
            Principal::Any => write!(f, "Any"),
        }
    }
}

impl From<Qualifier> for Principal {
    fn from(q: Qualifier) -> Self {
        match q {
            Qualifier::Public => Principal::Verifier,
            Qualifier::Private => Principal::Prover,
        }
    }
}

/// Pretty-printer for Principals
impl<'a, D, A> Pretty<'a, D, A> for Principal
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.text(format!("{}", self))
    }

    fn is_nil(&self) -> bool {
        false
    }
}
