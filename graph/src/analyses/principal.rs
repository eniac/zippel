use crate::{Op, Node, Dag, UDag, Dep};
use petgraph::{
    graph::{EdgeReference, NodeIndex},
    visit::EdgeRef,
    Graph,
    Direction,
};
use lang::id::Vid;
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
