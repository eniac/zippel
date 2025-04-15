use lang::ast::{BinOp, CSig};
use lang::typ::Nothing;
use share::traversal::ToTraversal2;

use crate::{Op, Principal};
use backend::{ATyp, ArkConfig};
use std::fmt;

/// A node in the DAG
#[derive(PartialEq, Eq, Clone)]
pub enum Node<C: ArkConfig, A> {
    /// Entry in the graph, annotated with a function or protocol signature
    Inp(CSig),
    /// A return value
    Return(Op<C>),
    /// Operation node
    Op(Op<C>, Principal, A),
}

/// A node in the DAG with no annotations
pub type UNode<C> = Node<C, Nothing>;

impl<C: ArkConfig> Node<C, Nothing> {
    pub fn inp(sig: CSig) -> Self {
        Node::Inp(sig)
    }

    pub fn coef(op: &Op<C>) -> Self {
        Node::Op(Op::coef(op.clone()), Principal::Any, Nothing)
    }
    pub fn eval(op: &Op<C>) -> Self {
        Node::Op(Op::eval(op.clone()), Principal::Any, Nothing)
    }
    pub fn bin(op: BinOp, a: &Op<C>, b: &Op<C>, typ: &ATyp) -> Self {
        Node::Op(Op::bin(op, a.clone(), b.clone(), typ.clone()), Principal::Any, Nothing)
    }
    pub fn challenge(typ: &ATyp) -> Self {
        Node::Op(Op::challenge(typ.clone()), Principal::Verifier, Nothing)
    }
    pub fn random(typ: &ATyp) -> Self {
        Node::Op(Op::random(typ.clone()), Principal::Any, Nothing)
    }
    pub fn hash(op: &Op<C>) -> Self {
        Node::Op(Op::hash(op.clone()), Principal::Verifier, Nothing)
    }
    pub fn assert(op: &Op<C>) -> Self {
        Node::Op(Op::check(op.clone()), Principal::Prover, Nothing)
    }
    pub fn verify(op: &Op<C>) -> Self {
        Node::Op(Op::check(op.clone()), Principal::Verifier, Nothing)
    }
    pub fn ret(op: &Op<C>) -> Self {
        Node::Return(op.clone())
    }
}

impl<C: ArkConfig, A: fmt::Display> fmt::Display for Node<C, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Node::Inp(sig) => write!(f, "{}", sig),
            Node::Return(op) => write!(f, "ret {}", op),
            Node::Op(op, principal, ann) => {
                let ann = ann.to_string();
                if ann.is_empty() {
                    return write!(f, "{} @ {}", op, principal);
                } else {
                    return write!(f, "{} @ {}, {}", op, principal, ann);
                }
            },
        }
    }
}

impl<C: ArkConfig, N> ToTraversal2<N> for Node<C, N> {
    type Output<Z> = Node<C, Z>;
    fn traverse2<Z, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Self::Output<Z>, E> {
        match self {
            Node::Inp(sig) => Ok(Node::Inp(sig)),
            Node::Return(op) => Ok(Node::Return(op)),
            Node::Op(op, principal, ann) => Ok(Node::Op(op, principal, f(ann)?)),
        }
    }
}

