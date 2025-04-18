use lang::ast::{BinOp, CSig};
use lang::id::{Fid, Vid};
use lang::typ::{Qualifier, Nothing};
use share::Ctx;
use share::traversal::ToTraversal2;

use crate::Op;
use backend::{ATyp, ArkConfig};
use std::fmt;

/// A node in the DAG
#[derive(PartialEq, Eq, Clone)]
pub enum Node<C: ArkConfig, A> {
    /// Entry in the graph, annotated with a function or protocol signature
    Inp(Fid, Ctx<Vid, (Qualifier, ATyp)>),
    /// A transcript transaction
    Transcr(Op<C>, A),
    /// Operation node
    Op(Op<C>, A),
}

/// A node in the DAG with no annotations
pub type UNode<C> = Node<C, Nothing>;

impl<C: ArkConfig, N> Node<C, N> {
    pub fn is_op(&self) -> bool {
        match self {
            Node::Op(_, _) => true,
            Node::Transcr(_, _) => true,
            _ => false,
        }
    }
    pub fn is_input(&self) -> bool {
        match self {
            Node::Inp(_, _) => true,
            _ => false,
        }
    }
    pub fn set_transcript(&mut self) where N: Clone {
        match &self {
            Node::Op(op, ann) => *self = Node::Transcr(op.clone(), ann.clone()),
            _ => {}
        }
    }

    pub fn set_annotation(&mut self, ann: N) {
        match self {
            Node::Op(_, a) => *a = ann,
            Node::Transcr(_, a) => *a = ann,
            _ => {}
        }
    }
}

impl<C: ArkConfig> Node<C, Nothing> {
    pub fn inp(f: Fid, sig: Ctx<Vid, (Qualifier, ATyp)>) -> Self {
        Node::Inp(f, sig)
    }
    pub fn coef(op: &Op<C>) -> Self {
        Node::Op(Op::coef(op.clone()), Nothing)
    }
    pub fn eval(op: &Op<C>) -> Self {
        Node::Op(Op::eval(op.clone()), Nothing)
    }
    pub fn bin(op: BinOp, a: &Op<C>, b: &Op<C>, typ: &ATyp) -> Self {
        Node::Op(Op::bin(op, a.clone(), b.clone(), typ.clone()), Nothing)
    }
    pub fn challenge(typ: &ATyp) -> Self {
        Node::Transcr(Op::challenge(typ.clone()), Nothing)
    }
    pub fn random(typ: &ATyp) -> Self {
        Node::Op(Op::random(typ.clone()), Nothing)
    }
    pub fn transcr(op: &Op<C>) -> Self {
        Node::Transcr(op.clone(), Nothing)
    }
    pub fn assert(op: &Op<C>) -> Self {
        Node::Op(Op::check(op.clone()), Nothing)
    }
    pub fn verify(op: &Op<C>) -> Self {
        Node::Transcr(Op::check(op.clone()), Nothing)
    }
    pub fn ret(op: &Op<C>) -> Self {
        Node::Op(op.clone(), Nothing)
    }
}

impl<C: ArkConfig, A: fmt::Display> fmt::Display for Node<C, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Node::Inp(fid, sig) => {
                write!(f, "{} (", fid)?;
                let (v, (q, t)) = sig.first().unwrap();
                write!(f, "{} {}: {}", q, v, t)?;
                for (vid, (qual, typ)) in sig.iter().skip(1) {
                    write!(f, ", {} {}: {}", qual, vid, typ)?;
                }
                write!(f, ")")
            },
            Node::Op(op, ann)
            | Node::Transcr(op, ann) => {
                let ann = ann.to_string();
                if ann.is_empty() {
                    return write!(f, "{}", op);
                } else {
                    return write!(f, "{} @ {}", op, ann);
                }
            },
        }
    }
}

impl<C: ArkConfig, N> ToTraversal2<N> for Node<C, N> {
    type Output<Z> = Node<C, Z>;
    fn traverse2<Z, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Self::Output<Z>, E> {
        match self {
            Node::Inp(fid, sig) => Ok(Node::Inp(fid, sig)),
            Node::Transcr(op, ann) => Ok(Node::Transcr(op, f(ann)?)),
            Node::Op(op, ann) => Ok(Node::Op(op, f(ann)?)),
        }
    }
}

