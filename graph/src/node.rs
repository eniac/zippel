use lang::ast::BinOp;
use lang::id::{Fid, Vid};
use lang::typ::{Qualifier, Nothing};
use share::Ctx;
use share::traversal::ToTraversal2;

use crate::{Ref, GOp};
use backend::{ATyp, ArkConfig};
use std::fmt;

/// A node in the DAG
#[derive(PartialEq, Eq, Clone)]
pub enum Node<C: ArkConfig, A> {
    /// Entry in the graph, annotated with a function or protocol signature
    Inp(Fid, Ctx<Vid, (Qualifier, ATyp)>),
    /// A transcript transaction
    Transcr(GOp<C>, A),
    /// Operation node
    Op(GOp<C>, A),
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

    pub fn into_op(self) -> GOp<C> {
        match self {
            Node::Op(op, _) => op,
            Node::Transcr(op, _) => op,
            _ => panic!("Cannot convert input to operation"),
        }
    }

    pub fn into_ann(self) -> N {
        match self {
            Node::Op(_, ann) => ann,
            Node::Transcr(_, ann) => ann,
            _ => panic!("Cannot convert input to annotation"),
        }
    }
}

impl<C: ArkConfig> Node<C, Nothing> {
    pub fn inp(f: Fid, sig: Ctx<Vid, (Qualifier, ATyp)>) -> Self {
        Node::Inp(f, sig)
    }
    pub fn coef(op: &GOp<C>) -> Self {
        Node::Op(GOp::coef(op.clone()), Nothing)
    }
    pub fn eval(op: &GOp<C>) -> Self {
        Node::Op(GOp::eval(op.clone()), Nothing)
    }
    pub fn bin(op: BinOp, a: &GOp<C>, b: &GOp<C>, typ: &ATyp) -> Self {
        Node::Op(GOp::bin(op, a.clone(), b.clone(), typ.clone()), Nothing)
    }
    pub fn challenge(typ: &ATyp) -> Self {
        Node::Transcr(GOp::challenge(typ.clone()), Nothing)
    }
    pub fn random(typ: &ATyp) -> Self {
        Node::Op(GOp::random(typ.clone()), Nothing)
    }
    pub fn generator(typ: &ATyp) -> Self {
        Node::Op(GOp::generator(typ.clone()), Nothing)
    }
    pub fn transcr(op: &GOp<C>) -> Self {
        Node::Transcr(op.clone(), Nothing)
    }
    pub fn assert(op: &GOp<C>) -> Self {
        Node::Op(GOp::check(op.clone()), Nothing)
    }
    pub fn verify(op: &GOp<C>) -> Self {
        Node::Transcr(GOp::check(op.clone()), Nothing)
    }
    pub fn ret(op: &GOp<C>) -> Self {
        Node::Op(op.clone(), Nothing)
    }

    pub fn with_annotation<M>(&self, ann: M) -> Node<C, M> {
        match self {
            Node::Op(op, _) => Node::Op(op.clone(), ann),
            Node::Transcr(op, _) => Node::Transcr(op.clone(), ann),
            Node::Inp(fid, sig) => Node::Inp(fid.clone(), sig.clone())
        }
    }

    pub fn is_underscore(&self) -> bool {
        matches!(self, Node::Op(GOp::Ref(Ref::Node(_), _), _))
    }

    pub fn is_var(&self) -> bool {
        matches!(self, Node::Op(GOp::Ref(Ref::Var(_, _), _), _))
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

