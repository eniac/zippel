use lang::ast::BinOp;
use lang::id::Vid;
use lang::typ::Nothing;
use share::traversal::ToTraversal2;

use crate::{Ref, PRef, GOp};
use backend::{ATyp, ArkConfig};
use std::fmt;

/// A node in the DAG
#[derive(PartialEq, Eq, Clone)]
pub enum Node<C: ArkConfig, A> {
    /// Entry in the graph, annotated with a function or protocol signature
    Inp(Vid, Vec<PRef>),
    /// Specification relation, annotated with a function or protocol signature
    Rel(Vid, Vec<PRef>),
    /// A transcript transaction
    Transcr(GOp<C>, A),
    /// Operation node
    Op(GOp<C>, A),
}

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
    pub fn is_relation(&self) -> bool {
        match self {
            Node::Rel(_, _) => true,
            _ => false,
        }
    }

    pub fn is_verifier_check(&self) -> bool {
        match self {
            Node::Op(GOp::Check(_), _) => true,
            Node::Transcr(GOp::Check(_), _) => true,
            _ => false,
        }
    }

    pub fn name(&self) -> Option<&Vid> {
        match self {
            Node::Inp(name, _) => Some(name),
            Node::Rel(name, _) => Some(name),
            _ => None,
        }
    }

    pub fn is_transcript(&self) -> bool {
        matches!(self, Node::Transcr(_, _))
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

    pub fn args(&self) -> Option<Vec<PRef>> {
        match self {
            Node::Inp(_, sig) => Some(sig.clone()),
            Node::Rel(_, sig) => Some(sig.clone()),
            _ => None,
        }
    }
}

impl<C: ArkConfig> Node<C, Nothing> {
    pub fn inp(f: Vid, sig: Vec<PRef>) -> Self {
        Node::Inp(f, sig)
    }
    pub fn rel(f: Vid, sig: Vec<PRef>) -> Self {
        Node::Rel(f, sig)
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
    pub fn challenge(typ: &ATyp, non_zero: bool) -> Self {
        Node::Transcr(GOp::Challenge(typ.clone(), non_zero), Nothing)
    }
    pub fn random(typ: &ATyp, non_zero: bool) -> Self {
        Node::Op(GOp::Random(typ.clone(), non_zero), Nothing)
    }
    pub fn transcr(op: &GOp<C>) -> Self {
        Node::Transcr(op.clone(), Nothing)
    }
    pub fn check(op: &GOp<C>) -> Self {
        Node::Op(GOp::check(op.clone()), Nothing)
    }
    pub fn ret(op: &GOp<C>) -> Self {
        Node::Op(op.clone(), Nothing)
    }

    pub fn with_annotation<M>(&self, ann: M) -> Node<C, M> {
        match self {
            Node::Op(op, _) => Node::Op(op.clone(), ann),
            Node::Transcr(op, _) => Node::Transcr(op.clone(), ann),
            Node::Inp(fid, sig) => Node::Inp(fid.clone(), sig.clone()),
            Node::Rel(fid, sig) => Node::Rel(fid.clone(), sig.clone()),
        }
    }

    pub fn is_var(&self) -> bool {
        matches!(self, Node::Op(GOp::Ref(Ref::Var(_, _), _), _))
    }
}

impl<C: ArkConfig, A: fmt::Display> fmt::Display for Node<C, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Node::Inp(fid, sig) => {
                write!(f, "Impl {} (", fid)?;
                let v= sig.first().unwrap();
                write!(f, "{}", v.verbose())?;
                for r in sig.iter().skip(1) {
                    write!(f, ", {}", r.verbose())?;
                }
                write!(f, ")")
            },
            Node::Rel(fid, sig) => {
                write!(f, "Spec {} (", fid)?;
                let v= sig.first().unwrap();
                write!(f, "{}", v.verbose())?;
                for r in sig.iter().skip(1) {
                    write!(f, ", {}", r.verbose())?;
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
            Node::Rel(fid, sig) => Ok(Node::Rel(fid, sig)),
            Node::Transcr(op, ann) => Ok(Node::Transcr(op, f(ann)?)),
            Node::Op(op, ann) => Ok(Node::Op(op, f(ann)?)),
        }
    }
}

