use lang::ast::CSig;
use share::traversal::ToTraversal2;

use crate::graph::{Op, Operand};
use crate::arkworks::ArkConfig;
use crate::graph::Principal;
use std::fmt;

/// A node in the DAG
#[derive(PartialEq, Eq, Clone)]
pub enum Node<C: ArkConfig, A> {
    /// Entry in the graph, annotated with a function or protocol signature
    Inp(CSig),
    /// A side relation that must hold on input arguments for a function
    Pre(CSig),
    /// Operation node
    Op(Op<C>, A)
}

/// Node annotated with a principal
pub type PNode<C> = Node<C, Principal>;

impl<C: ArkConfig> PNode<C> {
    pub fn inp(sig: CSig) -> Self {
        Node::Inp(sig)
    }

    pub fn pre(sig: CSig) -> Self {
        Node::Pre(sig)
    }

    pub fn set_principal(&mut self, ann: Principal) {
        match self {
            Node::Op(_, a) => *a = ann,
            _ => panic!("UncaughtError: Failed to assign principal {} to node {}", ann, self)
        }
    }

    pub fn coef(op: Operand<C>) -> Self {
        Node::Op(Op::coef(op), Principal::default())
    }
}

impl<C: ArkConfig, A: fmt::Display> fmt::Display for Node<C, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Node::Inp(sig) => write!(f, "{}", sig),
            Node::Pre(sig) => write!(f, "Pre({}, {}, {})", sig.name, sig.typevars, sig.args),
            Node::Op(op, ann) =>
                write!(f, "{} @ {}", op, ann)
        }
    }
}

impl<C: ArkConfig, N> ToTraversal2<N> for Node<C, N> {
    type Output<Z> = Node<C, Z>;
    fn traverse2<Z, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Self::Output<Z>, E> {
        match self {
            Node::Inp(sig) => Ok(Node::Inp(sig)),
            Node::Pre(sig) => Ok(Node::Pre(sig)),
            Node::Op(op, ann) => {
                let ann = f(ann)?;
                Ok(Node::Op(op, ann))
            }
        }
    }
}

