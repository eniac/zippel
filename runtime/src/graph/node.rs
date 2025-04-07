use lang::ast::{CSig, BinOp};
use lang::typ::CTyp;
use lang::id::Tid;
use share::traversal::ToTraversal1;

use crate::graph::{Op, Operand};
use crate::graph::Principal;
use crate::typ::RTyp;
use std::fmt;

/// A node in the DAG
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Node<A> {
    /// Entry in the graph, annotated with a function or protocol signature
    Inp(CSig),
    /// A side relation that must hold on input arguments for a function
    Pre(CSig),
    /// Operation node
    Op(Op<RTyp>, CTyp, A)
}

/// Node annotated with a principal
pub type PNode = Node<Principal>;

impl PNode {
    pub fn inp(sig: CSig) -> Self {
        Node::Inp(sig)
    }

    pub fn pre(sig: CSig) -> Self {
        Node::Pre(sig)
    }

    pub fn set_principal(&mut self, ann: Principal) {
        match self {
            Node::Op(_, _, a) => *a = ann,
            _ => panic!("UncaughtError: Failed to assign principal {} to node {}", ann, self)
        }
    }
}

impl<A: fmt::Display> fmt::Display for Node<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Node::Inp(sig) => write!(f, "{}", sig),
            Node::Pre(sig) => write!(f, "Pre({}, {}, {})", sig.name, sig.typevars, sig.args),
            Node::Op(op, typ, ann) =>
                write!(f, "{} : {} @ {}", op, typ, ann)
        }
    }
}

impl<N> ToTraversal1<N> for Node<N> {
    type Output<Z> = Node<Z>;
    fn traverse1<Z, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Node<Z>, E> {
        match self {
            Node::Inp(sig) => Ok(Node::Inp(sig)),
            Node::Pre(sig) => Ok(Node::Pre(sig)),
            Node::Op(op, typ, ann) => {
                let ann = f(ann)?;
                Ok(Node::Op(op, typ, ann))
            }
        }
    }
}

