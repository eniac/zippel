use lang::ast::BinOp;
use lang::id::Vid;
use lang::typ::Nothing;
use share::traversal::ToTraversal2;

use crate::PRef;
use backend::op::{GOp, HOp, HasOpFactory, Op, Ref, mk};
use backend::{ATyp, ArkConfig};
use petgraph::graph::NodeIndex;
use std::fmt;

/// A node in the DAG
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Node<C: ArkConfig, A> {
    /// Entry in the graph, annotated with a function or protocol signature
    Inp(Vid, Vec<PRef>),
    /// Specification relation, annotated with a function or protocol signature
    Rel(Vid, Vec<PRef>),
    /// A transcript transaction
    Transcr(HOp<C>, A),
    /// Operation node
    Op(HOp<C>, A),
}

impl<C: ArkConfig, N> Node<C, N> {
    pub fn is_op(&self) -> bool {
        self.op().is_some()
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

    pub fn op(&self) -> Option<&HOp<C>> {
        match self {
            Node::Op(op, _) => Some(op),
            Node::Transcr(op, _) => Some(op),
            _ => None,
        }
    }

    pub fn is_verifier_check(&self) -> bool {
        match self {
            Node::Op(op, _) | Node::Transcr(op, _) => matches!(&**op, Op::Check(_)),
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

    pub fn references(&self) -> Vec<Ref> {
        match self {
            Node::Op(op, _) => op.references().clone(),
            Node::Transcr(op, _) => op.references().clone(),
            Node::Inp(_, args) => args.iter().map(|pr| pr.reference.clone()).collect(),
            Node::Rel(_, args) => args.iter().map(|pr| pr.reference.clone()).collect(),
        }
    }

    pub fn is_transcript(&self) -> bool {
        matches!(self, Node::Transcr(_, _))
    }

    pub fn is_challenge(&self) -> bool {
        match self {
            Node::Transcr(op, _) => matches!(&**op, Op::Challenge(_, _)),
            _ => false,
        }
    }

    pub fn is_proof(&self) -> bool {
        self.is_transcript() && !self.is_challenge()
    }

    pub fn set_transcript(&mut self)
    where
        N: Clone,
    {
        match &self {
            Node::Op(op, ann) => *self = Node::Transcr(op.clone(), ann.clone()),
            _ => {}
        }
    }

    pub fn into_op(self) -> HOp<C> {
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

    pub fn add_annotation<M>(&self, ann: M) -> Node<C, (N, M)>
    where
        N: Clone,
    {
        match self {
            Node::Op(op, n) => Node::Op(op.clone(), (n.clone(), ann)),
            Node::Transcr(op, n) => Node::Transcr(op.clone(), (n.clone(), ann)),
            Node::Inp(fid, sig) => Node::Inp(fid.clone(), sig.clone()),
            Node::Rel(fid, sig) => Node::Rel(fid.clone(), sig.clone()),
        }
    }

    pub fn drop_annotation(&self) -> Node<C, Nothing> {
        match self {
            Node::Op(op, _) => Node::Op(op.clone(), Nothing),
            Node::Transcr(op, _) => Node::Transcr(op.clone(), Nothing),
            Node::Inp(fid, sig) => Node::Inp(fid.clone(), sig.clone()),
            Node::Rel(fid, sig) => Node::Rel(fid.clone(), sig.clone()),
        }
    }

    pub fn typ(&self) -> Option<ATyp> {
        match self {
            Node::Op(op, _) => Some(op.typ()),
            Node::Transcr(op, _) => Some(op.typ()),
            _ => None,
        }
    }
}

/// Methods requiring `HasOpFactory` (for creating new hash-consed operations)
impl<C: HasOpFactory, N> Node<C, N> {
    pub fn map_node_indices<F: Fn(NodeIndex) -> NodeIndex>(&self, f: &F) -> Node<C, N>
    where
        N: Clone,
    {
        match self {
            Node::Op(op, ann) => Node::Op(mk::<C>(op.map_node_indices(f)), ann.clone()),
            Node::Transcr(op, ann) => Node::Transcr(mk::<C>(op.map_node_indices(f)), ann.clone()),
            Node::Inp(fid, sig) => Node::Inp(fid.clone(), sig.clone()),
            Node::Rel(fid, sig) => Node::Rel(fid.clone(), sig.clone()),
        }
    }

    pub fn map_refs<F: Fn(Ref) -> Ref>(&self, f: &F) -> Node<C, N>
    where
        N: Clone,
    {
        match self {
            Node::Op(op, ann) => Node::Op(mk::<C>(op.map_refs(f)), ann.clone()),
            Node::Transcr(op, ann) => Node::Transcr(mk::<C>(op.map_refs(f)), ann.clone()),
            _ => self.clone(),
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

    pub fn with_annotation<M>(&self, ann: M) -> Node<C, M> {
        match self {
            Node::Op(op, _) => Node::Op(op.clone(), ann),
            Node::Transcr(op, _) => Node::Transcr(op.clone(), ann),
            Node::Inp(fid, sig) => Node::Inp(fid.clone(), sig.clone()),
            Node::Rel(fid, sig) => Node::Rel(fid.clone(), sig.clone()),
        }
    }
}

/// Constructors requiring `HasOpFactory` (for creating new hash-consed operations)
impl<C: HasOpFactory> Node<C, Nothing> {
    pub fn poly(op: &GOp<C>) -> Self {
        Node::Op(mk::<C>(GOp::poly(op.clone())), Nothing)
    }
    pub fn coef(op: &GOp<C>) -> Self {
        Node::Op(mk::<C>(GOp::coef(op.clone())), Nothing)
    }
    pub fn interpolate(points: Option<&GOp<C>>, evals: &GOp<C>) -> Self {
        Node::Op(
            mk::<C>(GOp::interpolate(points.cloned(), evals.clone())),
            Nothing,
        )
    }
    pub fn fft(op: &GOp<C>) -> Self {
        Node::Op(mk::<C>(GOp::fft(op.clone())), Nothing)
    }
    pub fn mle(op: &GOp<C>) -> Self {
        Node::Op(mk::<C>(GOp::mle(op.clone())), Nothing)
    }
    pub fn marginalize(op: &GOp<C>) -> Self {
        Node::Op(mk::<C>(GOp::marginalize(op.clone())), Nothing)
    }
    pub fn proj(op: &GOp<C>, field: &str, typ: &ATyp) -> Self {
        Node::Op(mk::<C>(GOp::proj(op.clone(), field.to_string(), typ.clone())), Nothing)
    }
    pub fn bin(op: BinOp, a: &GOp<C>, b: &GOp<C>, typ: &ATyp) -> Self {
        Node::Op(
            mk::<C>(GOp::bin(op, a.clone(), b.clone(), typ.clone())),
            Nothing,
        )
    }
    pub fn challenge(typ: &ATyp, non_zero: bool) -> Self {
        Node::Transcr(mk::<C>(Op::Challenge(typ.clone(), non_zero)), Nothing)
    }
    pub fn random(typ: &ATyp, non_zero: bool) -> Self {
        Node::Op(mk::<C>(Op::Random(typ.clone(), non_zero)), Nothing)
    }
    pub fn transcr(op: &GOp<C>) -> Self {
        Node::Transcr(mk::<C>(op.clone()), Nothing)
    }
    pub fn check(op: &GOp<C>) -> Self {
        Node::Op(mk::<C>(GOp::check(op.clone())), Nothing)
    }
    pub fn ret(op: &GOp<C>) -> Self {
        Node::Op(mk::<C>(op.clone()), Nothing)
    }

    pub fn is_var(&self) -> bool {
        match self {
            Node::Op(op, _) => matches!(&**op, Op::Ref(Ref::Var(_, _), _)),
            _ => false,
        }
    }
}

impl<C: ArkConfig, A: fmt::Display> fmt::Display for Node<C, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Node::Inp(fid, sig) => {
                write!(f, "Impl {} (", fid)?;
                let v = sig.first().unwrap();
                write!(f, "{}", v.verbose())?;
                for r in sig.iter().skip(1) {
                    write!(f, ", {}", r.verbose())?;
                }
                write!(f, ")")
            }
            Node::Rel(fid, sig) => {
                write!(f, "Spec {} (", fid)?;
                let v = sig.first().unwrap();
                write!(f, "{}", v.verbose())?;
                for r in sig.iter().skip(1) {
                    write!(f, ", {}", r.verbose())?;
                }
                write!(f, ")")
            }
            Node::Op(op, ann) | Node::Transcr(op, ann) => {
                let ann = ann.to_string();
                if ann.is_empty() {
                    return write!(f, "{}", &**op);
                } else {
                    return write!(f, "{} @ {}", &**op, ann);
                }
            }
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
