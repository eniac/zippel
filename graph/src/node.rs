use lang::ast::BinOp;
use lang::id::Vid;
use lang::typ::{Distribution, Nothing, Qualifier};
use share::traversal::ToTraversal2;

use backend::op::{GOp, HOp, HasOpFactory, Op, Ref, mk};
use backend::{ATyp, ArkConfig};
use petgraph::graph::NodeIndex;
use std::fmt;

/// Whether an `Arg` node belongs to a protocol implementation (`Input`)
/// or to its specification relation (`Relation`).
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum ArgKind {
    Input,
    Relation,
    /// Verifier-only argument materialised from a transcript (proof) value.
    TranscriptInput,
}

/// A node in the DAG
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Node<C: ArkConfig, A> {
    /// Entry in the graph: protocol/function name marker.
    /// Phase B: arguments are split out into per-arg `Node::Arg` nodes,
    /// each connected to this marker by a data edge.
    Inp(Vid),
    /// Specification relation marker. Same shape as `Inp`.
    Rel(Vid),
    /// A single typed argument to an Inp or Rel.
    Arg(Vid, ATyp, Qualifier, Distribution, ArgKind),
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
        matches!(self, Node::Inp(_))
    }
    pub fn is_relation(&self) -> bool {
        matches!(self, Node::Rel(_))
    }

    pub fn is_arg(&self) -> bool {
        matches!(self, Node::Arg(_, _, _, _, _))
    }

    pub fn is_input_arg(&self) -> bool {
        matches!(
            self,
            Node::Arg(_, _, _, _, ArgKind::Input) | Node::Arg(_, _, _, _, ArgKind::TranscriptInput)
        )
    }

    pub fn is_relation_arg(&self) -> bool {
        matches!(self, Node::Arg(_, _, _, _, ArgKind::Relation))
    }

    pub fn arg_kind(&self) -> Option<ArgKind> {
        match self {
            Node::Arg(_, _, _, _, k) => Some(*k),
            _ => None,
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
            Node::Inp(name) => Some(name),
            Node::Rel(name) => Some(name),
            Node::Arg(name, _, _, _, _) => Some(name),
            _ => None,
        }
    }

    pub fn references(&self) -> Vec<Ref> {
        match self {
            Node::Op(op, _) => op.references().clone(),
            Node::Transcr(op, _) => op.references().clone(),
            Node::Inp(_) | Node::Rel(_) | Node::Arg(_, _, _, _, _) => Vec::new(),
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
        if let Node::Op(op, ann) = &self {
            *self = Node::Transcr(op.clone(), ann.clone());
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

    pub fn add_annotation<M>(&self, ann: M) -> Node<C, (N, M)>
    where
        N: Clone,
    {
        match self {
            Node::Op(op, n) => Node::Op(op.clone(), (n.clone(), ann)),
            Node::Transcr(op, n) => Node::Transcr(op.clone(), (n.clone(), ann)),
            Node::Inp(fid) => Node::Inp(fid.clone()),
            Node::Rel(fid) => Node::Rel(fid.clone()),
            Node::Arg(v, t, q, d, k) => Node::Arg(v.clone(), t.clone(), *q, *d, *k),
        }
    }

    pub fn drop_annotation(&self) -> Node<C, Nothing> {
        match self {
            Node::Op(op, _) => Node::Op(op.clone(), Nothing),
            Node::Transcr(op, _) => Node::Transcr(op.clone(), Nothing),
            Node::Inp(fid) => Node::Inp(fid.clone()),
            Node::Rel(fid) => Node::Rel(fid.clone()),
            Node::Arg(v, t, q, d, k) => Node::Arg(v.clone(), t.clone(), *q, *d, *k),
        }
    }

    pub fn typ(&self) -> Option<ATyp> {
        match self {
            Node::Op(op, _) => Some(op.typ()),
            Node::Transcr(op, _) => Some(op.typ()),
            Node::Arg(_, t, _, _, _) => Some(t.clone()),
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
            Node::Inp(fid) => Node::Inp(fid.clone()),
            Node::Rel(fid) => Node::Rel(fid.clone()),
            Node::Arg(v, t, q, d, k) => Node::Arg(v.clone(), t.clone(), *q, *d, *k),
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
    pub fn inp(f: Vid) -> Self {
        Node::Inp(f)
    }
    pub fn rel(f: Vid) -> Self {
        Node::Rel(f)
    }
    pub fn arg(name: Vid, typ: ATyp, qual: Qualifier, dist: Distribution, kind: ArgKind) -> Self {
        Node::Arg(name, typ, qual, dist, kind)
    }

    pub fn with_annotation<M>(&self, ann: M) -> Node<C, M> {
        match self {
            Node::Op(op, _) => Node::Op(op.clone(), ann),
            Node::Transcr(op, _) => Node::Transcr(op.clone(), ann),
            Node::Inp(fid) => Node::Inp(fid.clone()),
            Node::Rel(fid) => Node::Rel(fid.clone()),
            Node::Arg(v, t, q, d, k) => Node::Arg(v.clone(), t.clone(), *q, *d, *k),
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
    pub fn interpolate(points: &GOp<C>, evals: &GOp<C>) -> Self {
        Node::Op(
            mk::<C>(GOp::interpolate(points.clone(), evals.clone())),
            Nothing,
        )
    }
    pub fn ifft(op: &GOp<C>) -> Self {
        Node::Op(mk::<C>(GOp::ifft(op.clone())), Nothing)
    }
    pub fn fft(op: &GOp<C>) -> Self {
        Node::Op(mk::<C>(GOp::fft(op.clone())), Nothing)
    }
    pub fn evaluate_grid(p: &GOp<C>) -> Self {
        Node::Op(mk::<C>(GOp::evaluate_grid(p.clone())), Nothing)
    }
    pub fn evaluate(p: &GOp<C>, x: &GOp<C>) -> Self {
        Node::Op(mk::<C>(GOp::evaluate(p.clone(), x.clone())), Nothing)
    }
    pub fn mle(op: &GOp<C>) -> Self {
        Node::Op(mk::<C>(GOp::mle(op.clone())), Nothing)
    }
    pub fn proj(op: &GOp<C>, field: &str, typ: &ATyp) -> Self {
        Node::Op(
            mk::<C>(GOp::proj(op.clone(), field.to_string(), typ.clone())),
            Nothing,
        )
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
}

impl<C: ArkConfig, A: fmt::Display> fmt::Display for Node<C, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Node::Inp(fid) => write!(f, "Impl {}", fid),
            Node::Rel(fid) => write!(f, "Spec {}", fid),
            Node::Arg(name, typ, qual, dist, kind) => {
                let prefix = match kind {
                    ArgKind::Input => "arg",
                    ArgKind::Relation => "rel-arg",
                    ArgKind::TranscriptInput => "transcript-arg",
                };
                if dist.is_uniform() {
                    write!(f, "{} {} uniform {}: {}", prefix, qual, name, typ)
                } else if dist.is_uniform_nz() {
                    write!(f, "{} {} uniform* {}: {}", prefix, qual, name, typ)
                } else {
                    write!(f, "{} {} {}: {}", prefix, qual, name, typ)
                }
            }
            Node::Op(op, ann) | Node::Transcr(op, ann) => {
                let ann = ann.to_string();
                if ann.is_empty() {
                    write!(f, "{}", **op)
                } else {
                    write!(f, "{} @ {}", **op, ann)
                }
            }
        }
    }
}

impl<C: ArkConfig, N> ToTraversal2<N> for Node<C, N> {
    type Output<Z> = Node<C, Z>;
    fn traverse2<Z, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Self::Output<Z>, E> {
        match self {
            Node::Inp(fid) => Ok(Node::Inp(fid)),
            Node::Rel(fid) => Ok(Node::Rel(fid)),
            Node::Arg(v, t, q, d, k) => Ok(Node::Arg(v, t, q, d, k)),
            Node::Transcr(op, ann) => Ok(Node::Transcr(op, f(ann)?)),
            Node::Op(op, ann) => Ok(Node::Op(op, f(ann)?)),
        }
    }
}
