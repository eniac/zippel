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
    /// Argument supplied to the protocol implementation itself.
    Input,
    /// Argument supplied only to the specification relation.
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
    /// Returns `true` when this node carries a hash-consed operation, i.e. it is
    /// either an `Op` or a `Transcr` node rather than a marker or argument.
    pub fn is_op(&self) -> bool {
        self.op().is_some()
    }

    /// Returns `true` for the protocol/function entry marker node.
    pub fn is_input(&self) -> bool {
        matches!(self, Node::Inp(_))
    }
    /// Returns `true` for the specification relation marker node.
    pub fn is_relation(&self) -> bool {
        matches!(self, Node::Rel(_))
    }

    /// Returns `true` for any per-argument node, regardless of its `ArgKind`.
    pub fn is_arg(&self) -> bool {
        matches!(self, Node::Arg(_, _, _, _, _))
    }

    /// Returns `true` for arguments belonging to the implementation side, which
    /// includes verifier arguments reconstructed from the transcript.
    pub fn is_input_arg(&self) -> bool {
        matches!(
            self,
            Node::Arg(_, _, _, _, ArgKind::Input) | Node::Arg(_, _, _, _, ArgKind::TranscriptInput)
        )
    }

    /// Returns `true` for arguments belonging to the specification relation.
    pub fn is_relation_arg(&self) -> bool {
        matches!(self, Node::Arg(_, _, _, _, ArgKind::Relation))
    }

    /// Returns the argument flavour, or `None` when this is not an `Arg` node.
    pub fn arg_kind(&self) -> Option<ArgKind> {
        match self {
            Node::Arg(_, _, _, _, k) => Some(*k),
            _ => None,
        }
    }

    /// Borrows the hash-consed operation of an `Op` or `Transcr` node.
    ///
    /// Marker and argument nodes have no operation and yield `None`.
    pub fn op(&self) -> Option<&HOp<C>> {
        match self {
            Node::Op(op, _) => Some(op),
            Node::Transcr(op, _) => Some(op),
            _ => None,
        }
    }

    /// Returns `true` when this node is an `Op::Verify` check, i.e. one of the
    /// boolean results collected by `run_verifier`.
    pub fn is_verifier_check(&self) -> bool {
        match self {
            Node::Op(op, _) | Node::Transcr(op, _) => matches!(&**op, Op::Verify(_)),
            _ => false,
        }
    }

    /// Returns the `Vid` naming this marker or argument node.
    ///
    /// Operation and transcript nodes are unnamed and yield `None`.
    pub fn name(&self) -> Option<&Vid> {
        match self {
            Node::Inp(name) => Some(name),
            Node::Rel(name) => Some(name),
            Node::Arg(name, _, _, _, _) => Some(name),
            _ => None,
        }
    }

    /// Collects the `Ref` handles this node's operation reads from.
    ///
    /// Markers and arguments read nothing and return an empty vector.
    pub fn references(&self) -> Vec<Ref> {
        match self {
            Node::Op(op, _) => op.references().clone(),
            Node::Transcr(op, _) => op.references().clone(),
            Node::Inp(_) | Node::Rel(_) | Node::Arg(_, _, _, _, _) => Vec::new(),
        }
    }

    /// Returns `true` when this node is part of the transcript, i.e. either a
    /// verifier challenge or a prover-emitted proof value.
    pub fn is_transcript(&self) -> bool {
        matches!(self, Node::Transcr(_, _))
    }

    /// Returns `true` for transcript nodes holding an `Op::Challenge`, the
    /// values the verifier samples during Fiat-Shamir.
    pub fn is_challenge(&self) -> bool {
        match self {
            Node::Transcr(op, _) => matches!(&**op, Op::Challenge(_, _)),
            _ => false,
        }
    }

    /// Returns `true` for transcript nodes that are prover messages rather than
    /// challenges; these make up the proof certificate.
    pub fn is_proof(&self) -> bool {
        self.is_transcript() && !self.is_challenge()
    }

    /// Promotes an `Op` node in place to a `Transcr` node, keeping its operation
    /// and annotation, so that its value is sent over the transcript.
    ///
    /// Nodes that are not `Op` nodes are left untouched.
    pub fn set_transcript(&mut self)
    where
        N: Clone,
    {
        if let Node::Op(op, ann) = &self {
            *self = Node::Transcr(op.clone(), ann.clone());
        }
    }

    /// Consumes the node and returns its hash-consed operation.
    ///
    /// # Panics
    /// Panics on marker and argument nodes, which carry no operation.
    pub fn into_op(self) -> HOp<C> {
        match self {
            Node::Op(op, _) => op,
            Node::Transcr(op, _) => op,
            _ => panic!("Cannot convert input to operation"),
        }
    }

    /// Consumes the node and returns its analysis annotation.
    ///
    /// # Panics
    /// Panics on marker and argument nodes, which carry no annotation.
    pub fn into_ann(self) -> N {
        match self {
            Node::Op(_, ann) => ann,
            Node::Transcr(_, ann) => ann,
            _ => panic!("Cannot convert input to annotation"),
        }
    }

    /// Pairs the existing annotation with `ann`, producing a node annotated by
    /// the tuple so a later analysis can be layered onto an earlier one.
    ///
    /// Markers and arguments are rebuilt unchanged since they hold no annotation.
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

    /// Erases the analysis annotation, turning this node back into the shape
    /// used by an unanalyzed `UDag`.
    pub fn drop_annotation(&self) -> Node<C, Nothing> {
        match self {
            Node::Op(op, _) => Node::Op(op.clone(), Nothing),
            Node::Transcr(op, _) => Node::Transcr(op.clone(), Nothing),
            Node::Inp(fid) => Node::Inp(fid.clone()),
            Node::Rel(fid) => Node::Rel(fid.clone()),
            Node::Arg(v, t, q, d, k) => Node::Arg(v.clone(), t.clone(), *q, *d, *k),
        }
    }

    /// Returns the arkworks-level type this node produces.
    ///
    /// Operation and transcript nodes delegate to `Op::typ`, argument nodes
    /// return their declared type, and markers have no value hence `None`.
    ///
    /// # Panics
    /// Propagates the panics of `Op::typ`, which asserts the shape invariants of
    /// the operation's children.
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
    /// Rewrites every `NodeIndex` embedded in this node's operation through `f`,
    /// re-interning the result; used when a subgraph is copied into another `Dag`
    /// and indices are renumbered.
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

    /// Rewrites every `Ref` in this node's operation through `f`, re-interning the
    /// result. Nodes without an operation are cloned unchanged.
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
    /// Builds the entry marker node for the protocol or function named `f`.
    pub fn inp(f: Vid) -> Self {
        Node::Inp(f)
    }
    /// Builds the marker node for the specification relation named `f`.
    pub fn rel(f: Vid) -> Self {
        Node::Rel(f)
    }
    /// Builds a single typed argument node with its qualifier, distribution and
    /// argument flavour.
    pub fn arg(name: Vid, typ: ATyp, qual: Qualifier, dist: Distribution, kind: ArgKind) -> Self {
        Node::Arg(name, typ, qual, dist, kind)
    }

    /// Attaches `ann` to an unannotated node, the step that turns a `UDag` node
    /// into an analyzed one such as a `QDag` node.
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
    /// Builds a node lifting a coefficient `Vec` into a univariate polynomial.
    pub fn poly(op: &GOp<C>) -> Self {
        Node::Op(mk::<C>(GOp::poly(op.clone())), Nothing)
    }
    /// Builds a node extracting the coefficient `Vec` of a polynomial.
    pub fn coef(op: &GOp<C>) -> Self {
        Node::Op(mk::<C>(GOp::coef(op.clone())), Nothing)
    }
    /// Builds a node interpolating the polynomial through `evals` taken at `points`.
    pub fn interpolate(points: &GOp<C>, evals: &GOp<C>) -> Self {
        Node::Op(
            mk::<C>(GOp::interpolate(points.clone(), evals.clone())),
            Nothing,
        )
    }
    /// Builds a node performing an inverse `FFT`, i.e. evaluations to coefficients.
    pub fn ifft(op: &GOp<C>) -> Self {
        Node::Op(mk::<C>(GOp::ifft(op.clone())), Nothing)
    }
    /// Builds a node performing a forward `FFT`, i.e. coefficients to evaluations.
    pub fn fft(op: &GOp<C>) -> Self {
        Node::Op(mk::<C>(GOp::fft(op.clone())), Nothing)
    }
    /// Builds a node evaluating `p` over its whole implicit evaluation grid,
    /// producing every point at once rather than a single value.
    pub fn evaluate_grid(p: &GOp<C>) -> Self {
        Node::Op(mk::<C>(GOp::evaluate_grid(p.clone())), Nothing)
    }
    /// Builds a node evaluating polynomial `p` at the single point `x`.
    pub fn evaluate(p: &GOp<C>, x: &GOp<C>) -> Self {
        Node::Op(mk::<C>(GOp::evaluate(p.clone(), x.clone())), Nothing)
    }
    /// Builds a node lifting a `Vec` of evaluations into a multilinear extension.
    pub fn mle(op: &GOp<C>) -> Self {
        Node::Op(mk::<C>(GOp::mle(op.clone())), Nothing)
    }
    /// Builds a node projecting the record field `field`, whose type is `typ`,
    /// out of `op`.
    pub fn proj(op: &GOp<C>, field: &str, typ: &ATyp) -> Self {
        Node::Op(
            mk::<C>(GOp::proj(op.clone(), field.to_string(), typ.clone())),
            Nothing,
        )
    }
    /// Builds a node for the binary operation `op` on `a` and `b`, carrying the
    /// authoritative result type `typ` chosen by the lowering code.
    pub fn bin(op: BinOp, a: &GOp<C>, b: &GOp<C>, typ: &ATyp) -> Self {
        Node::Op(
            mk::<C>(GOp::bin(op, a.clone(), b.clone(), typ.clone())),
            Nothing,
        )
    }
    /// Builds a transcript node sampling a Fiat-Shamir challenge of type `typ`;
    /// `non_zero` requests a value rejected if it is zero.
    pub fn challenge(typ: &ATyp, non_zero: bool) -> Self {
        Node::Transcr(mk::<C>(Op::Challenge(typ.clone(), non_zero)), Nothing)
    }
    /// Builds a node sampling prover-local randomness of type `typ`; `non_zero`
    /// requests a value rejected if it is zero.
    pub fn random(typ: &ATyp, non_zero: bool) -> Self {
        Node::Op(mk::<C>(Op::Random(typ.clone(), non_zero)), Nothing)
    }
    /// Builds a transcript node emitting `op` as a prover message in the proof.
    pub fn transcr(op: &GOp<C>) -> Self {
        Node::Transcr(mk::<C>(op.clone()), Nothing)
    }
    /// Builds a node asserting that `op` holds, a prover-side consistency check.
    pub fn assert(op: &GOp<C>) -> Self {
        Node::Op(mk::<C>(GOp::assert(op.clone())), Nothing)
    }
    /// Builds a node for a verifier check on `op`; its boolean result is part of
    /// the vector returned by `run_verifier`.
    pub fn verify(op: &GOp<C>) -> Self {
        Node::Op(mk::<C>(GOp::verify(op.clone())), Nothing)
    }
    /// Builds a plain operation node returning the value of `op`, used for the
    /// result position of a function or protocol body.
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
