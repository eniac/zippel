use crate::Ref;
use lang::id::Tid;
use lang::typ::{CKind, Qualifier};
use lang::{ast::CArg, id::Vid, typ::Distribution};
use petgraph::graph::NodeIndex;
use share::{BoxAllocator, Ctx, DocAllocator, DocBuilder, Pretty};

use backend::ATyp;
use std::fmt;

/// A reference to a node in the graph, with all associated metadata.
///
/// Issue #83 / Phase B: `Ref` is now a thin newtype around `NodeIndex`.
/// The variable name (when applicable) is stored on `PRef` directly via
/// the optional `name` field, populated at construction time from the
/// owning `Node::Arg` (or transcript variable). It is metadata only —
/// `PRef` equality is still ultimately driven by `reference`/`index`.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct PRef {
    pub reference: Ref,
    pub index: usize,
    pub typ: ATyp,
    pub qualifier: Qualifier,
    pub distribution: Distribution,
    pub from_transcript: bool,
    /// Source-level variable name, if any. For `Node::Arg` PRefs this
    /// is the argument's `Vid`; for transcript-source PRefs it is the
    /// log-variable name.
    pub name: Option<Vid>,
}

impl PRef {
    pub fn new(
        reference: Ref,
        typ: ATyp,
        index: usize,
        qualifier: Qualifier,
        distribution: Distribution,
    ) -> Self {
        PRef {
            reference,
            index,
            typ,
            qualifier,
            distribution,
            from_transcript: false,
            name: None,
        }
    }

    pub fn new_named(
        reference: Ref,
        name: Vid,
        typ: ATyp,
        index: usize,
        qualifier: Qualifier,
        distribution: Distribution,
    ) -> Self {
        PRef {
            reference,
            index,
            typ,
            qualifier,
            distribution,
            from_transcript: false,
            name: Some(name),
        }
    }

    pub fn from_node(
        node: NodeIndex,
        typ: ATyp,
        index: usize,
        qualifier: Qualifier,
        distribution: Distribution,
    ) -> Self {
        PRef {
            reference: Ref(node),
            index,
            typ,
            qualifier,
            distribution,
            from_transcript: false,
            name: None,
        }
    }

    /// Construct a PRef referencing the `Arg` node at `node`, carrying
    /// the variable name `v` as metadata.
    pub fn from_var(
        v: Vid,
        node: NodeIndex,
        typ: ATyp,
        index: usize,
        qualifier: Qualifier,
        distribution: Distribution,
    ) -> Self {
        PRef {
            reference: Ref(node),
            index,
            typ,
            qualifier,
            distribution,
            from_transcript: false,
            name: Some(v),
        }
    }

    pub fn from_ref(
        reference: Ref,
        typ: ATyp,
        qualifier: Qualifier,
        distribution: Distribution,
    ) -> Self {
        PRef {
            reference,
            index: 0,
            typ,
            qualifier,
            distribution,
            from_transcript: false,
            name: None,
        }
    }

    /// Construct a `PRef` for an arg expected to live at the `Arg` node `node`.
    pub fn from_arg(arg: &CArg, node: NodeIndex, kctx: &Ctx<Tid, CKind>) -> Option<Self> {
        let atyp = ATyp::from_ctyp(&arg.typ, kctx)?;
        Some(PRef::from_var(
            arg.id.clone(),
            node,
            atyp,
            0,
            arg.qualifier,
            arg.distribution,
        ))
    }

    pub fn is_public(&self) -> bool {
        self.qualifier.is_public()
    }
    pub fn is_private(&self) -> bool {
        self.qualifier.is_private()
    }
    pub fn is_local(&self) -> bool {
        self.qualifier.is_local()
    }
    pub fn is_uniform(&self) -> bool {
        match self.distribution {
            Distribution::Uniform | Distribution::UniformNonZero => true,
            Distribution::Nonuniform => false,
        }
    }
    pub fn is_uniform_nz(&self) -> bool {
        self.distribution == Distribution::UniformNonZero
    }

    pub fn is_transcript_source(&self) -> bool {
        self.from_transcript
    }

    pub fn mark_transcript_source(mut self) -> Self {
        self.from_transcript = true;
        self
    }

    pub fn with_transcript_source(mut self, flag: bool) -> Self {
        self.from_transcript = flag;
        self
    }

    pub fn node(&self) -> NodeIndex {
        self.reference.node()
    }

    /// Source-level variable name, if known (set at construction).
    pub fn name(&self) -> Option<&Vid> {
        self.name.as_ref()
    }

    pub fn with_index(&self, index: usize) -> Self {
        PRef {
            reference: self.reference,
            index: self.index + index,
            typ: self.typ.clone(),
            qualifier: self.qualifier,
            distribution: self.distribution,
            from_transcript: self.from_transcript,
            name: self.name.clone(),
        }
    }

    pub fn verbose(&self) -> String {
        let label: String = match &self.name {
            Some(v) => format!("{}", v),
            None => format!("{}", self.reference),
        };
        if self.typ.physical_len() > 1 && self.distribution.is_uniform() {
            format!(
                "{} uniform {}[{}]: {}",
                self.qualifier, label, self.index, self.typ
            )
        } else if self.typ.physical_len() > 1 && self.distribution.is_uniform_nz() {
            format!(
                "{} uniform* {}[{}]: {}",
                self.qualifier, label, self.index, self.typ
            )
        } else if self.typ.physical_len() > 1 {
            format!("{} {}[{}]: {}", self.qualifier, label, self.index, self.typ)
        } else if self.distribution.is_uniform() {
            format!("{} uniform {}: {}", self.qualifier, label, self.typ)
        } else if self.distribution.is_uniform_nz() {
            format!("{} uniform* {}: {}", self.qualifier, label, self.typ)
        } else {
            format!("{} {}: {}", self.qualifier, label, self.typ)
        }
    }
}

impl fmt::Display for PRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <PRef as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

impl<'a, D, A> Pretty<'a, D, A> for PRef
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        match self.name {
            Some(v) => allocator.text(format!("{}", v)),
            None => self.reference.pretty(allocator),
        }
    }

    fn is_nil(&self) -> bool {
        false
    }
}
