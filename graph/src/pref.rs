use crate::{GOp, HOp, Op, Ref, mk};
use backend::op::HasOpFactory;
use lang::id::Tid;
use lang::typ::{CKind, Qualifier};
use lang::{ast::CArg, id::Vid, typ::Distribution};
use petgraph::graph::NodeIndex;
use share::{BoxAllocator, Ctx, DocAllocator, DocBuilder, Pretty};

use backend::{ATyp, Value};
use std::fmt;

/// A reference to a node in the graph, with all associated metadata
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct PRef {
    pub reference: Ref,
    pub index: usize,
    pub typ: ATyp,
    pub qualifier: Qualifier,
    pub distribution: Distribution,
    pub from_transcript: bool,
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
            reference: Ref::Node(node),
            index,
            typ,
            qualifier,
            distribution,
            from_transcript: false,
        }
    }
    pub fn from_var(
        v: Vid,
        node: NodeIndex,
        typ: ATyp,
        index: usize,
        qualifier: Qualifier,
        distribution: Distribution,
    ) -> Self {
        PRef {
            reference: Ref::Var(v, node),
            index,
            typ,
            qualifier,
            distribution,
            from_transcript: false,
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
        }
    }
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
        match self.reference {
            Ref::Node(node) => node,
            Ref::Var(_, node) => node,
        }
    }
    pub fn var(&self) -> Option<Vid> {
        match &self.reference {
            Ref::Node(_) => None,
            Ref::Var(id, _) => Some(id.clone()),
        }
    }
    pub fn has_var(&self, v: &Vid) -> bool {
        self.var() == Some(v.clone())
    }
    pub fn is_var(&self) -> bool {
        self.var().is_some()
    }
    pub fn into_op<C: HasOpFactory>(&self) -> HOp<C> {
        if self.typ.size() > 1 {
            mk::<C>(GOp::Ram(
                mk::<C>(GOp::Ref(self.reference.clone(), self.typ.clone())),
                mk::<C>(Op::Value(Value::Index(self.index))),
            ))
        } else {
            mk::<C>(GOp::Ref(self.reference.clone(), self.typ.clone()))
        }
    }

    pub fn with_index(&self, index: usize) -> Self {
        PRef {
            reference: self.reference.clone(),
            index: self.index + index,
            typ: self.typ.clone(),
            qualifier: self.qualifier.clone(),
            distribution: self.distribution.clone(),
            from_transcript: self.from_transcript,
        }
    }

    pub fn verbose(&self) -> String {
        if self.typ.size() > 1 && self.distribution.is_uniform() {
            format!(
                "{} uniform {}[{}]: {}",
                self.qualifier, self.reference, self.index, self.typ
            )
        } else if self.typ.size() > 1 && self.distribution.is_uniform_nz() {
            format!(
                "{} uniform* {}[{}]: {}",
                self.qualifier, self.reference, self.index, self.typ
            )
        } else if self.typ.size() > 1 {
            format!(
                "{} {}[{}]: {}",
                self.qualifier, self.reference, self.index, self.typ
            )
        } else if self.distribution.is_uniform() {
            format!(
                "{} uniform {}: {}",
                self.qualifier, self.reference, self.typ
            )
        } else if self.distribution.is_uniform_nz() {
            format!(
                "{} uniform* {}: {}",
                self.qualifier, self.reference, self.typ
            )
        } else {
            format!("{} {}: {}", self.qualifier, self.reference, self.typ)
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
        self.reference.pretty(allocator)
        //allocator.text(self.verbose())
    }

    fn is_nil(&self) -> bool {
        false
    }
}
