use petgraph::graph::NodeIndex;
use lang::{ast::CArg, id::Vid, typ::Distribution};
use share::{Ctx, Pretty, DocAllocator, BoxAllocator, DocBuilder};
use backend::ArkConfig;
use crate::{GOp, Op, Ref};
use lang::typ::{Kind, Qualifier};
use lang::id::Tid;
use crate::analyses::groebner::sparsepoly::{Var, LexDegTerm};

use backend::{Value, ATyp};
use std::fmt;

/// A reference to a node in the graph, with all associated metadata
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct PRef {
    pub reference: Ref,
    pub index: usize,
    pub typ: ATyp,
    pub qualifier: Qualifier,
    pub distribution: Distribution
}

impl PRef {
    pub fn new(reference: Ref, typ: ATyp, index: usize, qualifier: Qualifier, distribution: Distribution) -> Self {
        PRef { reference, index, typ, qualifier, distribution }
    }
    pub fn from_node(node: NodeIndex, typ: ATyp, index: usize, qualifier: Qualifier, distribution: Distribution) -> Self {
        PRef { reference: Ref::Node(node), index, typ, qualifier, distribution }
    }
    pub fn from_var(v: Vid, node: NodeIndex, typ: ATyp, index: usize, qualifier: Qualifier, distribution: Distribution) -> Self {
        PRef { reference: Ref::Var(v, node), index, typ, qualifier, distribution }
    }
    pub fn from_ref(reference: Ref, typ: ATyp, qualifier: Qualifier) -> Self {
        PRef { reference, index: 0, typ, qualifier, distribution: Distribution::default() }
    }
    pub fn from_arg(arg: &CArg, node: NodeIndex, kctx: &Ctx<Tid, Kind>) -> Option<Self> {
        let atyp = ATyp::from_ctyp(&arg.typ, kctx)?;
        Some(PRef::from_var(arg.id.clone(), node, atyp, 0, arg.qualifier, arg.distribution))
    }
    pub fn is_public(&self) -> bool {
        self.qualifier.is_public()
    }
    pub fn is_private(&self) -> bool {
        self.qualifier.is_private()
    }
    pub fn is_uniform(&self) -> bool {
        self.distribution == Distribution::Uniform
    }
    pub fn is_uniform_nz(&self) -> bool {
        self.distribution == Distribution::UniformNonZero
    }
 
    pub fn node(&self) -> NodeIndex {
        match self.reference {
            Ref::Node(node) => node,
            Ref::Var(_, node) => node,
        }
    }
    pub fn id(&self) -> Option<Vid> {
        match &self.reference {
            Ref::Node(_) => None,
            Ref::Var(id, _) => Some(id.clone()),
        }
    }
    pub fn into_op<C: ArkConfig>(&self) -> GOp<C> {
        if self.typ.size() > 1 {
            GOp::Ram(Box::new(GOp::Ref(self.reference.clone(), self.typ.clone())), Box::new(Op::Value(Value::Index(self.index))))
        } else {
            GOp::Ref(self.reference.clone(), self.typ.clone())
        }
    }

    pub fn with_index(self, index: usize) -> Self {
        PRef { reference: self.reference, index, typ: self.typ, qualifier: self.qualifier, distribution: self.distribution }
    }

    pub fn verbose(&self) -> String {
        if self.typ.size() > 1 && self.distribution.is_uniform() {
            format!("{} uniform {}[{}]: {}", self.qualifier, self.reference, self.index, self.typ)
        } else if self.typ.size() > 1 {
            format!("{} {}[{}]: {}", self.qualifier, self.reference, self.index, self.typ)
        } else if self.distribution.is_uniform() {
            format!("{} uniform {}: {}", self.qualifier, self.reference, self.typ)
        } else if self.distribution.is_uniform_nz() {
            format!("{} uniform* {}: {}", self.qualifier, self.reference, self.typ)
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
        allocator.text(self.verbose())
    }

    fn is_nil(&self) -> bool {
        false
    }
}

impl Var for PRef {
    fn eliminate(&self) -> bool {
        self.qualifier == Qualifier::Private && self.distribution == Distribution::Uniform
    }
}

/// A monomial term with [PRef] as the variable type
pub type LexTerm = LexDegTerm<PRef>;
