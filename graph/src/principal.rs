use petgraph::graph::NodeIndex;
use lang::id::Vid;
use share::{Pretty, DocAllocator, BoxAllocator, DocBuilder};
use backend::ArkConfig;
use crate::{GOp, Op, Ref};
use lang::typ::Qualifier;
use crate::analyses::{Var, LexDegTerm};

use backend::{Value, ATyp};
use std::fmt;

/// Assign a principal to graph nodes
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash)]
pub enum Principal {
    Verifier,
    Prover,
    Any
}

impl fmt::Display for Principal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Principal::Verifier => write!(f, "Verifier"),
            Principal::Prover => write!(f, "Prover"),
            Principal::Any => write!(f, "Any"),
        }
    }
}

impl From<Qualifier> for Principal {
    fn from(q: Qualifier) -> Self {
        match q {
            Qualifier::Public => Principal::Verifier,
            Qualifier::Private => Principal::Prover,
        }
    }
}

/// Pretty-printer for Principals
impl<'a, D, A> Pretty<'a, D, A> for Principal
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.text(format!("{}", self))
    }

    fn is_nil(&self) -> bool {
        false
    }
}

/// A reference to a node in the graph, with all associated metadata
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct PRef {
    pub reference: Ref,
    pub index: Option<usize>,
    pub typ: ATyp,
    pub principal: Principal,
}

impl PRef {
    pub fn new(reference: Ref, typ: ATyp, index: Option<usize>, principal: Principal) -> Self {
        PRef { reference, index, typ, principal }
    }
    pub fn node(node: NodeIndex, typ: ATyp, principal: Principal) -> Self {
        PRef { reference: Ref::Node(node), index: None, typ, principal }
    }
    pub fn var(v: Vid, typ: ATyp, principal: Principal) -> Self {
        PRef { reference: Ref::Var(v, NodeIndex::new(0)), index: None, typ, principal }
    }
    pub fn var_index(v: Vid, index: usize, typ: ATyp, principal: Principal) -> Self {
        PRef { reference: Ref::Var(v, NodeIndex::new(0)), index: Some(index), typ, principal }
    }
    pub fn node_index(node: NodeIndex, index: usize, typ: ATyp, principal: Principal) -> Self {
        PRef { reference: Ref::Node(node), index: Some(index), typ, principal }
    }

    pub fn is_prover(&self) -> bool {
        self.principal == Principal::Prover
    }
    pub fn is_verifier(&self) -> bool {
        self.principal == Principal::Verifier
    }
    pub fn is_any(&self) -> bool {
        self.principal == Principal::Any
    }
    pub fn into_op<C: ArkConfig>(&self) -> GOp<C> {
        match self.index {
            Some(i) => GOp::Ram(Box::new(GOp::Ref(self.reference.clone(), self.typ.clone())), Box::new(Op::Value(Value::Index(i)))),
            None => GOp::Ref(self.reference.clone(), self.typ.clone()),
        }
    }

    pub fn with_index(self, index: usize) -> Self {
        PRef { reference: self.reference, index: Some(index), typ: self.typ, principal: self.principal }
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
        match self.index {
            Some(i) if self.typ.is_vec() => allocator.text(format!("{}[{}]", self.reference, i)),
            Some(_) => allocator.text(format!("{}", self.reference)),
            None => allocator.text(format!("{}", self.reference)),
        }
    }

    fn is_nil(&self) -> bool {
        false
    }
}

impl Var for PRef {
    fn eliminate(&self) -> bool {
        matches!(self.principal, Principal::Any)
    }
}

/// A monomial term with [PRef] as the variable type
pub type LexTerm = LexDegTerm<PRef>;
