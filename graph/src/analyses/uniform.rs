use crate::{GOp, Op, Ref, Node, Dag};
use petgraph::{
    graph::NodeIndex,
    visit::EdgeRef,
    Direction,
};
use std::fmt;
use share::{Set, Ctx};
use lang::typ::Qualifier;
use crate::PRef;
use backend::{ATyp, ArkConfig};

/// Which nodes are uniform random distributions
/// Sometimes this is allowed under constraints, for example:
/// a: F, b: F and uniform random means (a*b) is uniform Random
/// iff a != 0, and b != 0 and a \independent b
#[derive(Clone)]
pub struct Uniformity {
    pub non_zero: Set<PRef>,
    pub additive_deps: Ctx<PRef, Set<PRef>>,
    pub multiplicative_deps: Ctx<PRef, Set<PRef>>,
    pub uniform: Set<PRef>,
    pub vars: Set<PRef>,
}

impl Uniformity {

    pub fn find_ref(&self, r: &Ref) -> Option<PRef> {
        self.vars.iter().find(|v| v.reference == *r).cloned()
    }
}
