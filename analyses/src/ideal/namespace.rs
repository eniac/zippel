//! Namespace for division-witness and sentinel allocation shared across
//! Ideal builders.

use std::collections::HashMap;
use std::marker::PhantomData;

use backend::op::HasOpFactory;
use backend::{ATyp, ArkConfig};
use graph::Ref;
use lang::typ::Qualifier;
use petgraph::graph::NodeIndex;
use share::Ctx;

use crate::Var;

pub const GB_GENERATED_NAME_PREFIX: &str = "__zippel::gb::";

/// Canonical polynomial shape used when comparing division witness operands.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct CanonPolyTyp {
    pub num_vars: usize,
    pub max_degree: usize,
}

/// Canonical operand-content key for source-level polynomial division witnesses.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct DivWitnessKey {
    pub dividend_typ: CanonPolyTyp,
    pub divisor_typ: CanonPolyTyp,
    pub dividend_slots: Vec<String>,
    pub divisor_slots: Vec<String>,
}

/// Namespace for division-witness and sentinel allocation shared across
/// Ideal builders.
#[derive(Clone)]
pub struct IdealNamespace<C: ArkConfig> {
    pub div_wit: Ctx<DivWitnessKey, (Var, Var)>,
    /// Shared leading-coefficient inverse vars for arg polynomials.
    /// Keyed by arg `Ref`, stable across `build()` calls so prover,
    /// relation, and verifier clauses share the same `lead_inv` var.
    pub arg_inv: HashMap<Ref, Var>,
    sentinel_counter: usize,
    name_counters: HashMap<String, usize>,
    _phantom: PhantomData<C>,
}

impl<C: ArkConfig + HasOpFactory> Default for IdealNamespace<C> {
    fn default() -> Self {
        Self::new()
    }
}

impl<C: ArkConfig + HasOpFactory> IdealNamespace<C> {
    pub fn new() -> Self {
        Self {
            div_wit: Ctx::new(),
            arg_inv: HashMap::new(),
            sentinel_counter: usize::MAX,
            name_counters: HashMap::new(),
            _phantom: PhantomData,
        }
    }

    /// Allocate a fresh sentinel Var with a stable unique NodeIndex.
    pub fn sentinel_var(&mut self, name: &str, typ: ATyp) -> Var {
        let idx = NodeIndex::new(self.sentinel_counter);
        self.sentinel_counter -= 1;
        Var::from_var(name, idx, typ, Qualifier::Local)
    }

    /// Return a unique name for the given key by appending a per-key counter.
    pub fn next_name(&mut self, key: &str) -> String {
        let counter = self.name_counters.entry(key.to_string()).or_insert(0);
        let name = format!("{}{}::{}", GB_GENERATED_NAME_PREFIX, key, counter);
        *counter += 1;
        name
    }
}
