//! Namespace for sentinel allocation shared across Ideal builders.

use std::collections::HashMap;
use std::marker::PhantomData;

use backend::op::HasOpFactory;
use backend::{ATyp, ArkConfig};
use lang::typ::Qualifier;
use petgraph::graph::NodeIndex;

use crate::Var;

/// Prefix stamped on every variable name minted by the Gröbner-basis lowering.
///
/// It cannot collide with a source-level `Vid`, so any name carrying it is
/// known to be compiler-generated (division witnesses, sentinels, auxiliary
/// polynomial variables) rather than user-written.
pub const GB_GENERATED_NAME_PREFIX: &str = "__zippel::gb::";

/// Namespace for sentinel allocation shared across Ideal builders.
#[derive(Clone)]
pub struct IdealNamespace<C: ArkConfig> {
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
    /// Creates an empty namespace whose sentinel indices count down from
    /// `usize::MAX`, keeping them disjoint from the `petgraph` indices of real
    /// `TransClos` nodes, which count up from zero.
    pub fn new() -> Self {
        Self {
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
