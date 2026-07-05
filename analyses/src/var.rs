use backend::op::Ref;
use graph::{Dag, Node};
use lang::typ::Distribution;
use lang::typ::Qualifier;
use petgraph::graph::NodeIndex;
use share::{BoxAllocator, DocAllocator, DocBuilder, Pretty};

use backend::{ATyp, ArkConfig, binomial};
use std::fmt;

/// A reference to a node in the graph, with all associated metadata.
///
/// `index` is a logical multi-dimensional path (e.g. `[1, 0]` for the first
/// element of the second row of a 2D array). It is built up by `with_slot` /
/// `with_index` / `collect_slots` as they recurse into composite types.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct Var {
    pub reference: Ref,
    pub index: Vec<usize>,
    pub typ: ATyp,
    pub qualifier: Qualifier,
    pub distribution: Distribution,
    /// Source-level variable name. For `Node::Arg` PRefs this is the
    /// argument's `Vid`; for transcript-source PRefs it is the log-variable
    /// name; for unnamed PRefs it is derived from the node index.
    pub name: String,
}

impl Var {
    pub fn new_named(
        reference: Ref,
        name: impl Into<String>,
        typ: ATyp,
        qualifier: Qualifier,
        distribution: Distribution,
    ) -> Self {
        Var {
            reference,
            index: Vec::new(),
            typ,
            qualifier,
            distribution,
            name: name.into(),
        }
    }

    pub fn from_node(
        node: NodeIndex,
        typ: ATyp,
        qualifier: Qualifier,
        distribution: Distribution,
    ) -> Self {
        Var {
            reference: Ref(node),
            index: Vec::new(),
            typ,
            qualifier,
            distribution,
            name: format!("__zippel::node::{}", node.index()),
        }
    }

    /// Construct a Var referencing the `Arg` node at `node`, carrying
    /// the variable name `v` as metadata.
    pub fn from_var(
        v: impl Into<String>,
        node: NodeIndex,
        typ: ATyp,
        qualifier: Qualifier,
        distribution: Distribution,
    ) -> Self {
        Var {
            reference: Ref(node),
            index: Vec::new(),
            typ,
            qualifier,
            distribution,
            name: v.into(),
        }
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

    pub fn node(&self) -> NodeIndex {
        self.reference.node()
    }

    /// Source-level variable name (set at construction).
    pub fn name(&self) -> &str {
        &self.name
    }

    // TODO: check caller correctness
    pub fn with_slot(&self, index: usize) -> Option<Self> {
        let slot_typ = self.typ.physical_slot_type(index)?;
        // For base types (scalar, group), with_slot(0) is identity — the
        // value itself is the only slot, so no index component is pushed.
        if matches!(self.typ, ATyp::Base(_)) {
            return Some(self.clone());
        }
        let mut new_index = self.index.clone();
        new_index.push(index);
        Some(Var {
            reference: self.reference,
            index: new_index,
            typ: slot_typ,
            qualifier: self.qualifier,
            distribution: self.distribution,
            name: self.name.clone(),
        })
    }

    /// Logical slot access: returns a Var at logical slot `i` with the
    /// type of that slot.
    ///
    /// For `Vec(T, n)`, `with_index(i)` returns a Var of type `T`.
    /// For polynomial types (Uni, Mle, VPoly), every logical slot has
    /// type `ATyp::scalar()`.
    ///
    /// Returns `None` if `i >= logical_len()`.
    pub fn with_index(&self, i: usize) -> Option<Self> {
        let slot_typ = self.typ.logical_slot_type(i)?;
        // For base types, with_index(0) is identity.
        if matches!(self.typ, ATyp::Base(_)) {
            return Some(self.clone());
        }
        let mut new_index = self.index.clone();
        new_index.push(i);
        Some(Var {
            reference: self.reference,
            index: new_index,
            typ: slot_typ,
            qualifier: self.qualifier,
            distribution: self.distribution,
            name: self.name.clone(),
        })
    }

    /// Collect all physical slot PRefs for this value, flattened one per scalar position.
    ///
    /// For leaf types (scalar, group), returns a single-element vec with
    /// `self`. For `Vec(T, n)`, returns `n` logical elements, each
    /// recursively expanded via `T.logical_slots()`. For polynomial types,
    /// returns one Var per coefficient (all scalar-typed).
    fn collect_slots(&self) -> Vec<Self> {
        match &self.typ {
            ATyp::Base(_) => vec![self.clone()],
            ATyp::Uni(m) => (0..=*m).filter_map(|i| self.with_slot(i)).collect(),
            ATyp::Mle(n) => (0..(1usize << *n))
                .filter_map(|i| self.with_slot(i))
                .collect(),
            ATyp::VPoly(n, m) => {
                let count = binomial(*m + *n, *n);
                (0..count).filter_map(|i| self.with_slot(i)).collect()
            }
            ATyp::Vec(t, n) => {
                let mut out = Vec::with_capacity(self.typ.physical_len());
                for i in 0..*n {
                    let mut elem_index = self.index.clone();
                    elem_index.push(i);
                    let elem = Var {
                        reference: self.reference,
                        index: elem_index,
                        typ: (**t).clone(),
                        qualifier: self.qualifier,
                        distribution: self.distribution,
                        name: self.name.clone(),
                    };
                    out.extend(elem.collect_slots());
                }
                out
            }
            ATyp::Record(fields) => {
                let mut out = Vec::with_capacity(self.typ.physical_len());
                for (field_idx, (_, ft)) in fields.iter().enumerate() {
                    let mut field_index = self.index.clone();
                    field_index.push(field_idx);
                    let field = Var {
                        reference: self.reference,
                        index: field_index,
                        typ: ft.clone(),
                        qualifier: self.qualifier,
                        distribution: self.distribution,
                        name: self.name.clone(),
                    };
                    out.extend(field.collect_slots());
                }
                out
            }
        }
    }

    /// Returns all physical slot PRefs for this type, one per flattened
    /// scalar position.
    pub fn slots(&self) -> Vec<Self> {
        self.collect_slots()
    }

    pub fn verbose(&self) -> String {
        let label = &self.name;
        let idx_str = self
            .index
            .iter()
            .map(|i| i.to_string())
            .collect::<Vec<_>>()
            .join("][");
        let idx_part = if self.index.is_empty() {
            String::new()
        } else {
            format!("[{}]", idx_str)
        };
        if self.typ.physical_len() > 1 && self.distribution.is_uniform() {
            format!(
                "{} uniform {}{}: {}",
                self.qualifier, label, idx_part, self.typ
            )
        } else if self.typ.physical_len() > 1 && self.distribution.is_uniform_nz() {
            format!(
                "{} uniform* {}{}: {}",
                self.qualifier, label, idx_part, self.typ
            )
        } else if self.typ.physical_len() > 1 {
            format!("{} {}{}: {}", self.qualifier, label, idx_part, self.typ)
        } else if self.distribution.is_uniform() {
            format!(
                "{} uniform {}{}: {}",
                self.qualifier, label, idx_part, self.typ
            )
        } else if self.distribution.is_uniform_nz() {
            format!(
                "{} uniform* {}{}: {}",
                self.qualifier, label, idx_part, self.typ
            )
        } else {
            format!("{} {}{}: {}", self.qualifier, label, idx_part, self.typ)
        }
    }
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Var as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

impl<'a, D, A> Pretty<'a, D, A> for Var
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        let mut text = self.name;
        for i in &self.index {
            text.push_str(&format!("[{}]", i));
        }
        allocator.text(text)
    }

    fn is_nil(&self) -> bool {
        false
    }
}

/// Build `Var`s for all input Arg nodes of `dag`, preserving the sort order
/// of `Dag::input_args()`.
pub fn dag_args<C: ArkConfig, A>(dag: &Dag<C, A>) -> Vec<Var> {
    dag.input_args()
        .into_iter()
        .filter_map(|n| match &dag[n] {
            Node::Arg(name, typ, qual, dist, _kind) => Some(Var::new_named(
                Ref(n),
                name.0.clone(),
                typ.clone(),
                *qual,
                *dist,
            )),
            _ => None,
        })
        .collect()
}
