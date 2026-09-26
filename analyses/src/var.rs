use backend::op::Ref;
use graph::{Dag, Node};
use lang::typ::Qualifier;
use petgraph::graph::NodeIndex;

use backend::{ABase, ATyp, ArkConfig, binomial};
use std::fmt;

/// A reference to a node in the graph, with all associated metadata.
///
/// `index` is a logical multi-dimensional path (e.g. `[1, 0]` for the first
/// element of the second row of a 2D array). It is built up by
/// `with_index` / `collect_slots` as they recurse into composite types.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct Var {
    /// The graph node this `Var` ultimately reads from.
    pub reference: Ref,
    /// Logical path from `reference` down to this slot; empty for the whole value.
    pub index: Vec<usize>,
    /// Type of the value at `index` (already narrowed by `with_index`).
    pub typ: ATyp,
    /// Qualifier assigned to `reference` by qualifier propagation
    /// (`Witness`/`Instance`/`Local`/`Extra`).
    pub qualifier: Qualifier,
    /// Source-level variable name. For `Node::Arg` Vars this is the
    /// argument's `Vid`; for transcript-source Vars it is the log-variable
    /// name; for unnamed Vars it is derived from the node index.
    pub name: String,
}

impl Var {
    /// Builds a whole-value `Var` (empty `index`) with an explicit source name.
    pub fn new_named(
        reference: Ref,
        name: impl Into<String>,
        typ: ATyp,
        qualifier: Qualifier,
    ) -> Self {
        Var {
            reference,
            index: Vec::new(),
            typ,
            qualifier,
            name: name.into(),
        }
    }

    /// Builds a whole-value `Var` for `node` with a synthetic
    /// `__zippel::node::N` name, used when no source-level name exists.
    pub fn from_node(node: NodeIndex, typ: ATyp, qualifier: Qualifier) -> Self {
        Var {
            reference: Ref(node),
            index: Vec::new(),
            typ,
            qualifier,
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
    ) -> Self {
        Var {
            reference: Ref(node),
            index: Vec::new(),
            typ,
            qualifier,
            name: v.into(),
        }
    }

    /// Whether this slot is prover-private witness data.
    pub fn is_witness(&self) -> bool {
        self.qualifier.is_witness()
    }
    /// Whether this slot is verifier-visible instance data.
    pub fn is_instance(&self) -> bool {
        self.qualifier.is_instance()
    }
    /// Whether this slot is a prover-internal local (eliminated first during
    /// Gröbner elimination).
    pub fn is_local(&self) -> bool {
        self.qualifier.is_local()
    }

    /// The `petgraph` index of the node this `Var` refers to.
    pub fn node(&self) -> NodeIndex {
        self.reference.node()
    }

    /// Source-level variable name (set at construction).
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Logical slot access: returns a Var at logical slot `i` with the
    /// type of that slot.
    ///
    /// For `Vec(T, n)`, `with_index(i)` returns a Var of type `T`.
    /// For polynomial types (Uni, Mle, VPoly), every logical slot has
    /// type `ATyp::scalar()`.
    /// For `Record`, `with_index(i)` returns a Var for field `i`.
    ///
    /// Returns `None` for base types (scalars/groups/Unit are not
    /// indexable) or if `i` is out of bounds.
    pub fn with_index(&self, i: usize) -> Option<Self> {
        let slot_typ = match &self.typ {
            ATyp::Base(_) => return None,
            ATyp::Vec(t, n) => {
                if i >= *n {
                    return None;
                }
                (**t).clone()
            }
            ATyp::Uni(m) => {
                if i > *m {
                    return None;
                }
                ATyp::scalar()
            }
            ATyp::Mle(n) => {
                let len = 1usize
                    .checked_shl((*n).try_into().expect("with_index: Mle n exceeds u32"))
                    .expect("with_index: Mle 1 << n overflow");
                if i >= len {
                    return None;
                }
                ATyp::scalar()
            }
            ATyp::VPoly(n, m) => {
                let count = binomial(
                    m.checked_add(*n).expect("with_index: VPoly m + n overflow"),
                    *n,
                );
                if i >= count {
                    return None;
                }
                ATyp::scalar()
            }
            ATyp::Record(fields) => {
                let (_, t) = fields.iter().nth(i)?;
                t.clone()
            }
        };
        let mut new_index = self.index.clone();
        new_index.push(i);
        Some(Var {
            reference: self.reference,
            index: new_index,
            typ: slot_typ,
            qualifier: self.qualifier,
            name: self.name.clone(),
        })
    }

    /// Collect all physical slot Vars for this value, flattened one per scalar position.
    ///
    /// For leaf types (scalar, group), returns a single-element vec with
    /// `self`. For `Vec(T, n)`, returns `n` logical elements, each
    /// recursively expanded via `T.logical_slots()`. For polynomial types,
    /// returns one Var per coefficient (all scalar-typed).
    fn collect_slots(&self) -> Vec<Self> {
        match &self.typ {
            ATyp::Base(ABase::Unit) => vec![],
            ATyp::Base(_) => vec![self.clone()],
            ATyp::Uni(m) => (0..=*m).filter_map(|i| self.with_index(i)).collect(),
            ATyp::Mle(n) => {
                let len = 1usize
                    .checked_shl((*n).try_into().expect("collect_slots: Mle n exceeds u32"))
                    .expect("collect_slots: Mle 1 << n overflow");
                (0..len).filter_map(|i| self.with_index(i)).collect()
            }
            ATyp::VPoly(n, m) => {
                let count = binomial(
                    m.checked_add(*n)
                        .expect("collect_slots: VPoly m + n overflow"),
                    *n,
                );
                (0..count).filter_map(|i| self.with_index(i)).collect()
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
                        name: self.name.clone(),
                    };
                    out.extend(field.collect_slots());
                }
                out
            }
        }
    }

    /// Returns all physical slot Vars for this type, one per flattened
    /// scalar position.
    pub fn slots(&self) -> Vec<Self> {
        self.collect_slots()
    }

    /// Renders the fully-qualified slot as `qualifier name[i][j]: type`, the
    /// long form used in analysis diagnostics.
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
        format!("{} {}{}: {}", self.qualifier, label, idx_part, self.typ)
    }
}

/// `name[i][j]…`
impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.name)?;
        for i in &self.index {
            write!(f, "[{i}]")?;
        }
        Ok(())
    }
}

/// Build `Var`s for all input Arg nodes of `dag`, preserving the sort order
/// of `Dag::input_args()`.
pub fn dag_args<C: ArkConfig, A>(dag: &Dag<C, A>) -> Vec<Var> {
    dag.input_args()
        .into_iter()
        .filter_map(|n| match &dag[n] {
            Node::Arg(name, typ, qual, _dist, _kind) => {
                Some(Var::new_named(Ref(n), name.0.clone(), typ.clone(), *qual))
            }
            _ => None,
        })
        .collect()
}
