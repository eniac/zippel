//! CExp → EGraph<ZIR, ZAnalysis> conversion.
//!
//! See `docs/egraph-design-log.md` §6 for the full conversion code and
//! rationale. Key points:
//! - Let/Log-defined variables are inlined (scope stack with Inlined(Id))
//! - Var(tag) only for Map binders
//! - Seq wraps inlined let-bindings to preserve side effects
//! - Log is [Id;1] (absorb value only), continuation via Seq

use egg::{EGraph, Id, Symbol};
use lang::ast::{BinOp, CExp};
use lang::id::Vid;

use crate::lang::{ZAnalysis, ZIR};
use backend::{ArkConfig, Value};

/// Scope entry for the conversion scope stack.
enum ScopeEntry {
    /// Map binder: creates a Var(tag) node for the loop variable.
    Binder(Symbol),
    /// Let/Log: direct reference to the value's e-class (inlined).
    Inlined(Id),
}

/// Monotonic counter for generating fresh Symbol tags.
pub struct Counter {
    n: usize,
}

impl Counter {
    pub fn new() -> Self {
        Counter { n: 0 }
    }

    /// Generate a fresh Symbol tag.
    pub fn fresh(&mut self) -> Symbol {
        let s = Symbol::from(format!("__tag_{}", self.n));
        self.n += 1;
        s
    }
}

impl Default for Counter {
    fn default() -> Self {
        Self::new()
    }
}

/// Convert a CExp into a ZIR e-graph.
/// Returns the root Id of the e-graph.
pub fn convert_cexp<C: ArkConfig + std::fmt::Debug>(
    exp: &CExp,
    egraph: &mut EGraph<ZIR<C>, ZAnalysis<C>>,
    counter: &mut Counter,
) -> Id {
    let mut scope: Vec<(Vid, ScopeEntry)> = Vec::new();
    convert(exp, &mut scope, egraph, counter)
}

fn convert<C: ArkConfig + std::fmt::Debug>(
    exp: &CExp,
    scope: &mut Vec<(Vid, ScopeEntry)>,
    egraph: &mut EGraph<ZIR<C>, ZAnalysis<C>>,
    counter: &mut Counter,
) -> Id {
    match exp {
        // ---- leaves ----
        CExp::Lit(n) => egraph.add(ZIR::Constant(Value::Index(*n))),
        CExp::Unit => egraph.add(ZIR::Constant(Value::Unit)),
        CExp::Var(vid) => match scope.iter().rfind(|(v, _)| v == vid) {
            Some((_, ScopeEntry::Inlined(id))) => *id,
            Some((_, ScopeEntry::Binder(tag))) => egraph.add(ZIR::Var(*tag)),
            None => egraph.add(ZIR::Var(Symbol::from(vid.0.as_str()))),
        },

        // ---- binary arithmetic ----
        CExp::Bin(op, a, b) => {
            let a_id = convert(a, scope, egraph, counter);
            let b_id = convert(b, scope, egraph, counter);
            let node = match op {
                BinOp::Add => ZIR::Add([a_id, b_id]),
                BinOp::Sub => ZIR::Sub([a_id, b_id]),
                BinOp::Mul => ZIR::Mul([a_id, b_id]),
                BinOp::Div => ZIR::Div([a_id, b_id]),
                BinOp::Pow => ZIR::Pow([a_id, b_id]),
                BinOp::Dot => ZIR::Dot([a_id, b_id]),
                BinOp::Concat => ZIR::Concat([a_id, b_id]),
                BinOp::Rem => ZIR::Rem([a_id, b_id]),
            };
            egraph.add(node)
        }

        // ---- crypto ----
        CExp::Pair(a, b) => {
            let a_id = convert(a, scope, egraph, counter);
            let b_id = convert(b, scope, egraph, counter);
            egraph.add(ZIR::Pair([a_id, b_id]))
        }
        CExp::Random(_tid, non_zero) => {
            let tag = counter.fresh();
            egraph.add(ZIR::Random(tag, *non_zero))
        }
        CExp::Challenge(_tid, non_zero) => {
            let tag = counter.fresh();
            egraph.add(ZIR::Challenge(tag, *non_zero))
        }

        // ---- polynomial shape ops ----
        CExp::Poly(v) => {
            let id = convert(v, scope, egraph, counter);
            egraph.add(ZIR::Poly([id]))
        }
        CExp::Coef(v) => {
            let id = convert(v, scope, egraph, counter);
            egraph.add(ZIR::Coef([id]))
        }
        CExp::Mle(v) => {
            let id = convert(v, scope, egraph, counter);
            egraph.add(ZIR::Mle([id]))
        }
        CExp::Interpolate(points_opt, evals) => {
            let evals_id = convert(evals, scope, egraph, counter);
            match points_opt {
                None => egraph.add(ZIR::Ifft([evals_id])),
                Some(pts) => {
                    let pts_id = convert(pts, scope, egraph, counter);
                    egraph.add(ZIR::Interpolate([pts_id, evals_id]))
                }
            }
        }
        CExp::Evaluate(p, selector, points_opt) => {
            let p_id = convert(p, scope, egraph, counter);
            match (selector, points_opt) {
                (None, None) => egraph.add(ZIR::EvaluateGrid([p_id])),
                (None, Some(x)) => {
                    let x_id = convert(x, scope, egraph, counter);
                    egraph.add(ZIR::Evaluate([p_id, x_id]))
                }
                (Some(range), Some(fixed)) => {
                    let range_id = egraph.add(ZIR::Constant(Value::Index(0))); // placeholder
                    let fixed_id = convert(fixed, scope, egraph, counter);
                    let _ = range; // TODO: encode range as Constant
                    egraph.add(ZIR::EvaluateSelected([p_id, range_id, fixed_id]))
                }
                (Some(_), None) => {
                    panic!("CExp::Evaluate with selector but no points — parser rejects this");
                }
            }
        }

        // ---- structural ----
        CExp::Ram(a, b) => {
            let a_id = convert(a, scope, egraph, counter);
            let b_id = convert(b, scope, egraph, counter);
            egraph.add(ZIR::Ram([a_id, b_id]))
        }
        CExp::Vec(exps) => {
            let ids: Vec<Id> = exps
                .0
                .iter()
                .map(|e| convert(e, scope, egraph, counter))
                .collect();
            egraph.add(ZIR::Vec(ids.into_boxed_slice()))
        }
        CExp::Record(fields) => {
            let mut field_pairs: Vec<(Symbol, Id)> = Vec::new();
            for (name, val_exp) in fields.iter() {
                let val_id = convert(val_exp, scope, egraph, counter);
                field_pairs.push((Symbol::from(name.as_str()), val_id));
            }
            field_pairs.sort_by_key(|a| a.0);
            let names: Box<[Symbol]> = field_pairs.iter().map(|(s, _)| *s).collect();
            let values: Box<[Id]> = field_pairs.iter().map(|(_, id)| *id).collect();
            egraph.add(ZIR::Record(names, values))
        }
        CExp::Proj(record_exp, field_name) => {
            let record_id = convert(record_exp, scope, egraph, counter);
            egraph.add(ZIR::Proj(Symbol::from(field_name.as_str()), [record_id]))
        }
        CExp::SetRecord(record_exp, field_name, val_exp) => {
            // SetRecord is lowered during conversion: it creates a new
            // Record with the field replaced. For now, we lower it to
            // a Record with the updated field (TODO: full lowering).
            let record_id = convert(record_exp, scope, egraph, counter);
            let val_id = convert(val_exp, scope, egraph, counter);
            // Placeholder: just return the record (field update is a TODO)
            let _ = (field_name, val_id);
            record_id
        }

        // ---- loops ----
        CExp::Map(domain, binder, body) => {
            let dom_id = convert(domain, scope, egraph, counter);
            let tag = counter.fresh();
            scope.push((binder.clone(), ScopeEntry::Binder(tag)));
            let body_id = convert(body, scope, egraph, counter);
            scope.pop();
            egraph.add(ZIR::Map(tag, [dom_id, body_id]))
        }
        CExp::Reduce(op, v) => {
            let v_id = convert(v, scope, egraph, counter);
            egraph.add(ZIR::Reduce(*op, [v_id]))
        }

        // ---- control / side-effects ----
        CExp::Let(None, first, second) => {
            let first_id = convert(first, scope, egraph, counter);
            let second_id = convert(second, scope, egraph, counter);
            egraph.add(ZIR::Seq([first_id, second_id]))
        }
        CExp::Let(Some(binder), val, body) => {
            let val_id = convert(val, scope, egraph, counter);
            scope.push((binder.clone(), ScopeEntry::Inlined(val_id)));
            let body_id = convert(body, scope, egraph, counter);
            scope.pop();
            // Seq-wrap to preserve side effects in val_id
            egraph.add(ZIR::Seq([val_id, body_id]))
        }
        CExp::Log(binder, val, body) => {
            let val_id = convert(val, scope, egraph, counter);
            scope.push((binder.clone(), ScopeEntry::Inlined(val_id)));
            let body_id = convert(body, scope, egraph, counter);
            scope.pop();
            let tag = counter.fresh();
            let log_id = egraph.add(ZIR::Log(tag, [val_id]));
            egraph.add(ZIR::Seq([log_id, body_id]))
        }
        CExp::Assert(lhs, rhs) => {
            let lhs_id = convert(lhs, scope, egraph, counter);
            let rhs_id = convert(rhs, scope, egraph, counter);
            egraph.add(ZIR::Assert([lhs_id, rhs_id]))
        }
        CExp::Verify(lhs, rhs) => {
            let lhs_id = convert(lhs, scope, egraph, counter);
            let rhs_id = convert(rhs, scope, egraph, counter);
            egraph.add(ZIR::Verify([lhs_id, rhs_id]))
        }

        // ---- function definition / application (inlined) ----
        CExp::Fun(_vars, body) => {
            // Fun is inlined: convert the body directly.
            // TODO: handle poly variant creation
            convert(body, scope, egraph, counter)
        }
        CExp::App(_fid, _params) => {
            // App is inlined during conversion.
            // The graph crate's add_exp handles this via trampolining with
            // function context. For the egraph crate, App is expected to
            // be resolved before conversion (the caller inlines function
            // calls). If we reach here, it's an unhandled App.
            // TODO: handle App inlining (needs function context)
            panic!("CExp::App should be inlined before CExp→EGraph conversion");
        }

        // ---- Range (lowered during conversion) ----
        CExp::Range(r) => {
            // Range is lowered to a Constant holding the range info.
            // For now, encode as a pair of Index constants.
            // TODO: proper range encoding
            egraph.add(ZIR::Constant(Value::Index(r.start)))
        }
    }
}
