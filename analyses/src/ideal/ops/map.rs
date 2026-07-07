//! Map and ReduceMap body materialization: `map_to_poly`, `reduce_map_to_poly`,
//! `body_to_poly`, `body_child`, `rebuild_body_op`, `explode_domain`,
//! `const_eval_int`.

use std::collections::HashMap;

use graph::{GOp, HOp, Op, Ref, mk};
use lang::ast::BinOp;

use backend::op::HasOpFactory;
use backend::{ATyp, ArkConfig, Value};
use share::Ctx;

use crate::Var;
use crate::frontend::Polynomial;

use super::super::IdealBuilder;
use super::super::PolySource;
use super::super::ideal::Ideal;
use super::{EncodeCtx, link_to_polys, link_to_witness};

impl<C: ArkConfig + HasOpFactory> IdealBuilder<C> {
    /// Constant-fold an integer (`Fin`/`Bool`) subexpression over the enclosing
    /// loop indices. Returns `Some(value)` only when `op` is integer-typed and
    /// every enclosing loop binder has a concrete value; otherwise `None`.
    fn const_eval_int(&self, op: &HOp<C>, loop_vals: &[Option<Value<C>>]) -> Option<Value<C>> {
        let t = op.typ();
        if !(t.is_fin() || t.is_bool()) {
            return None;
        }
        let params: Vec<std::sync::Arc<Value<C>>> = loop_vals
            .iter()
            .map(|v| v.clone().map(std::sync::Arc::new))
            .collect::<Option<_>>()?;
        let env: HashMap<Ref, std::sync::Arc<Value<C>>> = HashMap::new();
        let mut rng = <rand::rngs::StdRng as rand::SeedableRng>::seed_from_u64(0);
        graph::eval::eval_op_with_loop_params(op.get(), &env, &mut rng, &params)
            .ok()
            .map(|v| (*v).clone())
    }

    /// Materialize an inline Map/ReduceMap body op-tree into registered
    /// sentinel Vars and return the Var bound to its ideal.
    fn body_to_poly(
        &mut self,
        body: &HOp<C>,
        loops: &[Var],
        loop_vals: &[Option<Value<C>>],
        ideal: &mut Ideal<C>,
    ) -> Option<Var> {
        match body.get() {
            Op::Ref(r, _) => Some(ideal.find_ref(r)),
            Op::LoopParam(level, _) => loops.get(*level).cloned(),
            Op::Value(_) => {
                let name = self.ns.next_name("gb_map_body");
                let pf = self.sentinel_var(&name, body.typ(), ideal);
                ideal.register(&pf);
                self.add_op(pf.clone(), body.get().clone(), ideal);
                Some(pf)
            }
            Op::Map(d, b) => {
                let name = self.ns.next_name("gb_map_body");
                let pf = self.sentinel_var(&name, body.typ(), ideal);
                ideal.register(&pf);
                self.map_to_poly(pf.clone(), d, b, loops, loop_vals, ideal);
                Some(pf)
            }
            Op::ReduceMap(rop, d, b) => {
                let name = self.ns.next_name("gb_map_body");
                let pf = self.sentinel_var(&name, body.typ(), ideal);
                ideal.register(&pf);
                self.reduce_map_to_poly(pf.clone(), *rop, d, b, loops, loop_vals, ideal);
                Some(pf)
            }
            _ => {
                if let Some(v) = self.const_eval_int(body, loop_vals) {
                    let name = self.ns.next_name("gb_map_body");
                    let pf = self.sentinel_var(&name, body.typ(), ideal);
                    ideal.register(&pf);
                    self.add_op(pf.clone(), Op::Value(v), ideal);
                    return Some(pf);
                }
                let rebuilt = self.rebuild_body_op(body, loops, loop_vals, ideal)?;
                let name = self.ns.next_name("gb_map_body");
                let pf = self.sentinel_var(&name, body.typ(), ideal);
                ideal.register(&pf);
                self.add_op(pf.clone(), rebuilt, ideal);
                Some(pf)
            }
        }
    }

    /// Materialize a body child to an add_op-ready operand: `Op::Value` and
    /// `Op::Ref` stay verbatim; everything else is bound to a fresh sentinel.
    fn body_child(
        &mut self,
        child: &HOp<C>,
        loops: &[Var],
        loop_vals: &[Option<Value<C>>],
        ideal: &mut Ideal<C>,
    ) -> Option<HOp<C>> {
        match child.get() {
            Op::Value(_) | Op::Ref(_, _) => Some(child.clone()),
            _ => {
                if let Some(v) = self.const_eval_int(child, loop_vals) {
                    return Some(mk::<C>(Op::Value(v)));
                }
                let pf = self.body_to_poly(child, loops, loop_vals, ideal)?;
                Some(mk::<C>(Op::Ref(pf.reference, pf.typ.clone())))
            }
        }
    }

    /// Rebuild a compound body op with each child replaced by an add_op-ready
    /// operand (see `body_child`). Returns `None` for an unsupported variant.
    fn rebuild_body_op(
        &mut self,
        body: &HOp<C>,
        loops: &[Var],
        loop_vals: &[Option<Value<C>>],
        ideal: &mut Ideal<C>,
    ) -> Option<GOp<C>> {
        Some(match body.get() {
            Op::Bin(op, a, b, typ) => Op::Bin(
                *op,
                self.body_child(a, loops, loop_vals, ideal)?,
                self.body_child(b, loops, loop_vals, ideal)?,
                typ.clone(),
            ),
            Op::Ram(a, b) => Op::Ram(
                self.body_child(a, loops, loop_vals, ideal)?,
                self.body_child(b, loops, loop_vals, ideal)?,
            ),
            Op::Evaluate(p, range, pts) => Op::Evaluate(
                self.body_child(p, loops, loop_vals, ideal)?,
                *range,
                match pts {
                    Some(x) => Some(self.body_child(x, loops, loop_vals, ideal)?),
                    None => None,
                },
            ),
            Op::Poly(a) => Op::Poly(self.body_child(a, loops, loop_vals, ideal)?),
            Op::Coef(a) => Op::Coef(self.body_child(a, loops, loop_vals, ideal)?),
            Op::Mle(a) => Op::Mle(self.body_child(a, loops, loop_vals, ideal)?),
            Op::Ifft(a) => Op::Ifft(self.body_child(a, loops, loop_vals, ideal)?),
            Op::Fft(a) => Op::Fft(self.body_child(a, loops, loop_vals, ideal)?),
            Op::Interpolate(pts, evals) => Op::Interpolate(
                self.body_child(pts, loops, loop_vals, ideal)?,
                self.body_child(evals, loops, loop_vals, ideal)?,
            ),
            Op::Proj(a, field, typ) => Op::Proj(
                self.body_child(a, loops, loop_vals, ideal)?,
                field.clone(),
                typ.clone(),
            ),
            Op::Vec(vs) => {
                let mut children = Vec::with_capacity(vs.len());
                for v in vs {
                    children.push(self.body_child(v, loops, loop_vals, ideal)?);
                }
                Op::Vec(children)
            }
            Op::Record(fields) => {
                let mut out: Ctx<String, HOp<C>> = Ctx::new();
                for (k, v) in fields.iter() {
                    let child = self.body_child(v, loops, loop_vals, ideal)?;
                    out.insert(k, &child);
                }
                Op::Record(out)
            }
            _ => return None,
        })
    }

    /// Explode a domain `v: [F; n]` into `n` registered element Vars.
    fn explode_domain(
        &mut self,
        domain: &HOp<C>,
        loops: &[Var],
        loop_vals: &[Option<Value<C>>],
        ideal: &mut Ideal<C>,
    ) -> Option<Vec<(Var, Option<Value<C>>)>> {
        let (elem_t, n) = match domain.typ() {
            ATyp::Vec(box e, n) => (e, n),
            _ => return None,
        };
        let elem_values: Vec<Option<Value<C>>> = match domain.get() {
            Op::Value(v) => v.clone().into_elements().into_iter().map(Some).collect(),
            _ => vec![None; n],
        };
        let src: PolySource<C> = match domain.get() {
            Op::Ref(_, _) | Op::Value(_) => PolySource::from_ref_vars(&ideal.vars, domain.get()),
            _ => {
                let dp = self.body_to_poly(domain, loops, loop_vals, ideal)?;
                PolySource::new(
                    dp.slots()
                        .into_iter()
                        .map(|s| Polynomial::var(&s))
                        .collect(),
                    dp.typ.clone(),
                )
            }
        };
        let mut elems = Vec::with_capacity(n);
        for i in 0..n {
            let es = src.at_index(i)?;
            let name = self.ns.next_name("gb_map_elem");
            let elem_pf = self.sentinel_var(&name, elem_t.clone(), ideal);
            ideal.register(&elem_pf);
            link_to_polys(ideal, &elem_pf, es.polys);
            elems.push((elem_pf, elem_values.get(i).cloned().flatten()));
        }
        Some(elems)
    }

    /// `Op::Map`: explode the domain, apply the body to each element, and
    /// link ideal slot `i` to the body's output for element `i`.
    pub(crate) fn map_to_poly(
        &mut self,
        var: Var,
        domain: &HOp<C>,
        body: &HOp<C>,
        parent_loops: &[Var],
        parent_vals: &[Option<Value<C>>],
        ideal: &mut Ideal<C>,
    ) {
        let elems = match self.explode_domain(domain, parent_loops, parent_vals, ideal) {
            Some(e) => e,
            None => Self::uncovered_op("map-domain", &var),
        };
        for (i, (elem, elem_val)) in elems.iter().enumerate() {
            let mut loops = parent_loops.to_vec();
            loops.push(elem.clone());
            let mut vals = parent_vals.to_vec();
            vals.push(elem_val.clone());
            match self.body_to_poly(body, &loops, &vals, ideal) {
                Some(vi) => link_to_witness(ideal, &var.with_index(i).unwrap(), &vi),
                None => Self::uncovered_op("map-body", &var),
            }
        }
    }

    /// `Op::ReduceMap`: explode the domain, map the body per element, and fold
    /// the ideals with `reduce_polysource`.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn reduce_map_to_poly(
        &mut self,
        var: Var,
        rop: BinOp,
        domain: &HOp<C>,
        body: &HOp<C>,
        parent_loops: &[Var],
        parent_vals: &[Option<Value<C>>],
        ideal: &mut Ideal<C>,
    ) {
        let elems = match self.explode_domain(domain, parent_loops, parent_vals, ideal) {
            Some(e) => e,
            None => Self::uncovered_op("reduce-map-domain", &var),
        };
        let n = elems.len();
        if n == 0 {
            Self::uncovered_op("reduce-map-empty", &var);
        }
        let mut mapped: Vec<Var> = Vec::with_capacity(n);
        for (elem, elem_val) in elems.iter() {
            let mut loops = parent_loops.to_vec();
            loops.push(elem.clone());
            let mut vals = parent_vals.to_vec();
            vals.push(elem_val.clone());
            match self.body_to_poly(body, &loops, &vals, ideal) {
                Some(vi) => mapped.push(vi),
                None => Self::uncovered_op("reduce-map-body", &var),
            }
        }
        if n == 1 {
            link_to_witness(ideal, &var, &mapped[0]);
            return;
        }
        let elem_t = mapped[0].typ.clone();
        let combined = PolySource::new(
            mapped
                .iter()
                .flat_map(|p| p.slots().into_iter().map(|s| Polynomial::var(&s)))
                .collect(),
            ATyp::vec(&elem_t, n),
        );
        let mut ctx = EncodeCtx {
            ns: &mut self.ns,
            ideal,
        };
        super::reduce::reduce_polysource(&mut ctx, var, rop, combined, elem_t, n);
    }
}
