//! Map and ReduceMap body materialization: `map_op`, `reduce_map_op`,
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

use super::PolySource;
use super::{EncodeCtx, link_to_polys, link_to_witness};

/// Constant-fold an integer (`Fin`/`Unit`) subexpression over the enclosing
/// loop indices. Returns `Some(value)` when `op` is integer-typed and every
/// loop level it references has a concrete value; otherwise `None`.
///
/// `loop_vals` may contain `None` entries for loop levels whose domains are
/// non-literal (e.g. an instance arg used as a reduce domain). If the op does
/// not reference such a level, the `None` entry is irrelevant and a dummy
/// fill is safe. If it does reference a `None` level, we return `None`.
fn const_eval_int<C: ArkConfig>(op: &HOp<C>, loop_vals: &[Option<Value<C>>]) -> Option<Value<C>> {
    let t = op.typ();
    if !(t.is_fin() || t.is_unit()) {
        return None;
    }
    // If the op references a loop level whose value is None, we can't eval.
    for (level, val) in loop_vals.iter().enumerate() {
        if val.is_none() && graph::eval::op_has_loop_param(op.get(), level) {
            return None;
        }
    }
    // All referenced levels have concrete values; fill None entries with a
    // dummy (never accessed) so the params vector has the right length.
    let params: Vec<std::sync::Arc<Value<C>>> = loop_vals
        .iter()
        .map(|v| {
            v.clone()
                .map(std::sync::Arc::new)
                .unwrap_or_else(|| std::sync::Arc::new(Value::Index(0)))
        })
        .collect();
    let env: HashMap<Ref, std::sync::Arc<Value<C>>> = HashMap::new();
    let mut rng = <rand::rngs::StdRng as rand::SeedableRng>::seed_from_u64(0);
    let mut check_sink = Vec::new();
    graph::eval::eval_op_with_loop_params(op.get(), &env, &mut rng, &params, &mut check_sink)
        .ok()
        .map(|v| (*v).clone())
}

/// Materialize an inline Map/ReduceMap body op-tree into registered
/// sentinel Vars and return the Var bound to its ideal.
fn body_to_poly<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    body: &HOp<C>,
    loops: &[Var],
    loop_vals: &[Option<Value<C>>],
) -> Option<Var> {
    match body.get() {
        Op::Ref(r, _) => Some(ctx.ideal.find_ref(r)),
        Op::LoopParam(level, _) => loops.get(*level).cloned(),
        Op::Value(_) => {
            let name = ctx.builder.ns.next_name("gb_map_body");
            let pf = ctx.sentinel_var(&name, body.typ());
            ctx.ideal.register(&pf);
            ctx.builder
                .add_op(pf.clone(), body.get().clone(), ctx.ideal);
            Some(pf)
        }
        Op::Map(d, b) => {
            let name = ctx.builder.ns.next_name("gb_map_body");
            let pf = ctx.sentinel_var(&name, body.typ());
            ctx.ideal.register(&pf);
            map_op(&mut *ctx, pf.clone(), d, b, loops, loop_vals);
            Some(pf)
        }
        Op::ReduceMap(rop, d, b) => {
            let name = ctx.builder.ns.next_name("gb_map_body");
            let pf = ctx.sentinel_var(&name, body.typ());
            ctx.ideal.register(&pf);
            reduce_map_op(&mut *ctx, pf.clone(), *rop, d, b, loops, loop_vals);
            Some(pf)
        }
        _ => {
            if let Some(v) = const_eval_int(body, loop_vals) {
                let name = ctx.builder.ns.next_name("gb_map_body");
                let pf = ctx.sentinel_var(&name, body.typ());
                ctx.ideal.register(&pf);
                ctx.builder.add_op(pf.clone(), Op::Value(v), ctx.ideal);
                return Some(pf);
            }
            let rebuilt = rebuild_body_op(&mut *ctx, body, loops, loop_vals)?;
            let name = ctx.builder.ns.next_name("gb_map_body");
            let pf = ctx.sentinel_var(&name, body.typ());
            ctx.ideal.register(&pf);
            ctx.builder.add_op(pf.clone(), rebuilt, ctx.ideal);
            Some(pf)
        }
    }
}

/// Materialize a body child to an add_op-ready operand: `Op::Value` and
/// `Op::Ref` stay verbatim; everything else is bound to a fresh sentinel.
fn body_child<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    child: &HOp<C>,
    loops: &[Var],
    loop_vals: &[Option<Value<C>>],
) -> Option<HOp<C>> {
    match child.get() {
        Op::Value(_) | Op::Ref(_, _) => Some(child.clone()),
        _ => {
            if let Some(v) = const_eval_int(child, loop_vals) {
                return Some(mk::<C>(Op::Value(v)));
            }
            let pf = body_to_poly(&mut *ctx, child, loops, loop_vals)?;
            Some(mk::<C>(Op::Ref(pf.reference, pf.typ.clone())))
        }
    }
}

/// Rebuild a compound body op with each child replaced by an add_op-ready
/// operand (see `body_child`). Returns `None` for an unsupported variant.
fn rebuild_body_op<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    body: &HOp<C>,
    loops: &[Var],
    loop_vals: &[Option<Value<C>>],
) -> Option<GOp<C>> {
    Some(match body.get() {
        Op::Bin(op, a, b, typ) => Op::Bin(
            *op,
            body_child(&mut *ctx, a, loops, loop_vals)?,
            body_child(&mut *ctx, b, loops, loop_vals)?,
            typ.clone(),
        ),
        Op::Ram(a, b) => Op::Ram(
            body_child(&mut *ctx, a, loops, loop_vals)?,
            body_child(&mut *ctx, b, loops, loop_vals)?,
        ),
        Op::Evaluate(p, range, pts) => Op::Evaluate(
            body_child(&mut *ctx, p, loops, loop_vals)?,
            range.clone(),
            match pts {
                Some(x) => Some(body_child(&mut *ctx, x, loops, loop_vals)?),
                None => None,
            },
        ),
        Op::Poly(a) => Op::Poly(body_child(&mut *ctx, a, loops, loop_vals)?),
        Op::Coef(a) => Op::Coef(body_child(&mut *ctx, a, loops, loop_vals)?),
        Op::Mle(a) => Op::Mle(body_child(&mut *ctx, a, loops, loop_vals)?),
        Op::Ifft(a) => Op::Ifft(body_child(&mut *ctx, a, loops, loop_vals)?),
        Op::Fft(a) => Op::Fft(body_child(&mut *ctx, a, loops, loop_vals)?),
        Op::Interpolate(pts, evals) => Op::Interpolate(
            body_child(&mut *ctx, pts, loops, loop_vals)?,
            body_child(&mut *ctx, evals, loops, loop_vals)?,
        ),
        Op::Proj(a, field, typ) => Op::Proj(
            body_child(&mut *ctx, a, loops, loop_vals)?,
            field.clone(),
            typ.clone(),
        ),
        Op::Vec(vs) => {
            let mut children = Vec::with_capacity(vs.len());
            for v in vs {
                children.push(body_child(&mut *ctx, v, loops, loop_vals)?);
            }
            Op::Vec(children)
        }
        Op::Record(fields) => {
            let mut out: Ctx<String, HOp<C>> = Ctx::new();
            for (k, v) in fields.iter() {
                let child = body_child(&mut *ctx, v, loops, loop_vals)?;
                out.insert(k, &child);
            }
            Op::Record(out)
        }
        _ => return None,
    })
}

/// Explode a domain `v: [F; n]` into `n` registered element Vars.
fn explode_domain<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    domain: &HOp<C>,
    loops: &[Var],
    loop_vals: &[Option<Value<C>>],
) -> Option<Vec<(Var, Option<Value<C>>)>> {
    let (elem_t, n) = match domain.typ() {
        ATyp::Vec(deref!(e), n) => (e, n),
        _ => return None,
    };
    let elem_values: Vec<Option<Value<C>>> = match domain.get() {
        Op::Value(v) => v.clone().into_elements().into_iter().map(Some).collect(),
        _ => vec![None; n],
    };
    let src: PolySource<C> = match domain.get() {
        Op::Ref(_, _) | Op::Value(_) => PolySource::from_ref_vars(&ctx.ideal.vars, domain.get()),
        _ => {
            let dp = body_to_poly(&mut *ctx, domain, loops, loop_vals)?;
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
        let name = ctx.builder.ns.next_name("gb_map_elem");
        let elem_pf = ctx.sentinel_var(&name, elem_t.clone());
        ctx.ideal.register(&elem_pf);
        link_to_polys(ctx.ideal, &elem_pf, es.polys);
        elems.push((elem_pf, elem_values.get(i).cloned().flatten()));
    }
    Some(elems)
}

/// `Op::Map`: explode the domain, apply the body to each element, and
/// link ideal slot `i` to the body's output for element `i`.
pub(crate) fn map_op<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: Var,
    domain: &HOp<C>,
    body: &HOp<C>,
    parent_loops: &[Var],
    parent_vals: &[Option<Value<C>>],
) {
    let elems = match explode_domain(&mut *ctx, domain, parent_loops, parent_vals) {
        Some(e) => e,
        None => super::uncovered_op("map-domain", &var),
    };
    for (i, (elem, elem_val)) in elems.iter().enumerate() {
        let mut loops = parent_loops.to_vec();
        loops.push(elem.clone());
        let mut vals = parent_vals.to_vec();
        vals.push(elem_val.clone());
        match body_to_poly(&mut *ctx, body, &loops, &vals) {
            Some(vi) => link_to_witness(ctx.ideal, &var.with_index(i).unwrap(), &vi),
            None => super::uncovered_op("map-body", &var),
        }
    }
}

/// `Op::ReduceMap`: explode the domain, map the body per element, and fold
/// the ideals with `reduce_op_inner`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn reduce_map_op<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: Var,
    rop: BinOp,
    domain: &HOp<C>,
    body: &HOp<C>,
    parent_loops: &[Var],
    parent_vals: &[Option<Value<C>>],
) {
    let elems = match explode_domain(&mut *ctx, domain, parent_loops, parent_vals) {
        Some(e) => e,
        None => super::uncovered_op("reduce-map-domain", &var),
    };
    let n = elems.len();
    if n == 0 {
        super::uncovered_op("reduce-map-empty", &var);
    }
    let mut mapped: Vec<Var> = Vec::with_capacity(n);
    for (elem, elem_val) in elems.iter() {
        let mut loops = parent_loops.to_vec();
        loops.push(elem.clone());
        let mut vals = parent_vals.to_vec();
        vals.push(elem_val.clone());
        match body_to_poly(&mut *ctx, body, &loops, &vals) {
            Some(vi) => mapped.push(vi),
            None => super::uncovered_op("reduce-map-body", &var),
        }
    }
    if n == 1 {
        link_to_witness(ctx.ideal, &var, &mapped[0]);
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
    super::reduce::reduce_op_inner(&mut *ctx, var, rop, combined, elem_t, n);
}
