pub mod error;

use crate::{GOp, HOp, Op, ReduceMapDomainFact, Ref};
use backend::{ABase, ATyp, ArkConfig, SelectedEvalShape, Value};
use error::EvalError;
use lang::ast::BinOp;
use rand::RngCore;
use rand::SeedableRng;
use rand::rngs::StdRng;
use rayon::prelude::*;
use share::Ctx;
use std::collections::HashMap;
use std::sync::Arc;

/// Evaluate a `GOp` against a reference environment.
///
/// This is the canonical dispatcher used by both the runtime's per-node
/// computation (`runtime::graph::MutexGraph::handle_op`) and the test
/// executors (`graph::tests::test_helpers::execute_graph` /
/// `execute_graph_all`). Per-variant semantics mirror the runtime exactly.
///
/// `env` maps each `Ref` reachable from `op` to its previously-computed
/// `Value<C>`. Callers populate it differently:
/// - `execute_graph` walks the DAG topologically and inserts each Op/Transcr
///   node's value as it is computed (pre-populating Arg nodes from inputs).
/// - The runtime snapshots referenced nodes via `MutexGraph::get_value`
///   into a local map before each call.
/// - Direct PBT-style callers that pass a fully-inlined `GOp` with no
///   `Op::Ref` leaves can pass an empty map.
///
/// `rng` powers `Op::Random` and `Op::Challenge`. Sponge-aware transcript
/// Challenge is the runtime driver's responsibility (see
/// `runtime::graph::run_graph` sync-channel handling); the bare
/// `Op::Challenge` arm here preserves the runtime's existing `ThreadRng`
/// fallback behavior.
fn selected_eval_shape<C: ArkConfig>(p: &HOp<C>, range: &lang::typ::CRange) -> SelectedEvalShape {
    let (input_num_vars, max_degree) = match p.typ() {
        ATyp::Uni(d) => (1, d),
        ATyp::Mle(n) => (n, 1),
        ATyp::VPoly(n, d) => (n, d),
        other => panic!("Selected eval expects polynomial input, got {other}"),
    };
    SelectedEvalShape::new(input_num_vars, range.len(), max_degree)
}

/// A point statically typed `Vec(Bool, _)` or `Vec(Fin<0..2>, _)` is a boolean
/// hypercube point. Coerce a `Fin<0..2>` index value to its boolean form so
/// `Value::eval` takes the table-index fast path; everything else is untouched.
fn coerce_boolean_eval_point<C: ArkConfig>(point: Value<C>, point_typ: &ATyp) -> Value<C> {
    let is_boolean_vec = match point_typ {
        ATyp::Vec(elem, _) => match &**elem {
            ATyp::Base(ABase::Bool) => true,
            ATyp::Base(ABase::Fin(r)) => r.len() == 2 && r.contains(0) && r.contains(1),
            _ => false,
        },
        _ => false,
    };
    if !is_boolean_vec {
        return point;
    }
    match point {
        Value::VecIndex(v) => Value::VecBool(v.into_iter().map(|i| i == 1).collect()),
        other => other,
    }
}

pub fn eval_op<C, R>(
    op: &GOp<C>,
    env: &HashMap<Ref, Arc<Value<C>>>,
    rng: &mut R,
) -> Result<Arc<Value<C>>, EvalError>
where
    C: ArkConfig,
    R: RngCore,
{
    eval_op_with_loop_params(op, env, rng, &[])
}

/// Internal evaluator threading a de Bruijn loop-parameter stack for
/// `Op::Map` / `Op::ReduceMap` bodies. `loop_params[level]` resolves
/// `Op::LoopParam(level, _)`; the public `eval_op` calls this with `&[]`.
fn eval_op_with_loop_params<C, R>(
    op: &GOp<C>,
    env: &HashMap<Ref, Arc<Value<C>>>,
    rng: &mut R,
    loop_params: &[Arc<Value<C>>],
) -> Result<Arc<Value<C>>, EvalError>
where
    C: ArkConfig,
    R: RngCore,
{
    match op {
        Op::Value(v) => Ok(Arc::new(v.clone())),
        Op::Ref(r, _) => env.get(r).cloned().ok_or(EvalError::UndefinedRef(*r)),
        Op::Bin(binop, a, b, _) => {
            let av = eval_op_with_loop_params(a, env, rng, loop_params)?;
            let bv = eval_op_with_loop_params(b, env, rng, loop_params)?;
            // Borrow `av` by reference (no clone of left operand); only the
            // right operand must be materialised as owned (one inner clone
            // when the Arc is shared, free when unique).
            let av_ref: &Value<C> = &av;
            Ok(Arc::new(match binop {
                BinOp::Add => {
                    let mut bv_owned = Arc::unwrap_or_clone(bv);
                    av_ref.value_add(&mut bv_owned);
                    bv_owned
                }
                BinOp::Sub => {
                    let mut bv_owned = Arc::unwrap_or_clone(bv);
                    av_ref.value_sub(&mut bv_owned);
                    bv_owned
                }
                BinOp::Mul => {
                    let mut bv_owned = Arc::unwrap_or_clone(bv);
                    av_ref.value_mul(&mut bv_owned);
                    bv_owned
                }
                BinOp::Div => {
                    let mut bv_owned = Arc::unwrap_or_clone(bv);
                    av_ref.value_div(&mut bv_owned);
                    bv_owned
                }
                BinOp::Rem => {
                    let mut bv_owned = Arc::unwrap_or_clone(bv);
                    av_ref.value_rem(&mut bv_owned);
                    bv_owned
                }
                BinOp::Pow => {
                    let mut bv_owned = Arc::unwrap_or_clone(bv);
                    av_ref.value_pow(&mut bv_owned);
                    bv_owned
                }
                BinOp::And => {
                    let mut bv_owned = Arc::unwrap_or_clone(bv);
                    av_ref.value_and(&mut bv_owned);
                    bv_owned
                }
                BinOp::Dot => {
                    let mut bv_owned = Arc::unwrap_or_clone(bv);
                    av_ref.value_dot(&mut bv_owned);
                    bv_owned
                }
                BinOp::Concat => {
                    let av_owned = Arc::unwrap_or_clone(av);
                    let bv_owned = Arc::unwrap_or_clone(bv);
                    av_owned.value_concat(bv_owned)
                }
                BinOp::Equ => av_ref.value_equ(&*bv),
            }))
        }
        Op::Vec(ops) => {
            let mut values = Vec::with_capacity(ops.len());
            for child in ops {
                values.push(Arc::unwrap_or_clone(eval_op_with_loop_params(
                    child,
                    env,
                    rng,
                    loop_params,
                )?));
            }
            Ok(Arc::new(Value::value_vec(values)))
        }
        Op::Record(fields) => {
            let mut out: Ctx<String, Value<C>> = Ctx::new();
            for (name, child) in fields.iter() {
                let v = eval_op_with_loop_params(child, env, rng, loop_params)?;
                out.insert(name, &*v);
            }
            Ok(Arc::new(Value::Record(out)))
        }
        Op::Ram(v, idx) => {
            let v_val = eval_op_with_loop_params(v, env, rng, loop_params)?;
            let idx_val = eval_op_with_loop_params(idx, env, rng, loop_params)?;
            Ok(Arc::new(v_val.ram_ref(&*idx_val)))
        }
        Op::Check(a) => eval_op_with_loop_params(a, env, rng, loop_params),
        Op::Pair(a, b, _) => {
            let av = Arc::unwrap_or_clone(eval_op_with_loop_params(a, env, rng, loop_params)?);
            let bv = Arc::unwrap_or_clone(eval_op_with_loop_params(b, env, rng, loop_params)?);
            Ok(Arc::new(av.pair(bv)))
        }
        Op::Random(typ, _) => Ok(Arc::new(Value::random(rng, typ))),
        Op::Challenge(typ, _) => Ok(Arc::new(Value::random(rng, typ))),
        Op::Evaluate(p, None, None) => {
            let p_val = Arc::unwrap_or_clone(eval_op_with_loop_params(p, env, rng, loop_params)?);
            Ok(Arc::new(p_val.value_fft()))
        }
        Op::Evaluate(p, None, Some(x)) => {
            let p_val = Arc::unwrap_or_clone(eval_op_with_loop_params(p, env, rng, loop_params)?);
            let x_val = coerce_boolean_eval_point(
                Arc::unwrap_or_clone(eval_op_with_loop_params(x, env, rng, loop_params)?),
                &x.typ(),
            );
            Ok(Arc::new(p_val.value_eval(x_val)))
        }
        Op::Evaluate(p, Some(range), Some(fixed)) => {
            let shape = selected_eval_shape(p, range);
            let p_val = Arc::unwrap_or_clone(eval_op_with_loop_params(p, env, rng, loop_params)?);
            let fixed_val =
                Arc::unwrap_or_clone(eval_op_with_loop_params(fixed, env, rng, loop_params)?);
            Ok(Arc::new(
                p_val.value_eval_selected(*range, fixed_val, shape),
            ))
        }
        Op::Evaluate(_, Some(_), None) => {
            panic!("Op::Evaluate selected mode requires explicit points/fixed values")
        }
        Op::LoopParam(level, _) => loop_params
            .get(*level)
            .cloned()
            .ok_or(EvalError::LoopParam(*level)),
        Op::Map(domain, body) => {
            let dom =
                Arc::unwrap_or_clone(eval_op_with_loop_params(domain, env, rng, loop_params)?);
            let results = eval_loop_body_each(body, env, dom.into_elements(), loop_params)?;
            Ok(Arc::new(Value::value_vec(results)))
        }
        Op::ReduceMap(op, domain, body, fact) => {
            if let Some(v) = try_eval_reduce_map_hypercube_selected(
                *op,
                domain,
                body,
                *fact,
                env,
                rng,
                loop_params,
            )? {
                return Ok(v);
            }
            let dom =
                Arc::unwrap_or_clone(eval_op_with_loop_params(domain, env, rng, loop_params)?);
            let results = eval_loop_body_each(body, env, dom.into_elements(), loop_params)?;
            Ok(Arc::new(Value::value_vec(results).value_reduce(*op)))
        }
        Op::Coef(a) => Ok(Arc::new(
            (*eval_op_with_loop_params(a, env, rng, loop_params)?).value_coef(),
        )),
        Op::Poly(a) => Ok(Arc::new(
            (*eval_op_with_loop_params(a, env, rng, loop_params)?).value_poly(),
        )),
        Op::Interpolate(points, evals) => {
            let points_val = eval_op_with_loop_params(points, env, rng, loop_params)?;
            let evals_val = eval_op_with_loop_params(evals, env, rng, loop_params)?;
            Ok(Arc::new((*evals_val).value_interpolate(Some(&*points_val))))
        }
        Op::Ifft(a) => Ok(Arc::new(
            (*eval_op_with_loop_params(a, env, rng, loop_params)?).value_interpolate(None),
        )),
        Op::Fft(a) => Ok(Arc::new(
            (*eval_op_with_loop_params(a, env, rng, loop_params)?).value_fft(),
        )),
        Op::Mle(a) => {
            // Consume the input via `value_mle_owned` to avoid a 500 MB
            // memcpy when the operand is a fresh or unique `VecScalar`.
            // When the Arc is shared (env still holds a strong ref), the
            // unwrap clones once — same cost as `value_mle`.
            let av = Arc::unwrap_or_clone(eval_op_with_loop_params(a, env, rng, loop_params)?);
            Ok(Arc::new(av.value_mle_owned()))
        }
        Op::Reduce(binop, v) => {
            let v_val = Arc::unwrap_or_clone(eval_op_with_loop_params(v, env, rng, loop_params)?);
            Ok(Arc::new(v_val.value_reduce(*binop)))
        }
        Op::Proj(record_op, field_name, _) => {
            let rec_val = eval_op_with_loop_params(record_op, env, rng, loop_params)?;
            let Value::Record(r) = &*rec_val else {
                unreachable!()
            };
            Ok(Arc::new(r.get(field_name).cloned().unwrap()))
        }
    }
}

/// Evaluate a pure loop body once per element, pushing the element onto the
/// loop-parameter stack. Bodies are pure templates (no Random/Challenge), so
/// the per-task rng is a throwaway; rayon parallelizes across elements.
fn eval_loop_body_each<C: ArkConfig>(
    body: &HOp<C>,
    env: &HashMap<Ref, Arc<Value<C>>>,
    elems: Vec<Value<C>>,
    loop_params: &[Arc<Value<C>>],
) -> Result<Vec<Value<C>>, EvalError> {
    elems
        .into_par_iter()
        .map(|elem| {
            let mut params: Vec<Arc<Value<C>>> = loop_params.to_vec();
            params.push(Arc::new(elem));
            let mut rng = StdRng::seed_from_u64(0);
            Ok(Arc::unwrap_or_clone(eval_op_with_loop_params(
                body, env, &mut rng, &params,
            )?))
        })
        .collect()
}

/// Sumcheck fast path: a `CompleteBooleanHypercube` reduce-map whose body is
/// `eval<range>(poly, loop_param)` routes to the parallel dense-MLE kernel
/// `value_hypercube_reduce_selected` and never materializes its 2^k domain.
fn try_eval_reduce_map_hypercube_selected<C, R>(
    op: BinOp,
    _domain: &HOp<C>,
    body: &HOp<C>,
    fact: ReduceMapDomainFact,
    env: &HashMap<Ref, Arc<Value<C>>>,
    rng: &mut R,
    loop_params: &[Arc<Value<C>>],
) -> Result<Option<Arc<Value<C>>>, EvalError>
where
    C: ArkConfig,
    R: RngCore,
{
    let ReduceMapDomainFact::CompleteBooleanHypercube { tail_num_vars } = fact else {
        return Ok(None);
    };
    if op != BinOp::Add {
        return Ok(None);
    }
    let Op::Evaluate(poly, Some(range), Some(fixed)) = body.get() else {
        return Ok(None);
    };
    let Op::LoopParam(level, _) = fixed.get() else {
        return Ok(None);
    };
    // Only fire when `fixed` is exactly this reduce-map's own binder.
    if *level != loop_params.len() {
        return Ok(None);
    }
    let shape = selected_eval_shape(poly, range);
    let p_val = Arc::unwrap_or_clone(eval_op_with_loop_params(poly, env, rng, loop_params)?);
    Ok(Some(Arc::new(p_val.value_hypercube_reduce_selected(
        *range,
        tail_num_vars,
        shape,
    ))))
}

/// Collect every `Op::Ref` leaf reachable from `op`, in DFS order with
/// duplicates retained. Used by the runtime to snapshot referenced node
/// values into the `eval_op` env before dispatch.
pub fn collect_refs<C: ArkConfig>(op: &GOp<C>) -> Vec<Ref> {
    let mut acc = Vec::new();
    collect_refs_into(op, &mut acc);
    acc
}

fn collect_refs_into<C: ArkConfig>(op: &GOp<C>, acc: &mut Vec<Ref>) {
    match op {
        Op::Value(_) | Op::Random(_, _) | Op::Challenge(_, _) => {}
        Op::Ref(r, _) => acc.push(*r),
        Op::Bin(_, a, b, _) | Op::Pair(a, b, _) | Op::Ram(a, b) | Op::Interpolate(a, b) => {
            collect_refs_into(a, acc);
            collect_refs_into(b, acc);
        }
        Op::Evaluate(a, _, maybe_b) => {
            collect_refs_into(a, acc);
            if let Some(b) = maybe_b {
                collect_refs_into(b, acc);
            }
        }
        Op::Vec(children) => {
            for child in children {
                collect_refs_into(child, acc);
            }
        }
        Op::Record(fields) => {
            for (_, child) in fields.iter() {
                collect_refs_into(child, acc);
            }
        }
        Op::Check(a)
        | Op::Coef(a)
        | Op::Poly(a)
        | Op::Ifft(a)
        | Op::Fft(a)
        | Op::Mle(a)
        | Op::Proj(a, _, _)
        | Op::Reduce(_, a) => {
            collect_refs_into(a, acc);
        }
        Op::LoopParam(_, _) => {}
        Op::Map(d, b) | Op::ReduceMap(_, d, b, _) => {
            collect_refs_into(d, acc);
            collect_refs_into(b, acc);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mk;
    use backend::ArkBn254;
    use rand::rngs::ThreadRng;

    type Fr = <ArkBn254 as ArkConfig>::F;
    type TestValue = Value<ArkBn254>;

    #[test]
    fn test_eval_value() {
        let op = mk::<ArkBn254>(Op::Value(TestValue::Scalar(Fr::from(42))));
        let env = HashMap::new();
        let mut rng = ThreadRng::default();
        let result = eval_op(&op, &env, &mut rng).unwrap();
        assert_eq!(*result, TestValue::Scalar(Fr::from(42)));
    }
}

#[cfg(test)]
mod boolean_coercion_tests {
    use super::coerce_boolean_eval_point;
    use backend::{ABase, ATyp, ArkBls12_381, Value};
    use lang::typ::CRange;

    type C = ArkBls12_381;

    #[test]
    fn fin02_index_point_coerces_to_bool() {
        // A Vec(Fin<0..2>) index point takes the same fast path as Vec(Bool).
        let ptyp = ATyp::Vec(Box::new(ATyp::Base(ABase::Fin(CRange::new(0, 2)))), 3);
        let coerced = coerce_boolean_eval_point::<C>(Value::VecIndex(vec![1, 0, 1]), &ptyp);
        assert_eq!(coerced, Value::VecBool(vec![true, false, true]));
    }

    #[test]
    fn bool_point_passes_through() {
        let ptyp = ATyp::vec_bool(3);
        let pt = Value::<C>::VecBool(vec![true, false, true]);
        assert_eq!(coerce_boolean_eval_point::<C>(pt.clone(), &ptyp), pt);
    }

    #[test]
    fn non_boolean_points_unchanged() {
        // Fin<0..4> is not the {0,1} hypercube -> left as VecIndex (generic path).
        let fin4 = ATyp::Vec(Box::new(ATyp::Base(ABase::Fin(CRange::new(0, 4)))), 3);
        let idx = Value::<C>::VecIndex(vec![1, 0, 1]);
        assert_eq!(coerce_boolean_eval_point::<C>(idx.clone(), &fin4), idx);
        // Scalar-vector points are never scanned/coerced.
        let svec = Value::<C>::VecScalar(vec![]);
        let sty = ATyp::vec_scalar(0);
        assert_eq!(coerce_boolean_eval_point::<C>(svec.clone(), &sty), svec);
    }
}
