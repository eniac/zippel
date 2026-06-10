pub mod error;

use crate::{GOp, HOp, Op, Ref};
use backend::{ATyp, ArkConfig, SelectedEvalShape, Value};
use error::EvalError;
use lang::ast::BinOp;
use rand::RngCore;
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

pub fn eval_op<C, R>(
    op: &GOp<C>,
    env: &HashMap<Ref, Arc<Value<C>>>,
    rng: &mut R,
) -> Result<Arc<Value<C>>, EvalError>
where
    C: ArkConfig,
    R: RngCore,
{
    match op {
        Op::Value(v) => Ok(Arc::new(v.clone())),
        Op::Ref(r, _) => env.get(r).cloned().ok_or(EvalError::UndefinedRef(*r)),
        Op::Bin(binop, a, b, _) => {
            let av = eval_op(a, env, rng)?;
            let bv = eval_op(b, env, rng)?;
            // Borrow `av` by reference (no clone of left operand); only the
            // right operand must be materialised as owned (one inner clone
            // when the Arc is shared, free when unique).
            let av_ref: &Value<C> = &*av;
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
                values.push(Arc::unwrap_or_clone(eval_op(child, env, rng)?));
            }
            Ok(Arc::new(Value::value_vec(values)))
        }
        Op::Record(fields) => {
            let mut out: Ctx<String, Value<C>> = Ctx::new();
            for (name, child) in fields.iter() {
                let v = eval_op(child, env, rng)?;
                out.insert(name, &*v);
            }
            Ok(Arc::new(Value::Record(out)))
        }
        Op::Ram(v, idx) => {
            let v_val = eval_op(v, env, rng)?;
            let idx_val = eval_op(idx, env, rng)?;
            Ok(Arc::new(v_val.ram_ref(&*idx_val)))
        }
        Op::Check(a) => eval_op(a, env, rng),
        Op::Pair(a, b, _) => {
            let av = Arc::unwrap_or_clone(eval_op(a, env, rng)?);
            let bv = Arc::unwrap_or_clone(eval_op(b, env, rng)?);
            Ok(Arc::new(av.pair(bv)))
        }
        Op::Random(typ, _) => Ok(Arc::new(Value::random(rng, typ))),
        Op::Challenge(typ, _) => Ok(Arc::new(Value::random(rng, typ))),
        Op::Evaluate(p, None, None) => {
            let p_val = Arc::unwrap_or_clone(eval_op(p, env, rng)?);
            Ok(Arc::new(p_val.value_fft()))
        }
        Op::Evaluate(p, None, Some(x)) => {
            let p_val = Arc::unwrap_or_clone(eval_op(p, env, rng)?);
            let x_val = Arc::unwrap_or_clone(eval_op(x, env, rng)?);
            Ok(Arc::new(p_val.value_eval(x_val)))
        }
        Op::Evaluate(p, Some(range), Some(fixed)) => {
            let shape = selected_eval_shape(p, range);
            let p_val = Arc::unwrap_or_clone(eval_op(p, env, rng)?);
            let fixed_val = Arc::unwrap_or_clone(eval_op(fixed, env, rng)?);
            Ok(Arc::new(
                p_val.value_eval_selected(*range, fixed_val, shape),
            ))
        }
        Op::Evaluate(_, Some(_), None) => {
            panic!("Op::Evaluate selected mode requires explicit points/fixed values")
        }
        Op::HypercubeReduceSelected(p, range, tail_num_vars) => {
            let shape = selected_eval_shape(p, range);
            let p_val = Arc::unwrap_or_clone(eval_op(p, env, rng)?);
            Ok(Arc::new(p_val.value_hypercube_reduce_selected(
                *range,
                *tail_num_vars,
                shape,
            )))
        }
        Op::Coef(a) => Ok(Arc::new((*eval_op(a, env, rng)?).value_coef())),
        Op::Poly(a) => Ok(Arc::new((*eval_op(a, env, rng)?).value_poly())),
        Op::Interpolate(points, evals) => {
            let points_val = eval_op(points, env, rng)?;
            let evals_val = eval_op(evals, env, rng)?;
            Ok(Arc::new((*evals_val).value_interpolate(Some(&*points_val))))
        }
        Op::Ifft(a) => Ok(Arc::new((*eval_op(a, env, rng)?).value_interpolate(None))),
        Op::Fft(a) => Ok(Arc::new((*eval_op(a, env, rng)?).value_fft())),
        Op::Mle(a) => {
            // Consume the input via `value_mle_owned` to avoid a 500 MB
            // memcpy when the operand is a fresh or unique `VecScalar`.
            // When the Arc is shared (env still holds a strong ref), the
            // unwrap clones once — same cost as `value_mle`.
            let av = Arc::unwrap_or_clone(eval_op(a, env, rng)?);
            Ok(Arc::new(av.value_mle_owned()))
        }
        Op::Reduce(binop, v) => {
            let v_val = Arc::unwrap_or_clone(eval_op(v, env, rng)?);
            Ok(Arc::new(v_val.value_reduce(*binop)))
        }
        Op::Proj(record_op, field_name, _) => {
            let rec_val = eval_op(record_op, env, rng)?;
            let Value::Record(r) = &*rec_val else {
                unreachable!()
            };
            Ok(Arc::new(r.get(field_name).cloned().unwrap()))
        }
    }
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
        | Op::HypercubeReduceSelected(a, _, _)
        | Op::Proj(a, _, _)
        | Op::Reduce(_, a) => {
            collect_refs_into(a, acc);
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
