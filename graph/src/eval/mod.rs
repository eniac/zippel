pub mod error;

use crate::{GOp, Op, Ref};
use backend::values::marginalize as backend_marginalize;
use backend::{ArkConfig, Value};
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
        Op::Evaluate(p, x) => {
            let p_val = Arc::unwrap_or_clone(eval_op(p, env, rng)?);
            let x_val = Arc::unwrap_or_clone(eval_op(x, env, rng)?);
            Ok(Arc::new(p_val.value_eval(x_val)))
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
        Op::Marginalize(a) => eval_marginalize(a, env, rng),
        Op::Proj(record_op, field_name, _) => {
            let rec_val = eval_op(record_op, env, rng)?;
            let Value::Record(r) = &*rec_val else {
                unreachable!()
            };
            Ok(Arc::new(r.get(field_name).cloned().unwrap()))
        }
    }
}

/// Body of `Op::Marginalize` evaluation, factored out for readability.
/// Mirrors `runtime::graph::MutexGraph::handle_op`'s Marginalize arm.
fn eval_marginalize<C, R>(
    a: &crate::HOp<C>,
    env: &HashMap<Ref, Arc<Value<C>>>,
    rng: &mut R,
) -> Result<Arc<Value<C>>, EvalError>
where
    C: ArkConfig,
    R: RngCore,
{
    let (poly_val, challenge_val, round_val, num_variables_val, max_degree_val) = match &**a {
        Op::Record(fields) => {
            let poly_op = fields
                .get(&"poly".to_string())
                .expect("marginalize: missing field 'poly'");
            let challenge_op = fields
                .get(&"challenge".to_string())
                .expect("marginalize: missing field 'challenge'");
            let round_op = fields.get(&"round".to_string());
            let num_variables_op = fields.get(&"num_variables".to_string());
            let max_degree_op = fields.get(&"max_degree".to_string());

            let poly_val = Arc::unwrap_or_clone(eval_op(poly_op, env, rng)?);
            let challenge_val = Arc::unwrap_or_clone(eval_op(challenge_op, env, rng)?);
            let round_val = match round_op {
                Some(op) => Some(Arc::unwrap_or_clone(eval_op(op, env, rng)?)),
                None => None,
            };
            let num_variables_val = match num_variables_op {
                Some(op) => Some(Arc::unwrap_or_clone(eval_op(op, env, rng)?)),
                None => None,
            };
            let max_degree_val = match max_degree_op {
                Some(op) => Some(Arc::unwrap_or_clone(eval_op(op, env, rng)?)),
                None => None,
            };
            (
                poly_val,
                challenge_val,
                round_val,
                num_variables_val,
                max_degree_val,
            )
        }
        _ => {
            let cfg_val = Arc::unwrap_or_clone(eval_op(a, env, rng)?);
            let Value::Record(record) = cfg_val else {
                unreachable!()
            };
            let poly_val = record.get(&"poly".to_string()).cloned().unwrap();
            let challenge_val = record.get(&"challenge".to_string()).cloned().unwrap();
            let round_val = record.get(&"round".to_string()).cloned();
            let num_variables_val = record.get(&"num_variables".to_string()).cloned();
            let max_degree_val = record.get(&"max_degree".to_string()).cloned();
            (
                poly_val,
                challenge_val,
                round_val,
                num_variables_val,
                max_degree_val,
            )
        }
    };

    let poly = poly_val.into_poly().clone();
    let challenge = Some(challenge_val.into_scalar());
    let round = round_val.map(|v| v.into_index()).unwrap_or(0usize);

    let num_variables = if let Some(v) = num_variables_val {
        v.into_index()
    } else {
        let current_poly_vars = poly.num_vars().unwrap_or(1);
        if round == 0 {
            current_poly_vars
        } else {
            current_poly_vars + (round - 1)
        }
    };

    let max_degree = max_degree_val
        .map(|v| v.into_index())
        .unwrap_or_else(|| poly.degree());

    let (evals, next_poly) =
        backend_marginalize::<C>(&poly, num_variables, max_degree, round, challenge);

    let mut out_fields: Ctx<String, Value<C>> = Ctx::new();
    out_fields.insert(&"evaluations".to_string(), &Value::VecScalar(evals));
    out_fields.insert(&"next_poly".to_string(), &Value::Poly(next_poly));
    Ok(Arc::new(Value::Record(out_fields)))
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
        Op::Bin(_, a, b, _)
        | Op::Pair(a, b, _)
        | Op::Ram(a, b)
        | Op::Evaluate(a, b)
        | Op::Interpolate(a, b) => {
            collect_refs_into(a, acc);
            collect_refs_into(b, acc);
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
        | Op::Marginalize(a)
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
