pub mod error;

use crate::{GOp, Op, Ref};
use backend::values::marginalize as backend_marginalize;
use backend::{ArkConfig, ArkScalarOps, Value};
use error::EvalError;
use lang::ast::BinOp;
use rand::RngCore;
use share::Ctx;
use std::collections::HashMap;

const FIELD_POLY: &str = "poly";
const FIELD_CHALLENGE: &str = "challenge";
const FIELD_ROUND: &str = "round";
const FIELD_NUM_VARIABLES: &str = "num_variables";
const FIELD_MAX_DEGREE: &str = "max_degree";
const FIELD_EVALUATIONS: &str = "evaluations";
const FIELD_NEXT_POLY: &str = "next_poly";

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
    env: &HashMap<Ref, Value<C>>,
    rng: &mut R,
) -> Result<Value<C>, EvalError>
where
    C: ArkConfig,
    R: RngCore,
{
    match op {
        Op::Value(v) => Ok(v.clone()),
        Op::Ref(r, _) => env.get(r).cloned().ok_or(EvalError::UndefinedRef(*r)),
        Op::Bin(binop, a, b, _) => {
            let av = eval_op(a, env, rng)?;
            let bv = eval_op(b, env, rng)?;
            Ok(match binop {
                BinOp::Add => av + bv,
                BinOp::Sub => av - bv,
                BinOp::Mul => av * bv,
                BinOp::Div => av / bv,
                BinOp::Rem => av % bv,
                BinOp::Pow => av ^ bv,
                BinOp::And => av & bv,
                BinOp::Dot => av.dot(bv),
                BinOp::Concat => av.value_concat(bv),
                BinOp::Equ => av.value_equ(&bv),
            })
        }
        Op::Vec(ops) => {
            let mut values = Vec::with_capacity(ops.len());
            for child in ops {
                values.push(eval_op(child, env, rng)?);
            }
            Ok(Value::value_vec(values))
        }
        Op::Record(fields) => {
            let mut out: Ctx<String, Value<C>> = Ctx::new();
            for (name, child) in fields.iter() {
                let v = eval_op(child, env, rng)?;
                out.insert(name, &v);
            }
            Ok(Value::Record(out))
        }
        Op::Ram(v, idx) => {
            let v_val = eval_op(v, env, rng)?;
            let idx_val = eval_op(idx, env, rng)?;
            Ok(v_val.ram(idx_val))
        }
        Op::Check(a) => eval_op(a, env, rng),
        Op::Pair(a, b, _) => {
            let av = eval_op(a, env, rng)?;
            let bv = eval_op(b, env, rng)?;
            Ok(av.pair(bv))
        }
        Op::Random(typ, _) => Ok(Value::random(rng, typ)),
        Op::Challenge(typ, _) => Ok(Value::random(rng, typ)),
        Op::Evaluate(p, x) => {
            let p_val = eval_op(p, env, rng)?;
            let x_val = eval_op(x, env, rng)?;
            Ok(p_val.value_eval(x_val))
        }
        Op::Coef(a) => Ok(eval_op(a, env, rng)?.value_coef()),
        Op::Poly(a) => Ok(eval_op(a, env, rng)?.value_poly()),
        Op::Interpolate(points, evals) => {
            let points_val = eval_op(points, env, rng)?;
            let evals_val = eval_op(evals, env, rng)?;
            Ok(evals_val.value_interpolate(Some(&points_val)))
        }
        Op::Ifft(a) => Ok(eval_op(a, env, rng)?.value_interpolate(None)),
        Op::Fft(a) => Ok(eval_op(a, env, rng)?.value_fft()),
        Op::Mle(a) => Ok(eval_op(a, env, rng)?.value_mle()),
        Op::Reduce(binop, v) => Ok(eval_op(v, env, rng)?.value_reduce(*binop)),
        Op::Marginalize(a) => eval_marginalize(a, env, rng),
        Op::Proj(record_op, field_name, _) => {
            let rec_val = eval_op(record_op, env, rng)?;
            let Value::Record(r) = rec_val else {
                unreachable!()
            };
            Ok(r.get(field_name).cloned().unwrap())
        }
    }
}

/// Body of `Op::Marginalize` evaluation, factored out for readability.
/// Mirrors `runtime::graph::MutexGraph::handle_op`'s Marginalize arm.
fn eval_marginalize<C, R>(
    a: &crate::HOp<C>,
    env: &HashMap<Ref, Value<C>>,
    rng: &mut R,
) -> Result<Value<C>, EvalError>
where
    C: ArkConfig,
    R: RngCore,
{
    let cfg = eval_op(a, env, rng)?;
    let Value::Record(fields) = cfg else {
        return Err(type_mismatch("marginalize config record", &cfg));
    };

    let poly = match required_marginalize_field(&fields, FIELD_POLY)? {
        Value::Poly(p) => p.clone(),
        got => return Err(type_mismatch(FIELD_POLY, got)),
    };
    let challenge = match required_marginalize_field(&fields, FIELD_CHALLENGE)? {
        Value::Scalar(f) => Some(*f),
        Value::Index(i) => Some(C::FOps::from_usize(*i)),
        got => return Err(type_mismatch("scalar challenge", got)),
    };
    let round = marginalize_index_field(&fields, FIELD_ROUND)?;
    let num_variables = marginalize_index_field(&fields, FIELD_NUM_VARIABLES)?;
    let max_degree = marginalize_index_field(&fields, FIELD_MAX_DEGREE)?;

    let (evals, next_poly) =
        backend_marginalize::<C>(&poly, num_variables, max_degree, round, challenge);

    let mut out_fields: Ctx<String, Value<C>> = Ctx::new();
    out_fields.insert(&FIELD_EVALUATIONS.to_string(), &Value::VecScalar(evals));
    out_fields.insert(&FIELD_NEXT_POLY.to_string(), &Value::Poly(next_poly));
    Ok(Value::Record(out_fields))
}

fn required_marginalize_field<'a, C>(
    fields: &'a Ctx<String, Value<C>>,
    name: &str,
) -> Result<&'a Value<C>, EvalError>
where
    C: ArkConfig,
{
    fields
        .get(&name.to_string())
        .ok_or_else(|| EvalError::ValueError(format!("marginalize: missing field '{name}'")))
}

fn marginalize_index_field<C>(
    fields: &Ctx<String, Value<C>>,
    name: &str,
) -> Result<usize, EvalError>
where
    C: ArkConfig,
{
    match required_marginalize_field(fields, name)? {
        Value::Index(i) => Ok(*i),
        got => Err(type_mismatch(format!("index field '{name}'"), got)),
    }
}

fn type_mismatch<C>(expected: impl Into<String>, got: &Value<C>) -> EvalError
where
    C: ArkConfig,
{
    EvalError::TypeMismatch {
        expected: expected.into(),
        got: format!("{got}"),
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
        assert_eq!(result, TestValue::Scalar(Fr::from(42)));
    }

    #[test]
    fn referenced_config_marginalize_returns_evaluations_and_next_poly() {
        use backend::ATyp;
        use lang::typ::CRange;
        use petgraph::graph::NodeIndex;

        let Value::Poly(poly) = Value::<ArkBn254>::VecIndex(vec![1, 2, 3]).value_poly() else {
            panic!("expected poly fixture");
        };
        let challenge = Fr::from(0);
        let round = 0usize;
        let num_variables = 1usize;
        let max_degree = 2usize;

        let mut cfg_fields = Ctx::new();
        cfg_fields.insert(&FIELD_POLY.to_string(), &Value::Poly(poly.clone()));
        cfg_fields.insert(&FIELD_CHALLENGE.to_string(), &Value::Scalar(challenge));
        cfg_fields.insert(&FIELD_ROUND.to_string(), &Value::Index(round));
        cfg_fields.insert(
            &FIELD_NUM_VARIABLES.to_string(),
            &Value::Index(num_variables),
        );
        cfg_fields.insert(&FIELD_MAX_DEGREE.to_string(), &Value::Index(max_degree));

        let config_ref = Ref(NodeIndex::new(0));
        let mut typ_fields = Ctx::new();
        typ_fields.insert(&FIELD_POLY.to_string(), &ATyp::vpoly(1, 2));
        typ_fields.insert(&FIELD_CHALLENGE.to_string(), &ATyp::scalar());
        typ_fields.insert(
            &FIELD_ROUND.to_string(),
            &ATyp::fin(CRange::singleton(round)),
        );
        typ_fields.insert(
            &FIELD_NUM_VARIABLES.to_string(),
            &ATyp::fin(CRange::singleton(num_variables)),
        );
        typ_fields.insert(
            &FIELD_MAX_DEGREE.to_string(),
            &ATyp::fin(CRange::singleton(max_degree)),
        );
        let record_typ = ATyp::Record(typ_fields);
        let op = mk::<ArkBn254>(Op::Marginalize(mk(Op::Ref(config_ref, record_typ))));

        let mut env = HashMap::new();
        env.insert(config_ref, Value::Record(cfg_fields));
        let mut rng = ThreadRng::default();

        let result = eval_op(&op, &env, &mut rng).expect("referenced config evaluates");
        let (expected_evals, expected_next_poly) = backend_marginalize::<ArkBn254>(
            &poly,
            num_variables,
            max_degree,
            round,
            Some(challenge),
        );

        let Value::Record(fields) = result else {
            panic!("expected Value::Record from marginalize");
        };
        assert_eq!(
            fields.get(&FIELD_EVALUATIONS.to_string()),
            Some(&Value::VecScalar(expected_evals))
        );
        assert_eq!(
            fields.get(&FIELD_NEXT_POLY.to_string()),
            Some(&Value::Poly(expected_next_poly))
        );
    }
}
