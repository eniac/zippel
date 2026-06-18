pub mod error;

use crate::{GOp, HOp, Op, Ref};
use ark_ff::{One, Zero};
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

fn op_has_loop_param<C: ArkConfig>(op: &GOp<C>, target_level: usize) -> bool {
    match op {
        Op::LoopParam(level, _) => *level == target_level,
        Op::Bin(_, a, b, _) => {
            op_has_loop_param(a.get(), target_level) || op_has_loop_param(b.get(), target_level)
        }
        Op::Ram(a, b) => {
            op_has_loop_param(a.get(), target_level) || op_has_loop_param(b.get(), target_level)
        }
        Op::Vec(vs) => vs.iter().any(|v| op_has_loop_param(v.get(), target_level)),
        Op::Record(fs) => fs
            .iter()
            .any(|(_, v)| op_has_loop_param(v.get(), target_level)),
        Op::Pair(a, b, _) => {
            op_has_loop_param(a.get(), target_level) || op_has_loop_param(b.get(), target_level)
        }
        Op::Ifft(a) => op_has_loop_param(a.get(), target_level),
        Op::Interpolate(a, b) => {
            op_has_loop_param(a.get(), target_level) || op_has_loop_param(b.get(), target_level)
        }
        Op::Fft(a) => op_has_loop_param(a.get(), target_level),
        Op::Poly(a) => op_has_loop_param(a.get(), target_level),
        Op::Mle(a) => op_has_loop_param(a.get(), target_level),
        Op::Proj(a, _, _) => op_has_loop_param(a.get(), target_level),
        Op::Coef(a) => op_has_loop_param(a.get(), target_level),
        Op::Evaluate(a, _, b) => {
            op_has_loop_param(a.get(), target_level)
                || b.as_ref()
                    .map(|x| op_has_loop_param(x.get(), target_level))
                    .unwrap_or(false)
        }
        Op::Map(domain, body) => {
            op_has_loop_param(domain.get(), target_level)
                || op_has_loop_param(body.get(), target_level)
        }
        Op::ReduceMap(_, domain, body) => {
            op_has_loop_param(domain.get(), target_level)
                || op_has_loop_param(body.get(), target_level)
        }
        Op::Check(a) => op_has_loop_param(a.get(), target_level),
        Op::Reduce(_, a) => op_has_loop_param(a.get(), target_level),
        Op::Value(_) | Op::Ref(_, _) | Op::Random(_, _) | Op::Challenge(_, _) => false,
    }
}

/// Check whether an `Op` represents a constant literal value of 2 (either as an index or a scalar field element).
fn is_const_two<C: ArkConfig>(op: &GOp<C>) -> bool {
    match op {
        Op::Value(val) => match val {
            Value::Index(2) => true,
            Value::Scalar(f) => *f == <C::F as From<u64>>::from(2u64),
            _ => false,
        },
        _ => false,
    }
}

fn match_bit_extraction_ast<C: ArkConfig>(
    op: &GOp<C>,
    outer_level: usize,
    inner_level: usize,
) -> bool {
    let Op::Bin(BinOp::Rem, lhs, rhs, _) = op else {
        return false;
    };
    if !is_const_two(rhs.get()) {
        return false;
    }
    let Op::Bin(BinOp::Div, lhs_div, rhs_div, _) = lhs.get() else {
        return false;
    };
    let Op::LoopParam(l_outer, _) = lhs_div.get() else {
        return false;
    };
    if *l_outer != outer_level {
        return false;
    }
    let Op::Bin(BinOp::Pow, lhs_pow, rhs_pow, _) = rhs_div.get() else {
        return false;
    };
    if !is_const_two(lhs_pow.get()) {
        return false;
    }
    let Op::LoopParam(l_inner, _) = rhs_pow.get() else {
        return false;
    };
    *l_inner == inner_level
}

fn is_value_one<C: ArkConfig>(v: &Value<C>) -> bool {
    match v {
        Value::Scalar(f) => *f == C::F::one(),
        Value::Index(1) => true,
        Value::Bool(true) => true,
        _ => false,
    }
}

fn is_value_zero<C: ArkConfig>(v: &Value<C>) -> bool {
    match v {
        Value::Scalar(f) => f.is_zero(),
        Value::Index(0) => true,
        Value::Bool(false) => true,
        _ => false,
    }
}

fn has_zero_one_at_start<C: ArkConfig>(v: &Value<C>) -> bool {
    match v {
        Value::Vec(elements) => {
            elements.len() >= 2 && is_value_zero(&elements[0]) && is_value_one(&elements[1])
        }
        Value::VecScalar(elements) => {
            elements.len() >= 2 && elements[0].is_zero() && elements[1] == C::F::one()
        }
        Value::VecIndex(elements) => elements.len() >= 2 && elements[0] == 0 && elements[1] == 1,
        Value::VecBool(elements) => elements.len() >= 2 && !elements[0] && elements[1],
        _ => false,
    }
}

fn verify_domain_is_canonical_indices<C: ArkConfig>(dom_val: &Value<C>, n: usize) -> bool {
    match dom_val {
        Value::VecIndex(v) => {
            if v.len() != n {
                return false;
            }
            v.iter().enumerate().all(|(i, &val)| val == i)
        }
        Value::VecScalar(v) => {
            if v.len() != n {
                return false;
            }
            v.iter()
                .enumerate()
                .all(|(i, &val)| val == <C::F as From<u64>>::from(i as u64))
        }
        Value::Vec(v) => {
            if v.len() != n {
                return false;
            }
            v.iter().enumerate().all(|(i, val)| match val {
                Value::Index(idx) => *idx == i,
                Value::Scalar(f) => *f == <C::F as From<u64>>::from(i as u64),
                _ => false,
            })
        }
        _ => false,
    }
}

/// Check whether a single `Value` represents canonical Boolean hypercube
/// coordinates for the hypercube vertex at index `i` with `k` bits.
///
/// The expected coordinate vector for index `i` is
/// `[bit(i,0), bit(i,1), ..., bit(i,k-1)]` where `bit(i,j) = (i >> j) & 1`.
///
/// Handles all runtime value representations: `VecScalar`, `VecIndex`,
/// `VecBool`, and heterogeneous `Vec`.
fn is_canonical_hypercube_vector<C: ArkConfig>(val: &Value<C>, i: usize, k: usize) -> bool {
    match val {
        Value::VecScalar(v) => {
            v.len() == k
                && (0..k).all(|j| {
                    let expected = if ((i >> j) & 1) == 1 {
                        C::F::one()
                    } else {
                        C::F::zero()
                    };
                    v[j] == expected
                })
        }
        Value::VecIndex(v) => v.len() == k && (0..k).all(|j| v[j] == ((i >> j) & 1)),
        Value::VecBool(v) => v.len() == k && (0..k).all(|j| v[j] == (((i >> j) & 1) == 1)),
        Value::Vec(v) => {
            v.len() == k
                && (0..k).all(|j| {
                    let expected_bit = ((i >> j) & 1) == 1;
                    match &v[j] {
                        Value::Scalar(f) => {
                            *f == if expected_bit {
                                C::F::one()
                            } else {
                                C::F::zero()
                            }
                        }
                        Value::Index(idx) => *idx == (expected_bit as usize),
                        Value::Bool(b) => *b == expected_bit,
                        _ => false,
                    }
                })
        }
        _ => false,
    }
}

fn verify_domain_is_canonical_coordinates<C: ArkConfig>(
    dom_val: &Value<C>,
    n: usize,
    k: usize,
) -> bool {
    match dom_val {
        Value::Vec(elements) => {
            elements.len() == n
                && elements
                    .iter()
                    .enumerate()
                    .all(|(i, val)| is_canonical_hypercube_vector::<C>(val, i, k))
        }
        _ => false,
    }
}

fn try_match_canonical_hypercube_ast<C: ArkConfig>(
    fixed: &HOp<C>,
    env: &HashMap<Ref, Arc<Value<C>>>,
    rng: &mut impl rand::RngCore,
    loop_params: &[Arc<Value<C>>],
) -> Result<bool, EvalError> {
    match fixed.get() {
        Op::Map(_inner_domain, inner_body) => {
            let outer_level = loop_params.len();
            let inner_level = loop_params.len() + 1;

            match inner_body.get() {
                // Case 1: Simple bit extraction
                body if match_bit_extraction_ast(body, outer_level, inner_level) => Ok(true),
                // Case 2: Multiplied bit extraction (scaling)
                Op::Bin(BinOp::Mul, lhs, rhs, _) => {
                    if match_bit_extraction_ast(lhs.get(), outer_level, inner_level)
                        && let Ok(x_val) = eval_op_with_loop_params(rhs, env, rng, loop_params)
                    {
                        return Ok(is_value_one(&x_val));
                    }
                    if match_bit_extraction_ast(rhs.get(), outer_level, inner_level)
                        && let Ok(x_val) = eval_op_with_loop_params(lhs, env, rng, loop_params)
                    {
                        return Ok(is_value_one(&x_val));
                    }
                    Ok(false)
                }
                // Case 3: Array index of bit extraction (e.g. pts3[(i / 2^j) % 2])
                Op::Ram(array, index) => {
                    if match_bit_extraction_ast(index.get(), outer_level, inner_level)
                        && let Ok(array_val) =
                            eval_op_with_loop_params(array, env, rng, loop_params)
                    {
                        return Ok(has_zero_one_at_start(&array_val));
                    }
                    Ok(false)
                }
                _ => Ok(false),
            }
        }
        _ => Ok(false),
    }
}

fn verify_hypercube_coordinates<C: ArkConfig, R: RngCore>(
    fixed: &HOp<C>,
    env: &HashMap<Ref, Arc<Value<C>>>,
    rng: &mut R,
    loop_params: &[Arc<Value<C>>],
    dom_val: &Value<C>,
    n: usize,
    k: usize,
) -> Result<bool, EvalError> {
    let get_elem = |i: usize| -> Arc<Value<C>> {
        match dom_val {
            Value::VecScalar(v) => Arc::new(Value::Scalar(v[i])),
            Value::VecIndex(v) => Arc::new(Value::Index(v[i])),
            Value::VecBool(v) => Arc::new(Value::Bool(v[i])),
            Value::VecG1(v) => Arc::new(Value::G1(v[i])),
            Value::VecG2(v) => Arc::new(Value::G2(v[i])),
            Value::VecGT(v) => Arc::new(Value::GT(v[i])),
            Value::VecG1Affine(v) => Arc::new(Value::G1Affine(v[i])),
            Value::VecG2Affine(v) => Arc::new(Value::G2Affine(v[i])),
            Value::Vec(v) => Arc::new(v[i].clone()),
            _ => panic!("Expected vector, found {}", dom_val),
        }
    };

    for i in 0..n {
        let mut params = loop_params.to_vec();
        params.push(get_elem(i));
        let coord_val = eval_op_with_loop_params(fixed, env, rng, &params)?;
        if !is_canonical_hypercube_vector::<C>(coord_val.as_ref(), i, k) {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Sumcheck fast path: detect `reduce(+, [eval<0>(poly, loop_param) for _ in hypercube])`
/// and route to the fused hypercube reduction kernel.
///
/// Pattern requirements (all checked structurally on the Op tree, not on values):
///   1. op == BinOp::Add
///   2. body == Op::Evaluate(poly, Some(range), Some(fixed))
///   3. fixed must reference this ReduceMap's own loop parameter
///   4. range.len() == 1 && range.start == 0  (canonical eval<0>)
///   5. domain type is Vec(_, n) where n == 2^k for some k  (complete hypercube)
///
/// Returns `Ok(None)` if the structural pattern is not matched (the caller
/// should proceed with the generic `ReduceMap` path). When the pattern *is*
/// matched, the domain is eagerly evaluated for hypercube verification;
/// if the domain turns out to be non-canonical, the function computes the
/// result via the generic loop body and returns `Ok(Some(result))` to avoid
/// re-evaluating the domain.
fn try_eval_reduce_map_fused_hypercube<C, R>(
    op: BinOp,
    domain: &HOp<C>,
    body: &HOp<C>,
    env: &HashMap<Ref, Arc<Value<C>>>,
    rng: &mut R,
    loop_params: &[Arc<Value<C>>],
) -> Result<Option<Arc<Value<C>>>, EvalError>
where
    C: ArkConfig,
    R: RngCore,
{
    // (1) Must be additive reduction
    if op != BinOp::Add {
        return Ok(None);
    }

    // (2) Body must be a selected evaluation: eval<range>(poly, fixed)
    let Op::Evaluate(poly, Some(range), Some(fixed)) = body.get() else {
        return Ok(None);
    };

    // (3) fixed must be either the loop parameter itself, or a Map/Comprehension
    // whose body references it but whose domain does not.
    let is_valid_fixed = match fixed.get() {
        Op::LoopParam(level, _) => *level == loop_params.len(),
        Op::Map(inner_domain, inner_body) => {
            !op_has_loop_param(inner_domain.get(), loop_params.len())
                && op_has_loop_param(inner_body.get(), loop_params.len())
        }
        _ => false,
    };
    if !is_valid_fixed {
        return Ok(None);
    }

    // Guard: poly must be loop-invariant (cannot reference this loop's binder)
    if op_has_loop_param(poly.get(), loop_params.len()) {
        return Ok(None);
    }

    // (4) Canonical eval<0>: single free variable at position 0
    if range.len() != 1 || range.start != 0 {
        return Ok(None);
    }

    // (5) Domain type is Vec(_, n) where n is a power of 2
    let ATyp::Vec(_, n) = domain.typ() else {
        return Ok(None);
    };
    if n == 0 || !n.is_power_of_two() {
        return Ok(None);
    }
    let tail_num_vars = n.trailing_zeros() as usize;

    // Evaluate domain
    let dom_val = Arc::unwrap_or_clone(eval_op_with_loop_params(domain, env, rng, loop_params)?);
    if !is_vector_value(&dom_val) {
        return Err(EvalError::TypeMismatch {
            expected: "vector".to_string(),
            got: format!("{}", dom_val),
        });
    }
    // Verify that evaluating fixed at each index of the domain produces canonical hypercube coordinates
    let is_hypercube = match fixed.get() {
        Op::LoopParam(level, _) if *level == loop_params.len() => {
            verify_domain_is_canonical_coordinates(&dom_val, n, tail_num_vars)
        }
        _ => {
            verify_domain_is_canonical_indices(&dom_val, n)
                && (try_match_canonical_hypercube_ast(fixed, env, rng, loop_params)?
                    || verify_hypercube_coordinates(
                        fixed,
                        env,
                        rng,
                        loop_params,
                        &dom_val,
                        n,
                        tail_num_vars,
                    )?)
        }
    };

    if is_hypercube {
        let shape = selected_eval_shape(poly, range);
        if tail_num_vars == shape.input_num_vars.saturating_sub(range.len()) {
            // Fast path — evaluate the polynomial and fuse
            let p_val =
                Arc::unwrap_or_clone(eval_op_with_loop_params(poly, env, rng, loop_params)?);
            Ok(Some(Arc::new(p_val.value_hypercube_reduce_selected(
                *range,
                tail_num_vars,
                shape,
            ))))
        } else {
            // Fallback using already evaluated dom_val
            let results = eval_loop_body_each(body, env, dom_val.into_elements(), loop_params)?;
            Ok(Some(Arc::new(Value::value_vec(results).value_reduce(op))))
        }
    } else {
        // Fallback using already evaluated dom_val
        let results = eval_loop_body_each(body, env, dom_val.into_elements(), loop_params)?;
        Ok(Some(Arc::new(Value::value_vec(results).value_reduce(op))))
    }
}

fn is_vector_value<C: ArkConfig>(v: &Value<C>) -> bool {
    matches!(
        v,
        Value::VecBool(_)
            | Value::VecIndex(_)
            | Value::VecScalar(_)
            | Value::VecG1(_)
            | Value::VecG2(_)
            | Value::VecGT(_)
            | Value::VecG1Affine(_)
            | Value::VecG2Affine(_)
            | Value::Vec(_)
    )
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
pub fn eval_op_with_loop_params<C, R>(
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
            if !is_vector_value(&dom) {
                return Err(EvalError::TypeMismatch {
                    expected: "vector".to_string(),
                    got: format!("{}", dom),
                });
            }
            let results = eval_loop_body_each(body, env, dom.into_elements(), loop_params)?;
            Ok(Arc::new(Value::value_vec(results)))
        }
        Op::ReduceMap(op, domain, body) => {
            if let Some(v) =
                try_eval_reduce_map_fused_hypercube(*op, domain, body, env, rng, loop_params)?
            {
                return Ok(v);
            }
            let dom =
                Arc::unwrap_or_clone(eval_op_with_loop_params(domain, env, rng, loop_params)?);
            if !is_vector_value(&dom) {
                return Err(EvalError::TypeMismatch {
                    expected: "vector".to_string(),
                    got: format!("{}", dom),
                });
            }
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
        Op::Map(d, b) | Op::ReduceMap(_, d, b) => {
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
