use ark_ec::CurveGroup;
use lang::ast::BinOp;

use backend::{ATyp, ArkConfig};
use crate::{Op, Node, Dag, UDag, Dep};
use petgraph::{
    graph::{EdgeReference, NodeIndex},
    visit::EdgeRef,
    Graph,
    Direction,
};
use ark_ff::{Field, PrimeField};

/// Implement this trait to give costs to operations in the DAG.
pub trait CostModel<C: ArkConfig> {
    fn cost(op: &Op<C>, nthreads: usize) -> f64;
}

/// An implementation, asymptotic cost model that estimates the cost of operations based on their types.
pub struct AsymptoticCost<C: ArkConfig>(pub Dag<C, f64>);

impl<C: ArkConfig> AsymptoticCost<C> {
    const INT_ADD: f64 = 1.0;
    const INT_MUL: f64 = 2.0;
    const SCALAR_ADD: f64 = C::F::MODULUS_BIT_SIZE as f64;
    const SCALAR_MUL: f64 = Self::SCALAR_ADD * 2.0;
    const SCALAR_INV: f64 = Self::SCALAR_ADD * 8.0;
    const G_SCALAR_MUL: f64 = C::F::MODULUS_BIT_SIZE.pow(2) as f64;
    const G_ADD: f64 = 16 as f64 * (<<C::G1 as CurveGroup>::BaseField as Field>::BasePrimeField::MODULUS_BIT_SIZE.pow(2) as f64);
    const G_AFFINE_ADD: f64 = 16 as f64 * (<<C::G1 as CurveGroup>::BaseField as Field>::BasePrimeField::MODULUS_BIT_SIZE as f64);

    /// Creates a new `AsymptoticCost`.
    pub fn new<A>(dag: Dag<C, A>, nthreads: usize) -> Self {
        AsymptoticCost(Dag(dag.0.map(|_, node|
                match node {
                    Node::Inp(a, b) => Node::Inp(a.clone(), b.clone()),
                    Node::Op(op, _) => {
                        let cost = Self::cost(&op, nthreads);
                        Node::Op(op.clone(), cost)
                    },
                    Node::Transcr(op, _) => {
                        let cost = Self::cost(&op, nthreads);
                        Node::Transcr(op.clone(), cost)
                    }
                },
                |_, e| e.clone())))
    }

    pub fn cost_add(lt: &ATyp, rt: &ATyp, nthreads: usize) -> f64 {
        match (lt, rt) {
            (ATyp::Fin(_), ATyp::Fin(_)) => Self::INT_ADD,
            (ATyp::Scalar, ATyp::Scalar) => Self::SCALAR_ADD,
            (ATyp::G1, ATyp::G1) => Self::G_ADD,
            (ATyp::G1Affine, ATyp::G1Affine) => Self::G_AFFINE_ADD,
            (ATyp::G2, ATyp::G2) => Self::G_ADD,
            (ATyp::G2Affine, ATyp::G2Affine) => Self::G_AFFINE_ADD,
            (ATyp::G1, ATyp::G1Affine) | (ATyp::G1Affine, ATyp::G1) => Self::G_AFFINE_ADD,
            (ATyp::G2, ATyp::G2Affine) | (ATyp::G2Affine, ATyp::G2) => Self::G_AFFINE_ADD,
            (ATyp::Vec(box lt, _), ATyp::Vec(box rt, n)) =>
                (*n as f64) * Self::cost_add(lt, rt, nthreads) / (nthreads as f64),
            (a, b) => unreachable!(),
        }
    }

    pub fn cost_mul(lt: &ATyp, rt: &ATyp, nthreads: usize) -> f64 {
        match (lt, rt) {
            (ATyp::Fin(_), ATyp::Fin(_)) => Self::INT_MUL,
            (ATyp::Scalar, ATyp::Scalar) => Self::SCALAR_MUL,
            (ATyp::Scalar, g) | (g, ATyp::Scalar) if g.is_group() => Self::G_SCALAR_MUL,
            (ATyp::Vec(box lt, _), ATyp::Vec(box rt, n)) =>
                (*n as f64) * Self::cost_mul(lt, rt, nthreads) / (nthreads as f64),
            (ATyp::Vec(box lt, n), rt)
            | (lt, ATyp::Vec(box rt, n)) =>
                (*n as f64) * Self::cost_mul(lt, rt, nthreads) / (nthreads as f64),
            (a, b) => unreachable!(),
        }
    }

    pub fn cost_div(lt: &ATyp, rt: &ATyp, nthreads: usize) -> f64 {
        match (lt, rt) {
            (ATyp::Fin(_), ATyp::Fin(_)) => Self::INT_MUL,
            (ATyp::Scalar, ATyp::Scalar) => Self::SCALAR_INV + Self::SCALAR_MUL,
            (ATyp::Scalar, g) | (g, ATyp::Scalar) if g.is_group() => Self::G_SCALAR_MUL + Self::SCALAR_INV,
            (ATyp::Vec(box lt, _), ATyp::Vec(box rt, n)) =>
                (*n as f64) * Self::cost_div(lt, rt, nthreads) / (nthreads as f64),
           (ATyp::Vec(box lt, n), rt)
            | (lt, ATyp::Vec(box rt, n)) =>
                (*n as f64) * Self::cost_div(lt, rt, nthreads) / (nthreads as f64),
            (a, b) => unreachable!(),
        }
    }

    pub fn cost_dot(lt: &ATyp, rt: &ATyp, nthreads: usize) -> f64 {
        match (lt, rt) {
            // MSM
            (ATyp::Vec(box lt, n), ATyp::Vec(box rt, _))
                if (lt.is_scalar() && rt.is_group()) || (lt.is_group() && rt.is_scalar()) =>
                (Self::G_SCALAR_MUL * (*n as f64) / ((*n as f64).log2() * (nthreads as f64))),
            (ATyp::Vec(box lt, n), ATyp::Vec(box rt, _)) =>
                (Self::cost_mul(lt, rt, nthreads) * (*n as f64) / nthreads as f64) * (*n as f64).log2(),
            (a, b) => Self::cost_mul(lt, rt, nthreads)
        }
    }

    pub fn cost_pow(lt: &ATyp, rt: &ATyp, nthreads: usize) -> f64 {
        match (lt, rt) {
            (ATyp::Fin(_), ATyp::Fin(r)) => Self::INT_MUL * r.len() as f64,
            (ATyp::Scalar, ATyp::Fin(r)) => Self::SCALAR_MUL * r.len() as f64,
            (ATyp::Vec(box lt, n), ATyp::Vec(box rt, _)) =>
                Self::cost_pow(lt, rt, nthreads) * (*n as f64) / nthreads as f64,
            (ATyp::Vec(box lt, n), rt) =>
                Self::cost_pow(lt, rt, nthreads) * (*n as f64) / nthreads as f64,
            (a, b) => unreachable!(),
        }
    }
    pub fn cost_bool(lt: &ATyp, rt: &ATyp, nthreads: usize) -> f64 {
        match (lt, rt) {
            (ATyp::Bool, ATyp::Bool) => 1.0,
            (ATyp::Vec(box lt, _), ATyp::Vec(box rt, n)) =>
                (*n as f64) * Self::cost_bool(lt, rt, nthreads) / nthreads as f64,
            (a, b) => unreachable!(),
        }
    }
}

impl<C: ArkConfig> CostModel<C> for AsymptoticCost<C> {
    fn cost(op: &Op<C>, nthreads: usize) -> f64 {
        let mut cost = 0.0;
        match op {
            Op::Bin(op, box l, box r, typ) => {
                cost += Self::cost(l, nthreads);
                cost += Self::cost(r, nthreads);
                match (op, l.typ(), r.typ()) {
                    (BinOp::Add | BinOp::Sub | BinOp::Equ, lt, rt) => cost += Self::cost_add(&lt, &rt, nthreads),
                    (BinOp::Mul, lt, rt) => cost += Self::cost_mul(&lt, &rt, nthreads),
                    (BinOp::Div | BinOp::Rem, lt, rt) => cost += Self::cost_div(&lt, &rt, nthreads),
                    (BinOp::Dot, lt, rt) => cost += Self::cost_dot(&lt, &rt, nthreads),
                    (BinOp::And | BinOp::Or, lt, rt) => cost += Self::cost_bool(&lt, &rt, nthreads),
                    (BinOp::Pow, lt, rt) => cost += Self::cost_pow(&lt, &rt, nthreads),
                    (BinOp::Concat, _, _) => {},
                    (BinOp::Contains, ATyp::Vec(box lt, n), _) => cost += (n as f64),
                    (_, _, _) => unreachable!(),
                }
            },
            Op::Not(box op) => cost += Self::cost(op, nthreads),
            Op::Value(_)
            | Op::Gen(_)
            | Op::Underscore(_, _)
            | Op::Var(_, _, _)
            | Op::Random(_) => {},
            Op::Range(r) => cost += r.len() as f64 * Self::INT_ADD,
            Op::Ram(box l, box r) => cost += Self::cost(l, nthreads) + Self::cost(r, nthreads),
            Op::Vec(vs) => cost += vs.iter().fold(0.0, |acc, v| { acc + Self::cost(v, nthreads) }) / nthreads as f64,
            Op::Challenge(t) => cost += Self::SCALAR_ADD,
            Op::Coef(box op) | Op::Eval(box op) => {
                let n = op.typ().size() as f64;
                cost += Self::cost(op, nthreads) +
                    (n * (n as f64).log2() * Self::SCALAR_MUL / nthreads as f64)
            },
            Op::Check(box op) => cost += Self::cost(op, nthreads),
        };
        println!("Cost of {} with type {} is {}", op, op.typ(), cost);
        cost
    }
}

#[cfg(test)] use lang::ast::UModule;
#[cfg(test)] use share::unwrap;
#[cfg(test)] use backend::ArkBls12_381;
#[test]
fn asymptotic_cost_foo() {
    let ex = r#"
        proto foo<G: Group, F: Scalar<G>>(private s: [F; 1000], private g: [G; 1000]) where s == s {
            let r = random<F>;
            a <- r * s;
            b <- r * g;
            let x = a . b;
            let y = s . g;
            verify(x == r * y);
        }"#;
    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    let g = unwrap!(UDag::<ArkBls12_381>::from_module(m));

    // Compute transitive closure
    let cm = AsymptoticCost::new(g, 16);

    cm.0.write_pdf("cost_foo").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });
}
