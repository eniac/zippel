use ark_ec::CurveGroup;
use lang::ast::BinOp;

use backend::{ATyp, ArkConfig};
use crate::Op;
use crate::scheduler::{Cost, CostModel};
use ark_ff::{Field, PrimeField};
use std::marker::PhantomData;
/// An implementation, asymptotic cost model that estimates the cost of operations based on their types.
pub struct AsymptoticCost<C: ArkConfig>(PhantomData<C>);

impl<C: ArkConfig> AsymptoticCost<C> {
    const INT_ADD: f64 = 1.0;
    const INT_MUL: f64 = 2.0;
    const SCALAR_ADD: f64 = C::F::MODULUS_BIT_SIZE as f64;
    const SCALAR_MUL: f64 = Self::SCALAR_ADD * 2.0;
    const SCALAR_INV: f64 = Self::SCALAR_ADD * 8.0;
    const G_SCALAR_MUL: f64 = C::F::MODULUS_BIT_SIZE.pow(2) as f64;
    const G_ADD: f64 = 64.0 * (<<C::G1 as CurveGroup>::BaseField as Field>::BasePrimeField::MODULUS_BIT_SIZE as f64);
    const G_AFFINE_ADD: f64 = 16.0 * (<<C::G1 as CurveGroup>::BaseField as Field>::BasePrimeField::MODULUS_BIT_SIZE as f64);

    pub fn new() -> Self {
        Self(PhantomData)
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
            (_, _) => unreachable!(),
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
            (_, _) => unreachable!(),
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
            (_, _) => unreachable!(),
        }
    }

    pub fn cost_dot(lt: &ATyp, rt: &ATyp, nthreads: usize) -> f64 {
        match (lt, rt) {
            // MSM
            (ATyp::Vec(box lt, n), ATyp::Vec(box rt, _))
                if (lt.is_scalar() && rt.is_group()) || (lt.is_group() && rt.is_scalar()) =>
                Self::G_SCALAR_MUL * (*n as f64) / ((*n as f64).log2() * (nthreads as f64)),
            (ATyp::Vec(box lt, n), ATyp::Vec(box rt, _)) =>
                (Self::cost_mul(lt, rt, nthreads) * (*n as f64) / nthreads as f64) * (*n as f64).log2(),
            (_, _) => Self::cost_mul(lt, rt, nthreads)
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
            (_, _) => unreachable!(),
        }
    }
    pub fn cost_bool(lt: &ATyp, rt: &ATyp, nthreads: usize) -> f64 {
        match (lt, rt) {
            (ATyp::Bool, ATyp::Bool) => 1.0,
            (ATyp::Vec(box lt, _), ATyp::Vec(box rt, n)) =>
                (*n as f64) * Self::cost_bool(lt, rt, nthreads) / nthreads as f64,
            (_, _) => unreachable!(),
        }
    }
}

impl<C: ArkConfig> CostModel<C> for AsymptoticCost<C> {
    fn cost(&self, op: &Op<C>, nthreads: usize) -> Cost {
        let mut cost = 0.0;
        match op {
            Op::Bin(op, box l, box r, _) => {
                cost += self.cost(l, nthreads).0;
                cost += self.cost(r, nthreads).0;
                match (op, l.typ(), r.typ()) {
                    (BinOp::Add | BinOp::Sub | BinOp::Equ, lt, rt) => cost += Self::cost_add(&lt, &rt, nthreads),
                    (BinOp::Mul, lt, rt) => cost += Self::cost_mul(&lt, &rt, nthreads),
                    (BinOp::Div | BinOp::Rem, lt, rt) => cost += Self::cost_div(&lt, &rt, nthreads),
                    (BinOp::Dot, lt, rt) => cost += Self::cost_dot(&lt, &rt, nthreads),
                    (BinOp::And | BinOp::Or, lt, rt) => cost += Self::cost_bool(&lt, &rt, nthreads),
                    (BinOp::Pow, lt, rt) => cost += Self::cost_pow(&lt, &rt, nthreads),
                    (BinOp::Concat, _, _) => {},
                    (_, _, _) => unreachable!(),
                }
            },
            Op::Value(_)
            | Op::Gen(_)
            | Op::Underscore(_, _)
            | Op::Var(_, _, _)
            | Op::Random(_) => cost += 1.0,
            Op::Range(r) => cost += r.len() as f64 * Self::INT_ADD,
            Op::Ram(box l, box r) =>
                cost += self.cost(l, nthreads).0 + self.cost(r, nthreads).0,
            Op::Vec(vs) =>
                cost += vs.iter().fold(0.0, |acc, v| { acc + self.cost(v, nthreads).0 }) / nthreads as f64,
            Op::Challenge(t) => cost += Self::SCALAR_ADD * t.size() as f64,
            Op::Coef(box op) | Op::Eval(box op) => {
                let n = op.typ().size() as f64;
                cost += self.cost(op, nthreads).0 +
                    (n * (n as f64).log2() * Self::SCALAR_MUL / nthreads as f64)
            },
            Op::Check(box op) => cost += self.cost(op, nthreads).0,
        };
        cost.into()
    }
}

