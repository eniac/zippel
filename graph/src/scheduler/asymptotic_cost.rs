use log::debug;
use ark_ec::CurveGroup;
use lang::ast::BinOp;
use lang::typ::CRange;

use backend::{ABase, ATyp, ArkConfig};
use crate::{Op, GOp, Ref};
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
    const G_SCALAR_MUL: f64 = C::F::MODULUS_BIT_SIZE.pow(2) as f64;
    const G_ADD: f64 = 64.0 * (<<C::G1 as CurveGroup>::BaseField as Field>::BasePrimeField::MODULUS_BIT_SIZE as f64);
    const G_PAIR: f64 = 32.0 * (<<C::G1 as CurveGroup>::BaseField as Field>::BasePrimeField::MODULUS_BIT_SIZE as f64);


    pub fn new() -> Self {
        Self(PhantomData)
    }

    fn base_add(lt: &ABase, rt: &ABase) -> f64 {
        match (lt, rt) {
            (ABase::Fin(_), ABase::Fin(_)) => Self::INT_ADD,
            (ABase::Scalar, ABase::Scalar) => Self::SCALAR_ADD,
            (ABase::G1, ABase::G1) => Self::G_ADD,
            (ABase::G2, ABase::G2) => Self::G_ADD,
            (ABase::GT, ABase::GT) => Self::G_ADD,
            (ABase::Fin(_), ABase::Scalar) | (ABase::Scalar, ABase::Fin(_)) => {
                2.0
            }
            // Mixed base types we don't care to distinguish: treat as unit cost.
            (_, _) => 1.0,
        }
    }

    pub fn cost_add(lt: &ATyp, rt: &ATyp, nthreads: usize) -> f64 {
        match (lt, rt) {
            (ATyp::Base(a), ATyp::Base(b)) => Self::base_add(a, b),
            (ATyp::Vec(box lt, _), ATyp::Vec(box rt, n)) =>
                (*n as f64) * Self::cost_add(lt, rt, nthreads) / (nthreads as f64),
            (ATyp::Uni(lt), ATyp::Uni(rt)) =>
                (*lt.max(rt) as f64) * Self::SCALAR_ADD / (nthreads as f64),
            (ATyp::Uni(_lt), _) => {
                1.0
            },
            (_, _) => {
                1.0
            }
            // (_, _) => unreachable!(),
        }
    }

    fn base_mul(lt: &ABase, rt: &ABase) -> f64 {
        match (lt, rt) {
            (ABase::Fin(_), ABase::Fin(_)) => Self::INT_MUL,
            (ABase::Scalar, ABase::Scalar) => Self::SCALAR_MUL,
            (ABase::Scalar, ABase::Fin(_))
            | (ABase::Fin(_), ABase::Scalar) => Self::SCALAR_MUL,
            (ABase::G1, _) | (_, ABase::G1) => Self::G_SCALAR_MUL,
            (ABase::G2, _) | (_, ABase::G2) => Self::G_SCALAR_MUL,
            (ABase::GT, _) | (_, ABase::GT) => Self::G_SCALAR_MUL,
            (_, _) => unreachable!(),
        }
    }

    pub fn cost_mul(lt: &ATyp, rt: &ATyp, nthreads: usize) -> f64 {
        match (lt, rt) {
            (ATyp::Base(a), ATyp::Base(b)) => Self::base_mul(a, b),
            (ATyp::Vec(box lt, _), ATyp::Vec(box rt, n)) =>
                (*n as f64) * Self::cost_mul(lt, rt, nthreads) / (nthreads as f64),
            (ATyp::Vec(box lt, n), rt)
            | (lt, ATyp::Vec(box rt, n)) =>
                (*n as f64) * Self::cost_mul(lt, rt, nthreads) / (nthreads as f64),
            (ATyp::Uni(n), ATyp::Base(ABase::Scalar))
            | (ATyp::Base(ABase::Scalar), ATyp::Uni(n)) =>
                (*n as f64) * Self::SCALAR_MUL / (nthreads as f64),
            (a, b) => {debug!("{} {}", a, b); 1.0}//unreachable!()} TODO: fix this
        }
    }

    pub fn cost_div(lt: &ATyp, rt: &ATyp, nthreads: usize) -> f64 {
        match (lt, rt) {
            (ATyp::Base(a), ATyp::Base(b)) => Self::base_mul(a, b),
            (ATyp::Vec(box lt, _), ATyp::Vec(box rt, n)) =>
                (*n as f64) * Self::cost_div(lt, rt, nthreads) / (nthreads as f64),
           (ATyp::Vec(box lt, n), rt)
            | (lt, ATyp::Vec(box rt, n)) =>
                (*n as f64) * Self::cost_div(lt, rt, nthreads) / (nthreads as f64),
            (_, _) => 1.0,//unreachable!(),
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

    pub fn cost_pow(lt: &ATyp, rt: &CRange, nthreads: usize) -> f64 {
        Self::cost_mul(lt, lt, nthreads) * (rt.len() as f64) / nthreads as f64
    }

    pub fn cost_bool(lt: &ATyp, rt: &ATyp, nthreads: usize) -> f64 {
        match (lt, rt) {
            (ATyp::Base(ABase::Bool), ATyp::Base(ABase::Bool)) => 1.0,
            (ATyp::Vec(box lt, _), ATyp::Vec(box rt, n)) =>
                (*n as f64) * Self::cost_bool(lt, rt, nthreads) / nthreads as f64,
            (_, _) => unreachable!(),
        }
    }

    pub fn cost_pair(lt: &ATyp, rt: &ATyp, nthreads: usize) -> f64 {
        match (lt, rt) {
            (ATyp::Base(ABase::G1), ATyp::Base(ABase::G2)) => Self::G_PAIR,
            (ATyp::Base(ABase::G2), ATyp::Base(ABase::G1)) => Self::G_PAIR,
            (ATyp::Vec(box lt, n), ATyp::Vec(box rt, _)) =>
                (*n as f64) * Self::cost_pair(lt, rt, nthreads) / (nthreads as f64),
            (_, _) => 1.0// unreachable!(),
        }
    }
}

impl<C: ArkConfig> CostModel<C, Ref> for AsymptoticCost<C> {
    fn cost(&self, op: &GOp<C>, nthreads: usize) -> Cost {
        let mut cost = 0.0;
        match op {
            Op::Bin(op, l, r, _) => {
                cost += self.cost(l, nthreads).0;
                cost += self.cost(r, nthreads).0;
                match (op, l.typ(), r.typ()) {
                    (BinOp::Add | BinOp::Sub | BinOp::Equ, lt, rt) => cost += Self::cost_add(&lt, &rt, nthreads),
                    (BinOp::Mul, lt, rt) => cost += Self::cost_mul(&lt, &rt, nthreads),
                    (BinOp::Div | BinOp::Rem, lt, rt) => cost += Self::cost_div(&lt, &rt, nthreads),
                    (BinOp::Dot, lt, rt) => cost += Self::cost_dot(&lt, &rt, nthreads),
                    (BinOp::And, lt, rt) => cost += Self::cost_bool(&lt, &rt, nthreads),
                    (BinOp::Pow, lt, ATyp::Base(ABase::Fin(r))) => cost += Self::cost_pow(&lt, &r, nthreads),
                    (BinOp::Concat, _, _) => {},
                    _ => unreachable!(),
                }
            },
            Op::Pair(l, r, _) => {
                cost += self.cost(l, nthreads).0;
                cost += self.cost(r, nthreads).0;
                cost += Self::cost_pair(&l.typ(), &r.typ(), nthreads);
            },
            Op::Value(_)
            | Op::Ref(_, _)
            | Op::Random(_, _) => cost += 1.0,
            Op::Ram(l, r) =>
                cost += self.cost(l, nthreads).0 + self.cost(r, nthreads).0,
            Op::Vec(vs) =>
                cost += vs.iter().fold(0.0, |acc, v| { acc + self.cost(v, nthreads).0 }) / nthreads as f64,
            Op::Record(fields) =>
                cost += fields.iter().fold(0.0, |acc, (_, v)| { acc + self.cost(v, nthreads).0 }) / nthreads as f64,
            Op::Challenge(t, _) => cost += Self::SCALAR_ADD * t.size() as f64,
            Op::Ifft(op) | Op::Fft(op) => {
                let n = op.typ().size() as f64;
                cost += self.cost(op, nthreads).0 +
                    (n * (n as f64).log2() * Self::SCALAR_MUL / nthreads as f64)
            },
            Op::Check(op) => cost += self.cost(op, nthreads).0,
            Op::Poly(_op) => cost += 1.0,
            Op::Mle(_op) => cost += 1.0,
            Op::Eval(_p, _x) => cost += 1.0,
            Op::Coef(_op) => cost += 1.0,
            Op::Reduce(_, v) => {
                let (_, n) = v.typ().into_vec();
                cost += self.cost(v, nthreads).0 + (n as f64 - 1.0) * Self::SCALAR_MUL;
            },
            Op::Marginalize(box op) => cost += self.cost(op, nthreads).0,
            Op::Proj(box op, _, _) => cost += self.cost(op, nthreads).0,
        };
        cost.into()
    }
}

