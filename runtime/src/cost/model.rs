use lang::ast::BinOp;
use crate::cost::CostModel;
use crate::arkworks::{ATyp, ArkConfig};
use crate::graph::Op;

use ark_ff::PrimeField;
use std::marker::PhantomData;

/// A cost model that estimates the cost of operations based on their types.
pub struct AsymptoticModel<C: ArkConfig>(PhantomData<C>);

impl<C: ArkConfig> AsymptoticModel<C> {
    /// Creates a new `AsymptoticModel`.
    pub fn new() -> Self {
        AsymptoticModel(PhantomData)
    }

    const SCALAR_ADD: f64 = C::F::MODULUS_BIT_SIZE;
    const SCALAR_MUL: f64 = C::F::MODULUS_BIT_SIZE.pow(2);
    const G_ADD: f64 = 16*C::G1::MODULUS_BIT_SIZE.pow(2);
    const GAFFINE_ADD: f64 = 16*C::G1::MODULUS_BIT_SIZE;

    pub fn cost_add(lt: &ATyp, rt: &ATyp, nthreads: usize) -> f64 {
        match (lt, rt) {
            (ATyp::Scalar, ATyp::Scalar) => Self::SCALAR_ADD,
            (ATyp::G1, ATyp::G1) => C::G_ADD,
            (ATyp::G1Affine, ATyp::G1Affine) => C::GAFFINE_ADD,
            (ATyp::G2, ATyp::G2) => C::G_ADD,
            (ATyp::G2Affine, ATyp::G2Affine) => C::GAFFINE_ADD,
            (ATyp::G1, ATyp::G1Affine) | (ATyp::G1Affine, ATyp::G1) => C::GAFFINE_ADD,
            (ATyp::G2, ATyp::G2Affine) | (ATyp::G2Affine, ATyp::G2) => C::GAFFINE_ADD,
            (ATyp::Vec(box lt, _), ATyp::Vec(box rt, n)) =>
                n * Self::cost_add(lt, rt, nthreads) / nthreads,
            (a, b) => panic!("UncaughtError: Add operands must be of the same type: {} != {}", a, b),
        }
    }

}

impl<C: ArkConfig> CostModel<C> for AsymptoticModel<C> {
    fn cost(&mut self, op: &Op<C>, nthreads: usize) -> f64 {
        let mut cost = 0.0;
        match op {
            Op::Value(v) => 0.0,
            Op::Bin(op, box l, box r, typ) =>
                match (op, typ, l.typ(), r.typ()) {
                    (BinOp::Add | BinOp::Sub, ATyp::Scalar, ATyp::Scalar, ATyp::Scalar) => Self::SCALAR_ADD,
                    (BinOp::Mul | BinOp::Div | BinOp::Rem | BinOp::Dot, ATyp::Scalar, ATyp::Scalar, ATyp::Scalar) => Self::SCALAR_MUL,
                    (BinOp::Add | BinOp::Sub, ATyp::Vec(box typ, _), _, _) => {
                        let size = typ.size();
                        let cost = Self::SCALAR_ADD * size as f64;
                        cost / nthreads as f64
                    }
            Op::Not(box op) => Self::cost(op, nthreads),
            Op::Gen(t) => t.clone(),
            Op::Underscore(_, t) => t.clone(),
            Op::Var(_, _, t) => t.clone(),
            Op::Range(r) => ATyp::vec(ATyp::Fin(r.clone()), r.len()),
            Op::Ram(box l, box r) =>
                match (l.typ(), r.typ()) {
                    (ATyp::Vec(box typ, _), ATyp::Fin(_)) => typ,
                    (ATyp::Vec(box typ, _), ATyp::Vec(box ATyp::Fin(_), m)) =>
                        ATyp::vec(typ, m),
                    (a, b) =>
                        panic!("UncaughtError: Ram operand must be a vector, not {} [ {} ]", a, b),
                }
            Op::Vec(vs) => {
                let typ = vs[0].typ();
                for v in vs.iter().skip(1) {
                    if v.typ() != typ {
                        panic!("UncaughtError: Vector operands must be of the same type: {} != {}", typ, v.typ());
                    }
                }
                ATyp::vec(typ, vs.len())
            }
            Op::Random(t) => t.clone(),
            Op::Challenge(t) => t.clone(),
            Op::Coef(box op) => op.typ(),
            Op::Eval(box op) => op.typ(),
            Op::Hash(_) => ATyp::Scalar,
            Op::Check(box op) => op.typ(),
        }

