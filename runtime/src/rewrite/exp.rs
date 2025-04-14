use std::marker::PhantomData;
pub use lang::typ::{CRange, ATyp, Typeable, TypeError};
pub use lang::ast::{BinOp, CExp, Exps};
pub use std::ops::Index;
pub use crate::arkworks::{Value, ATyp, ArkConfig, ArkScalarOps};

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ExpSimpl<C: ArkConfig> {
    Value(Value<C>),
    Exp(CExp),
}

impl<C: ArkConfig> From<CExp> for ExpSimpl<C> {
    fn from(exp: CExp) -> Self {
        ExpSimpl::Exp(exp)
    }
}

impl<C: ArkConfig> From<Value<C>> for ExpSimpl<C> {
    fn from(value: Value<C>) -> Self {
        ExpSimpl::Value(value)
    }
}

impl<C: ArkConfig> From<usize> for ExpSimpl<C> {
    fn from(value: usize) -> Self {
        ExpSimpl::Value(Value::Index(value as u64))
    }
}

impl<C: ArkConfig> ExpSimpl<C> {

    /// Create an integer value
    pub fn index(i: usize) -> Self {
        ExpSimpl::Value(Value::Index(i as u64))
    }

    /// Random access simplifications
    pub fn ram(v: Self, i: Self) -> Self {
        match (v, i) {
            // a[r1][r2] = a[r1.compose(r2)]
            (ExpSimpl::Exp(CExp::Ram(box v, box CExp::Range(l))), ExpSimpl::Exp(CExp::Range(r))) =>
                ExpSimpl::ram(v.into(), ExpSimpl::range(l.compose(&r))),
            // a[r1][i] = a[r1.compose_index(i)]
            (ExpSimpl::Exp(CExp::Ram(box v, box CExp::Range(r))), ExpSimpl::Value(Value::Index(i))) =>
                ExpSimpl::ram(v.into(), ExpSimpl::index(r.compose_index(i as usize))),
            // [e0, e1, ..., en][i] = e_i
            (ExpSimpl::Exp(CExp::Vec(vs)), ExpSimpl::Value(Value::Index(i))) => ExpSimpl::Exp(vs[i as usize].clone()),
            // [e0, e1, ..., en][r] = [e_i for i in r]
            (ExpSimpl::Exp(CExp::Vec(vs)), ExpSimpl::Exp(CExp::Range(r))) =>
                ExpSimpl::vec(r.into_iter().map(|i| vs[i].clone()).collect::<Vec<_>>()),
            // r[i] = r.compose_index(i)
            (ExpSimpl::Exp(CExp::Range(r)), ExpSimpl::Value(Value::Index(i))) =>
                ExpSimpl::index(r.compose_index(i as usize)),
            // r[r2] = r.compose(r2)
            (ExpSimpl::Exp(CExp::Range(r)), ExpSimpl::Exp(CExp::Range(i))) =>
                ExpSimpl::Exp(CExp::Range(r.compose(&i))),
            // v[v2]
            (ExpSimpl::Value(a), ExpSimpl::Value(b)) => ExpSimpl::Value(a.ram(b)),
            (ExpSimpl::Exp(a), ExpSimpl::Exp(b))=> ExpSimpl::Exp(CExp::ram(a, b)),
        }
    }

    /// Concatenation simplifications
    pub fn concat(v1: Self, v2: Self) -> Self {
        match (v1, v2) {
            // [e0, e1, ..., en] + [e_n+1, e_n+2, ..., e_m] = [e0, e1, ..., e_m]
            (ExpSimpl::Exp(CExp::Vec(Exps(mut vs1))), ExpSimpl::Exp(CExp::Vec(Exps(vs2)))) => {
                vs1.extend(vs2);
                ExpSimpl::vec(vs1)
            },
            // [e0, e1, ..., en] + e = [e0, e1, ..., e_n, e]
            (ExpSimpl::Exp(CExp::Vec(Exps(mut vs))), ExpSimpl::Exp(v))
            | (ExpSimpl::Exp(v), ExpSimpl::Exp(CExp::Vec(Exps(mut vs)))) => {
                vs.push(v);
                ExpSimpl::vec(vs)
            },
            // v1 + v2 = v1.concat(v2)
            (ExpSimpl::Value(a), ExpSimpl::Value(mut b)) => {
                a.concat(&mut b);
                ExpSimpl::Value(b)
            },
            (ExpSimpl::Exp(v1), ExpSimpl::Exp(v2)) =>
                ExpSimpl::Exp(CExp::Bin(BinOp::Concat, Box::new(v1), Box::new(v2)))
        }
    }

    pub fn add(v1: Self, v2: Self) -> Self {
        match (v1, v2) {
            // v1 + v2 = v1.add(v2)
            (ExpSimpl::Value(a), ExpSimpl::Value(mut b)) => {
                Value::value_add(&a, &mut b);
                ExpSimpl::Value(b)
            },
            // i + v = i + v
            (ExpSimpl::Exp(CExp::Lit(i)), ExpSimpl::Value(mut v))
            | (ExpSimpl::Value(mut v), ExpSimpl::Exp(CExp::Lit(i))) => {
                Value::value_add(&Value::Index(i as u64), &mut v);
                ExpSimpl::Value(v)
            },
            // [e0, ..., en] + v = [e0 + v0, e1 + v1, ..., en + vn]
            (ExpSimpl::Exp(CExp::Vec(Exps(l))), ExpSimpl::Value(mut v))
            | (ExpSimpl::Value(mut v), ExpSimpl::Exp(CExp::Vec(Exps(l)))) =>
                ExpSimpl::vec(v.into_vec_mut().into_iter()
                    .zip(l.into_iter())
                    .map(|(v, l)| ExpSimpl::add((*v).into(), l.into()))),

            // r1 + r2 = r1 + r2
            (ExpSimpl::Exp(CExp::Range(l)), ExpSimpl::Exp(CExp::Range(r))) =>
                ExpSimpl::range(l + r),

            // r1 + i = r1 + i
            (ExpSimpl::Exp(CExp::Range(l)), ExpSimpl::Value(Value::Index(r)))
            | (ExpSimpl::Value(Value::Index(r)), ExpSimpl::Exp(CExp::Range(l))) =>
                ExpSimpl::range(l + CRange::singleton(r as usize)),

            // [e0, e1, ... en] + [e0', e1', ... em'] = [e0 + e0', e1 + e1', ... en + em']
            (ExpSimpl::Exp(CExp::Vec(Exps(l))), ExpSimpl::Exp(CExp::Vec(Exps(r)))) =>
                ExpSimpl::vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| ExpSimpl::add(l.into(), r.into()))
                    .collect()),

            // [e0, e1, ... en] + r = [e0 + r0, e1 + r1, ... en + rn]
            (ExpSimpl::Exp(CExp::Vec(Exps(l))), ExpSimpl::Exp(CExp::Range(r)))
            | (ExpSimpl::Exp(CExp::Range(r)), ExpSimpl::Exp(CExp::Vec(Exps(l)))) =>
                ExpSimpl::vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| ExpSimpl::add(l.into(), r.into()))
                    .collect()),

            // Commuting conversion (eval a + eval b) = eval (a + b)
            (ExpSimpl::Exp(CExp::Eval(box l)), ExpSimpl::Exp(CExp::Eval(box r))) =>
                ExpSimpl::eval(ExpSimpl::add(l.into(), r.into())),
            // Commuting conversion (coef a + coef b) = coef (a + b)
            (ExpSimpl::Exp(CExp::Coef(box l)), ExpSimpl::Exp(CExp::Coef(box r))) =>
                ExpSimpl::coef(ExpSimpl::add(l.into(), r.into())),
            (ExpSimpl::Exp(v1), ExpSimpl::Exp(v2)) =>
                ExpSimpl::Exp(CExp::Bin(BinOp::Add, Box::new(v1), Box::new(v2))),
        }
    }

    pub fn sub(v1: Self, v2: Self) -> Self {
        match (v1, v2) {
            // v1 - v2 = v1.sub(v2)
            (ExpSimpl::Value(a), ExpSimpl::Value(b)) => {
                Value::value_sub(&a, &mut b);
                ExpSimpl::Value(b)
            },
            // i - v
            (ExpSimpl::Exp(CExp::Lit(i)), ExpSimpl::Value(mut v)) => {
                Value::value_sub(&Value::Index(i as u64), &mut v);
                ExpSimpl::Value(v)
            },
            // v - i
            (ExpSimpl::Value(v), ExpSimpl::Exp(CExp::Lit(i))) => {
                let mut b = Value::Index(i as u64);
                Value::value_sub(&v, &mut b);
                ExpSimpl::Value(b)
            },
            // [e0, ..., en] - v = [e0 - v0, e1 - v1, ..., en - vn]
            (ExpSimpl::Exp(CExp::Vec(Exps(l))), ExpSimpl::Value(mut v)) =>
                ExpSimpl::vec(l.into_iter()
                    .zip(v.into_vec_mut().into_iter())
                    .map(|(v, l)| ExpSimpl::sub(v.into(), (*l).into()))),

            // [e0, ..., en] - v = [e0 - v0, e1 - v1, ..., en - vn]
            (ExpSimpl::Value(mut v), ExpSimpl::Exp(CExp::Vec(Exps(l)))) =>
                ExpSimpl::vec(v.into_vec_mut().into_iter()
                    .zip(l.into_iter())
                    .map(|(v, l)| ExpSimpl::sub((*v).into(), l.into()))),

            // r1 - r2 = r1 - r2
            (ExpSimpl::Exp(CExp::Range(l)), ExpSimpl::Exp(CExp::Range(r))) =>
                ExpSimpl::range(l - r),

            // r1 - i = r1 - i
            (ExpSimpl::Exp(CExp::Range(l)), ExpSimpl::Value(Value::Index(r)))
            | (ExpSimpl::Value(Value::Index(r)), ExpSimpl::Exp(CExp::Range(l))) =>
                ExpSimpl::range(l - CRange::singleton(r as usize)),

            // [e0, e1, ... en] - [e0', e1', ... em'] = [e0 - e0', e1 - e1', ... en - em']
            (ExpSimpl::Exp(CExp::Vec(Exps(l))), ExpSimpl::Exp(CExp::Vec(Exps(r)))) =>
                ExpSimpl::vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| ExpSimpl::sub(l.into(), r.into()))
                    .collect()),

            // [e0, e1, ... en] - r = [e0 - r0, e1 - r1, ... en - rn]
            (ExpSimpl::Exp(CExp::Vec(Exps(l))), ExpSimpl::Exp(CExp::Range(r))) =>
                ExpSimpl::vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| ExpSimpl::sub(l.into(), r.into()))
                    .collect()),
            // r - [e0, e1, ... en] = [r - e0, r - e1, ... r - en]
            (ExpSimpl::Exp(CExp::Range(r)), ExpSimpl::Exp(CExp::Vec(Exps(l)))) =>
                ExpSimpl::vec(r.into_iter().zip(l.into_iter())
                    .map(|(r, l)| ExpSimpl::sub(r.into(), l.into()))
                    .collect()),
            // Commuting conversion (eval a - eval b) = eval (a - b)
            (ExpSimpl::Exp(CExp::Eval(box l)), ExpSimpl::Exp(CExp::Eval(box r))) =>
                ExpSimpl::eval(ExpSimpl::sub(l.into(), r.into())),
            // Commuting conversion (coef a - coef b) = coef (a - b)
            (ExpSimpl::Exp(CExp::Coef(box l)), ExpSimpl::Exp(CExp::Coef(box r))) =>
                ExpSimpl::coef(ExpSimpl::sub(l.into(), r.into())),
            (ExpSimpl::Exp(v1), ExpSimpl::Exp(v2)) =>
                ExpSimpl::Exp(CExp::Bin(BinOp::Add, Box::new(v1), Box::new(v2))),
        }
    }

    pub fn mul(v1: Self, v2: Self, typ: ATyp) -> Self {
        match (v1, v2) {
            // v1 * v2 = v1.mul(v2)
            (ExpSimpl::Value(a), ExpSimpl::Value(mut b)) => {
                Value::value_mul(&a, &mut b);
                ExpSimpl::Value(b)
            },
            // i * v = i * v
            (ExpSimpl::Exp(CExp::Lit(i)), ExpSimpl::Value(mut v))
            | (ExpSimpl::Value(mut v), ExpSimpl::Exp(CExp::Lit(i))) => {
                Value::value_mul(&Value::Index(i as u64), &mut v);
                ExpSimpl::Value(v)
            },
            // [e0, ..., en] * v = [e0 * v0, e1 * v1, ..., en * vn]
            (ExpSimpl::Exp(CExp::Vec(Exps(l))), ExpSimpl::Value(mut v))
            | (ExpSimpl::Value(mut v), ExpSimpl::Exp(CExp::Vec(Exps(l)))) => {
                let (t, _) = typ.clone().into_vec();
                if v.is_vec() {
                    ExpSimpl::vec(v.into_vec_mut().into_iter()
                        .zip(l.into_iter())
                        .map(|(v, l)| ExpSimpl::mul((*v).into(), l.into(), t)))
                } else {
                    ExpSimpl::vec(l.into_iter()
                        .map(|l| ExpSimpl::mul(v.clone().into(), l.into(), t)).collect())
                }
            },

            // r1 * r2 = r1 * r2
            (ExpSimpl::Exp(CExp::Range(l)), ExpSimpl::Exp(CExp::Range(r))) =>
                ExpSimpl::range(l * r),

            // r1 * i = r1 * i
            (ExpSimpl::Exp(CExp::Range(l)), ExpSimpl::Value(Value::Index(r)))
            | (ExpSimpl::Value(Value::Index(r)), ExpSimpl::Exp(CExp::Range(l))) =>
                ExpSimpl::range(l * CRange::singleton(r as usize)),

            // [e0, e1, ... en] * [e0', e1', ... en'] = [e0 * e0', e1 * e1', ... en * en']
            (ExpSimpl::Exp(CExp::Vec(l)), ExpSimpl::Exp(CExp::Vec(r))) => {
                let (t, _) = typ.into_vec();
                ExpSimpl::vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| ExpSimpl::mul(l.into(), r.into(), t.clone()))
                    .collect())
            },

            // [e0, e1, ... en] * r = [e0 * r0, e1 * r1, ... en * rn]
            (ExpSimpl::Exp(CExp::Vec(l)), ExpSimpl::Exp(CExp::Range(r)))
            | (ExpSimpl::Exp(CExp::Range(r)), ExpSimpl::Exp(CExp::Vec(l))) => {
                let (t, _) = typ.clone().into_vec();
                ExpSimpl::vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| ExpSimpl::mul(l.into(), r.into(), t.clone()))
                    .collect())
            },

            // Commuting conversions, (coef a * coef b) = coef (a * b)
            (ExpSimpl::Exp(CExp::Coef(box l)), ExpSimpl::Exp(CExp::Coef(box r))) => {
                let (t, n) = typ.clone().into_vec();
                ExpSimpl::coef(ExpSimpl::mul(l.into().pad_zeroes(n), r.into().pad_zeroes(n), typ))
            },
            // Default case, constructor
            (ExpSimpl::Exp(v1), ExpSimpl::Exp(v2)) => ExpSimpl::Exp(CExp::Bin(BinOp::Mul, Box::new(v1), Box::new(v2))),
        }
    }

    pub fn pad_zeroes(self, n: usize) -> Self {
        ExpSimpl::concat(self,
            ExpSimpl::Value(Value::VecScalar(vec![C::FOps::zero(); n])))
    }

    pub fn coef(op: Self) -> Self {
        match op {
            // coef . eval p = p
            ExpSimpl::Exp(CExp::Eval(box op)) => op.into(),
            ExpSimpl::Exp(e) => ExpSimpl::Exp(CExp::Coef(Box::new(e))),
            ExpSimpl::Value(_) => unimplemented!("Constant propagate FFT and IFFT"),
        }
    }

    pub fn eval(op: Self) -> Self {
        match op {
            // eval . coef p = p
            ExpSimpl::Exp(CExp::Coef(box op)) => op.into(),
            ExpSimpl::Exp(op) => ExpSimpl::Exp(CExp::Eval(Box::new(op))),
            ExpSimpl::Value(_) => unimplemented!("Constant propagate FFT and IFFT"),
        }
    }

    // TODO
    pub fn div(v1: Self, v2: Self, typ: ATyp) -> Self {
        match (v1, v2) {
            (ExpSimpl::Exp(CExp::Value(a), ExpSimpl::Exp(CExp::Value(b)) => CExp::Value(a / b))),
            (ExpSimpl::Exp(CExp::Range(l), ExpSimpl::Exp(CExp::Range(r)) => CExp::Range(l / r))),
            (ExpSimpl::Exp(CExp::Range(l)), ExpSimpl::Exp(CExp::Value(Value::Index(r))))
            | (ExpSimpl::Exp(CExp::Value(Value::Index(r))), ExpSimpl::Exp(CExp::Range(l))) =>
                ExpSimpl::Exp(CExp::Range(l / CRange::singleton(r as usize))),
            (ExpSimpl::Exp(CExp::Vec(l)), ExpSimpl::Exp(CExp::Vec(r))) => {
                let (t, _) = typ.into_vec();
                CExp::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| CExp::div(l, r, t.clone()))
                    .collect())
            },
            (ExpSimpl::Exp(CExp::Vec(l)), ExpSimpl::Exp(CExp::Range(r))) => {
                let (t, _) = typ.into_vec();
                CExp::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| CExp::div(l, r.into(), t.clone()))
                    .collect())
            },
            (ExpSimpl::Exp(CExp::Range(r)), ExpSimpl::Exp(CExp::Vec(l))) => {
                let (t, _) = typ.into_vec();
                CExp::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| CExp::div(r.into(), l, t.clone()))
                    .collect())
            },
           (ExpSimpl::Exp(CExp::Vec(l)), ExpSimpl::Exp(CExp::Value(Value::Index(r))))
            | (ExpSimpl::Exp(CExp::Value(Value::Index(r))), ExpSimpl::Exp(CExp::Vec(l))) => {
                let (t, _) = typ.into_vec();
                CExp::Vec(l.into_iter()
                    .map(|l| CExp::div(l, r.into(), t.clone()))
                    .collect())
            },
            // Commuting conversions
            (ExpSimpl::Exp(CExp::Coef(box l)), ExpSimpl::Exp(CExp::Coef(box r))) => {
                let (_, n) = typ.clone().into_vec();
                CExp::coef(CExp::div(CExp::pad_zeroes(l, n), CExp::pad_zeroes(r, n), typ))
            },
            // Default case, constructor
            (v1, v2) => ExpSimpl::Exp(CExp::Bin(BinOp::Div, Box::new(v1), Box::new(v2)), typ)
        }
    }

    pub fn rem(v1: Self, v2: Self, typ: ATyp) -> Self {
        match (v1, v2) {
            (ExpSimpl::Exp(CExp::Value(a), ExpSimpl::Exp(CExp::Value(b)) => CExp::Value(a % b))),
            (ExpSimpl::Exp(CExp::Range(l), ExpSimpl::Exp(CExp::Range(r)) => CExp::Range(l % r))),
            (ExpSimpl::Exp(CExp::Range(l)), ExpSimpl::Exp(CExp::Value(Value::Index(r))))
            | (ExpSimpl::Exp(CExp::Value(Value::Index(r))), ExpSimpl::Exp(CExp::Range(l))) =>
                ExpSimpl::Exp(CExp::Range(l % CRange::singleton(r as usize))),
            (ExpSimpl::Exp(CExp::Vec(l)), ExpSimpl::Exp(CExp::Vec(r))) => {
                let (t, _) = typ.into_vec();
                CExp::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| CExp::rem(l, r, t.clone()))
                    .collect())
            },
            (ExpSimpl::Exp(CExp::Vec(l)), ExpSimpl::Exp(CExp::Range(r))) => {
                let (t, _) = typ.into_vec();
                CExp::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| CExp::rem(l, r.into(), t.clone()))
                    .collect())
            },
            (ExpSimpl::Exp(CExp::Range(r)), ExpSimpl::Exp(CExp::Vec(l))) => {
                let (t, _) = typ.into_vec();
                CExp::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| CExp::rem(r.into(), l, t.clone()))
                    .collect())
            },
           (ExpSimpl::Exp(CExp::Vec(l)), ExpSimpl::Exp(CExp::Value(Value::Index(r))))
            | (ExpSimpl::Exp(CExp::Value(Value::Index(r))), ExpSimpl::Exp(CExp::Vec(l))) => {
                let (t, _) = typ.into_vec();
                CExp::Vec(l.into_iter()
                    .map(|l| CExp::rem(l, r.into(), t.clone()))
                    .collect())
            },
            // Commuting conversions
            (ExpSimpl::Exp(CExp::Coef(box l)), ExpSimpl::Exp(CExp::Coef(box r))) => {
                let (_, n) = typ.clone().into_vec();
                CExp::coef(CExp::rem(CExp::pad_zeroes(l, n), CExp::pad_zeroes(r, n), typ))
            },
            // Default case, constructor
            (v1, v2) => ExpSimpl::Exp(CExp::Bin(BinOp::Rem, Box::new(v1), Box::new(v2)), typ)
        }
    }

    pub fn one(typ: &ATyp) -> Op<C> {
        match typ {
            ATyp::Fin(_) => ExpSimpl::Exp(CExp::Value(Value::Index(1))),
            ATyp::Vec(box typ, n) => {
                let mut vs = vec![];
                for _ in 0..*n {
                    vs.push(CExp::one(typ));
                }
                CExp::Vec(vs)
            },
            ATyp::Scalar => ExpSimpl::Exp(CExp::Value(Value::Scalar(C::FOps::one()))),
            _ => unreachable!("UncaughtError: CExp::one() not implemented for type {}", typ),
        }
    }

    pub fn pow(v1: Self, v2: Self, typ: ATyp) -> Self {
        match v2 {
            CExp::Value(Value::Index(r)) => {
                let mut exp: u64 = r;
                let mut base = CExp::one(&typ);
                while exp > 0 {
                    if exp % 2 == 1 {
                        base = CExp::mul(v1.clone(), base.clone(), typ.clone());
                    }
                    base = CExp::mul(base.clone(), base.clone(), typ.clone());
                    exp /= 2;
                };
                base
            },
            CExp::Range(r) => {
                let (t, _) = typ.into_vec();
                CExp::Vec(r.into_iter()
                    .map(|r| CExp::pow(v1.clone(), r.into(), t.clone()))
                    .collect())
            },
            v2 => ExpSimpl::Exp(CExp::Bin(BinOp::Pow, Box::new(v1), Box::new(v2), typ)),
        }
    }

    pub fn dot(v1: Self, v2: Self, typ: ATyp) -> Self {
        match (v1, v2) {
            (ExpSimpl::Exp(CExp::Value(a), ExpSimpl::Exp(CExp::Value(b)) => CExp::Value(a.dot(b)))),
            (ExpSimpl::Exp(CExp::Range(l)), ExpSimpl::Exp(CExp::Range(r))) =>
                CExp::Value(Value::Index(
                    l.into_iter()
                    .zip(r.into_iter())
                    .map(|(a, b)| (a * b) as u64)
                    .sum())),
            (ExpSimpl::Exp(CExp::Range(l)), ExpSimpl::Exp(CExp::Value(Value::Index(r))))
            | (ExpSimpl::Exp(CExp::Value(Value::Index(r))), ExpSimpl::Exp(CExp::Range(l))) =>
                CExp::Value(Value::Index(
                    l.into_iter()
                    .map(|a| (a * r as usize) as u64)
                    .sum())),
            // Default case, constructor
            (v1, v2) => ExpSimpl::Exp(CExp::Bin(BinOp::Dot, Box::new(v1), Box::new(v2), typ)),
        }
    }

    pub fn not(v: Self) -> Op<C> {
        match v {
            CExp::Not(box v) => v,
            _ => ExpSimpl::Exp(CExp::Not(Box::new(v))),
        }
    }

    pub fn equ(v1: Self, v2: Self) -> Self {
        match (v1, v2) {
            (ExpSimpl::Exp(CExp::Range(l), ExpSimpl::Exp(CExp::Range(r)) => CExp::Value(Value::Bool(l == r)))),
            (ExpSimpl::Exp(CExp::Value(a), ExpSimpl::Exp(CExp::Value(b)) => CExp::Value(Value::Bool(a == b)))),
            (v1, v2) => ExpSimpl::Exp(CExp::Bin(BinOp::Equ, Box::new(v1), Box::new(v2), ATyp::Bool)),
        }
    }

    pub fn and(v1: Self, v2: Self) -> Self {
        match (v1, v2) {
            (ExpSimpl::Exp(CExp::Value(Value::Bool(false))), _)
            | (_, ExpSimpl::Exp(CExp::Value(Value::Bool(false))) => CExp::bfalse()),
            (ExpSimpl::Exp(CExp::Value(a), ExpSimpl::Exp(CExp::Value(b)) => CExp::Value(a & b))),
            (v1, v2) => ExpSimpl::Exp(CExp::Bin(BinOp::And, Box::new(v1), Box::new(v2), ATyp::Bool)),
        }
    }

    pub fn btrue() -> Self {
        CExp::Value(Value::Bool(true))
    }
    pub fn bfalse() -> Self {
        CExp::Value(Value::Bool(false))
    }

    pub fn or(v1: Self, v2: Self) -> Self {
        match (v1, v2) {
            (ExpSimpl::Exp(CExp::Value(Value::Bool(true))), _)
            | (_, ExpSimpl::Exp(CExp::Value(Value::Bool(true))) => CExp::btrue()),
            (ExpSimpl::Exp(CExp::Value(a), ExpSimpl::Exp(CExp::Value(b)) => CExp::Value(a | b))),
            (v1, v2) => ExpSimpl::Exp(CExp::Bin(BinOp::Or, Box::new(v1), Box::new(v2), ATyp::Bool)),
        }
    }

    pub fn contains(v1: Self, v2: Self) -> Self {
        match (v1, v2) {
            (ExpSimpl::Exp(CExp::Range(l)), ExpSimpl::Exp(CExp::Value(Value::Index(r)))) =>
                ExpSimpl::Exp(CExp::Value(Value::Bool(l.contains(r as usize)))),
            (ExpSimpl::Exp(CExp::Vec(vs)), v2) =>
                vs.iter().map(|v| CExp::equ(v.clone(), v2.clone()))
                    .reduce(|a, b| CExp::or(a, b))
                    .unwrap_or(ExpSimpl::Exp(CExp::Value(Value::Bool(false)))),
            (v1, v2) => ExpSimpl::Exp(CExp::Bin(BinOp::Contains, Box::new(v1), Box::new(v2), ATyp::Bool)),
        }
    }

    pub fn vec(vs: Vec<Op<C>>) -> Op<C> {
        CExp::Vec(vs)
    }
    pub fn underscore(n: &NodeIndex, typ: ATyp) -> Op<C> {
        CExp::Underscore(*n, typ)
    }
    pub fn var(v: &Vid, n: &NodeIndex, typ: ATyp) -> Op<C> {
        ExpSimpl::Exp(CExp::Var(v.clone()), *n, typ)
    }
    pub fn range(r: CRange) -> Op<C> {
        CExp::Range(r)
    }

    pub fn challenge(typ: ATyp) -> Op<C> {
        CExp::Challenge(typ)
    }
    pub fn random(typ: ATyp) -> Op<C> {
        CExp::Random(typ)
    }
    pub fn hash(op: Op<C>) -> Op<C> {
        CExp::Hash(Box::new(op))
    }

    pub fn check(op: Op<C>) -> Op<C> {
        CExp::Check(Box::new(op))
    }

    pub fn edges(&self) -> Vec<(NodeIndex, Edge)> {
        match self {
            CExp::Underscore(n, _) => vec![(*n, Edge::data())],
            CExp::Bin(_, box a, box b, _)
            | CExp::Ram(box a, box b) =>
                a.edges().into_iter()
                    .chain(b.edges().into_iter())
                    .collect(),
            CExp::Var(v, n, _) => vec![(*n, Edge::var(v.clone()))],
            CExp::Vec(vs) =>
                vs.into_iter()
                    .flat_map(|v| v.edges())
                    .collect(),
            CExp::Not(box v)
            | CExp::Coef(box v)
            | CExp::Check(box v)
            | CExp::Hash(box v)
            | ExpSimpl::Exp(CExp::Eval(box v) => v.edges()),
            CExp::Value(_)
            | CExp::Gen(_)
            | CExp::Random(_)
            | CExp::Challenge(_)
            | CExp::Range(_) => vec![],
        }
    }
}
