use crate::lang::{AExp, BExp, Exp};

/// Cost represents the runtime and memory cost of running
/// a zippel expression.
pub trait Cost {
    fn runtime(&self, num_thread: usize) -> f64;
    fn memory(&self, num_thread: usize) -> f64;
}

/// Cost instance for AExp
impl<N, A> Cost for AExp<N, A> {
    fn runtime(&self, num_thread: usize) -> f64 {
        let fnum_thread = num_thread as f64;
        match self {
            AExp::Lit(_, _) => 1.0,
            AExp::Var(_, _) => 2.0,
            AExp::Bin(_, _, _, _) => (30.0 + (50.0 / fnum_thread)),
            AExp::Coef(_, _) => (40.0 + (50.0 / fnum_thread)),
            AExp::Mle(_, _) => (40.0 + (50.0 / fnum_thread)),
            AExp::App(_, _, _) => (50.0 + (50.0 / fnum_thread)),
            AExp::Vec(_, _) => (60.0 + (50.0 / fnum_thread)),
            AExp::Map(_, _, _, _) => (70.0 + (50.0 / fnum_thread)),
            AExp::Concat(_, _, _) => (80.0 + (50.0 / fnum_thread)),
            AExp::Reduce(_, _, _) => (90.0 + (50.0 / fnum_thread)),
            AExp::Random(_, _) => (100.0 + (50.0 / fnum_thread)),
            AExp::Challenge(_, _) => (100.0 + (50.0 / fnum_thread)),
            AExp::Gen(_, _) => (100.0 + (50.0 / fnum_thread)),
            AExp::Interpolate(_, _, _) => (110.0 + (50.0 / fnum_thread)),
            AExp::Index(_, _, _) => (120.0 + (50.0 / fnum_thread)),
            AExp::Let(_, _, _, _) => (130.0 + (50.0 / fnum_thread)),
            AExp::Log(_, _, _, _) => (140.0 + (50.0 / fnum_thread)),
            AExp::Assert(_, _, _) => (150.0 + (50.0 / fnum_thread)),
            AExp::Range(_, _) => (150.0 + (50.0 / fnum_thread)),
        }
    }

    fn memory(&self, num_thread: usize) -> f64 {
        unimplemented!()
    }
}

/// Cost instance for BExp
impl<T> Cost for BExp<T> {
    fn runtime(&self, num_thread: usize) -> f64 {
        let fnum_thread = num_thread as f64;
        match self {
            BExp::Contains(_, _) => 20.0,
            BExp::And(_, _) => 12.0,
            BExp::Or(_, _) => 13.0,
            BExp::Eq(_, _) => 14.0,
            BExp::App(_, _) => 15.0,
        }
    }
    fn memory(&self, num_thread: usize) -> f64 {
        unimplemented!()
    }
}

impl<T> Cost for Exp<T> {
    fn runtime(&self, num_thread: usize) -> f64 {
        match self {
            Exp::A(aexp) => aexp.runtime(num_thread),
            Exp::B(bexp) => bexp.runtime(num_thread),
        }
    }

    fn memory(&self, num_thread: usize) -> f64 {
        match self {
            Exp::A(aexp) => aexp.memory(num_thread),
            Exp::B(bexp) => bexp.memory(num_thread),
        }
    }
}
