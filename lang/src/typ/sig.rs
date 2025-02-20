use crate::typ::{Kind, CTyp};
use crate::typ::lub::{Lub, ArithmeticTypeError};
use share::{Pretty, Ctx, DocAllocator, DocBuilder, BoxAllocator};
use crate::id::Tid;
use std::fmt;
use thiserror::Error;

#[derive(PartialEq, Error, Debug)]
pub enum SigError {
    #[error("Arity mismatch: expected {0} arguments, got {1} in {2}")]
    ArityMismatch(usize, usize, Sig),
    #[error(transparent)]
    ArithmeticError(#[from] ArithmeticTypeError)
}

/// Function and protocol signatures
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub enum Sig {
    Func { args: Vec<CTyp>, ret: CTyp },
    Proto { args: Vec<CTyp> }
}

impl Sig {
    pub fn func(args: Vec<CTyp>, ret: CTyp) -> Self {
        Sig::Func { args, ret }
    }

    pub fn proto(args: Vec<CTyp>) -> Self {
        Sig::Proto { args }
    }

    pub fn args(&self) -> &Vec<CTyp> {
        match self {
            Sig::Func { args, .. } => args,
            Sig::Proto { args } => args
        }
    }

    pub fn lub_all(self, v: Vec<CTyp>, ctx: &Ctx<Tid, Kind>) -> Result<Vec<CTyp>, SigError> {
        let args = self.args();
        if args.len() != v.len() {
            return Err(SigError::ArityMismatch(args.len(), v.len(), self));
        }

        let mut res = Vec::new();
        for (l, r) in args.iter().zip(v.iter()) {
            res.push(CTyp::lub_equ(l.clone(), r.clone(), ctx)?);
        }
        Ok(res)
    }
}

/// Pretty-printer for function signature
impl<'a, D, A> Pretty<'a, D, A> for Sig
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        match self {
            Sig::Func { args, ret } => allocator.concat([
                allocator.text("Fn("),
                allocator.intersperse(
                    args.iter().map(|a| a.clone().pretty(allocator)),
                    allocator.text(", ")),
                allocator.text(") -> "),
                ret.pretty(allocator)
            ]),
            Sig::Proto { args } => allocator.concat([
                allocator.text("Proto("),
                allocator.intersperse(
                    args.iter().map(|a| a.clone().pretty(allocator)),
                    allocator.text(", ")),
                allocator.text(")")
            ])
        }
    }

    fn is_nil(&self) -> bool {
        false
    }
}

impl fmt::Display for Sig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Sig as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}
