use crate::typ::{Kind, CTyp};
use crate::typ::subst::AliasSubsts;
use crate::typ::unify::{Unify, UnifyError};
use share::{Pretty, Ctx, DocAllocator, DocBuilder, BoxAllocator};
use crate::id::Tid;
use std::fmt;
use thiserror::Error;

#[derive(PartialEq, Error, Debug)]
pub enum SigError {
    #[error("Arity mismatch: expected {0} arguments, got {1}")]
    ArityMismatch(usize, usize),
    #[error(transparent)]
    Unify(#[from] UnifyError)
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

    pub fn ret(&self) -> &CTyp {
        match self {
            Sig::Func { ret, .. } => ret,
            _ => &CTyp::Bool
        }
    }

    pub fn unify_all(self, v: Vec<CTyp>, ctx: &Ctx<Tid, Kind>, subs: &mut AliasSubsts) -> Result<Self, SigError> {
        let args = self.args();
        if args.len() != v.len() {
            return Err(SigError::ArityMismatch(args.len(), v.len()));
        }

        let mut res = Vec::new();
        for (l, r) in args.iter().zip(v.iter()) {
            res.push(CTyp::unify_equ(l.clone(), r.clone(), ctx, subs)?);
        }
        match self {
            Sig::Func { ret, .. } => Ok(Sig::Func { args: res, ret }),
            Sig::Proto { .. } => Ok(Sig::Proto { args: res })
        }
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
