use crate::typ::{Kind, CTyp, Typs, CTyps};
use crate::typ::subst::AliasSubsts;
use crate::typ::unify::{Unify, UnifyError};
use share::{Pretty, Ctx, DocAllocator, DocBuilder, BoxAllocator};
use crate::id::{Tid, TidTraversal};
use std::fmt;
use thiserror::Error;

#[derive(PartialEq, Error, Debug)]
pub enum SigError {
    #[error("SigError: Arity mismatch: expected {0} got {1}")]
    ArityMismatch(Sig, CTyps),
    #[error("SigError: Unifying signatures {0} ~ {1}\n\n{2}")]
    Unify(Sig, CTyps, UnifyError)
}

/// Function and protocol argument signatures
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub struct Sig {
    pub args: CTyps,
    pub ret: CTyp
}

impl Sig {
    pub fn len(&self) -> usize {
        self.args.len()
    }
    pub fn unify_typs(self, typs: CTyps, ctx: &Ctx<Tid, Kind>, subs: &mut AliasSubsts) -> Result<Sig, SigError> {

        if self.args.len() != typs.len() {
            return Err(SigError::ArityMismatch(self, typs));
        }

        let mut args = Vec::new();
        for (l, r) in self.args.iter().zip(typs.iter()) {
            args.push(CTyp::unify(l.clone(), r.clone(), ctx, subs)
                .map_err(|e| SigError::Unify(self.clone(), typs.clone(), e))?);
        }

        // Substitute alias in the return type
        let ret = self.ret.tid_traverse(&mut |id| Ok(subs.get_repr(&id).unwrap_or(id)))?;
        Ok(Sig { args: Typs(args), ret })
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
        allocator.concat([
            allocator.text("("),
            allocator.intersperse(self.args.iter().map(|a| a.clone().pretty(allocator)),", "),
            allocator.text(") -> "),
            self.ret.pretty(allocator)
        ])
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
