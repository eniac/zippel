use crate::typ::{Typ, Size, Kind, CTyp, Typs, CTyps, Range, RangeTraversal};
use crate::typ::subst::AliasSubsts;
use crate::typ::unify::{Unify, UnifyError};
use crate::module::{Arg, Args};
use share::{Pretty, Ctx, DocAllocator, DocBuilder, BoxAllocator};
use share::traversal::ToTraversal1;
use crate::id::{Fid, Tid, TidTraversal};
use std::fmt;
use thiserror::Error;

#[derive(PartialEq, Error, Debug)]
pub enum SigError {
    #[error("SigError: Arity mismatch: expected {0} arguments, got {1}")]
    ArityMismatch(usize, usize),
    #[error("SigError: Unifying signatures {0} ~ {1}\n\n{2}")]
    Unify(CSig, CTyps, UnifyError)
}

/// Function and protocol argument signatures
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub struct Sig<N> {
    pub name: Fid,
    pub args: Args<N>,
    pub ret: Typ<N>
}

/// Symbolic sized signature
pub type USig = Sig<Size>;

/// Concrete sized signature
pub type CSig = Sig<usize>;

impl CSig {
    pub fn unify(self, typs: &CTyps, ctx: &Ctx<Tid, Kind>, subs: &mut AliasSubsts) -> Result<CSig, SigError> {
        if self.args.len() != typs.len() {
            return Err(SigError::ArityMismatch(self.args.len(), typs.len()));
        }

        let mut args = Vec::new();
        for (l, r) in self.args.iter().zip(typs.iter()) {
            let typ = CTyp::unify(l.typ.clone(), r.clone(), ctx, subs)
                    .map_err(|e| SigError::Unify(self.clone(), typs.clone(), e))?;
            args.push(Arg { qualifier: l.qualifier.clone(), id: l.id.clone(), typ });
        }

        // Substitute alias in the return type
        let ret = self.ret.tid_traverse(&mut |id| Ok(subs.get_repr(&id).unwrap_or(id)))?;

        Ok(Sig { name: self.name, args: Args(args), ret })
    }
}

/// Traversable1 instance for Sig (N)
impl<N> ToTraversal1<N> for Sig<N> {
    type Output<Z> = Sig<Z>;
    fn traverse1<Z, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Sig<Z>, E> {
        let Sig { name, args, ret } = self;
        Ok(Sig { name, args: args.traverse1(f)?, ret: ret.traverse1(f)? })
    }
}

impl<N> RangeTraversal<N> for Sig<N> {
    fn range_traverse<E>(self, f: &mut dyn FnMut(Range<N>) -> Result<Range<N>, E>) -> Result<Self, E> {
        Ok(Sig { name: self.name, args: self.args.range_traverse(f)?, ret: self.ret.range_traverse(f)? })
    }
}

/// Pretty-printer for function signature
impl<'a, D, A, N> Pretty<'a, D, A> for Sig<N>
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    N: Pretty<'a, D, A> + Clone + 'a,
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

impl<'a, N: Pretty<'a, BoxAllocator, ()> + Clone + 'a> fmt::Display for Sig<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Sig<N> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}
