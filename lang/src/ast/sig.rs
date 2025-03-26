use crate::typ::{TTyp, Size, Kind, CTyp, TypeVars, CTyps, Range, RangeTraversal};
use crate::typ::subst::AliasSubsts;
use crate::typ::unify::{Unify, UnifyError};
use crate::ast::{Arg, Args, ExpSubst};
use share::{Pretty, Set, Ctx, DocAllocator, DocBuilder, BoxAllocator};
use share::traversal::{ToTraversal1, ToTraversal2};
use crate::id::{Gen, Vid, Fid, Tid, TidSubst};
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
    pub typevars: TypeVars,
    pub args: Args<N>,
    pub ret: TTyp<N>
}

/// Symbolic sized signature
pub type USig = Sig<Size>;

/// Concrete sized signature
pub type CSig = Sig<usize>;

impl CSig {
    pub fn unify(self, typs: &CTyps, kctx: &Ctx<Tid, Kind>) -> Result<(CSig, AliasSubsts), SigError> {
        // Check arity first
        if self.args.len() != typs.len() {
            return Err(SigError::ArityMismatch(self.args.len(), typs.len()));
        }

        // New substitutions context
        let mut subs = AliasSubsts::new();

        // If any type vars are captured by [kctx], shift them
        let keys = kctx.keys();
        let mut shifted = self.clone();
        for id in kctx.keys() {
            shifted.tid_subst(&id, &Tid::gen(&id, &keys));
        }

        // New kind context for type vars, after shifting we know there will be no conflicts
        let kind_ctx = shifted.typevars.to_ctx().union(&kctx);

        // Unification of arguments and parameters
        let mut args = Vec::new();
        for (l, r) in shifted.args.iter().zip(typs.iter()) {
            let typ = CTyp::unify(l.typ.clone(), r.clone(), &kind_ctx, &mut subs)
                    .map_err(|e| SigError::Unify(shifted.clone(), typs.clone(), e))?;
            args.push(Arg { qualifier: l.qualifier.clone(), id: l.id.clone(), typ });
        }

        // Substitute alias in the return type and typevars
        subs.tid_subst(&mut shifted);

        Ok((shifted, subs))
    }
}

/// Traversable1 instance for Sig (N)
impl<N> ToTraversal1<N> for Sig<N> {
    type Output<Z> = Sig<Z>;
    fn traverse1<Z, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Sig<Z>, E> {
        let Sig { name, typevars, args, ret } = self;
        Ok(Sig { name, typevars, args: args.traverse1(f)?, ret: ret.traverse2(f)? })
    }
}

impl<N> TidSubst for Sig<N> {
    fn tid_subst(&mut self, from: &Tid, to: &Tid) {
        self.typevars.tid_subst(from, to);
        self.args.tid_subst(from, to);
        self.ret.tid_subst(from, to);
    }
}

impl<N> RangeTraversal<N> for Sig<N> {
    fn range_traverse<E>(self, f: &mut dyn FnMut(Range<N>) -> Result<Range<N>, E>) -> Result<Self, E> {
        Ok(Sig { name: self.name, typevars: self.typevars, args: self.args.range_traverse(f)?, ret: self.ret.range_traverse(f)? })
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
            self.name.pretty(allocator),
            allocator.text("<"),
            self.typevars.pretty(allocator),
            allocator.text(">"),
            allocator.text("("),
            self.args.pretty(allocator),
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
