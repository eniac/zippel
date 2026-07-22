use crate::ast::{GArg, GArgs};
use crate::id::{Fresh, Tid, TidSubst, Vid};
use crate::typ::subst::AliasSubsts;
use crate::typ::unify::{Unify, UnifyError};
use crate::typ::{CKind, CTyp, CTyps, GTyp, Range, RangeTraversal, Size, TypeInline, TypeVars};
use share::traversal::{ToTraversal1, ToTraversal2};
use share::{BoxAllocator, Ctx, DocAllocator, DocBuilder, Pretty};
use std::fmt;
use thiserror::Error;

#[derive(PartialEq, Error, Debug)]
#[allow(clippy::large_enum_variant)]
pub enum SigError {
    #[error("SigError: Arity mismatch: expected {0} arguments, got {1}")]
    ArityMismatch(usize, usize),
    #[error("SigError: Unifying signatures {0} ~ {1}\n\n{2}")]
    Unify(CSig, CTyps, UnifyError),
}

/// Function and protocol argument signatures
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub struct Sig<N> {
    pub name: Vid,
    pub typevars: TypeVars<N>,
    pub args: GArgs<N>,
    pub ret: GTyp<N>,
}

/// Symbolic sized signature
pub type USig = Sig<Size>;

/// Concrete sized signature
pub type CSig = Sig<usize>;

impl CSig {
    pub fn unify(
        self,
        typs: &CTyps,
        kctx: &Ctx<Tid, CKind>,
    ) -> Result<(CSig, AliasSubsts), SigError> {
        // Check arity first
        if self.args.len() != typs.len() {
            return Err(SigError::ArityMismatch(self.args.len(), typs.len()));
        }

        // New substitutions context
        let mut subs = AliasSubsts::new();

        // If any type vars are captured by [kctx], shift them
        let mut keys = kctx.keys();
        let mut shifted = self.clone();
        for id in kctx.keys() {
            shifted.tid_subst(&id, &Tid::fresh(&id.0, &mut keys));
        }

        let kind_ctx = shifted.typevars.to_ctx().union(kctx);

        // Unification of arguments and parameters
        let mut args = Vec::new();
        for (l, r) in shifted.args.iter().zip(typs.iter()) {
            let typ = CTyp::unify(&l.typ, r, &kind_ctx, &mut subs)
                .map_err(|e| SigError::Unify(shifted.clone(), typs.clone(), e))?;
            args.push(GArg {
                qualifier: l.qualifier,
                distribution: l.distribution,
                id: l.id.clone(),
                typ,
            });
        }

        // Substitute alias in the return type and typevars
        subs.tid_subst(&mut shifted);

        Ok((shifted, subs))
    }
}

/// Traversable1 instance for Sig (N)
impl<N: Clone> ToTraversal1<N> for Sig<N> {
    type Output<Z> = Sig<Z>;
    fn traverse1<Z: Clone, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Sig<Z>, E> {
        let Sig {
            name,
            typevars,
            args,
            ret,
        } = self;
        Ok(Sig {
            name,
            typevars: typevars.traverse1(f)?,
            args: args.traverse2(f)?,
            ret: ret.traverse2(f)?,
        })
    }
}

impl<N: Clone> TidSubst for Sig<N> {
    fn tid_subst(&mut self, from: &Tid, to: &Tid) {
        self.typevars.tid_subst(from, to);
        self.args.tid_subst(from, to);
        self.ret.tid_subst(from, to);
    }
}

impl<N: Clone> RangeTraversal<N> for Sig<N> {
    fn range_traverse<E>(
        self,
        f: &mut dyn FnMut(Range<N>) -> Result<Range<N>, E>,
    ) -> Result<Self, E> {
        Ok(Sig {
            name: self.name,
            typevars: self.typevars.range_traverse(f)?,
            args: self.args.range_traverse(f)?,
            ret: self.ret.range_traverse(f)?,
        })
    }
}

impl<N: Clone> TypeInline<N> for Sig<N> {
    fn type_inline(self, ctx: &Ctx<Tid, GTyp<N>>) -> Self {
        Sig {
            name: self.name,
            typevars: self.typevars,
            args: self.args.type_inline(ctx),
            ret: self.ret.type_inline(ctx),
        }
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
            self.ret.pretty(allocator),
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::decl::Decl;
    use crate::typ::{CKind, CTyp, Typs};
    use share::Ctx;

    fn make_csig(decl_str: &str) -> CSig {
        let udecl = Decl::from_str(decl_str).unwrap();
        let cdecl = udecl
            .concretize(&crate::typ::subst::SizeSubsts::new())
            .unwrap();
        cdecl.sig
    }

    #[test]
    fn test_sig_unify_success() {
        let sig = make_csig("fn foo<T: Field>(instance x: T) -> T { x }");

        let t_f = Tid::from("F");
        let arg_typ = CTyp::base(&t_f);
        let typs = Typs(vec![arg_typ.clone()]);

        let mut kctx = Ctx::new();
        kctx.insert(&t_f, &CKind::Field);

        let res = sig.unify(&typs, &kctx);
        assert!(res.is_ok());

        let (unified_sig, _subs) = res.unwrap();
        assert_eq!(unified_sig.ret, arg_typ);
        assert_eq!(unified_sig.args.0[0].typ, arg_typ);
    }

    #[test]
    fn test_sig_unify_arity_mismatch() {
        let sig = make_csig("fn foo<T: Field>(instance x: T) -> T { x }");
        let kctx = Ctx::new();
        let res = sig.clone().unify(&Typs(vec![]), &kctx);
        assert_eq!(res, Err(SigError::ArityMismatch(1, 0)));

        let t_f = Tid::from("F");
        let res2 = sig.unify(&Typs(vec![CTyp::base(&t_f), CTyp::base(&t_f)]), &kctx);
        assert_eq!(res2, Err(SigError::ArityMismatch(1, 2)));
    }

    #[test]
    fn test_sig_unify_type_mismatch() {
        let sig = make_csig("fn foo<T: Group>(instance x: T) -> T { x }");

        let t_f = Tid::from("F");
        let arg_typ = CTyp::base(&t_f);
        let typs = Typs(vec![arg_typ.clone()]);

        let mut kctx = Ctx::new();
        kctx.insert(&t_f, &CKind::Field);

        let res = sig.unify(&typs, &kctx);
        assert!(res.is_err());
        assert!(matches!(res.unwrap_err(), SigError::Unify(_, _, _)));
    }

    #[test]
    fn test_sig_helpers() {
        let mut sig = make_csig("fn foo<T: Field>(instance x: T) -> T { x }");
        sig.tid_subst(&Tid::from("T"), &Tid::from("U"));
        assert_eq!(sig.ret, CTyp::base(&Tid::from("U")));

        let display_str = sig.to_string();
        assert!(display_str.contains("foo"));
        assert!(display_str.contains("<U: Field>"));
    }
}
