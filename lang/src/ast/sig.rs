use crate::ast::GArgs;
use crate::ast::Size;
use crate::ast::spanned::Spanned;
use crate::id::{Fresh, Tid, TidSubst, Vid};
use crate::typ::subst::AliasSubsts;
use crate::typ::unify::{Unify, UnifyError};
use crate::typ::{CKind, CTyp, CTyps, GTyp, Range, RangeTraversal, TypeInline, TypeVars};
use share::Ctx;
use share::traversal::{ToTraversal1, ToTraversal2};
use std::fmt;
use thiserror::Error;

/// Failure of matching a call site against a declaration signature.
#[derive(PartialEq, Error, Debug)]
#[allow(clippy::large_enum_variant)]
pub enum SigError {
    /// The call supplies a different number of arguments than the signature
    /// declares; carries `(expected, got)`.
    #[error("SigError: Arity mismatch: expected {0} arguments, got {1}")]
    ArityMismatch(usize, usize),
    /// Unifying the signature's parameter types with the actual argument
    /// types failed; carries the signature, the actual types and the
    /// underlying `UnifyError`.
    #[error("SigError: Unifying signatures {0} ~ {1}\n\n{2}")]
    Unify(CSig, CTyps, UnifyError),
}

/// Function and protocol argument signatures
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Sig<N> {
    /// Declared name of the function or protocol; also the overload key.
    pub name: Spanned<Vid>,
    /// Type variables bound by the declaration, with their kinds — size
    /// variables, range-kinded variables, field/group tags.
    pub typevars: Spanned<TypeVars<N>>,
    /// Formal parameters, in declaration order.
    pub args: Spanned<GArgs<N>>,
    /// Declared return type; `None` when the declaration leaves it implicit.
    pub ret: Option<Spanned<GTyp<N>>>,
}

/// Symbolic sized signature
pub type USig = Sig<Size>;

/// Concrete sized signature
pub type CSig = Sig<usize>;

impl CSig {
    /// Resolve this signature against the actual argument types of a call.
    ///
    /// Type variables captured by `kctx` are first freshened so a caller's
    /// names cannot collide with the declaration's own. Each parameter type
    /// is then unified with the corresponding actual type under the union of
    /// the signature's own kind context and `kctx`, and the resulting alias
    /// substitution is applied to the signature. Returns the instantiated
    /// signature together with those substitutions, which overload
    /// resolution uses to pick between declarations of the same name.
    ///
    /// # Errors
    /// Returns `SigError::ArityMismatch` if the argument count differs from
    /// the declared arity, and `SigError::Unify` if some parameter type
    /// fails to unify with the corresponding actual type.
    pub fn unify(
        self,
        typs: &CTyps,
        kctx: &Ctx<Tid, CKind>,
    ) -> Result<(CSig, AliasSubsts), SigError> {
        // Check arity first
        if self.args.node.len() != typs.len() {
            return Err(SigError::ArityMismatch(self.args.node.len(), typs.len()));
        }

        // New substitutions context
        let mut subs = AliasSubsts::new();

        // If any type vars are captured by [kctx], shift them
        let mut keys = kctx.keys();
        let mut shifted = self.clone();
        for id in kctx.keys() {
            shifted.tid_subst(&id, &Tid::fresh(&id.0, &mut keys));
        }

        let kind_ctx = shifted.typevars.node.to_ctx().union(kctx);

        // Unification of arguments and parameters
        for (l, r) in shifted.args.node.iter().zip(typs.iter()) {
            CTyp::unify(&l.typ.node, r, &kind_ctx, &mut subs)
                .map_err(|e| SigError::Unify(shifted.clone(), typs.clone(), e))?;
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
            ret: ret.map(|r| r.traverse2(f)).transpose()?,
        })
    }
}

impl<N: Clone> TidSubst for Sig<N> {
    fn tid_subst(&mut self, from: &Tid, to: &Tid) {
        self.typevars.node.tid_subst(from, to);
        self.args.node.tid_subst(from, to);
        if let Some(ret) = &mut self.ret {
            ret.node.tid_subst(from, to);
        }
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
            ret: self.ret.map(|r| r.range_traverse(f)).transpose()?,
        })
    }
}

impl<N: Clone> TypeInline<N> for Sig<N> {
    fn type_inline(self, ctx: &Ctx<Tid, GTyp<N>>) -> Self {
        Sig {
            name: self.name,
            typevars: self.typevars,
            args: self.args.type_inline(ctx),
            ret: self.ret.map(|r| r.type_inline(ctx)),
        }
    }
}

/// `name<typevars>(args)[ -> ret]`
impl<N: fmt::Display> fmt::Display for Sig<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}<{}>({})", self.name, self.typevars, self.args)?;
        if let Some(ret) = &self.ret {
            write!(f, " -> {ret}")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::parser::parse_decls;
    use crate::typ::{CKind, CTyp, Typs};
    use share::Ctx;

    fn make_csig(decl_str: &str) -> CSig {
        let (mut decls, errors) = parse_decls(decl_str);
        assert!(errors.is_empty(), "parse errors: {:?}", errors);
        let udecl = decls.pop().map(|s| s.node).unwrap();
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
        let typs = Typs(vec![Spanned::dummy(arg_typ.clone())]);

        let mut kctx = Ctx::new();
        kctx.insert(&t_f, &CKind::Field);

        let res = sig.unify(&typs, &kctx);
        assert!(res.is_ok());

        let (unified_sig, _subs) = res.unwrap();
        assert_eq!(
            unified_sig.ret.as_ref().map(|r| &r.node),
            Some(&arg_typ.clone())
        );
        assert_eq!(unified_sig.args.node.0[0].typ.node, arg_typ);
    }

    #[test]
    fn test_sig_unify_arity_mismatch() {
        let sig = make_csig("fn foo<T: Field>(instance x: T) -> T { x }");
        let kctx = Ctx::new();
        let res = sig.clone().unify(&Typs(vec![]), &kctx);
        assert_eq!(res, Err(SigError::ArityMismatch(1, 0)));

        let t_f = Tid::from("F");
        let res2 = sig.unify(
            &Typs(vec![
                Spanned::dummy(CTyp::base(&t_f)),
                Spanned::dummy(CTyp::base(&t_f)),
            ]),
            &kctx,
        );
        assert_eq!(res2, Err(SigError::ArityMismatch(1, 2)));
    }

    #[test]
    fn test_sig_unify_type_mismatch() {
        let sig = make_csig("fn foo<T: Group>(instance x: T) -> T { x }");

        let t_f = Tid::from("F");
        let arg_typ = CTyp::base(&t_f);
        let typs = Typs(vec![Spanned::dummy(arg_typ.clone())]);

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
        assert_eq!(
            sig.ret.as_ref().map(|r| r.node.clone()),
            Some(CTyp::base(&Tid::from("U")))
        );

        let display_str = sig.to_string();
        assert!(display_str.contains("foo"));
        assert!(display_str.contains("<U: Field>"));
    }
}
