use crate::ast::GArgs;
use crate::ast::Size;
use crate::ast::spanned::Spanned;
use crate::id::{Tid, TidSubst, Vid};
use crate::typ::unify::UnifyError;
use crate::typ::{CKind, CTyp, GTyp, Range, RangeTraversal, TypeInline, TypeVars};
use share::Ctx;
use share::traversal::{ToTraversal1, ToTraversal2};
use std::fmt;
use thiserror::Error;

/// Why a call does not fit a signature. Type parameters are named as declared.
#[derive(PartialEq, Error, Debug)]
#[allow(clippy::large_enum_variant)]
pub enum SigError {
    /// Carries `(expected, got)`.
    #[error("it takes {0} argument{}, but got {1}", if *.0 == 1 { "" } else { "s" })]
    ArityMismatch(usize, usize),
    /// Argument `index` (from 0) does not fit its parameter type.
    #[error("argument {} has type {found}, which does not fit {expected}", index + 1)]
    Mismatch {
        index: usize,
        expected: CTyp,
        found: CTyp,
        cause: UnifyError,
    },
    /// A type parameter has no solution.
    #[error("type parameter `{param}` ({kind}) {reason}")]
    Uninferable {
        param: Tid,
        kind: CKind,
        reason: Uninferable,
    },
    /// A type parameter's solution violates its kind under the other solutions.
    #[error("type parameter `{param}` ({kind}) cannot be `{bound_to}`")]
    KindUnsatisfied {
        param: Tid,
        kind: CKind,
        bound_to: Tid,
    },
}

/// Why a type parameter has no solution, as a predicate on the parameter.
#[derive(PartialEq, Error, Debug, Clone)]
pub enum Uninferable {
    /// No argument type mentions it and its kind does not determine it.
    #[error("appears in no argument type")]
    Undetermined,
    /// Its kind refers to this parameter, which is itself unsolved.
    #[error("depends on `{0}`, which appears in no argument type")]
    DependsOn(Tid),
    /// No caller type has the kind it requires (in caller names).
    #[error("must be a type of kind {0}, but none is in scope")]
    NoMatch(CKind),
    /// Several caller types have the kind it requires.
    #[error("could be {}", one_of(.0))]
    Ambiguous(Vec<Tid>),
}

/// "`A`, `B` or `C`".
fn one_of(ts: &[Tid]) -> String {
    let names: Vec<String> = ts.iter().map(|t| format!("`{t}`")).collect();
    match names.split_last() {
        Some((last, rest)) if !rest.is_empty() => format!("{} or {last}", rest.join(", ")),
        _ => names.concat(),
    }
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
    fn map_tids(&mut self, f: &dyn Fn(&Tid) -> Option<Tid>) {
        self.typevars.node.map_tids(f);
        self.args.node.map_tids(f);
        if let Some(ret) = &mut self.ret {
            ret.node.map_tids(f);
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
    fn test_sig_display() {
        let sig = make_csig("fn foo<T: Field>(instance x: T) -> T { x }");
        let display_str = sig.to_string();
        assert!(display_str.contains("foo"));
        assert!(display_str.contains("<T: Field>"));
    }
}
