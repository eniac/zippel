use bumpalo::Bump;
use std::fmt;
use thiserror::Error;

use crate::ast::{CSig, Exp, FreeVars, GArgs, Sig};
use crate::id::{Tid, TidSubst, Vid};
use crate::typ::infer::{TypeError, Typeable};
use crate::typ::lub::Lub;
use crate::typ::subst::SubstError;
use crate::typ::{
    CKind, CTyp, EvalError, GTyp, Range, RangeError, RangeTraversal, Size, SizeSubsts, TypeInline,
    TypeVars,
};
use share::traversal::ToTraversal1;
use share::{BoxAllocator, Ctx, DocAllocator, DocBuilder, Pretty, Set};

/// Body of Zippel declarations (protocols, functions, and type aliases).
/// Specs are given either by an explicit relation on inputs (precondition)
/// or by the return type of the function.
/// Parametrized by `N` the type of sizes and `T` the type of types.
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub enum Body<N> {
    /// A protocol body declaration
    ///
    /// # fields
    /// - `body`: The body of the protocol.
    /// - `relation`: The relation describing the protocol — a single
    ///   expression from the `where` clause, structured as
    ///   `Let(r, val, seq(Assert(a, b), seq(Assert(c, d), Unit)))`.
    ///   Let-bindings are evaluated once and shared by all constraints.
    Proto { body: Exp<N>, relation: Exp<N> },

    /// A function body declaration
    ///
    /// # fields
    /// - `body`: The body of the function.
    Func { body: Exp<N> },

    /// A type alias declaration (e.g., `type Point = { x: F, y: F };`)
    /// The aliased type is stored in the Sig's return type.
    TypeAlias,
}

/// A zippel declaration is either a protocol or a function.
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Decl<N> {
    pub sig: Sig<N>,
    pub body: Body<N>,
}

#[derive(Error, PartialEq, Debug)]
pub enum DeclError {
    #[error("DeclError: Error evaluating size type variables: \n\n{0}")]
    EvalError(#[from] EvalError),
    #[error("DeclError: Invalid ranges in declaration {0}: \n\n{1}")]
    InvalidRange(CSig, RangeError),
    #[error("DeclError: {0}")]
    SubstError(#[from] SubstError),
}

impl<N> Body<N> {
    pub fn is_proto(&self) -> bool {
        matches!(self, Body::Proto { .. })
    }

    pub fn is_func(&self) -> bool {
        matches!(self, Body::Func { .. })
    }

    pub fn is_type_alias(&self) -> bool {
        matches!(self, Body::TypeAlias)
    }

    pub fn body(self) -> Exp<N> {
        match self {
            Body::Proto { body, .. } => body,
            Body::Func { body } => body,
            Body::TypeAlias => panic!("TypeAlias has no body"),
        }
    }
    pub fn relation(self) -> Option<Exp<N>> {
        match self {
            Body::Proto { relation, .. } => Some(relation),
            _ => None,
        }
    }
}

impl FreeVars for CBody {
    fn freevars(&self) -> Set<Vid> {
        match self {
            Body::Proto { body, relation } => body.freevars().union(relation.freevars()),
            Body::Func { body } => body.freevars(),
            Body::TypeAlias => Set::new(),
        }
    }
}

/// Useful constructors
impl<N> Decl<N> {
    pub fn proto(
        name: Vid,
        typevars: TypeVars<N>,
        args: GArgs<N>,
        relation: Exp<N>,
        body: Exp<N>,
    ) -> Self {
        let sig = Sig {
            name,
            typevars,
            args,
            ret: None,
        };
        let body = Body::Proto { relation, body };
        Decl { sig, body }
    }

    pub fn func(
        name: Vid,
        typevars: TypeVars<N>,
        args: GArgs<N>,
        ret: Option<GTyp<N>>,
        body: Exp<N>,
    ) -> Self {
        let sig = Sig {
            name,
            typevars,
            args,
            ret,
        };
        let body = Body::Func { body };
        Decl { sig, body }
    }

    pub fn type_alias(name: Vid, typ: GTyp<N>) -> Self {
        use crate::ast::arg::Args;
        let sig = Sig {
            name,
            typevars: TypeVars(vec![]),
            args: Args(vec![]),
            ret: Some(typ),
        };
        Decl {
            sig,
            body: Body::TypeAlias,
        }
    }
}

/// A collection of declarations
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Decls<N>(pub Vec<Decl<N>>);

/// Untyped body with symbolic sizes
pub type UBody = Body<Size>;

/// Concrete sized body
pub type CBody = Body<usize>;

/// Untyped decl with symbolic sizes
pub type UDecl = Decl<Size>;

/// Concrete sized declaration
pub type CDecl = Decl<usize>;

/// Untyped declarations with symbolic sizes
pub type UDecls = Decls<Size>;

/// Concrete sized declarations
pub type CDecls = Decls<usize>;

impl UDecl {
    /// Parse a string into a Zippel declaration
    #[allow(clippy::should_implement_trait)]
    pub fn from_str(input_str: &str) -> Result<Self, crate::parser::ParseError> {
        let (mut spanned, errors) = crate::parser::parse_decls(input_str);
        if let Some(e) = errors.into_iter().next() {
            return Err(e);
        }
        spanned.pop().map(|s| s.node).ok_or_else(|| {
            crate::parser::ParseError::custom(
                "empty input: expected at least one declaration".to_string(),
            )
        })
    }

    /// Each declaration has typevariables that can be concretized to different sizes.
    /// This method returns all possible size substitutions for the declaration.
    /// If `sizes` pins a Range typevar, only that value is generated.
    pub fn get_size_substitutions(
        &'_ self,
        sizes: &Ctx<Tid, usize>,
    ) -> Result<Set<SizeSubsts>, DeclError> {
        Ok(SizeSubsts::from_typevars(&self.sig.typevars, sizes)?)
    }

    /// Concretize a declaration with a given size substitution
    pub fn concretize(&self, substs: &SizeSubsts) -> Result<CDecl, DeclError> {
        let mut csig = self.sig.clone().traverse1(&mut |x| x.eval(&substs.0))?;
        let cbody = self.body.clone().traverse1(&mut |x| x.eval(&substs.0))?;

        // Remove typevars substituted
        csig.typevars = csig
            .typevars
            .into_iter()
            .filter(|tv| !substs.contains(&tv.id))
            .collect();

        // Check the ranges
        Ok(CDecl {
            sig: csig
                .clone()
                .range_traverse(&mut |r| {
                    r.check()?;
                    Ok(r)
                })
                .map_err(|e| DeclError::InvalidRange(csig.clone(), e))?,
            body: cbody
                .clone()
                .range_traverse(&mut |r| {
                    r.check()?;
                    Ok(r)
                })
                .map_err(|e| DeclError::InvalidRange(csig.clone(), e))?,
        })
    }
}

/// .zippel files get parsed to [UDecls].
impl UDecls {
    /// Parse a string into a Zippel declarations list
    #[allow(clippy::should_implement_trait)]
    pub fn from_str(input_str: &str) -> Result<Self, crate::parser::ParseError> {
        let (spanned, errors) = crate::parser::parse_decls(input_str);
        if let Some(e) = errors.into_iter().next() {
            return Err(e);
        }
        let decls: Vec<UDecl> = spanned.into_iter().map(|s| s.node).collect();
        Ok(Decls(decls))
    }

    /// Parse a file into a Zippel declarations list
    pub fn from_file(file: &str, _allocator: &Bump) -> Result<Self, crate::parser::ParseError> {
        let input_str = std::fs::read_to_string(file).unwrap();
        Decls::from_str(&input_str)
    }
}

impl<N> IntoIterator for Decls<N> {
    type Item = Decl<N>;
    type IntoIter = std::vec::IntoIter<Decl<N>>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<N> FromIterator<Decl<N>> for Decls<N> {
    fn from_iter<I: IntoIterator<Item = Decl<N>>>(iter: I) -> Self {
        Decls(iter.into_iter().collect())
    }
}

impl CBody {
    pub fn typecheck(&self, sig: CSig, fctx: &Set<CSig>) -> Result<(), TypeError> {
        // Kind context
        let kctx = sig.typevars.to_ctx();
        // Add arguments to [vctx] and [vars]
        let mut vctx = sig.args.to_ctx();
        for (tid, kind) in kctx.iter() {
            if let CKind::Range(r) = kind {
                if r.step == 1 && r.end == r.start + 1 {
                    vctx.insert(&Vid::new(&tid.0), &CTyp::Fin(*r));
                }
            }
        }
        match self {
            Body::Proto { body, relation } => {
                // Relation must be relation-pure (no Challenge/Log/Verify)
                if !relation.is_relation_pure() {
                    return Err(TypeError::decl(
                        &sig.name,
                        TypeError::not_pure_rel(relation),
                    ));
                }
                // Relation must infer to Unit (Let/Assert chain ending in Unit)
                relation.infer(&kctx, fctx, &vctx)?;
                // Body must infer to Unit
                let br = body.infer(&kctx, fctx, &vctx)?;
                if br != CTyp::Unit {
                    return Err(TypeError::decl(
                        &sig.name,
                        TypeError::unit(&kctx, &vctx, body),
                    ));
                }
                Ok(())
            }
            Body::Func { body } => {
                let br = body.infer(&kctx, fctx, &vctx)?;
                // Use lub_equ rather than strict structural equality so that
                // a body inferred as `Fin<n>` (e.g. a bare numeric literal)
                // coerces to a `Base(F)` return type via the scalar
                // fallback in `CTyp::lub_equ` (`lang/src/typ/lub.rs:510`).
                // Same lift the binary operator arms apply via `lub_add`
                // (`lang/src/typ/lub.rs:597-613`), now extended to the
                // return-type check.
                let ret = sig.ret.as_ref().unwrap_or(&CTyp::Unit);
                match CTyp::lub_equ(&br, ret, &kctx) {
                    Ok(_) => Ok(()),
                    Err(_) => Err(TypeError::decl(
                        &sig.name,
                        TypeError::func_ret(&kctx, &vctx, body, &sig.name, ret, &br),
                    )),
                }
            }
            Body::TypeAlias => Ok(()),
        }
    }
}

/// Traversable1 instance for Body (N)
impl<N: Clone> ToTraversal1<N> for Body<N> {
    type Output<Z> = Body<Z>;
    fn traverse1<Z: Clone, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Body<Z>, E> {
        match self {
            Body::Proto { relation, body } => Ok(Body::Proto {
                relation: relation.traverse1(f)?,
                body: body.traverse1(f)?,
            }),
            Body::Func { body } => Ok(Body::Func {
                body: body.traverse1(f)?,
            }),
            Body::TypeAlias => Ok(Body::TypeAlias),
        }
    }
}

impl TidSubst for CBody {
    fn tid_subst(&mut self, from: &Tid, to: &Tid) {
        match self {
            Body::Proto { relation, body } => {
                relation.tid_subst(from, to);
                body.tid_subst(from, to);
            }
            Body::Func { body } => body.tid_subst(from, to),
            Body::TypeAlias => {}
        }
    }
}

impl<N: Clone> RangeTraversal<N> for Body<N> {
    fn range_traverse<E>(
        self,
        f: &mut dyn FnMut(Range<N>) -> Result<Range<N>, E>,
    ) -> Result<Self, E> {
        match self {
            Body::Proto { relation, body } => Ok(Body::Proto {
                relation: relation.range_traverse(f)?,
                body: body.range_traverse(f)?,
            }),
            Body::Func { body } => Ok(Body::Func {
                body: body.range_traverse(f)?,
            }),
            Body::TypeAlias => Ok(Body::TypeAlias),
        }
    }
}

impl<N: Clone> TypeInline<N> for Body<N> {
    fn type_inline(self, _ctx: &Ctx<Tid, GTyp<N>>) -> Self {
        self
    }
}

impl<N: Clone + Ord> TypeInline<N> for Decl<N>
where
    Sig<N>: TypeInline<N>,
{
    fn type_inline(self, ctx: &Ctx<Tid, GTyp<N>>) -> Self {
        Decl {
            sig: self.sig.type_inline(ctx),
            body: self.body.type_inline(ctx),
        }
    }
}

/// Pretty printer instance for Body
impl<'a, D, N, A> Pretty<'a, D, A> for Body<N>
where
    D: DocAllocator<'a, A>,
    N: Clone + Pretty<'a, D, A> + 'a,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        match self {
            Body::Proto { relation, body } => allocator.concat([
                allocator.text(" where "),
                relation.pretty(allocator),
                allocator.text(" {"),
                allocator.line(),
                body.pretty(allocator).group().indent(2),
                allocator.line(),
                allocator.text("}"),
            ]),
            Body::Func { body } => allocator.concat([
                allocator.text("{"),
                allocator.line(),
                body.pretty(allocator).group().indent(2),
                allocator.line(),
                allocator.text("}"),
            ]),
            Body::TypeAlias => allocator.nil(),
        }
    }

    fn is_nil(&self) -> bool {
        false
    }
}

/// Pretty printer instance
impl<'a, D, N, A> Pretty<'a, D, A> for Decl<N>
where
    D: DocAllocator<'a, A>,
    N: Clone + Pretty<'a, D, A> + 'a,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        let Decl { sig, body, .. } = self;
        allocator.concat([
            if body.is_proto() {
                allocator.text("proto")
            } else {
                allocator.text("fn")
            },
            allocator.space(),
            sig.pretty(allocator),
            allocator.space(),
            body.pretty(allocator),
        ])
    }

    fn is_nil(&self) -> bool {
        false
    }
}

/// Display instance calls the pretty printer
impl<'a, N> fmt::Display for Decl<N>
where
    N: Clone + Pretty<'a, BoxAllocator, ()> + 'a,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Decl<N> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}
/// Pretty instance for decls
impl<'a, D, N, A> Pretty<'a, D, A> for Decls<N>
where
    D: DocAllocator<'a, A>,
    N: Clone + Pretty<'a, D, A> + 'a,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.intersperse(
            self.0.into_iter().map(|d| d.pretty(allocator)),
            allocator.hardline(),
        )
    }

    fn is_nil(&self) -> bool {
        self.0.is_empty()
    }
}

/// Display instance calls the pretty printer
impl<'a, N> fmt::Display for Decls<N>
where
    N: Clone + Pretty<'a, BoxAllocator, ()> + 'a,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Decls<N> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}
