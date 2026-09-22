use std::fmt;
use thiserror::Error;

use crate::ast::size::EvalError;
use crate::ast::spanned::Spanned;
use crate::ast::Size;
use crate::ast::{CSig, Exp, FreeVars, GArgs, Sig};
use crate::id::{Tid, TidSubst, Vid};
use crate::typ::infer::{TypeError, Typeable};
use crate::typ::lub::Lub;
use crate::typ::subst::SubstError;
use crate::typ::{
    CKind, CTyp, GTyp, Range, RangeError, RangeTraversal, SizeSubsts, TypeInline, TypeVars,
};
use share::traversal::ToTraversal1;
use share::{BoxAllocator, Ctx, DocAllocator, DocBuilder, Pretty, Set};

/// Body of Zippel declarations (protocols, functions, and type aliases).
/// Specs are given either by an explicit relation on inputs (precondition)
/// or by the return type of the function.
/// Parametrized by `N` the type of sizes and `T` the type of types.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Body<N> {
    /// A protocol body declaration
    ///
    /// # fields
    /// - `body`: The body of the protocol.
    /// - `relation`: The relation describing the protocol — a single
    ///   `Bool` expression from the `where` clause, combined with `&&`
    ///   and let bindings. The graph wraps it in `Assert` (the relation
    ///   IS the assertion).
    Proto {
        /// Executable part of the protocol, lowered into the DAG; `None`
        /// for an empty body `{}`.
        body: Option<Spanned<Exp<N>>>,
        /// The `Bool` relation this protocol must satisfy; the graph
        /// builder turns it into the protocol's assertion.
        relation: Spanned<Exp<N>>,
    },

    /// A function body declaration
    ///
    /// # fields
    /// - `body`: The body of the function. `None` for an empty body `{}`,
    ///   which is semantically equivalent to `Unit`.
    Func {
        /// The body of the function. `None` for an empty body `{}`,
        /// which is semantically equivalent to `Unit`.
        body: Option<Spanned<Exp<N>>>,
    },

    /// A type alias declaration (e.g., `type Point = { x: F, y: F };`)
    /// The aliased type is stored in the Sig's return type.
    TypeAlias,
}

/// A zippel declaration is either a protocol or a function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Decl<N> {
    /// Name, size-type variables, arguments, and (for functions) return type.
    pub sig: Sig<N>,
    /// What the declaration computes: protocol, function, or type alias.
    pub body: Body<N>,
}

/// Failures raised while concretizing a symbolically sized declaration.
#[derive(Error, Debug)]
pub enum DeclError {
    /// A size expression in the declaration could not be evaluated to a `usize`.
    #[error("DeclError: Error evaluating size type variables: \n\n{0}")]
    EvalError(#[from] EvalError),
    /// A `Range` size-type variable of the named signature violates its own
    /// `start`/`end`/`step` well-formedness check after substitution.
    #[error("DeclError: Invalid ranges in declaration {0}: \n\n{1}")]
    InvalidRange(CSig, RangeError),
    /// Substituting size-type variables into the declaration's types failed.
    #[error("DeclError: {0}")]
    SubstError(#[from] SubstError),
}

impl<N> Body<N> {
    /// Whether this body is a protocol body (has a relation).
    pub fn is_proto(&self) -> bool {
        matches!(self, Body::Proto { .. })
    }

    /// Whether this body is a function body.
    pub fn is_func(&self) -> bool {
        matches!(self, Body::Func { .. })
    }

    /// Whether this body is a type alias, which carries no expression at all.
    pub fn is_type_alias(&self) -> bool {
        matches!(self, Body::TypeAlias)
    }

    /// Consumes the body and returns its expression, `None` for an empty body.
    ///
    /// # Panics
    /// Panics on `Body::TypeAlias`, which has no expression; callers must
    /// guard with [`Body::is_type_alias`].
    pub fn body(self) -> Option<Spanned<Exp<N>>> {
        match self {
            Body::Proto { body, .. } => body,
            Body::Func { body } => body,
            Body::TypeAlias => panic!("TypeAlias has no body"),
        }
    }
    /// Consumes the body and returns the protocol relation, or `None` for
    /// function bodies and type aliases.
    pub fn relation(self) -> Option<Spanned<Exp<N>>> {
        match self {
            Body::Proto { relation, .. } => Some(relation),
            _ => None,
        }
    }
}

impl FreeVars for CBody {
    fn freevars(&self) -> Set<Vid> {
        match self {
            Body::Proto { body, relation } => body
                .as_ref()
                .map(|b| b.freevars())
                .unwrap_or_default()
                .union(relation.freevars()),
            Body::Func { body } => body.as_ref().map(|b| b.freevars()).unwrap_or_default(),
            Body::TypeAlias => Set::new(),
        }
    }
}

/// Useful constructors
impl<N> Decl<N> {
    /// Builds a protocol declaration: a signature with no return type plus a
    /// [`Body::Proto`] holding the `where`-clause relation and optional body.
    pub fn proto(
        name: Spanned<Vid>,
        typevars: Spanned<TypeVars<N>>,
        args: Spanned<GArgs<N>>,
        relation: Spanned<Exp<N>>,
        body: Option<Spanned<Exp<N>>>,
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

    /// Builds a function declaration from its signature parts and optional body.
    pub fn func(
        name: Spanned<Vid>,
        typevars: Spanned<TypeVars<N>>,
        args: Spanned<GArgs<N>>,
        ret: Option<Spanned<GTyp<N>>>,
        body: Option<Spanned<Exp<N>>>,
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

    /// Builds a type-alias declaration; the aliased type is stored as the
    /// signature's return type, with no type variables and no arguments.
    pub fn type_alias(name: Spanned<Vid>, typ: Spanned<GTyp<N>>) -> Self {
        use crate::ast::arg::Args;
        let sig = Sig {
            name,
            typevars: Spanned::dummy(TypeVars(vec![])),
            args: Spanned::dummy(Args(vec![])),
            ret: Some(typ),
        };
        Decl {
            sig,
            body: Body::TypeAlias,
        }
    }
}

/// A collection of declarations
#[derive(Debug, Clone, PartialEq, Eq)]
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
    /// Each declaration has typevariables that can be concretized to different sizes.
    /// This method returns all possible size substitutions for the declaration.
    /// If `sizes` pins a Range typevar, only that value is generated.
    ///
    /// # Errors
    /// Returns `DeclError::SubstError` if a size-type variable cannot be
    /// enumerated (for example a non-`Range` kind or an unbound variable).
    pub fn get_size_substitutions(
        &'_ self,
        sizes: &Ctx<Tid, usize>,
    ) -> Result<Set<SizeSubsts>, DeclError> {
        Ok(SizeSubsts::from_typevars(&self.sig.typevars.node, sizes)?)
    }

    /// Concretize a declaration with a given size substitution
    ///
    /// # Errors
    /// Returns `DeclError::EvalError` if a size expression in the signature or
    /// body cannot be evaluated under `substs`, and `DeclError::InvalidRange`
    /// if a resulting `Range` fails its well-formedness check.
    pub fn concretize(&self, substs: &SizeSubsts) -> Result<CDecl, DeclError> {
        let mut csig = self.sig.clone().traverse1(&mut |x| x.eval(&substs.0))?;
        let cbody = self.body.clone().traverse1(&mut |x| x.eval(&substs.0))?;

        // Remove typevars substituted
        csig.typevars.node = csig
            .typevars
            .node
            .into_iter()
            .filter(|tv| !substs.contains(&tv.id.node))
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
    /// Type-checks this body against its own (concretized) signature and the
    /// set of visible function signatures `fctx`.
    ///
    /// The kind context is taken from the signature's type variables, and
    /// singleton `Range` type variables are additionally bound as `Fin` values
    /// so they can be used as ordinary scalars inside the body.
    ///
    /// # Errors
    /// Returns a `TypeError` if inference of the relation or body fails; if a
    /// protocol relation is not relation-pure (mentions `Challenge`, `Log`,
    /// `Verify`, or `Assert`); if the relation does not infer to `Bool`; if a
    /// protocol body does not infer to `Unit`; or if a function body's type has
    /// no least upper bound with the declared return type.
    pub fn typecheck(&self, sig: CSig, fctx: &Set<CSig>) -> Result<(), TypeError> {
        // Kind context
        let kctx = sig.typevars.node.to_ctx();
        // Add arguments to [vctx] and [vars]
        let mut vctx = sig.args.node.to_ctx();
        for (tid, kind) in kctx.iter() {
            if let CKind::Range(r) = kind {
                if r.step() == 1 && r.end() == r.start() + 1 {
                    vctx.insert(&Vid::new(&tid.0), &CTyp::Fin(r.clone()));
                }
            }
        }
        match self {
            Body::Proto { body, relation } => {
                // Relation must be relation-pure (no Challenge/Log/Verify/Assert)
                if !relation.node.is_relation_pure() {
                    return Err(TypeError::decl(
                        &sig.name,
                        TypeError::located(&relation.span, TypeError::not_pure_rel(&relation.node)),
                    ));
                }
                // Relation must infer to Bool (the relation IS the assertion)
                let rel_typ = relation.infer(&kctx, fctx, &vctx)?;
                if !matches!(rel_typ, CTyp::Bool) {
                    return Err(TypeError::decl(
                        &sig.name,
                        TypeError::located(
                            &relation.span,
                            TypeError::relation_not_bool(&rel_typ, &relation.node),
                        ),
                    ));
                }
                // Body must infer to Unit (empty body is Unit)
                if let Some(body) = body {
                    let br = body.infer(&kctx, fctx, &vctx)?;
                    if br != CTyp::Unit {
                        return Err(TypeError::decl(
                            &sig.name,
                            TypeError::located(
                                &body.span,
                                TypeError::unit(&kctx, &vctx, &body.node),
                            ),
                        ));
                    }
                }
                Ok(())
            }
            Body::Func { body } => {
                let ret = sig.ret.as_ref().map(|r| &r.node).unwrap_or(&CTyp::Unit);
                match body {
                    Some(body) => {
                        let br = body.infer(&kctx, fctx, &vctx)?;
                        // Use lub_equ rather than strict structural equality so that
                        // a body inferred as `Fin<n>` (e.g. a bare numeric literal)
                        // coerces to a `Base(F)` return type via the scalar
                        // fallback in `CTyp::lub_equ` (`lang/src/typ/lub.rs:510`).
                        // Same lift the binary operator arms apply via `lub_add`
                        // (`lang/src/typ/lub.rs:597-613`), now extended to the
                        // return-type check.
                        match CTyp::lub_equ(&br, ret, &kctx) {
                            Ok(_) => Ok(()),
                            Err(_) => Err(TypeError::decl(
                                &sig.name,
                                TypeError::located(
                                    &body.span,
                                    TypeError::func_ret(
                                        &kctx,
                                        &vctx,
                                        &body.node,
                                        &sig.name.node,
                                        ret,
                                        &br,
                                    ),
                                ),
                            )),
                        }
                    }
                    None => {
                        // Empty body `{}` is semantically Unit.
                        match CTyp::lub_equ(&CTyp::Unit, ret, &kctx) {
                            Ok(_) => Ok(()),
                            Err(_) => Err(TypeError::decl(
                                &sig.name,
                                TypeError::located(
                                    &sig.ret.as_ref().map_or(0..0, |r| r.span.clone()),
                                    TypeError::func_ret(
                                        &kctx,
                                        &vctx,
                                        &Spanned::new(Exp::Unit, 0..0),
                                        &sig.name.node,
                                        ret,
                                        &CTyp::Unit,
                                    ),
                                ),
                            )),
                        }
                    }
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
                body: body.map(|b| b.traverse1(f)).transpose()?,
            }),
            Body::Func { body } => Ok(Body::Func {
                body: body.map(|b| b.traverse1(f)).transpose()?,
            }),
            Body::TypeAlias => Ok(Body::TypeAlias),
        }
    }
}

impl TidSubst for CBody {
    fn tid_subst(&mut self, from: &Tid, to: &Tid) {
        match self {
            Body::Proto { relation, body } => {
                relation.node.tid_subst(from, to);
                if let Some(body) = body {
                    body.node.tid_subst(from, to);
                }
            }
            Body::Func { body } => {
                if let Some(body) = body {
                    body.node.tid_subst(from, to);
                }
            }
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
                body: body.map(|b| b.range_traverse(f)).transpose()?,
            }),
            Body::Func { body } => Ok(Body::Func {
                body: body.map(|b| b.range_traverse(f)).transpose()?,
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

impl<N: Clone> TypeInline<N> for Decl<N>
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
            Body::Proto { relation, body } => {
                let body_doc = match body {
                    Some(body) => allocator.concat([
                        allocator.text(" {"),
                        allocator.line(),
                        body.pretty(allocator).group().indent(2),
                        allocator.line(),
                        allocator.text("}"),
                    ]),
                    None => allocator.text(" {}"),
                };
                allocator.concat([
                    allocator.text(" where "),
                    relation.pretty(allocator),
                    body_doc,
                ])
            }
            Body::Func { body } => match body {
                Some(body) => allocator.concat([
                    allocator.text("{"),
                    allocator.line(),
                    body.pretty(allocator).group().indent(2),
                    allocator.line(),
                    allocator.text("}"),
                ]),
                None => allocator.text("{}"),
            },
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
