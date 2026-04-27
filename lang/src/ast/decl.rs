use bumpalo::Bump;
use from_pest::{ConversionError, FromPest};
use pest::iterators::Pairs;
use pest::Parser;
use std::fmt;
use thiserror::Error;

use crate::ast::{CSig, Exp, FreeVars, GArgs, Sig};
use crate::id::{Tid, TidSubst, Vid};
use crate::parser::*;
use crate::typ::backend::BackendConfig;
use crate::typ::infer::{TypeError, Typeable};
use crate::typ::subst::SubstError;
use crate::typ::{
    CTyp, EvalError, GTyp, Range, RangeError, RangeTraversal, Size, SizeSubsts, TypeInline,
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
    /// - `relation`: The relation describing the protocol.
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
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
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
            ret: GTyp::bool(),
        };
        let body = Body::Proto { relation, body };
        Decl { sig, body }
    }

    pub fn func(
        name: Vid,
        typevars: TypeVars<N>,
        args: GArgs<N>,
        ret: GTyp<N>,
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
            ret: typ,
        };
        Decl {
            sig,
            body: Body::TypeAlias,
        }
    }
}

/// A collection of declarations
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
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
    pub fn from_str<'a>(input_str: &'a str) -> Result<Self, ConversionError<InputError<'a>>> {
        let mut pairs = ZippelParser::parse(Rule::decl, input_str).unwrap();
        UDecl::from_pest(&mut pairs)
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
    pub fn concretize<'a, 'b>(&'a self, substs: &'b SizeSubsts) -> Result<CDecl, DeclError> {
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
    pub fn from_str<'a>(input_str: &'a str) -> Result<Self, ConversionError<InputError<'a>>> {
        let mut pairs = ZippelParser::parse(Rule::decls, input_str).unwrap();
        Decls::from_pest(&mut pairs)
    }

    /// Parse a file into a Zippel declarations list
    pub fn from_file<'a>(
        file: &str,
        allocator: &'a Bump,
    ) -> Result<Self, ConversionError<InputError<'a>>> {
        let input_str = std::fs::read_to_string(file).unwrap();
        let stored_str = allocator.alloc_str(&input_str);
        Decls::from_str(stored_str)
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
    pub fn typecheck<C: BackendConfig>(
        &self,
        sig: CSig,
        fctx: &Set<CSig>,
    ) -> Result<(), TypeError> {
        // Kind context
        let kctx = sig.typevars.to_ctx();
        // Add arguments to [vctx] and [vars]
        let vctx = sig.args.to_ctx();
        match self {
            Body::Proto { body, relation } => {
                // Relation must be pure (no side-effects)
                if !relation.is_pure() {
                    return Err(TypeError::decl(
                        &sig.name,
                        TypeError::not_pure_rel(relation),
                    ));
                }

                // Type infer relation and body
                let tr = relation.infer::<C>(&kctx, &fctx, &vctx)?;
                let br = body.infer::<C>(&kctx, &fctx, &vctx)?;
                if tr == CTyp::Bool && br == CTyp::Bool {
                    Ok(())
                } else {
                    Err(TypeError::decl(&sig.name, TypeError::bool(&kctx, &vctx, &relation)).into())
                }
            }
            Body::Func { body } => {
                let br = body.infer::<C>(&kctx, &fctx, &vctx)?;
                if br == sig.ret {
                    Ok(())
                } else {
                    Err(TypeError::decl(
                        &sig.name,
                        TypeError::func_ret(&kctx, &vctx, body, &sig.name, &sig.ret, &br),
                    )
                    .into())
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
                body: body.traverse1(f)?,
                relation: relation.traverse1(f)?,
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
                allocator.text(" where ("),
                relation.pretty(allocator),
                allocator.text(") {"),
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
        let Decl { sig, body } = self;
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

impl<'pest> FromPest<'pest> for UDecl {
    type Rule = Rule;
    type FatalError = InputError<'pest>;

    fn from_pest(
        pest: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        let pair = pest.next().ok_or(ConversionError::NoMatch)?;
        match pair.as_rule() {
            Rule::decl => Decl::from_pest(&mut pair.into_inner()),
            // Protocol with a [where] clause
            Rule::proto_decl => {
                let mut inner = pair.into_inner();
                // Protocol's name
                let name = Vid::from_pest(&mut Pairs::single(inner.next().unwrap()))?;
                // Type variables
                let typevars = TypeVars::from_pest(&mut Pairs::single(inner.next().unwrap()))?;
                // Arguments
                let args = GArgs::from_pest(&mut Pairs::single(inner.next().unwrap()))?;
                // External relation
                let relation = Exp::from_pest(&mut Pairs::single(inner.next().unwrap()))?;
                // Protocol's body (single expression, chains via let/log/verify/assert continuations)
                let body = Exp::from_pest(&mut Pairs::single(
                    inner.next().ok_or(ConversionError::NoMatch)?,
                ))?;
                Ok(Decl::proto(name, typevars, args, relation, body))
            }
            Rule::func_decl => {
                let mut inner = pair.into_inner();
                // Function's name
                let name = Vid::from_pest(&mut inner)?;
                // Type variables
                let typevars = TypeVars::from_pest(&mut inner)?;
                // Function's arguments
                let args = GArgs::from_pest(&mut inner)?;
                // Function return type
                let ret = GTyp::from_pest(&mut inner)?;
                // Function's body (single expression, chains via let/log continuations)
                let body = Exp::from_pest(&mut Pairs::single(
                    inner.next().ok_or(ConversionError::NoMatch)?,
                ))?;
                Ok(Decl::func(name, typevars, args, ret, body))
            }
            Rule::type_decl => {
                let mut inner = pair.into_inner();
                let name = Vid(inner.next().unwrap().as_str().to_string());
                let typ = GTyp::from_pest(&mut Pairs::single(inner.next().unwrap()))?;
                Ok(Decl::type_alias(name, typ))
            }
            _ => Err(ConversionError::Malformed(InputError::UnexpectedExp(pair))),
        }
    }
}

/// A collection of declarations is also a module
impl<'pest> FromPest<'pest> for UDecls {
    type Rule = Rule;
    type FatalError = InputError<'pest>;

    fn from_pest(
        pest: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        let pair = pest.next().ok_or(ConversionError::NoMatch)?;
        match pair.as_rule() {
            Rule::decls => {
                let mut decls = Vec::new();
                for p in pair.into_inner() {
                    match p.as_rule() {
                        Rule::decl => {
                            decls.push(Decl::from_pest(&mut Pairs::single(p))?);
                        }
                        Rule::EOI => (),
                        _ => unreachable!(),
                    }
                }
                Ok(Decls(decls))
            }
            _ => unreachable!(),
        }
    }
}

#[cfg(test)]
use crate::{
    ast::{Exps, GArg, UExp},
    typ::{Kind, TypeVar},
};

#[test]
fn proto_easy() {
    let ex = "proto test<F: Field>(public a: F) where a == a { verify(a == a) }";

    let pairs = ZippelParser::parse(Rule::decl, ex).unwrap();
    UDecl::from_pest(&mut pairs.into_iter()).unwrap();
}

#[test]
fn proto_parser() {
    let ex = concat!(
        "proto test<F: Field>(public a: F) where a == a {\n",
        "    let x = 3*a;\n",
        "    verify(x == x)\n",
        "}"
    );
    let mut pairs = ZippelParser::parse(Rule::decl, ex).unwrap();
    assert_eq!(
        UDecl::from_pest(&mut pairs).unwrap(),
        UDecl::proto(
            Vid::from("test"),
            TypeVars(vec![TypeVar::new_str("F", Kind::Field)]),
            GArgs::from([GArg::public("a", GTyp::varstr("F"))]),
            UExp::equ(UExp::varstr("a"), UExp::varstr("a")),
            UExp::letx(
                Vid::from("x"),
                UExp::from(3) * UExp::varstr("a"),
                UExp::verify(UExp::equ(UExp::varstr("x"), UExp::varstr("x")))
            )
        )
    );
}

#[test]
fn fn_parser1() {
    let ex = concat!(
        "fn test<F: Field, N: 0..10>(private a: [F; N]) -> F {\n",
        "    let x = 3*a[0];\n",
        "    x + x\n",
        "}"
    );
    let mut pairs = ZippelParser::parse(Rule::decl, ex).unwrap();
    assert_eq!(
        UDecl::from_pest(&mut pairs).unwrap(),
        UDecl::func(
            Vid::from("test"),
            TypeVars(vec![
                TypeVar::new_str("F", Kind::Field),
                TypeVar::new_str(
                    "N",
                    Kind::Range(Range {
                        start: Size::Lit(0),
                        step: Size::Lit(1),
                        end: Size::Lit(10)
                    })
                )
            ]),
            GArgs::from([GArg::private(
                "a",
                GTyp::vec(&GTyp::varstr("F"), Size::from("N"))
            )]),
            GTyp::varstr("F"),
            UExp::letx(
                Vid::from("x"),
                UExp::from(3) * UExp::ram(UExp::from("a"), UExp::from(0)),
                UExp::varstr("x") + UExp::varstr("x")
            )
        )
    );
}

#[test]
fn fn_parser2() {
    let ex = concat!(
        "fn test<F: Field>(public a: F) -> F {\n",
        "    let v = [1,2,3];\n",
        "    p <- ifft(v * [0,1,2]);\n",
        "    x <- challenge<F>;\n",
        "    p(x)\n",
        "}"
    );
    let mut pairs = ZippelParser::parse(Rule::decl, ex).unwrap();
    assert_eq!(
        UDecl::from_pest(&mut pairs).unwrap(),
        UDecl::func(
            Vid::from("test"),
            TypeVars(vec![TypeVar::new_str("F", Kind::Field)]),
            GArgs::from([GArg::public("a", GTyp::varstr("F"))]),
            GTyp::varstr("F"),
            UExp::letx(
                Vid::from("v"),
                UExp::vec(vec![UExp::from(1), UExp::from(2), UExp::from(3)]),
                UExp::logx(
                    Vid::from("p"),
                    UExp::ifft(UExp::mul(
                        UExp::varstr("v"),
                        UExp::vec(vec![UExp::from(0), UExp::from(1), UExp::from(2)])
                    )),
                    UExp::logx(
                        Vid::from("x"),
                        UExp::challenge(Tid::from("F")),
                        UExp::app(Vid::from("p"), Exps::from([UExp::varstr("x")]))
                    )
                )
            )
        )
    );
}

#[test]
fn decls_parser() {
    let ex = concat!(
        "proto test<F: Field>(public a: F) where a == a {\n",
        "    let x = 3*a;\n",
        "    verify(x == x)\n",
        "}\n",
        "fn test<F: Field, N: 0..10>(public a: [F; N]) -> F {\n",
        "    let x = 3*a[0];\n",
        "    x + x\n",
        "}"
    );
    let mut pairs = ZippelParser::parse(Rule::decls, ex).unwrap();
    assert_eq!(
        UDecls::from_pest(&mut pairs).unwrap(),
        Decls(vec![
            UDecl::proto(
                Vid::from("test"),
                TypeVars(vec![TypeVar::new_str("F", Kind::Field)]),
                GArgs::from([GArg::public("a", GTyp::varstr("F"))]),
                UExp::equ(UExp::varstr("a"), UExp::varstr("a")),
                UExp::letx(
                    Vid::from("x"),
                    UExp::mul(UExp::from(3), UExp::varstr("a")),
                    UExp::verify(UExp::equ(UExp::varstr("x"), UExp::varstr("x")))
                )
            ),
            UDecl::func(
                Vid::from("test"),
                TypeVars(vec![
                    TypeVar::new_str("F", Kind::Field),
                    TypeVar::new_str(
                        "N",
                        Kind::Range(Range {
                            start: Size::Lit(0),
                            step: Size::Lit(1),
                            end: Size::Lit(10)
                        })
                    ),
                ]),
                GArgs::from([GArg::public(
                    "a",
                    GTyp::vec(&GTyp::varstr("F"), Size::from("N"))
                )]),
                GTyp::varstr("F"),
                UExp::letx(
                    Vid::from("x"),
                    UExp::mul(UExp::from(3), UExp::ram(UExp::varstr("a"), UExp::from(0))),
                    UExp::varstr("x") + UExp::varstr("x")
                )
            )
        ])
    );
}
