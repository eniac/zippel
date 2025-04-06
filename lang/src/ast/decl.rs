use std::fmt;
use from_pest::{ConversionError, FromPest};
use pest::iterators::Pairs;
use pest::Parser;
use bumpalo::Bump;

use share::{Set, Pretty, BoxAllocator, DocAllocator, DocBuilder};
use share::traversal::ToTraversal1;
use crate::ast::{Exp, ExpSubst, FreeVars, CExp, Sig, Args};
use crate::id::{Tid, TidSubst, Fid, Vid};
use crate::typ::{Typ, Range, Size, TypeVars, RangeTraversal};
use crate::parser::*;


/// Body of Zippel declarations (protocols and functions).
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
    Proto {
        body: Exp<N>,
        relation: Exp<N>,
    },

    /// A function body declaration
    ///
    /// # fields
    /// - `body`: The body of the function.
    Func {
        body: Exp<N>
    },
}

/// A zippel declaration is either a protocol or a function.
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub struct Decl<N> {
    pub sig: Sig<N>,
    pub body: Body<N>,
}

impl<N> Body<N> {
    pub fn is_proto(&self) -> bool {
        match self {
            Body::Proto { .. } => true,
            _ => false,
        }
    }

    pub fn is_func(&self) -> bool {
        ! self.is_proto()
    }
    pub fn body(&self) -> &Exp<N> {
        match self {
            Body::Proto { body, .. } => body,
            Body::Func { body } => body,
        }
    }
}

impl FreeVars for CBody {
    fn freevars(&self) -> Set<Vid> {
        match self {
            Body::Proto { body, relation } => body.freevars().union(relation.freevars()),
            Body::Func { body } => body.freevars()
        }
    }
}

/// Useful constructors
impl<N> Decl<N> {
    pub fn proto(name: Fid, typevars: TypeVars, args: Args<N>, relation: Exp<N>, body: Exp<N>) -> Self {
        let sig = Sig { name, typevars, args, ret: Typ::bool() };
        let body = Body::Proto { relation, body };
        Decl { sig, body }
    }

    pub fn func(name: Fid, typevars: TypeVars, args: Args<N>, ret: Typ<N>, body: Exp<N>) -> Self {
        let sig = Sig { name, typevars, args, ret };
        let body = Body::Func { body };
        Decl { sig, body }
    }
}

/// A collection of declarations
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub struct Decls<N>(pub Vec<Decl<N>>);

/// Untyped body with symbolic sizes
pub type UBody =  Body<Size>;

/// Concrete sized body
pub type CBody = Body<usize>;

/// Untyped decl with symbolic sizes
pub type UDecl =  Decl<Size>;

/// Concrete sized decl
pub type CDecl = Decl<usize>;

/// Untyped declarations with symbolic sizes
pub type UDecls =  Decls<Size>;

/// Concrete sized declarations
pub type CDecls = Decls<usize>;


impl UDecl {
    pub fn from_str<'a>(input_str: &'a str) -> Result<Self, ConversionError<InputError<'a>>> {
        let mut pairs = ZippelParser::parse(Rule::decl, input_str).unwrap();
        UDecl::from_pest(&mut pairs)
    }
}

/// .zippel files get parses to [UDecls] that
/// is the entry point to the zippel compiler
impl UDecls {
    /// Parse a string into a Zippel declarations list
    pub fn from_str<'a>(input_str: &'a str) -> Result<Self, ConversionError<InputError<'a>>> {
        let mut pairs = ZippelParser::parse(Rule::decls, input_str).unwrap();
        Decls::from_pest(&mut pairs)
    }

    /// Parse a file into a Zippel declarations list
    pub fn from_file<'a>(file: &str, allocator: &'a Bump) -> Result<Self, ConversionError<InputError<'a>>> {
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

/// Traversable1 instance for Body (N)
impl<N> ToTraversal1<N> for Body<N> {
    type Output<Z> = Body<Z>;
    fn traverse1<Z, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Body<Z>, E> {
        match self {
            Body::Proto { relation, body } =>
                Ok(Body::Proto {
                    body: body.traverse1(f)?,
                    relation: relation.traverse1(f)?,
                }),
            Body::Func { body } =>
                Ok(Body::Func {
                    body: body.traverse1(f)?,
                }),
        }
    }
}

impl TidSubst for CBody {
    fn tid_subst(&mut self, from: &Tid, to: &Tid) {
        match self {
            Body::Proto { relation, body } => {
                relation.tid_subst(from, to);
                body.tid_subst(from, to);
            },
            Body::Func { body } => body.tid_subst(from, to)
        }
    }
}

impl ExpSubst for CBody {
    fn subst(&mut self, from: &Vid, to: &CExp, ctx: &mut Set<Vid>) {
        match self {
            Body::Proto { relation, body } => {
                relation.subst(from, to, ctx);
                body.subst(from, to, ctx);
            },
            Body::Func { body } => body.subst(from, to, ctx)
        }
    }
}

impl<N> RangeTraversal<N> for Body<N> {
    fn range_traverse<E>(self, f: &mut dyn FnMut(Range<N>) -> Result<Range<N>, E>) -> Result<Self, E> {
        match self {
            Body::Proto { relation, body } =>
                Ok(Body::Proto {
                    relation: relation.range_traverse(f)?,
                    body: body.range_traverse(f)?,
                }),
            Body::Func { body } =>
                Ok(Body::Func {
                    body: body.range_traverse(f)?,
                }),
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
            Body::Proto { relation, body } =>
                allocator.concat([
                    allocator.text("where ("),
                    relation.pretty(allocator),
                    allocator.text(") {"),
                    allocator.line(),
                    body.pretty(allocator).indent(2),
                    allocator.line(),
                    allocator.text("}"),
                ]),
            Body::Func { body } =>
                allocator.concat([
                    allocator.text("{"),
                    allocator.line(),
                    body.pretty(allocator).indent(2),
                    allocator.line(),
                    allocator.text("}"),
                ]),
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
            if body.is_proto() { allocator.text("proto") } else { allocator.text("fn") },
            allocator.space(),
            sig.pretty(allocator),
            allocator.space(),
            body.pretty(allocator)
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
impl <'a, D, N, A> Pretty<'a, D, A> for Decls<N>
where
    D: DocAllocator<'a, A>,
    N: Clone + Pretty<'a, D, A> + 'a,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.intersperse(
            self.0.into_iter().map(|d| d.pretty(allocator)),
            allocator.hardline()
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
                let name = Fid::from_pest(&mut Pairs::single(inner.next().unwrap()))?;
                // Type variables
                let typevars = TypeVars::from_pest(&mut Pairs::single(inner.next().unwrap()))?;
                // Arguments
                let args = Args::from_pest(&mut Pairs::single(inner.next().unwrap()))?;
                // External relation
                let relation = Exp::from_pest(&mut Pairs::single(inner.next().unwrap()))?;
                // Protocol's body
                let next = inner.next().ok_or(ConversionError::NoMatch)?;
                let body =
                    match next.as_rule() {
                        Rule::stmts => {
                            let mut aexps = Vec::new();
                            for p in next.into_inner() {
                                match p.as_rule() {
                                    Rule::aexp => {
                                        aexps.push(Exp::from_pest(&mut Pairs::single(p))?);
                                    },
                                    _ => unreachable!(),
                                }
                            }
                            match aexps.as_slice() {
                                [] => Err(ConversionError::Malformed(InputError::EmptyDecl(name.clone(), typevars.clone(), args.clone()))),
                                [body] => Ok(body.clone()),
                                [h, ts @ ..] => Ok(Exp::from_vec(h.clone(), ts))
                            }
                        },
                        _ => Err(ConversionError::Malformed(InputError::UnexpectedExp(next)))
                    }?;
                Ok(Decl::proto(name, typevars, args, relation, body))
            },
            Rule::func_decl => {
                let mut inner = pair.into_inner();
                // Function's name
                let name = Fid::from_pest(&mut inner)?;
                // Type variables
                let typevars = TypeVars::from_pest(&mut inner)?;
                // Function's arguments
                let args = Args::from_pest(&mut inner)?;
                // Function return type
                let ret = Typ::from_pest(&mut inner)?;
                // Function's body
                let next = inner.next().ok_or(ConversionError::NoMatch)?;
                let body =
                    match next.as_rule() {
                        Rule::stmts => {
                            let mut aexps = Vec::new();
                            for p in next.into_inner() {
                                match p.as_rule() {
                                    Rule::aexp => {
                                        aexps.push(Exp::from_pest(&mut Pairs::single(p))?);
                                    },
                                    _ => unreachable!(),
                                }
                            }
                            match aexps.as_slice() {
                                [] => Err(ConversionError::Malformed(InputError::EmptyDecl(name.clone(), typevars.clone(), args.clone()))),
                                [body] => Ok(body.clone()),
                                [h, ts @ ..] => Ok(Exp::from_vec(h.clone(), ts))
                            }
                        },
                        _ => Err(ConversionError::Malformed(InputError::UnexpectedExp(next)))
                    }?;
                Ok(Decl::func(name, typevars, args, ret, body))
            },
            _ => Err(ConversionError::Malformed(InputError::UnexpectedExp(pair)))
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
                        },
                        Rule::EOI => (),
                        _ => unreachable!(),
                    }
                }
                Ok(Decls(decls))
            }
            _ => unreachable!()
        }
    }
}

#[cfg(test)] use crate::{
        ast::{UExp, Exps, Arg},
        typ::{Kind, TypeVar}
};

#[test]
fn proto_easy() {
    let ex =
        "proto test<F: Field>(public a: F) where a == a { verify(a == a) }";

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
    assert_eq!(UDecl::from_pest(&mut pairs).unwrap(), UDecl::proto(
        Fid::from("test"),
        TypeVars(vec![TypeVar::new("F", Kind::Field)]),
        Args(vec![Arg::public("a", Typ::varstr("F"))]),
        UExp::equ(UExp::varstr("a"), UExp::varstr("a")),
        UExp::letx(Vid::from("x"), UExp::from(3) * UExp::varstr("a"),
            UExp::verify(UExp::equ(UExp::varstr("x"), UExp::varstr("x"))))
    ));
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
    assert_eq!(UDecl::from_pest(&mut pairs).unwrap(), UDecl::func(
        Fid::from("test"),
        TypeVars(vec![
            TypeVar::new("F", Kind::Field),
            TypeVar::new("N", Kind::Range(Range { start: 0, step: 1, end: 10 }))
        ]),
        Args(vec![Arg::private("a", Typ::vec(Typ::varstr("F"), Size::from("N")))]),
        Typ::varstr("F"),
        UExp::letx(Vid::from("x"), UExp::from(3) * UExp::ram(UExp::from("a"), UExp::from(0)),
            UExp::varstr("x") + UExp::varstr("x"))
    ));
}

#[test]
fn fn_parser2() {
    let ex = concat!(
        "fn test<F: Field>(public a: F) -> F {\n",
        "    let v = [1,2,3];\n",
        "    p <- interpolate(v * [0,1,2]);\n",
        "    x <- challenge<F>;\n",
        "    p(x)\n",
        "}"
    );
    let mut pairs = ZippelParser::parse(Rule::decl, ex).unwrap();
    assert_eq!(UDecl::from_pest(&mut pairs).unwrap(), UDecl::func(
        Fid::from("test"),
        TypeVars(vec![TypeVar::new("F", Kind::Field)]),
        Args(vec![Arg::public("a", Typ::varstr("F"))]),
        Typ::varstr("F"),
        UExp::letx(Vid::from("v"), UExp::vec(vec![UExp::from(1), UExp::from(2), UExp::from(3)]),
            UExp::logx(Vid::from("p"),
                UExp::interpolate(UExp::mul(UExp::varstr("v"), UExp::vec(vec![UExp::from(0), UExp::from(1), UExp::from(2)]))),
                UExp::logx(Vid::from("x"), UExp::challenge(Tid::from("F")),
                    UExp::app(Fid::from("p"), Exps::from([UExp::varstr("x")])))))
    ));
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
    assert_eq!(UDecls::from_pest(&mut pairs).unwrap(), Decls(vec![
        UDecl::proto(
            Fid::from("test"),
            TypeVars(vec![TypeVar::new("F", Kind::Field)]),
            Args(vec![Arg::public("a", Typ::varstr("F"))]),
            UExp::equ(UExp::varstr("a"), UExp::varstr("a")),
            UExp::letx(Vid::from("x"), UExp::mul(UExp::from(3), UExp::varstr("a")),
                UExp::verify(UExp::equ(UExp::varstr("x"), UExp::varstr("x"))))
        ),
        UDecl::func(
            Fid::from("test"),
            TypeVars(vec![
                TypeVar::new("F", Kind::Field),
                TypeVar::new("N", Kind::Range(Range { start:0, step:1, end: 10 })),
            ]),
            Args(vec![Arg::public("a", Typ::vec(Typ::varstr("F"), Size::from("N")))]),
            Typ::varstr("F"),
            UExp::letx(Vid::from("x"), UExp::mul(UExp::from(3), UExp::ram(UExp::varstr("a"), UExp::from(0))),
                UExp::varstr("x") + UExp::varstr("x"))
        )
    ]));
}
