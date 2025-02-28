use std::fmt;
use from_pest::{ConversionError, FromPest};
use pest::iterators::Pairs;
use pest::Parser;
use bumpalo::Bump;

use share::{Pretty, BoxAllocator, DocAllocator, DocBuilder};
use share::traversal::{ToTraversal1, ToTraversal2};
use crate::typ::TypeVars;
use crate::sig::Sig;
use crate::id::{Tid, TidTraversal, Fid};
use crate::typ::{Typ, Size, Nothing};
use crate::arg::Args;
use crate::exp::{AExp, AExps, BExp};
use crate::parser::*;


/// Body of Zippel declarations (protocols and functions).
/// Specs are given either by an explicit relation on inputs (precondition)
/// or by the return type of the function.
/// Parametrized by `N` the type of sizes and `T` the type of types.
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub enum Body<N, T> {
    /// A protocol body declaration
    ///
    /// # fields
    /// - `body`: The body of the protocol.
    /// - `relation`: The relation describing the protocol.
    Proto {
        body: AExps<N, T>,
        relation: BExp<N, T>,
    },

    /// A function body declaration
    ///
    /// # fields
    /// - `body`: The body of the function.
    Func {
        body: AExps<N, T>
    },
}

/// A zippel declaration is either a protocol or a function.
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub struct Decl<N, T> {
    pub sig: Sig<N>,
    pub typevars: TypeVars,
    pub body: Body<N, T>,
}

impl<N, T> Body<N, T> {
    pub fn is_proto(&self) -> bool {
        match self {
            Body::Proto { .. } => true,
            _ => false,
        }
    }

    pub fn is_func(&self) -> bool {
        ! self.is_proto()
    }
    pub fn last(&self) -> Option<&AExp<N, T>> {
        match self {
            Body::Proto { body, .. } => body.0.last(),
            Body::Func { body } => body.0.last(),
        }
    }
}

/// Useful constructors
impl<N, T> Decl<N, T> {
    pub fn proto(name: Fid, typevars: TypeVars, args: Args<N>, relation: BExp<N, T>, body: AExps<N, T>) -> Self {
        let sig = Sig { name, args, ret: Typ::bool() };
        let body = Body::Proto { relation, body };
        Decl { sig, typevars, body }
    }

    pub fn func(name: Fid, typevars: TypeVars, args: Args<N>, ret: Typ<N>, body: AExps<N, T>) -> Self {
        let sig = Sig { name, args, ret };
        let body = Body::Func { body };
        Decl { sig, typevars, body }
    }
}

/// A collection of declarations
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub struct Decls<N, T>(pub Vec<Decl<N, T>>);

/// Untyped body with symbolic sizes
pub type UBody =  Body<Size, Nothing>;

/// Concrete sized body
pub type CBody = Body<usize, Nothing>;

/// Typed body
pub type TBody = Body<usize, Typ<usize>>;

/// Untyped decl with symbolic sizes
pub type UDecl =  Decl<Size, Nothing>;

/// Concrete sized decl
pub type CDecl = Decl<usize, Nothing>;

/// Typed decl
pub type TDecl = Decl<usize, Typ<usize>>;

/// Untyped declarations with symbolic sizes
pub type UDecls =  Decls<Size, Nothing>;

/// Concrete sized declarations
pub type CDecls = Decls<usize, Nothing>;

/// Typed declarations
pub type TDecls = Decls<usize, Typ<usize>>;

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

impl<N, T> IntoIterator for Decls<N, T> {
    type Item = Decl<N, T>;
    type IntoIter = std::vec::IntoIter<Decl<N, T>>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<N, T> FromIterator<Decl<N, T>> for Decls<N, T> {
    fn from_iter<I: IntoIterator<Item = Decl<N, T>>>(iter: I) -> Self {
        Decls(iter.into_iter().collect())
    }
}

/// Traversable1 instance for Body (N)
impl<N, T> ToTraversal1<N> for Body<N, T> {
    type Output<Z> = Body<Z, T>;
    fn traverse1<Z, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Body<Z, T>, E> {
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

/// Traversable2 instance for Body (T)
impl<N, T> ToTraversal2<T> for Body<N, T> {
    type Output<Z> = Body<N, Z>;
    fn traverse2<Z, E>(self, f: &mut dyn FnMut(T) -> Result<Z, E>) -> Result<Body<N, Z>, E> {
        match self {
            Body::Proto { relation, body } =>
                Ok(Body::Proto {
                    body: body.traverse2(f)?,
                    relation: relation.traverse2(f)?,
                }),
            Body::Func { body } =>
                Ok(Body::Func {
                    body: body.traverse2(f)?,
                }),
        }
    }
}

impl TidTraversal for TBody {
    fn tid_traverse<E>(self, f: &mut dyn FnMut(Tid) -> Result<Tid, E>) -> Result<Self, E> {
        match self {
            Body::Proto { relation, body } =>
                Ok(TBody::Proto {
                    relation: relation.tid_traverse(f)?,
                    body: body.tid_traverse(f)?,
                }),
            Body::Func { body } =>
                Ok(TBody::Func {
                    body: body.tid_traverse(f)?,
                }),
        }
    }
}

/// Pretty printer instance for Body
impl<'a, D, N, A, T> Pretty<'a, D, A> for Body<N, T>
where
    T: Pretty<'a, D, A>,
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
impl<'a, D, N, A, T> Pretty<'a, D, A> for Decl<N, T>
where
    T: Pretty<'a, D, A>,
    D: DocAllocator<'a, A>,
    N: Clone + Pretty<'a, D, A> + 'a,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        let Decl { sig, typevars, body } = self;
        allocator.concat([
            if body.is_proto() { allocator.text("proto") } else { allocator.text("fn") },
            allocator.space(),
            typevars.pretty(allocator),
            sig.pretty(allocator),
            body.pretty(allocator)
        ])
    }

    fn is_nil(&self) -> bool {
        false
    }
}

/// Display instance calls the pretty printer
impl<'a, N, T> fmt::Display for Decl<N, T>
where
    T: Clone + Pretty<'a, BoxAllocator, ()> + 'a,
    N: Clone + Pretty<'a, BoxAllocator, ()> + 'a,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Decl<N, T> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}
/// Pretty instance for decls
impl <'a, D, N, A, T> Pretty<'a, D, A> for Decls<N, T>
where
    T: Pretty<'a, D, A>,
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
impl<'a, N, T> fmt::Display for Decls<N, T>
where
    T: Clone + Pretty<'a, BoxAllocator, ()> + 'a,
    N: Clone + Pretty<'a, BoxAllocator, ()> + 'a,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Decls<N, T> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
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
                let relation = BExp::from_pest(&mut Pairs::single(inner.next().unwrap()))?;
                // Protocol's body
                let body = AExps::from_pest(&mut inner)?;

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
                let body = AExps::from_pest(&mut inner)?;

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
        arg::Arg,
        id::Vid,
        range::Range,
        exp::{UAExp, UBExp},
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
        UBExp::equ(UAExp::varstr("a"), UAExp::varstr("a")),
        AExps(vec![
            UAExp::letx(Vid::from("x"), UAExp::from(3) * UAExp::varstr("a")),
            UAExp::verify(UBExp::equ(UAExp::varstr("x"), UAExp::varstr("x"))),
        ]),
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
        AExps(vec![
            UAExp::letx(Vid::from("x"), UAExp::from(3) * UAExp::ram(UAExp::from("a"), UAExp::from(0))),
            UAExp::varstr("x") + UAExp::varstr("x"),
        ]),
    ));
}

#[test]
fn fn_parser2() {
    let ex = concat!(
        "fn test<F: Field>(public a: F) -> F {\n",
        "    let v = [1,2,3];\n",
        "    p <- interpolate(v, [0,1,2]);\n",
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
        AExps(vec![
            UAExp::letx(Vid::from("v"), UAExp::vec(vec![UAExp::from(1), UAExp::from(2), UAExp::from(3)])),
            UAExp::logx(Vid::from("p"), UAExp::interpolate(UAExp::varstr("v"), UAExp::vec(vec![UAExp::from(0), UAExp::from(1), UAExp::from(2)]))),
            UAExp::logx(Vid::from("x"), UAExp::challenge(Tid::from("F"))),
            UAExp::app(Fid::from("p"), AExps(vec![UAExp::varstr("x")])),
        ]),
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
            UBExp::equ(UAExp::varstr("a"), UAExp::varstr("a")),
            AExps(vec![
                UAExp::letx(Vid::from("x"), UAExp::mul(UAExp::from(3), UAExp::varstr("a"))),
                UAExp::verify(UBExp::equ(UAExp::varstr("x"), UAExp::varstr("x"))),
            ]),
        ),
        UDecl::func(
            Fid::from("test"),
            TypeVars(vec![
                TypeVar::new("F", Kind::Field),
                TypeVar::new("N", Kind::Range(Range { start:0, step:1, end: 10 })),
            ]),
            Args(vec![Arg::public("a", Typ::vec(Typ::varstr("F"), Size::from("N")))]),
            Typ::varstr("F"),
            AExps(vec![
                UAExp::letx(Vid::from("x"), UAExp::mul(UAExp::from(3), UAExp::ram(UAExp::varstr("a"), UAExp::from(0)))),
                UAExp::varstr("x") + UAExp::varstr("x"),
            ]),
        ),
    ]));
}
