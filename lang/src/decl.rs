use std::fmt;
use from_pest::{ConversionError, FromPest};
use pest::iterators::Pairs;
use pest::Parser;
use bumpalo::Bump;

use share::{Pretty, Traversable1, Traversable2, BoxAllocator, DocAllocator, DocBuilder};

use crate::typ::TypeVars;
use crate::id::Fid;
use crate::typ::{Typ, Size, Nothing};
use crate::arg::Args;
use crate::exp::{UAExp, UAExps, AExps, BExp};
use crate::parser::*;

/// Different kinds of declarations in zippel programming language.
/// It is parametrized by `T` the type of annotations.
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub enum Decl<N, T> {
    /// A protocol declaration.
    ///
    /// # fields
    /// - `name`: The name/identifier of the protocol.
    /// - `typevars`: A vector of type variables
    /// - `args`: A vector of arguments for the protocol.
    /// - `body`: The body of the protocol, represented as a vector of statements
    /// - `principal`: Who owns this protocol.
    /// - `assert`: The final assertion of the protocol.
    Proto {
        name: Fid,
        typevars: TypeVars,
        args: Args<N>,
        relation: BExp<N, T>,
        body: AExps<N, T>,
    },

    /// A function declaration.
    ///
    /// # fields
    /// - `name`: The name/identifier of the protocol.
    /// - `typevars`: A vector of type variables
    /// - `args`: A vector of arguments for the protocol.
    /// - `body`: The body of the protocol, represented as a vector of statements
    /// - `typ`: The return type of the function.
    Func {
        name: Fid,
        typevars: TypeVars,
        args: Args<N>,
        typ: Typ<N>,
        body: AExps<N, T>,
    },
}

/// A collection of declarations
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub struct Decls<N, T>(pub Vec<Decl<N, T>>);

/// Typed declaration
pub type TDecl<N, A> = Decl<N, (A, Typ<N>)>;

/// Untyped declaration with symbolic sizes
pub type UDecl =  Decl<Size, Nothing>;

/// Typed declarations
pub type TDecls<N, A> = Decls<N, (A, Typ<N>)>;

/// Untyped declarations with symbolic sizes
pub type UDecls =  Decls<Size, Nothing>;

impl UDecl {
    pub fn from_str<'a>(input_str: &'a str) -> Result<Self, ConversionError<InputError<'a>>> {
        let mut pairs = ZippelParser::parse(Rule::decl, input_str).unwrap();
        UDecl::from_pest(&mut pairs)
    }
}

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

impl IntoIterator for UDecls {
    type Item = UDecl;
    type IntoIter = std::vec::IntoIter<UDecl>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl FromIterator<UDecl> for UDecls {
    fn from_iter<I: IntoIterator<Item = UDecl>>(iter: I) -> Self {
        Decls(iter.into_iter().collect())
    }
}

/// Traversable1 instance for Decl (N)
impl<N, T> Traversable1<N> for Decl<N, T> {
    type Output<Z> = Decl<Z, T>;
    fn traverse1<Z, E>(
        self,
        f: &mut dyn FnMut(N) -> Result<Z, E>,
    ) -> Result<Decl<Z, T>, E> {
        match self {
            Decl::Proto { name, typevars, args, relation, body } =>
                Ok(Decl::Proto {
                    name,
                    typevars,
                    args: args.traverse1(f)?,
                    body: body.traverse1(f)?,
                    relation: relation.traverse1(f)?,
                }),
            Decl::Func { name, typevars, args, typ, body } =>
                Ok(Decl::Func {
                    name,
                    typevars,
                    args: args.traverse1(f)?,
                    body: body.traverse1(f)?,
                    typ: typ.traverse1(f)?
                }),
        }
    }
}

impl<N, T> Traversable2<T> for Decl<N, T> {
    type Output<Z> = Decl<N, Z>;
    fn traverse2<Z, E>(
        self,
        f: &mut dyn FnMut(T) -> Result<Z, E>,
    ) -> Result<Decl<N, Z>, E> {
        match self {
            Decl::Proto { name, typevars, args, relation, body } =>
                Ok(Decl::Proto {
                    name,
                    typevars,
                    args,
                    relation: relation.traverse2(f)?,
                    body: body.traverse2(f)?,
                }),
            Decl::Func { name, typevars, args, typ, body } =>
                Ok(Decl::Func {
                    name,
                    typevars,
                    args,
                    typ,
                    body: body.traverse2(f)?,
                }),
        }
    }
}

/// Traversable1 instance for Decls (N)
impl<N, T> Traversable1<N> for Decls<N, T> {
    type Output<Z> = Decls<Z, T>;
    fn traverse1<Z, E>(
        self,
        f: &mut dyn FnMut(N) -> Result<Z, E>,
    ) -> Result<Decls<Z, T>, E> {
        Ok(Decls(self.0.into_iter().map(|d| d.traverse1(f)).collect::<Result<_, _>>()?))
    }
}

impl<N, T> Traversable2<T> for Decls<N, T> {
    type Output<Z> = Decls<N, Z>;
    fn traverse2<Z, E>(
        self,
        f: &mut dyn FnMut(T) -> Result<Z, E>,
    ) -> Result<Decls<N, Z>, E> {
        Ok(Decls(self.0.into_iter().map(|d| d.traverse2(f)).collect::<Result<_, _>>()?))
    }
}

/// Getters for Decl
impl<N, T> Decl<N, T> {
    pub fn typevars(&self) -> &TypeVars {
        match self {
            Decl::Proto { typevars, .. }
            | Decl::Func { typevars, .. } => typevars
        }
    }
    pub fn name(&self) -> &Fid {
        match self {
            Decl::Proto { name, .. }
            | Decl::Func { name, .. } => name
        }
    }
    pub fn args(&self) -> &Args<N> {
         match self {
            Decl::Proto { args, .. }
            | Decl::Func { args, .. } => args
         }
    }
    pub fn body(&self) -> &AExps<N, T> {
        match self {
            Decl::Proto { body, .. }
            | Decl::Func { body, .. } => body
        }
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
        match self {
            Decl::Proto {
                name,
                typevars,
                args,
                relation,
                body,
            } => allocator.concat([
                    allocator.text("proto "),
                    name.pretty(allocator),
                    if <TypeVars as Pretty<'a, D, A>>::is_nil(&typevars) {
                        allocator.nil()
                    } else {
                        allocator.concat([
                            allocator.text("<"),
                            typevars.pretty(allocator),
                            allocator.text(">")
                        ])
                    },
                    args.pretty(allocator),
                    allocator.text(") where ("),
                    relation.pretty(allocator),
                    allocator.text(") {"),
                    allocator.line(),
                    body.pretty(allocator).indent(2),
                    allocator.text("}")
                ]),
            Decl::Func {
                name,
                typevars,
                args,
                body,
                typ
            } => allocator.concat([
                    allocator.text("fn "),
                    name.pretty(allocator),
                    if <TypeVars as Pretty<'a, D, A>>::is_nil(&typevars) {
                        allocator.nil()
                    } else {
                        allocator.concat([
                            allocator.text("<"),
                            typevars.pretty(allocator),
                            allocator.text(">")
                        ])
                    },
                    args.pretty(allocator),
                    allocator.text(") -> "),
                    typ.pretty(allocator),
                    allocator.text(" {"),
                    allocator.line(),
                    body.pretty(allocator).indent(2),
                    allocator.text("}")
                ]),
        }
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
                Ok(Decl::Proto {
                    name,
                    typevars,
                    args,
                    relation,
                    body,
                })
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
                let typ = Typ::from_pest(&mut inner)?;
                // Function's body
                let body = AExps::from_pest(&mut inner)?;
                Ok(Decl::Func {
                    name,
                    typevars,
                    args,
                    typ,
                    body,
                })
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
        exp::UBExp,
        typ::{Kind, TypeVar}
};

#[test]
fn proto_easy() {
    let ex =
        "proto test<F: Field>(public a: F) where a == a { verify(a == a) }";

    let pairs = ZippelParser::parse(Rule::decl, ex).unwrap();
    let decl = UDecl::from_pest(&mut pairs.into_iter()).unwrap();
    println!("{}", decl);
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
    assert_eq!(UDecl::from_pest(&mut pairs).unwrap(), UDecl::Proto {
        name: Fid::from("test"),
        typevars: TypeVars(vec![TypeVar::new("F", Kind::Field)]),
        args: Args(vec![Arg::public("a", Typ::varstr("F"))]),
        relation: UBExp::eq(UAExp::varstr("a"), UAExp::varstr("a")),
        body: AExps(vec![
            UAExp::letx(Vid::from("x"), UAExp::from(3) * UAExp::varstr("a")),
            UAExp::verify(UBExp::eq(UAExp::varstr("x"), UAExp::varstr("x"))),
        ]),
    });
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
    assert_eq!(UDecl::from_pest(&mut pairs).unwrap(), UDecl::Func {
        name: Fid::from("test"),
        typevars: TypeVars(vec![
            TypeVar::new("F", Kind::Field),
            TypeVar::new("N", Kind::Range(Range { start: 0, step: 1, end: 10 }))
        ]),
        args: Args(vec![Arg::private("a", Typ::vec(Typ::varstr("F"), Size::from("N")))]),
        typ: Typ::varstr("F"),
        body: AExps(vec![
            UAExp::letx(Vid::from("x"), UAExp::from(3) * UAExp::ram(UAExp::from("a"), UAExp::from(0))),
            UAExp::varstr("x") + UAExp::varstr("x"),
        ]),
    });
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
    assert_eq!(UDecl::from_pest(&mut pairs).unwrap(), UDecl::Func {
        name: Fid::from("test"),
        typevars: TypeVars(vec![TypeVar::new("F", Kind::Field)]),
        args: Args(vec![Arg::public("a", Typ::varstr("F"))]),
        typ: Typ::varstr("F"),
        body: AExps(vec![
            UAExp::letx(Vid::from("v"), UAExp::vec(vec![UAExp::from(1), UAExp::from(2), UAExp::from(3)])),
            UAExp::logx(Vid::from("p"), UAExp::interpolate(UAExp::varstr("v"), UAExp::vec(vec![UAExp::from(0), UAExp::from(1), UAExp::from(2)]))),
            UAExp::logx(Vid::from("x"), UAExp::challenge(Typ::varstr("F"))),
            UAExp::app(Fid::from("p"), AExps(vec![UAExp::varstr("x")])),
        ]),
    });
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
        UDecl::Proto {
            name: Fid::from("test"),
            typevars: TypeVars(vec![TypeVar::new("F", Kind::Field)]),
            args: Args(vec![Arg::public("a", Typ::varstr("F"))]),
            relation: UBExp::eq(UAExp::varstr("a"), UAExp::varstr("a")),
            body: AExps(vec![
                UAExp::letx(Vid::from("x"), UAExp::mul(UAExp::from(3), UAExp::varstr("a"))),
                UAExp::verify(UBExp::eq(UAExp::varstr("x"), UAExp::varstr("x"))),
            ]),
        },
        UDecl::Func {
            name: Fid::from("test"),
            typevars: TypeVars(vec![
                TypeVar::new("F", Kind::Field),
                TypeVar::new("N", Kind::Range(Range { start:0, step:1, end: 10 })),
            ]),
            args: Args(vec![Arg::public("a", Typ::vec(Typ::varstr("F"), Size::from("N")))]),
            typ: Typ::varstr("F"),
            body: AExps(vec![
                UAExp::letx(Vid::from("x"), UAExp::mul(UAExp::from(3), UAExp::ram(UAExp::varstr("a"), UAExp::from(0)))),
                UAExp::varstr("x") + UAExp::varstr("x"),
            ]),
        },
    ]));
}
