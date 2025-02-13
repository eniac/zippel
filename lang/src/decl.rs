use std::fmt;
use from_pest::{ConversionError, FromPest, Void};
use pest::Parser;
use pest::iterators::{Pair, Pairs};

use share::{Pretty, Traversable1, Traversable2, BoxAllocator, DocAllocator, DocBuilder};

use crate::typ::TypeVars;
use crate::id::Fid;
use crate::typ::{Typ, Size, Nothing};
use crate::arg::Args;
use crate::exp::{AExp, AExps, BExp};
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

/// Typed declaration
pub type TDecl<N, A> = Decl<N, (A, Typ<N>)>;

/// Untyped declaration with symbolic sizes
pub type UDecl =  Decl<Size, Nothing>;

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
            _ => unreachable!(),
        }
    }
}

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
    let pairs = ZippelParser::parse(Rule::decl, ex).unwrap();
    dbg!(&pairs);
    let decl = UDecl::from_pest(&mut pairs.into_iter()).unwrap();
    assert!(ZippelParser::parse(Rule::decl, ex).is_ok())
}

#[test]
fn fn_parser1() {
    let ex = concat!(
        "fn test<F: Field, N: 0..10>(public a: [F; N]) -> F {\n",
        "    let x = 3*a[0];\n",
        "    x + x\n",
        "}"
    );
    assert!(ZippelParser::parse(Rule::decl, ex).is_ok())
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
    assert!(ZippelParser::parse(Rule::decl, ex).is_ok())
}
