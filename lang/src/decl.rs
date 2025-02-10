use std::convert::From;
use std::fmt;
use std::ops::{Add, Div, Mul, Rem, Sub};
use share::{Pretty, Traversable1, Traversable2, DocAllocator, DocBuilder, Ctx, Set};

use crate::typ::TypeVar;
use crate::id::{Tid, Vid, Fid};
use crate::typ::{Typ, Size, Bin, Nothing};
use exp::{AExp, BExp, Arg};

/// Different kinds of declarations in zippel programming language.
/// It is parametrized by `A` the type of annotations.
#[derive(PartialEq, Eq, Clone)]
pub enum Decl<N, T> {
    /// A protocol declaration.
    ///
    /// # fields
    /// - `name`: The name/identifier of the protocol.
    /// - `generics`: A vector of type variables
    /// - `args`: A vector of arguments for the protocol.
    /// - `body`: The body of the protocol, represented as a vector of statements
    /// - `principal`: Who owns this protocol.
    /// - `assert`: The final assertion of the protocol.
    Proto {
        name: Fid,
        generics: Vec<TypeVar>,
        args: Vec<Arg<N>>,
        body: AExp<N, T>,
        relation: BExp<N, T>,
        verify: BExp<N, T>
    },

    /// A function declaration.
    ///
    /// # fields
    /// - `name`: The name/identifier of the protocol.
    /// - `generics`: A vector of type variables
    /// - `args`: A vector of arguments for the protocol.
    /// - `body`: The body of the protocol, represented as a vector of statements
    /// - `typ`: The return type of the function.
    Func {
        name: Fid,
        generics: Vec<TypeVar>,
        args: Vec<Arg<N>>,
        body: AExp<N, T>,
        typ: Typ<N>,
    },
}

/// Typed declaration
pub type TDecl<N, A> = Decl<N, (A, Typ<N>)>;

/// Traversable1 instance for Decl (N)
impl<N, T> Traversable1<N> for Decl<N, T> {
    type Output<Z> = Decl<Z, T>;
    fn traverse1<Z, E>(
        self,
        mut f: &mut dyn FnMut(N) -> Result<Z, E>,
    ) -> Result<Decl<Z, T>, E> {
        match self {
            Decl::Proto { name, generics, args, body, relation, verify } =>
                Ok(Decl::Proto {
                    name,
                    generics,
                    args: args.traverse1(f)?,
                    body: body.traverse1(f)?,
                    relation: relation.traverse1(f)?,
                    verify: verify.traverse1(f)?
                }),
            Decl::Func { name, generics, args, body, typ } =>
                Ok(Decl::Func {
                    name,
                    generics,
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
        mut f: &mut dyn FnMut(T) -> Result<Z, E>,
    ) -> Result<Decl<N, Z>, E> {
        match self {
            Decl::Proto { name, generics, args, body, relation, verify } =>
                Ok(Decl::Proto {
                    name,
                    generics,
                    args,
                    body: body.traverse2(f)?,
                    relation: relation.traverse2(f)?,
                    verify: verify.traverse2(f)?
                }),
            Decl::Func { name, generics, args, body, typ } =>
                Ok(Decl::Func {
                    name,
                    generics,
                    args,
                    body: body.traverse2(f)?,
                    typ
                }),
        }
    }
}

/// Getters for Decl
impl<N, T> Decl<N, T> {
    pub fn generics(&self) -> &Set<TypeVar> {
        match self {
            Decl::Proto { generics, .. }
            | Decl::Func { generics, .. } => generics
        }
    }
    pub fn name(&self) -> &Fid {
        match self {
            Decl::Proto { name, .. }
            | Decl::Func { name, .. } => name
        }
    }
    pub fn args(&self) -> &Vec<Arg<N>> {
         match self {
            Decl::Proto { args, .. }
            | Decl::Func { args, .. } => args
         }
    }
    pub fn body(&self) -> &AExp<N, T> {
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
    N: 'a + Clone + Pretty<'a, D, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        match self {
            Decl::Proto {
                name,
                generics,
                args,
                body,
                relation,
                verify
            } => allocator.concat([
                    allocator.text("proto<"),
                    principal.pretty(allocator),
                    allocator.text("> "),
                    name.pretty(allocator),
                    allocator.text(" <"),
                    allocator.intersperse(generics.into_iter().map(|g| g.pretty(allocator)), ", "),
                    allocator.text("> ("),
                    allocator.intersperse(args.into_iter().map(|x| x.pretty(allocator)), ", "),
                    allocator.text(") where ("),
                    relation.pretty(allocator),
                    allocator.text(") {"),
                    allocator.line(),
                    allocator.concat([
                        body.pretty(allocator),
                        allocator.line(),
                        verify.pretty(allocator),
                        allocator.line()
                    ]).indent(2),
                    allocator.text("}")
                ]),
            Decl::Func {
                name,
                generics,
                args,
                body,
                typ
            } => allocator.concat([
                    allocator.text("fn "),
                    name.pretty(allocator),
                    allocator.text(" <"),
                    allocator.intersperse(generics.into_iter().map(|g| g.pretty(allocator)), ", "),
                    allocator.text("> ("),
                    allocator.intercalate(allocator.text(", "), args.into_iter().map(|x| x.pretty(allocator))),
                    allocator.text(") -> "),
                    typ.pretty(allocator),
                    allocator.text(" {"),
                    allocator.line(),
                    allocator.concat([
                        body.pretty(allocator),
                        allocator.line(),
                    ]).indent(2),
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
    T: Clone + Pretty<'a, BoxAllocator, ()>,
    N: Clone + Pretty<'a, BoxAllocator, ()>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Decl<N, T> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(120, f)
    }
}
