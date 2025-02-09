use std::convert::From;
use std::fmt;
use std::ops::{Add, Div, Mul, Rem, Sub};
use pretty::{BoxAllocator, DocAllocator, DocBuilder};

use crate::lang::types::syntax::TypeVar;
use crate::lang::{
    id::{Tid, Vid, Fid},
    context::{Ctx, Set},
    types::constraints::Constr,
    syntax::exp::{AExp, BExp, Arg},
    traits::{Pretty, Traversable1},
    types::{Nothing, Size, Bin, Typ},
};

/// Different kinds of declarations in zippel programming language.
/// It is parametrized by `A` the type of annotations.
#[derive(PartialEq, Eq, Clone)]
pub enum Decl<T> {
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
        generics: Set<TypeVar>,
        args: Vec<Arg>,
        body: AExp<T>,
        relation: BExp<T>,
        verify: BExp<T>
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
        generics: Set<TypeVar>,
        args: Vec<Arg>,
        body: AExp<T>,
        typ: Typ,
    },
}

/// Typed declaration
pub type TDecl<A> = Decl<(A, Typ)>;

/// Traversable2 instance for Decl (N)
impl<T> Traversable1<T> for Decl<T> {
    type Output<Z> = Decl<Z>;
    fn traverse1<Z, E>(
        self,
        mut f: &mut dyn FnMut(T) -> Result<Z, E>,
    ) -> Result<Decl<Z>, E> {
        match self {
            Decl::Proto { name, generics, args, body, principal, relation, assert } =>
                Ok(Decl::Proto {
                    name,
                    generics,
                    args,
                    body: body.traverse1(f)?,
                    principal,
                    relation: relation.traverse1(f)?,
                    assert: assert.traverse1(f)?
                }),
            Decl::Func { name, generics, args, body, typ } =>
                Ok(Decl::Func {
                    name,
                    generics,
                    args,
                    body: body.traverse1(f)?,
                    typ
                }),
        }
    }
}

/// Getters for Decl
impl<T> Decl<T> {
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
    pub fn args(&self) -> &Vec<Arg> {
         match self {
            Decl::Proto { args, .. }
            | Decl::Func { args, .. } => args
         }
    }
    pub fn body(&self) -> &AExp<T> {
        match self {
            Decl::Proto { body, .. }
            | Decl::Func { body, .. } => body
        }
    }
}

/// Pretty printer instance
impl<'a, D, A, T> Pretty<'a, D, A> for Decl<T>
where
    T: Pretty<'a, D, A>,
    D: DocAllocator<'a, A>,
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
                principal,
                relation,
                assert
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
                        assert.pretty(allocator),
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
impl<'a, T> fmt::Display for Decl<T>
where
    T: Clone + Pretty<'a, BoxAllocator, ()>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Decl<T> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(120, f)
    }
}
