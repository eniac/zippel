use crate::ast::{Sig, Body, CSig};
use crate::ast::decl::{UDecls, UDecl, DeclError};
use crate::id::Tid;

use std::fmt;
use thiserror::Error;
use bumpalo::Bump;
use from_pest::{ConversionError, FromPest};
use pest::Parser;

use share::{Pretty, DocAllocator, DocBuilder, BoxAllocator, Ctx};
use crate::typ::Size;
use crate::parser::*;

/// Polymorphic Module, a collection of declarations indexed by their typevars and signature
pub struct Module<N>(pub Ctx<Sig<N>, Body<N>>);

impl<N: Clone> Clone for Module<N> where Sig<N>: Clone, Body<N>: Clone {
    fn clone(&self) -> Self { Module(self.0.clone()) }
}

impl<N: Ord + Clone> PartialEq for Module<N> where Sig<N>: Ord + PartialEq, Body<N>: PartialEq + Clone {
    fn eq(&self, other: &Self) -> bool { self.0 == other.0 }
}

impl<N: Ord + Clone> Eq for Module<N> where Sig<N>: Ord + Eq, Body<N>: Eq + Clone {}

impl<N: Ord + Clone> PartialOrd for Module<N> where Sig<N>: Ord + PartialOrd + Clone, Body<N>: PartialOrd + Clone {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> { self.0.partial_cmp(&other.0) }
}

impl<N: Ord + Clone> Ord for Module<N> where Sig<N>: Ord + Clone, Body<N>: Ord + Clone {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering { self.0.cmp(&other.0) }
}

impl<N: Ord + Clone> fmt::Debug for Module<N> where Sig<N>: Ord + fmt::Debug, Body<N>: fmt::Debug + Clone {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Module").field(&self.0).finish()
    }
}


#[derive(Error, PartialEq, Debug)]
pub enum ModuleError {
    #[error("Overlaping declarations: {0}")]
    OverlapDeclaration(CSig),
    #[error("Declaration error: {0}")]
    DeclarationError(#[from] DeclError),
    #[error("Declaration not found: {0}")]
    DeclarationNotFound(String),
}

/// Polymorphic module with symbolic sizes
pub type UModule = Module<Size>;

/// Polymorphic module with concrete sizes
pub type CModule = Module<usize>;

impl<N: Ord> Module<N> {
    pub fn len(&self) -> usize {
        self.0.len()
    }
    pub fn iter(&self) -> impl Iterator<Item = (&Sig<N>, &Body<N>)> + DoubleEndedIterator {
        self.0.iter()
    }
    pub fn get_names<'a>(&'a self) -> impl Iterator<Item = &'a str> {
        self.0.iter().map(|(sig, _)| sig.name.0.as_str())
    }
}

/// Polymorphic module with symbolic sizes
impl UModule {
    /// Entry point to the zippel compiler.
    /// Parse a Zippel declarations list into a polymorphic,
    /// untyped module, with symbolic sizes.
    pub fn from_str<'a>(input_str: &'a str) -> Result<Self, ConversionError<InputError<'a>>> {
        let mut pairs = ZippelParser::parse(Rule::decls, input_str).unwrap();
        let decls = UDecls::from_pest(&mut pairs)?;
        // Catch duplicate declarations here
        let mut m = Ctx::new();
        for d in decls.into_iter() {
            m.insert_with(d.sig, d.body,
                &|sig, _, _| Err(ConversionError::Malformed(InputError::DuplicateDecl(sig.clone()))))?;
        }
        Ok(Module(m))
    }

    /// Parse a file into a Zippel declarations list
    pub fn from_file<'a>(file: &str, allocator: &'a Bump) -> Result<Self, ConversionError<InputError<'a>>> {
        let input_str = std::fs::read_to_string(file).unwrap();
        let stored_str = allocator.alloc_str(&input_str);
        Self::from_str(stored_str)
    }

    pub fn iter_decls(&self) -> impl Iterator<Item = UDecl> + '_ {
        self.0.iter().map(|(sig, body)| UDecl { sig: sig.clone(), body: body.clone() })
    }

    /// Concretize sizes in all declarations to generate a CModule
    pub fn concretize(&self, sizes: &Ctx<Tid, usize>) -> Result<CModule, ModuleError> {
        let mut ctx = Ctx::new();

        for decl in self.iter_decls() {
             let all_substs = decl.get_size_substitutions(sizes)?;
             for mut substs in all_substs.into_iter() {
                // Merge externally-provided size values (e.g. S: Size) into the
                // substitution context so that concretize can resolve all Size::Var references
                for (k, v) in sizes.iter() {
                    substs.0.insert(k, v);
                }
                let cdecl = decl.concretize(&substs)?;
                 ctx.insert_with(cdecl.sig, cdecl.body,
                     &|sig, _, _| Err(ModuleError::OverlapDeclaration(sig.clone())))?;
             }
        }
        // Return the concretized module
        Ok(Module(ctx))
    }

}

impl<N: Ord + Clone> IntoIterator for Module<N> where Sig<N>: Ord + Clone, Body<N>: Clone {
    type Item = (Sig<N>, Body<N>);
    type IntoIter = share::CtxConsumingIter<(Sig<N>, Body<N>)>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<N: Ord + Clone> FromIterator<(Sig<N>, Body<N>)> for Module<N> where Sig<N>: Ord + Clone, Body<N>: Clone {
    fn from_iter<I: IntoIterator<Item = (Sig<N>, Body<N>)>>(iter: I) -> Self {
        Module(iter.into_iter().collect())
    }
}

/// Pretty printer instance
impl<'a, D, A, N> Pretty<'a, D, A> for Module<N>
where
    N: Pretty<'a, D, A> + Ord + Clone + 'a,
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
       allocator.intersperse(
            self.0.into_iter().map(|(sig, body)|
                    allocator.concat([
                        if body.is_proto() { allocator.text("proto") } else { allocator.text("fn") },
                        allocator.space(),
                        sig.pretty(allocator),
                        body.pretty(allocator),
                        allocator.hardline(),
                    ])),
       allocator.hardline())
    }

    fn is_nil(&self) -> bool {
        self.0.is_empty()
    }
}

/// Display instance calls the pretty printer
impl<'a, N> fmt::Display for Module<N>
where
    N: Clone + Ord + Pretty<'a, BoxAllocator, ()> + 'a,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Module<N> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

#[test]
fn from_decl_subst1() {
    let ex = concat!(
        "fn sum<N: 1..4, F: Field>(public a: [F; N]) -> F {\n",
        "    sum(a[0..2^(N-1)]) + sum(a[2^(N-1)..2^N])\n",
        "}\n",
        "fn sum<F: Field>(public a: [F; 0]) -> F {\n",
        "   a[0]\n",
        "}");
    let umod = UModule::from_str(ex).unwrap();
    assert_eq!(umod.len(), 2);
    let cmod = umod.concretize(&Ctx::new()).unwrap();
    assert_eq!(cmod.len(), 4);
}

#[test]
fn from_decl_duplicate() {
    let ex = concat!(
        "fn sum<N: 1..2, F: Field>(public a: [F; N]) -> F {\n",
        "    sum(a[0..2^(N-1)]) + sum(a[2^(N-1)..2^N])\n",
        "}\n",
        "fn sum<F: Field>(public a: [F; 1]) -> F {\n",
        "   a[0]\n",
        "}");
    assert!(UModule::from_str(ex).unwrap().concretize(&Ctx::new()).is_err());
}

#[test]
fn from_decl_underflow() {
    let ex = concat!(
        "fn sum<N: 0..3, F: Field>(public a: [F; N]) -> F {\n",
        "    sum(a[0..2^(N-1)]) + sum(a[2^(N-1)..2^N])\n",
        "}");
    assert!(UModule::from_str(ex).unwrap().concretize(&Ctx::new()).is_err());
}

#[test]
fn from_decl_subst2() {
    let ex = concat!(
       "fn sum<N: 1..4, F: Field>(public a: [F; N]) -> F {\n",
        "    sum(a[0..2^(N-1)]) + sum(a[2^(N-1)..2^N])\n",
        "}\n",
        "fn sum<F: Field>(public a: [F; 0]) -> F {\n",
        "   a[0]\n",
        "}\n",
        "fn prod_sum<N: 0..4, M: 0..3, F: Field>(public a: [F; N], public b: [F; M]) -> F {\n",
        "   sum(a) * sum(b)\n",
        "}\n");
    let umod = UModule::from_str(ex).unwrap();
    assert_eq!(umod.len(), 3);
    let cmod = umod.concretize(&Ctx::new()).unwrap();
    assert_eq!(cmod.len(), 16);
}
