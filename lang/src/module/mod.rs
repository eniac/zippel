pub mod decl;
pub mod sig;
pub mod arg;

pub use arg::{Arg, Args};
pub use sig::Sig;

use std::fmt;
use thiserror::Error;
use bumpalo::Bump;
use from_pest::{ConversionError, FromPest};
use pest::Parser;

use crate::typ::SizeSubsts;
use share::{Pretty, DocAllocator, DocBuilder, BoxAllocator, Ctx};
use share::traversal::ToTraversal1;
use sig::CSig;
use decl::{Body, UDecls};
use crate::typ::{Size, TypeVars, EvalError, RangeError, RangeTraversal};
use crate::parser::*;

/// Polymorphic Module, a collection of declarations indexed by their typevars and signature
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub struct Polymod<N>(pub Ctx<(TypeVars, Sig<N>), Body<N>>);

#[derive(Error, PartialEq, Debug)]
pub enum ModuleError {
    #[error("Overlaping declarations: {0}")]
    OverlapDeclaration(CSig),
    #[error("ModuleError: Error evaluating size type variables: \n\n{0}")]
    EvalError(#[from] EvalError),
    #[error("ModuleError: Invalid ranges in declaration {0}: \n\n{1}")]
    InvalidRange(CSig, RangeError),
}

/// Polymorphic module with symbolic sizes
pub type UPolymod = Polymod<Size>;

/// Polymorphic module with concrete sizes
pub type CPolymod = Polymod<usize>;

impl<N> Polymod<N> {
    pub fn len(&self) -> usize {
        self.0.len()
    }
}
/// Entry point to the zippel compiler.
/// Parse a Zippel declarations list into a polymorphic,
/// untyped module, with symbolic sizes.
impl UPolymod {
    pub fn from_str<'a>(input_str: &'a str) -> Result<Self, ConversionError<InputError<'a>>> {
        let mut pairs = ZippelParser::parse(Rule::decls, input_str).unwrap();
        let decls = UDecls::from_pest(&mut pairs)?;
        // Catch duplicate declarations here
        let mut m = Ctx::new();
        for d in decls.into_iter() {
            m.insert_with((d.typevars, d.sig), d.body,
                &|(_, sig), _, _| Err(ConversionError::Malformed(InputError::DuplicateDecl(sig.clone()))))?;
        }
        Ok(Polymod(m))
    }

    /// Parse a file into a Zippel declarations list
    pub fn from_file<'a>(file: &str, allocator: &'a Bump) -> Result<Self, ConversionError<InputError<'a>>> {
        let input_str = std::fs::read_to_string(file).unwrap();
        let stored_str = allocator.alloc_str(&input_str);
        Self::from_str(stored_str)
    }

    /// Concretize sizes in all declarations to generate a CPolymod
    pub fn concretize(self) -> Result<CPolymod, ModuleError> {
        let mut ctx = Ctx::new();
        for ((typevars, sig), body) in self.into_iter() {

            // Generate all possible size substitutions for this declaration (guaranteed non-empty)
            let all_substs = SizeSubsts::from_typevars(&typevars);

            // For each size substitution, evaluate the sizes
            for substs in all_substs.into_iter() {
                // Evaluate all sizes in the body
                let b = body.clone().traverse1(&mut |x| x.eval(&substs.0))?;

                // Evaluate all sizes in the signature
                let s = sig.clone().traverse1(&mut |x| x.eval(&substs.0))?;

                // Check the ranges
                b.clone().range_traverse(&mut |r| { r.check()?; Ok(r) })
                    .map_err(|e| ModuleError::InvalidRange(s.clone(), e))?;
                s.clone().range_traverse(&mut |r| { r.check()?; Ok(r) })
                    .map_err(|e| ModuleError::InvalidRange(s.clone(), e))?;

                // Remove typevars substituted
                let tv = typevars.clone().into_iter().filter(|tv| !substs.contains(&tv.id)).collect();

                // No size substitutions, just add the declaration with concrete sizes
                ctx.insert_with((tv, s), b,
                    &|(_, sig), _, _| Err(ModuleError::OverlapDeclaration(sig.clone())))?;
            }
        }
        // Return the concretized module
        Ok(Polymod(ctx))
    }

}

impl<N: Ord> IntoIterator for Polymod<N> {
    type Item = ((TypeVars, Sig<N>), Body<N>);
    type IntoIter = std::collections::btree_map::IntoIter<(TypeVars, Sig<N>), Body<N>>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<N: Ord> FromIterator<((TypeVars, Sig<N>), Body<N>)> for Polymod<N> {
    fn from_iter<I: IntoIterator<Item = ((TypeVars, Sig<N>), Body<N>)>>(iter: I) -> Self {
        Polymod(iter.into_iter().collect())
    }
}

/// Pretty printer instance
impl<'a, D, A, N> Pretty<'a, D, A> for Polymod<N>
where
    N: Pretty<'a, D, A> + Ord + Clone + 'a,
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
       allocator.intersperse(
            self.0.into_iter().map(|((tvs, sig), body)|
                    allocator.concat([
                        if body.is_proto() { allocator.text("proto") } else { allocator.text("fn") },
                        allocator.space(),
                        tvs.pretty(allocator),
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
impl<'a, N> fmt::Display for Polymod<N>
where
    N: Clone + Ord + Pretty<'a, BoxAllocator, ()> + 'a,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Polymod<N> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
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
    let umod = UPolymod::from_str(ex).unwrap();
    assert_eq!(umod.len(), 2);
    let cmod = umod.concretize().unwrap();
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
    assert!(UPolymod::from_str(ex).unwrap().concretize().is_err());
}

#[test]
fn from_decl_underflow() {
    let ex = concat!(
        "fn sum<N: 0..3, F: Field>(public a: [F; N]) -> F {\n",
        "    sum(a[0..2^(N-1)]) + sum(a[2^(N-1)..2^N])\n",
        "}");
    assert!(UPolymod::from_str(ex).unwrap().concretize().is_err());
}
#[test]
fn from_decl_subst2() {
    let ex = concat!(
       "fn sum<N: 1..4, F: Field>(public a: [F; N]) -> F {\n",
        "    sum(a[0..2^(N-1)]) + sum(a[2^(N-1)..2^N])\n",
        "}\n",
        "fn sum<F: Field>(public a: [F; 0]) -> F {\n",
        "   a[0]\n",
        "}",
        "fn prod_sum<N: 0..4, M: 0..3, F: Field>(public a: [F; N], public b: [F; M]) -> F {\n",
        "   sum(a) * sum(b)\n",
        "}");
    let umod = UPolymod::from_str(ex).unwrap();
    assert_eq!(umod.len(), 3);
    let cmod = umod.concretize().unwrap();
    assert_eq!(cmod.len(), 16);
}
