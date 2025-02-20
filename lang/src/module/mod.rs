use std::fmt;
use thiserror::Error;

use crate::typ::SizeSubsts;
use share::{Pretty, Traversal, DocAllocator, DocBuilder, BoxAllocator, Ctx};
use share::traversal::ToTraversal1;
use crate::id::Fid;
use crate::arg::Args;
use crate::decl::{Decl, UDecls};
use crate::typ::{EvalError, Nothing};

/// Module is a collection of declarations with concrete sizes
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub struct Module<T>(Ctx<(Fid, Args<usize>), Decl<usize, T>>);

/// Module with no size substitutions
pub type UModule = Module<Nothing>;

#[derive(Error, PartialEq, Debug)]
pub enum ModuleError {
    #[error("Duplicate declarations: \n---------------------- \n{0} \n=====================\n{1}")]
    DuplicateDeclaration(Decl<usize, Nothing>, Decl<usize, Nothing>),
    #[error("Error evaluating size type variables: \n-----------------------\n{0}")]
    EvalError(#[from] EvalError),
}

impl UModule {
    /// Concretize sizes in all declarations to generate a module
    pub fn from_decls(decls: UDecls) -> Result<UModule, ModuleError> {
        let mut ctx = Ctx::new();
        for decl in decls.into_iter() {
            // Generate all possible size substitutions for this declaration
            let all_substs = SizeSubsts::from_typevars(decl.typevars());

            if all_substs.is_empty() {
                let d = decl.clone()
                            .traverse1(&mut |s| s.eval(&Ctx::new()))?
                            .range_traverse(&mut |r| r.check())?;

                // No size substitutions, just add the declaration with concrete sizes
                ctx.insert_with(
                    (
                        d.name().clone(),
                        d.args().clone(),
                    ),
                    d,
                    &|d1, d2| Err(ModuleError::DuplicateDeclaration(d1, d2))
                )?;
                continue;
            }

            // For each size substitution, evaluate the sizes
            for substs in all_substs.iter() {
                // Evaluate all sizes, with [EvalError]
                let mut d = decl.clone()
                                .traverse1(&mut |s| s.eval(&substs.0))?
                                .range_traverse(&mut |r| r.check())?;

                // Remove typevars substituted
                for tid in substs.0.keys() {
                    d.remove_typevar(&tid);
                }
                ctx.insert_with(
                    (
                        d.name().clone(),
                        d.args().clone()
                    ),
                    d,
                    &|d1, d2| Err(ModuleError::DuplicateDeclaration(d1, d2))
                )?;
            }
        }
        Ok(Module(ctx))
    }
}

/// Traversable1 instance for Module (T)
struct ModuleTraversal1<T>(std::marker::PhantomData<T>);
impl<T, Z> Traversal<T, Z> for ModuleTraversal1<T> {
    type Domain = Module<T>;
    type Codomain = Module<Z>;
    fn traverse<E>(on: Self::Domain, f: &mut dyn FnMut(T) -> Result<Z, E>) -> Result<Self::Codomain, E> {
        Ok(Module(on.0.traverse2(&mut |x| x.traverse2(f))?))
    }
}

impl<T> ToTraversal1<T> for Module<T> {
    type Output<Z> = Module<Z>;
    fn traverse1<Z, E>(self, f: &mut dyn FnMut(T) -> Result<Z, E>) -> Result<Module<Z>, E> {
        ModuleTraversal1::traverse(self, f)
    }
}

/// Pretty printer instance
impl<'a, D, A, T> Pretty<'a, D, A> for Module<T>
where
    T: Pretty<'a, D, A>,
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
       allocator.intersperse(
            self.0.into_iter().map(|((fid, args), decl)|
                    allocator.concat([
                        fid.pretty(allocator),
                        allocator.text(" ("),
                        args.pretty(allocator),
                        allocator.text(") -> "),
                        allocator.hardline(),
                        decl.pretty(allocator).indent(2)
                    ])),
       allocator.hardline()
       )
    }

    fn is_nil(&self) -> bool {
        false
    }
}

/// Display instance calls the pretty printer
impl<'a, T> fmt::Display for Module<T>
where
    T: Clone + Pretty<'a, BoxAllocator, ()> ,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Module<T> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
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
    let decls = UDecls::from_str(ex).unwrap();
    let module = UModule::from_decls(decls).unwrap();
    assert_eq!(module.0.len(), 4);
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
    let decls = UDecls::from_str(ex).unwrap();
    assert!(UModule::from_decls(decls).is_err());
}

#[test]
fn from_decl_underflow() {
    let ex = concat!(
        "fn sum<N: 0..3, F: Field>(public a: [F; N]) -> F {\n",
        "    sum(a[0..2^(N-1)]) + sum(a[2^(N-1)..2^N])\n",
        "}");
    let decls = UDecls::from_str(ex).unwrap();
    assert!(UModule::from_decls(decls).is_err());
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
    let decls = UDecls::from_str(ex).unwrap();
    let module = UModule::from_decls(decls).unwrap();
    assert_eq!(module.0.len(), 16);
}
