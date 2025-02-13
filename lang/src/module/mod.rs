mod sizesubsts;
use std::fmt;

pub use sizesubsts::SizeSubsts;
use share::{Pretty, Traversable1, Traversable2, DocAllocator, DocBuilder, BoxAllocator, Ctx};
use crate::id::Fid;
use crate::decl::{Decl, UDecls};
use crate::typ::{EvalError, Nothing};

/// Module is a collection of declarations with concrete sizes
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub struct Module<T>(pub Ctx<(Fid, SizeSubsts), Decl<usize, T>>);

/// Module with no size substitutions
pub type UModule = Module<Nothing>;

impl UModule {
    /// Concretize sizes in all declarations to generate a module
    pub fn from_decls(decls: UDecls) -> Result<UModule, EvalError> {
        let mut ctx = Ctx::new();
        for decl in decls.into_iter() {
            // Generate all possible size substitutions for this declaration
            let all_substs = SizeSubsts::from_decl(&decl);

            // For each size substitution, evaluate the sizes in the declaration
            for substs in all_substs.iter() {
                // Evaluate all sizes, with [EvalError]
                let d = decl.clone().traverse1(&mut |s| s.eval(&substs.0))?;
                ctx.insert((d.name().clone(), substs.clone()), d);
            }
        }
        Ok(Module(ctx))
    }
}

/// Traversable1 instance for Module (T)
impl<T> Traversable1<T> for Module<T> {
    type Output<Z> = Module<Z>;
    fn traverse1<Z, E>(
        self,
        f: &mut dyn FnMut(T) -> Result<Z, E>,
    ) -> Result<Module<Z>, E> {
        Ok(Module(self.0.traverse2(&mut |x| x.traverse2(f))?))
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
            self.0.into_iter().map(|(_, decl)| decl.pretty(allocator)),
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
