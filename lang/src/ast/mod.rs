/// Function/protocol parameters: qualifier, distribution, name and type.
pub mod arg;
/// Declaration bodies: protocols, functions and type aliases.
pub mod decl;
/// Expressions and binary operators — the bulk of the surface syntax.
pub mod exp;
/// A whole compilation unit: signatures mapped to declaration bodies.
pub mod module;
/// Strided integer ranges, used for sizes, slices and range-kinded typevars.
pub mod range;
/// Declaration signatures (name, type variables, arguments, return type).
pub mod sig;
/// Symbolic size arithmetic, evaluated away during concretization.
pub mod size;
/// Source-span wrapper attached to AST nodes by the parser.
pub mod spanned;

pub use arg::{Arg, Args, CArg, CArgs, GArg, GArgs};
pub use decl::{Body, CBody};
pub use exp::{BinOp, CExp, CExps, Exp, Exps, FreeVars, UExp, UExps};
pub use module::{CModule, Module, UModule};
pub use range::{CRange, Range, RangeError, RangeTraversal};
pub use sig::{CSig, Sig};
pub use size::{EvalError, Size};
pub use spanned::Spanned;
