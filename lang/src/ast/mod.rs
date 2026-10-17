/// The arena expression trees live in.
pub mod arena;
/// Function/protocol parameters: qualifier, distribution, name and type.
pub mod arg;
/// Declaration bodies: protocols, functions and type aliases.
pub mod decl;
/// What a `random` or `challenge` sample excludes.
pub mod exclusion;
/// Expressions and binary operators — the bulk of the surface syntax.
pub mod exp;
mod minimal_sizes;
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
/// The shape of expression nodes: their children, and the variables each child sees bound.
pub mod walk;

pub use arena::{ExpId, ExpRef, Expr, Exprs};
pub use arg::{Arg, Args, CArg, CArgs, GArg, GArgs};
pub use decl::{Body, BodyTypes, CBody};
pub use exclusion::Exclusion;
pub use exp::{
    BinOp, CExp, CExpr, CExps, CRef, Exp, ExpExclusion, ExpLiteral, ExpTraversal, Exps, UExp,
    UExpr, UExps, URef,
};
pub use minimal_sizes::{
    MAX_DEFAULT_SIZE, SizeRejection, SizeSearchError, SizeSearchLimit, SizeSearchStage,
    minimal_sizes,
};
pub use module::{CModule, Module, TypedModule, UModule};
pub use range::{CRange, Range, RangeError, RangeTraversal};
pub use sig::{CSig, Sig};
pub use size::{EvalError, Size};
pub use spanned::Spanned;
pub use walk::{Children, Visit, Walk};
