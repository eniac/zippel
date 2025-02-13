#![feature(extract_if)]
#![feature(btree_extract_if)]
mod context;
mod traits;

pub use pretty::{DocAllocator, DocBuilder, BoxAllocator};
pub use traits::{Traversable1, Traversable2, Traversable3, Pretty, Proj1, Proj2};
pub use context::{Ctx, Set};

