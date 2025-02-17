#![feature(extract_if)]
#![feature(btree_extract_if)]
mod context;
mod pretty;

pub use pretty::{Pretty, DocAllocator, DocBuilder, BoxAllocator};
pub use context::{Ctx, Set};

