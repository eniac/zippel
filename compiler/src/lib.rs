use std::io::Write;

use backend::ArkConfig;
use graph::Dag;

mod emit;
mod error;
mod expr;
mod options;
mod plan;
mod schedule;
mod transcript;
mod types;

pub use error::{CompilerError, Result};
pub use options::{CodegenMode, CodegenOptions, RustTarget};

pub fn compile_with_options<C, A, W>(
    dag: &Dag<C, A>,
    options: &CodegenOptions,
    writer: W,
) -> Result<()>
where
    C: ArkConfig,
    W: Write,
{
    emit::emit_dag(dag, options, writer)
}

pub fn compile_prover<C, A, W>(dag: &Dag<C, A>, writer: W) -> Result<()>
where
    C: ArkConfig,
    W: Write,
{
    let options = CodegenOptions::prover();
    compile_with_options(dag, &options, writer)
}

pub fn compile_verifier<C, A, W>(dag: &Dag<C, A>, writer: W) -> Result<()>
where
    C: ArkConfig,
    W: Write,
{
    let options = CodegenOptions::verifier();
    compile_with_options(dag, &options, writer)
}

#[cfg(any(test, feature = "testing"))]
pub mod testing {
    use backend::ATyp;

    use crate::{CodegenOptions, Result, types};

    pub fn render_type(typ: &ATyp, options: &CodegenOptions) -> Result<String> {
        types::render_type(typ, options)
    }
}
