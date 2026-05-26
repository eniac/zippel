use std::io::Write;

use backend::ArkConfig;
use graph::Dag;

use crate::error::Result;
use crate::options::CodegenOptions;

pub(crate) fn emit_dag<C, A, W>(
    _dag: &Dag<C, A>,
    _options: &CodegenOptions,
    _writer: W,
) -> Result<()>
where
    C: ArkConfig,
    W: Write,
{
    Ok(())
}
