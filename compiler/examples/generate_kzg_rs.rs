use std::fs;
use std::path::PathBuf;

use backend::ArkBls12_381;
use compiler::{CodegenMode, CodegenOptions, compile_with_options};
use share::Ctx;
use zippel::{ZippelArgs, ZippelHandler};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let workspace = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("compiler crate must be inside the workspace")
        .to_path_buf();
    let source = workspace.join("examples/kzg/kzg.zippel");
    let out_dir = workspace.join("examples/kzg-rs/src");

    let args = ZippelArgs::new(source);
    let mut handler = ZippelHandler::<ArkBls12_381>::new(args);
    handler.compile(&Ctx::new());

    fs::create_dir_all(&out_dir)?;

    let prover_options = CodegenOptions {
        mode: CodegenMode::Prover,
        session: "examples/kzg/kzg.zippel".to_string(),
        ..CodegenOptions::default()
    };
    let verifier_options = CodegenOptions {
        mode: CodegenMode::Verifier,
        session: "examples/kzg/kzg.zippel".to_string(),
        ..CodegenOptions::default()
    };

    let mut prover = fs::File::create(out_dir.join("prover.rs"))?;
    compile_with_options(
        handler.prover_graph.as_ref().unwrap(),
        &prover_options,
        &mut prover,
    )?;

    let mut verifier = fs::File::create(out_dir.join("verifier.rs"))?;
    compile_with_options(
        handler.verifier_graph.as_ref().unwrap(),
        &verifier_options,
        &mut verifier,
    )?;

    Ok(())
}
