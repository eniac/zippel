use std::fs;
use std::path::PathBuf;

use backend::ArkBls12_381;
use compiler::{compile_prover, compile_verifier};
use share::Ctx;
use zippel::{ZippelArgs, ZippelHandler};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let workspace = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("compiler crate must be inside the workspace")
        .to_path_buf();
    let source = workspace.join("examples/schnorr/schnorr.zippel");
    let out_dir = workspace.join("examples/schnorr-rs/src");

    let args = ZippelArgs::new(source);
    let mut handler = ZippelHandler::<ArkBls12_381>::new(args);
    handler.compile(&Ctx::new());

    fs::create_dir_all(&out_dir)?;

    let mut prover = fs::File::create(out_dir.join("prover.rs"))?;
    compile_prover(handler.prover_graph.as_ref().unwrap(), &mut prover)?;

    let mut verifier = fs::File::create(out_dir.join("verifier.rs"))?;
    compile_verifier(handler.verifier_graph.as_ref().unwrap(), &mut verifier)?;

    Ok(())
}
