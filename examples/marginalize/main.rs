use backend::ArkBls12_381;
use share::Ctx;
use std::path::PathBuf;
use zippel::*;

fn main() {
    println!("=== Marginalize (ArkBls12_381, compile-only) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/marginalize/marginalize.zippel"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    handler.compile(&Ctx::new());
    println!("Compilation:    ✓ OK");

    // Static analysis (completeness & ZK)
    println!("\n--- Static Analysis ---");
    let analysis_args = ZippelArgs::new(PathBuf::from("examples/marginalize/marginalize.zippel"));
    let mut analysis_handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(analysis_args);
    let analysis = analysis_handler.minimal_analysis();
    match &analysis.completeness {
        Ok(()) => println!("Completeness:   ✓"),
        Err(e) => println!("Completeness:   ✗ {}", e),
    }
    match &analysis.zk {
        Ok(()) => println!("ZK:             ✓"),
        Err(e) => println!("ZK:             ✗ {}", e),
    }
}
