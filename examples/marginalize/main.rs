use zippel::*;
use std::{path::PathBuf, time::Instant};
use backend::ArkBls12_381;
use share::Ctx;

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
    let analysis_start = Instant::now();
    let analysis = analysis_handler.minimal_analysis();
    let analysis_elapsed = analysis_start.elapsed();
    match &analysis.completeness {
        Ok(()) => println!("Completeness:   ✓"),
        Err(e) => println!("Completeness:   ✗ {}", e),
    }
    match &analysis.zk {
        Ok(()) => println!("ZK:             ✓"),
        Err(e) => println!("ZK:             ✗ {}", e),
    }
    println!("Analysis time:  {analysis_elapsed:.2?}");
}
