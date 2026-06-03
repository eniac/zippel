use backend::ArkBls12_381;
use share::Ctx;
use std::path::PathBuf;
use zippel::*;

fn main() {
    println!("=== Sumcheck Utils / Stdlib (ArkBls12_381, compile-only) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/tests/stdlib/sumcheck_utils.zippel"));
    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    handler.compile(&Ctx::new());
    println!("Compilation:    ✓ OK");
}
