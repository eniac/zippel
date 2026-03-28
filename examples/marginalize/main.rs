use zippel::*;
use std::path::PathBuf;
use backend::ArkBls12_381;
use share::Ctx;

fn main() {
    println!("=== Marginalize (ArkBls12_381, compile-only) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/marginalize_test.zippel"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    handler.compile(&Ctx::new());
    println!("Compilation:    ✓ OK");
}
