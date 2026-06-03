use backend::ArkBls12_381;
use std::path::PathBuf;
use zippel::*;

fn main() {
    println!("=== Pairing (ArkBls12_381, fn-only, compile-only) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/tests/ex_pairing/ex_pairing.zippel"));
    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    handler.parse();
    println!("Parse:          ✓ OK");
}
