use backend::ArkBls12_381;
use std::path::PathBuf;
use zippel::*;

fn main() {
    println!("=== Recursive Commit (ArkBls12_381, fn-only, compile-only) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/tests/ex_rec/ex_rec.zippel"));
    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    handler.parse();
    println!("Parse:          ✓ OK");
}
