use backend::ArkBls12_381;
use std::path::PathBuf;
use zippel::*;

fn main() {
    println!("=== Hyrax Sum (ArkBls12_381, fn-only, compile-only) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/ex_hyrax_sum/ex_hyrax_sum.zippel"));
    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    handler.parse();
    println!("Parse:          ✓ OK");
}
