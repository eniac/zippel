use zippel::*;
use std::path::PathBuf;
use backend::ArkBls12_381;

fn main() {
    println!("Starting marginalize example");
    // Compile-only integration check for the Zippel stdlib-style marginalize helper.
    let args = ZippelArgs::new(PathBuf::from("examples/marginalize_test.zippel"))
        .with_pdf(PathBuf::from("marginalize_test.pdf"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    handler.compile();
    println!("Compiled and wrote PDF");
    println!("Finished marginalize example (compile-only test)");
}
