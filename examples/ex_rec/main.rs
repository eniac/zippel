use backend::ArkBls12_381;
use lang::id::Tid;
use share::Ctx;
use std::path::PathBuf;
use zippel::*;

fn main() {
    println!("=== Recursive Commit (ArkBls12_381, fn-only, compile-only) ===");
    println!("Note: This file defines fn helpers, not a proto. No prover/verifier to run.");
    let args = ZippelArgs::new(PathBuf::from("examples/ex_rec/ex_rec.zippel"));
    let result = std::panic::catch_unwind(|| {
        let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
        let mut sizes = Ctx::new();
        sizes.insert(&Tid::new("N"), &3);
        handler.compile(&sizes);
    });
    match result {
        Ok(_) => println!("Compilation:    ✓ OK"),
        Err(e) => {
            if let Some(msg) = e.downcast_ref::<String>() {
                println!("Compilation:    ✗ {}", msg);
            } else {
                println!("Compilation:    ✗ (recursive fn definitions overlap)");
            }
        }
    }
}
