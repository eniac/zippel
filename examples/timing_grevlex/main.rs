//! Wall-clock timings of zippel's Buchberger driver for katsura_n /
//! cyclic_n in degrevlex, mirroring `~/git/ark-gb/examples/timing_grevlex.rs`.

use std::env;
use std::time::Instant;

use graph::analyses::groebner::GrevLexTerm;

#[path = "../../benches/groebner_shared.rs"]
mod shared;
use shared::{cyclic_basis, katsura_basis};

fn main() {
    let mut args = env::args().skip(1);
    let system = args
        .next()
        .expect("usage: timing_grevlex <katsura|cyclic> n1 n2 ...");
    let sizes: Vec<usize> = args
        .map(|s| s.parse().expect("size must be a positive integer"))
        .collect();
    let reduce: bool = env::var("ZIPPEL_TIMING_REDUCE")
        .map(|s| s == "1" || s.to_ascii_lowercase() == "true")
        .unwrap_or(true);

    println!(
        "# zippel buchberger wall-clock timings (BLS12-381 Fr, degrevlex, reduce={reduce})"
    );

    for n in sizes {
        let label = format!("{system}_{n}");
        let sys = match system.as_str() {
            "katsura" => katsura_basis::<GrevLexTerm>(n),
            "cyclic" => cyclic_basis::<GrevLexTerm>(n),
            other => panic!("unknown system {other:?}"),
        };
        // ark-gb always returns a reduced basis, so `reduce` is no longer
        // a separate path — both branches call `buchberger` (kept under
        // the flag for the timing label, not because the work differs).
        let _ = reduce;
        let t0 = Instant::now();
        let gb = sys.buchberger();
        let dt = t0.elapsed().as_secs_f64() * 1000.0;
        let len = gb.len();
        println!("{label:>14}  |G|={len:>3}  time={dt:>12.2} ms");
    }
}
