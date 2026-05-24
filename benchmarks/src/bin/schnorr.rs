use benchmarks::schnorr::{native_side, zippel_side};

fn main() {
    println!("=== Schnorr: zippel vs. ark-crypto-primitives ===");
    println!("statement: prove knowledge of x s.t. h = g·x on BLS12-381 G1");
    println!();

    print!("zippel:     compiling... ");
    let mut z = zippel_side::Setup::new();
    println!("done");
    let zt = z.time_protocol();

    print!("ark-cp:     setup...     ");
    let n = native_side::Setup::new();
    println!("done");
    let nt = n.time_protocol();

    println!();
    println!("                  prove           verify");
    println!("zippel        {:>10.2?}      {:>10.2?}", zt.prove, zt.verify);
    println!("ark-cp        {:>10.2?}      {:>10.2?}", nt.prove, nt.verify);
    println!();
    println!(
        "ratio (zippel / ark-cp)       prove: {:.2}x    verify: {:.2}x",
        zt.prove.as_secs_f64() / nt.prove.as_secs_f64(),
        zt.verify.as_secs_f64() / nt.verify.as_secs_f64(),
    );
}
