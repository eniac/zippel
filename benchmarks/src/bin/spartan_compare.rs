use benchmarks::spartan::{DEFAULT_M, Setup as ZippelSetup, hyrax_split};
use clap::Parser;
use libspartan::{Instance, NIZK, NIZKGens};
use merlin::Transcript;
use std::time::{Duration, Instant};

#[derive(Parser, Debug, Clone)]
#[command(name = "spartan_compare", about = "zippel-Spartan-Hyrax vs MS Spartan NIZK")]
struct Args {
    #[arg(long, default_value_t = DEFAULT_M)]
    m: usize,
    #[arg(long, num_args = 2)]
    sweep: Option<Vec<usize>>,
}

fn main() {
    let args = Args::parse();

    let ms: Vec<usize> = match args.sweep {
        Some(v) => {
            assert_eq!(v.len(), 2, "--sweep takes exactly LO HI");
            (v[0]..=v[1]).collect()
        }
        None => vec![args.m],
    };

    println!("=== Spartan-NIZK: zippel-Hyrax vs Microsoft `libspartan` — both on Curve25519 ===");
    println!("zippel side    = `examples/spartan/main.rs` proto on `ArkCurve25519` (arkworks Edwards-form)");
    println!("native side    = `libspartan::NIZK` on Curve25519 via `curve25519-dalek` (Ristretto255)");
    println!("prove timer    = NIZK::prove (commit + sum-checks + PCS open) + matrix+io FS-bind");
    println!("verify timer   = NIZK::verify + matrix+io FS-bind");
    println!(
        "matvec timer   = Instance::is_sat — same Az/Bz/Cz that NIZK::prove computes\n\
                  internally, plus an O(N) equality check. Subtracted from\n\
                  raw native prove to match zippel (which precomputes Az/Bz/Cz\n\
                  outside its timer)."
    );
    println!(
        "matrix-bind    = throwaway merlin transcript absorbing serialized\n\
                  Instance + io bytes. Added to both native timers because\n\
                  zippel's runtime auto-absorbs every `instance` Inp on both\n\
                  prover and verifier; libspartan binds matrices implicitly\n\
                  via the verifier's eval step instead. Equalizes the byte-\n\
                  shoveling cost so the comparison reflects protocol +\n\
                  curve, not FS-binding strategy."
    );
    println!();
    println!(
        "  M | num_cons | hyrax-split  | zippel prove   zippel verify | native prove   matvec  prove-matvec   native verify | prove ratio  prove ratio (adj)  verify ratio | zippel pf  native pf"
    );
    println!(
        "----+----------+--------------+-----------------------------+----------------------------------------------------+----------------------------------------------+---------------------"
    );

    for &m in &ms {
        if m < 3 {
            eprintln!("[skip M={m}] Hyrax needs NW = M-1 >= 2; M=2 has NW=1 (degenerate)");
            continue;
        }

        let mut z_setup = ZippelSetup::new(m);
        let z = z_setup.time_protocol();
        assert!(z.passed, "zippel-Hyrax-Spartan FAILED at M={m}");

        let num_cons = 1usize << m;
        let num_vars = 1usize << (m - 1);
        let num_inputs = num_vars - 1;
        let (inst, vars, inputs) =
            Instance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);

        let n_matvec = {
            let mut best = Duration::MAX;
            for _ in 0..3 {
                let t0 = Instant::now();
                let sat = inst.is_sat(&vars, &inputs).expect("is_sat");
                let dt = t0.elapsed();
                assert!(sat, "synthetic R1CS unsat at M={m}");
                if dt < best {
                    best = dt;
                }
            }
            best
        };

        let gens = NIZKGens::new(num_cons, num_vars, num_inputs);

        let inst_bytes = vec![0u8; 3 * num_cons * 40];
        let inputs_bytes = bincode::serialize(&inputs).expect("serialize inputs");

        let mut pt = Transcript::new(b"phase3_spartan_compare");
        let prover_start = Instant::now();
        {
            let mut bind = Transcript::new(b"matrix_bind");
            bind.append_message(b"inst", &inst_bytes);
            bind.append_message(b"io", &inputs_bytes);
        }
        let proof = NIZK::prove(&inst, vars.clone(), &inputs, &gens, &mut pt);
        let n_prove = prover_start.elapsed();
        let n_prove_adj = n_prove.saturating_sub(n_matvec);
        let native_proof_bytes = bincode::serialize(&proof).expect("encode proof").len();

        let mut vt = Transcript::new(b"phase3_spartan_compare");
        let verifier_start = Instant::now();
        {
            let mut bind = Transcript::new(b"matrix_bind");
            bind.append_message(b"inst", &inst_bytes);
            bind.append_message(b"io", &inputs_bytes);
        }
        let verified_ok = proof.verify(&inst, &inputs, &mut vt, &gens).is_ok();
        let n_verify = verifier_start.elapsed();
        assert!(verified_ok, "native MS Spartan NIZK verify FAILED at M={m}");

        let (l, m_h) = hyrax_split(m);
        let split_lbl = format!("L={l}, M_h={m_h}");
        println!(
            " {m:>2} | {num_cons:>8} | {split_lbl:>12} | {:>11.2?}  {:>13.2?} | {:>11.2?}  {:>7.2?}  {:>12.2?}  {:>13.2?} | {:>10.2}x  {:>16.2}x  {:>11.2}x | {zpf:>7}B  {npf:>7}B",
            z.prove,
            z.verify,
            n_prove,
            n_matvec,
            n_prove_adj,
            n_verify,
            ratio(z.prove, n_prove),
            ratio(z.prove, n_prove_adj),
            ratio(z.verify, n_verify),
            zpf = z.proof_bytes,
            npf = native_proof_bytes,
        );
    }
}

fn ratio(a: Duration, b: Duration) -> f64 {
    a.as_secs_f64() / b.as_secs_f64()
}
