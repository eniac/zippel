use ark_ff::{Field, Zero};
use ark_std::UniformRand;
use backend::{ArkConfig, ArkCurve25519, PolyVariant, Value, VirtualPolynomial};
use lang::id::{Tid, Vid};
use rand::Rng;
use share::Ctx;
use std::{
    fs::OpenOptions,
    io::Write,
    path::{Path, PathBuf},
    time::{Duration, Instant},
};
use zippel::*;

#[derive(Clone, Debug)]
struct RunOpts {
    sweep: Vec<usize>,
    invalid: bool,
    csv_path: Option<String>,
    manual_zippel: Option<String>,
}

fn parse_args() -> RunOpts {
    let mut args = std::env::args().skip(1);
    let mut sweep: Vec<usize> = Vec::new();
    let mut invalid = false;
    let mut csv_path: Option<String> = None;
    let mut manual_zippel: Option<String> = None;

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--m" => {
                let v: usize = args
                    .next()
                    .expect("--m expects an integer")
                    .parse()
                    .expect("invalid --m");
                sweep.push(v);
            }
            "--sweep" => {
                let lo: usize = args
                    .next()
                    .expect("--sweep expects LO HI")
                    .parse()
                    .expect("invalid --sweep LO");
                let hi: usize = args
                    .next()
                    .expect("--sweep expects LO HI")
                    .parse()
                    .expect("invalid --sweep HI");
                sweep.extend(lo..=hi);
            }
            "--invalid" => {
                invalid = true;
            }
            "--csv" => {
                csv_path = Some(args.next().expect("--csv expects PATH"));
            }
            "--manual-zippel" => {
                manual_zippel = Some(args.next().expect("--manual-zippel expects PATH"));
            }
            other => {
                eprintln!("unknown arg: {other}");
                std::process::exit(2);
            }
        }
    }

    if sweep.is_empty() {
        sweep.push(3);
    }

    RunOpts {
        sweep,
        invalid,
        csv_path,
        manual_zippel,
    }
}

#[derive(Clone, Debug)]
struct RunResult {
    m: usize,
    prover: Duration,
    verifier: Duration,
    proof_bytes: usize,
    passed: bool,
}

fn main() {
    let opts = parse_args();

    println!("=== Spartan-NIZK (PIOP + Hyrax PCS, ArkCurve25519) ===");
    println!(
        "sweep: {:?}{}",
        opts.sweep,
        if opts.invalid {
            "    [mode: --invalid → expect Verification FAILED]"
        } else {
            ""
        }
    );

    let mut results: Vec<RunResult> = Vec::new();
    for &m in &opts.sweep {
        let r = run_one(m, opts.invalid, opts.manual_zippel.as_deref());
        results.push(r.clone());
        let (l, m_h) = hyrax_split(m);
        println!(
            "M={m:>2}  num_cons={n:>8}  |w|={w:>8}  |io|={io:>8}  hyrax=(L={l},M_h={m_h})  prover={prover:>10.2?}  verifier={verifier:>10.2?}  proof={bytes:>7}B  verdict={verdict}",
            n = 1usize << m,
            w = 1usize << (m - 1),
            io = (1usize << (m - 1)) - 1,
            prover = r.prover,
            verifier = r.verifier,
            bytes = r.proof_bytes,
            verdict = if r.passed { "PASS" } else { "FAIL" },
        );
    }

    if let Some(path) = opts.csv_path {
        emit_csv(&path, &results);
    }
}

const fn hyrax_split(m: usize) -> (usize, usize) {
    let nw = m - 1;
    let l = nw / 2;
    let m_h = nw - l;
    (l, m_h)
}

fn run_one(m: usize, invalid: bool, manual_zippel: Option<&str>) -> RunResult {
    assert!(
        m >= 3,
        "M must be >= 3 (Hyrax needs NW = M-1 >= 2 to split L,M_h both >= 1)"
    );

    let zippel_path = manual_zippel.map_or_else(
        || PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/spartan/spartan.zippel"),
        std::path::PathBuf::from,
    );

    let args = ZippelArgs::new(zippel_path);
    let mut handler: ZippelHandler<ArkCurve25519> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("M"), &m);
    handler.compile(&sizes);

    let mut inputs = prover_create_inputs(m);
    if invalid {
        type F = <ArkCurve25519 as ArkConfig>::F;
        if let Some(v) = inputs.get(&Vid("az".to_string()))
            && let Value::VecScalar(mut a) = v.clone()
        {
            a[0] += F::from(7u64);
            inputs.insert(&Vid("az".to_string()), &Value::VecScalar(a));
        }
    }
    let prover_start = Instant::now();
    let proof = handler.run_prover(&inputs).expect("run_prover failed");
    let prover_elapsed = prover_start.elapsed();
    let proof_bytes = proof_size_bytes::<ArkCurve25519>(&proof);
    let verifier_start = Instant::now();
    let verifier_result = handler.run_verifier(&proof).expect("run_verifier failed");
    let verifier_elapsed = verifier_start.elapsed();
    if std::env::var("SPARTAN_DEBUG_VERIFIES").is_ok() {
        for (i, v) in verifier_result.iter().enumerate() {
            eprintln!("  verify[{i}] = {v}");
        }
    }
    let passed = check_verification(&verifier_result);

    RunResult {
        m,
        prover: prover_elapsed,
        verifier: verifier_elapsed,
        proof_bytes,
        passed,
    }
}

fn emit_csv(path: &str, results: &[RunResult]) {
    let header = "m,num_constraints,witness_len,io_len,prover_ms,verifier_ms,proof_bytes,passed\n";
    if path == "-" {
        print!("{header}");
        for r in results {
            println!(
                "{m},{n},{w},{io},{p:.3},{v:.3},{b},{ok}",
                m = r.m,
                n = 1usize << r.m,
                w = 1usize << (r.m - 1),
                io = (1usize << (r.m - 1)) - 1,
                p = r.prover.as_secs_f64() * 1000.0,
                v = r.verifier.as_secs_f64() * 1000.0,
                b = r.proof_bytes,
                ok = r.passed,
            );
        }
    } else {
        let need_header = !Path::new(path).exists();
        let mut f = OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)
            .expect("opening csv");
        if need_header {
            f.write_all(header.as_bytes()).expect("write header");
        }
        for r in results {
            writeln!(
                f,
                "{m},{n},{w},{io},{p:.3},{v:.3},{b},{ok}",
                m = r.m,
                n = 1usize << r.m,
                w = 1usize << (r.m - 1),
                io = (1usize << (r.m - 1)) - 1,
                p = r.prover.as_secs_f64() * 1000.0,
                v = r.verifier.as_secs_f64() * 1000.0,
                b = r.proof_bytes,
                ok = r.passed,
            )
            .expect("write row");
        }
    }
}

struct R1csInstance<F> {
    mat_a: Vec<(usize, usize, F)>,
    mat_b: Vec<(usize, usize, F)>,
    mat_c: Vec<(usize, usize, F)>,
    io: Vec<F>,
    w: Vec<F>,
}

fn random_r1cs<F, R>(rng: &mut R, m: usize, w: &[F], io: &[F]) -> R1csInstance<F>
where
    F: Field,
    R: Rng + ?Sized,
{
    const K_NNZ_PER_ROW: usize = 1;
    let num_vars = w.len() + io.len() + 1;
    assert_eq!(num_vars, m, "z = w ++ io ++ [1] must have length m");

    let mut z = Vec::with_capacity(m);
    z.extend_from_slice(w);
    z.extend_from_slice(io);
    z.push(F::from(1u64));

    let const_col = m - 1;
    let pick_k_cols = |rng: &mut R, force_include: Option<usize>| -> Vec<usize> {
        let mut cols: Vec<usize> = Vec::with_capacity(K_NNZ_PER_ROW);
        if let Some(c) = force_include {
            cols.push(c);
        }
        while cols.len() < K_NNZ_PER_ROW && cols.len() < m {
            let c = rng.gen_range(0..m);
            if !cols.contains(&c) {
                cols.push(c);
            }
        }
        cols
    };
    let mut mat_a: Vec<(usize, usize, F)> = Vec::with_capacity(K_NNZ_PER_ROW * m);
    let mut mat_b: Vec<(usize, usize, F)> = Vec::with_capacity(K_NNZ_PER_ROW * m);
    let mut mat_c: Vec<(usize, usize, F)> = Vec::with_capacity(K_NNZ_PER_ROW * m);

    for i in 0..m {
        let a_cols = pick_k_cols(rng, None);
        let b_cols = pick_k_cols(rng, None);
        let c_cols = pick_k_cols(rng, Some(const_col));

        let a_vals: Vec<F> = (0..a_cols.len()).map(|_| F::rand(rng)).collect();
        let b_vals: Vec<F> = (0..b_cols.len()).map(|_| F::rand(rng)).collect();
        let mut c_vals: Vec<F> = (0..c_cols.len()).map(|_| F::rand(rng)).collect();

        let az_i: F = a_cols
            .iter()
            .zip(a_vals.iter())
            .map(|(c, v)| z[*c] * *v)
            .sum();
        let bz_i: F = b_cols
            .iter()
            .zip(b_vals.iter())
            .map(|(c, v)| z[*c] * *v)
            .sum();
        let target = az_i * bz_i;

        let const_col_pos_in_c = c_cols
            .iter()
            .position(|&c| c == const_col)
            .expect("c_cols must include const_col");
        let other: F = c_cols
            .iter()
            .zip(c_vals.iter())
            .enumerate()
            .filter(|(idx, _)| *idx != const_col_pos_in_c)
            .map(|(_, (c, v))| z[*c] * *v)
            .sum();
        c_vals[const_col_pos_in_c] = target - other;

        for (c, v) in a_cols.iter().zip(a_vals.iter()) {
            mat_a.push((i, *c, *v));
        }
        for (c, v) in b_cols.iter().zip(b_vals.iter()) {
            mat_b.push((i, *c, *v));
        }
        for (c, v) in c_cols.iter().zip(c_vals.iter()) {
            mat_c.push((i, *c, *v));
        }
    }

    R1csInstance {
        mat_a,
        mat_b,
        mat_c,
        io: io.to_vec(),
        w: w.to_vec(),
    }
}

fn prover_create_inputs(m: usize) -> Ctx<Vid, Value<ArkCurve25519>> {
    type F = <ArkCurve25519 as ArkConfig>::F;
    type G1 = <ArkCurve25519 as ArkConfig>::G1;
    use ark_ec::CurveGroup;

    let num_cons = 1usize << m;
    let witness_len = 1usize << (m - 1);
    let io_len = witness_len - 1;
    let (_l, m_h) = hyrax_split(m);
    let ncols = 1usize << m_h;

    let mut rng = rand::rngs::OsRng;
    let one = F::from(1u64);

    let witness: Vec<F> = (0..witness_len).map(|_| F::rand(&mut rng)).collect();
    let instance: Vec<F> = (0..io_len).map(|_| F::rand(&mut rng)).collect();

    let r1cs = random_r1cs::<F, _>(&mut rng, num_cons, &witness, &instance);

    let mut z: Vec<F> = Vec::with_capacity(num_cons);
    z.extend_from_slice(&witness);
    z.extend_from_slice(&instance);
    z.push(one);

    let mut az: Vec<F> = vec![F::from(0u64); num_cons];
    let mut bz: Vec<F> = vec![F::from(0u64); num_cons];
    let mut cz: Vec<F> = vec![F::from(0u64); num_cons];
    for &(i, c, v) in &r1cs.mat_a {
        az[i] += v * z[c];
    }
    for &(i, c, v) in &r1cs.mat_b {
        bz[i] += v * z[c];
    }
    for &(i, c, v) in &r1cs.mat_c {
        cz[i] += v * z[c];
    }
    for i in 0..num_cons {
        assert_eq!(
            az[i] * bz[i],
            cz[i],
            "row {i} of random R1CS is unsatisfied"
        );
    }

    let triples_to_mle_evals = |triples: &[(usize, usize, F)]| -> Vec<(usize, F)> {
        triples
            .iter()
            .filter(|(_, _, v)| !v.is_zero())
            .map(|(i, c, v)| (c * num_cons + i, *v))
            .collect()
    };
    let two_m_vars = 2 * m;
    let mk_sparse_mle = |evals: Vec<(usize, F)>| {
        Value::Poly(VirtualPolynomial::from_poly(PolyVariant::SparseMle {
            num_vars: two_m_vars,
            evals,
        }))
    };
    let mat_a_t = mk_sparse_mle(triples_to_mle_evals(&r1cs.mat_a));
    let mat_b_t = mk_sparse_mle(triples_to_mle_evals(&r1cs.mat_b));
    let mat_c_t = mk_sparse_mle(triples_to_mle_evals(&r1cs.mat_c));

    let g_vec_proj: Vec<G1> = (0..ncols).map(|_| G1::rand(&mut rng)).collect();
    let g_vec_aff = G1::normalize_batch(&g_vec_proj);
    let g_base_w = G1::rand(&mut rng);
    let h_base_w = G1::rand(&mut rng);

    let g_evs_d3_proj: Vec<G1> = (0..4).map(|_| G1::rand(&mut rng)).collect();
    let g_evs_d3_aff = G1::normalize_batch(&g_evs_d3_proj);
    let g_evs_d2_proj: Vec<G1> = (0..3).map(|_| G1::rand(&mut rng)).collect();
    let g_evs_d2_aff = G1::normalize_batch(&g_evs_d2_proj);
    let h_evs = G1::rand(&mut rng);

    let placeholder_tau: Vec<F> = vec![F::from(0u64); m];

    Ctx::<Vid, Value<ArkCurve25519>>::from_iter([
        (Vid("mat_a_t".to_string()), mat_a_t),
        (Vid("mat_b_t".to_string()), mat_b_t),
        (Vid("mat_c_t".to_string()), mat_c_t),
        (Vid("io".to_string()), Value::VecScalar(r1cs.io)),
        (Vid("w".to_string()), Value::VecScalar(r1cs.w)),
        (Vid("az".to_string()), Value::VecScalar(az)),
        (Vid("bz".to_string()), Value::VecScalar(bz)),
        (Vid("cz".to_string()), Value::VecScalar(cz)),
        (Vid("g_vec_w".to_string()), Value::VecG1Affine(g_vec_aff)),
        (Vid("g_base_w".to_string()), Value::G1(g_base_w)),
        (Vid("h_base_w".to_string()), Value::G1(h_base_w)),
        (
            Vid("g_evs_d3".to_string()),
            Value::VecG1Affine(g_evs_d3_aff),
        ),
        (
            Vid("g_evs_d2".to_string()),
            Value::VecG1Affine(g_evs_d2_aff),
        ),
        (Vid("h_evs".to_string()), Value::G1(h_evs)),
        (
            Vid("placeholder_tau".to_string()),
            Value::VecScalar(placeholder_tau),
        ),
        (Vid("f_one".to_string()), Value::Scalar(one)),
    ])
}
