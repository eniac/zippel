use ark_ff::{Field, Zero};
use ark_std::UniformRand;
use backend::{ArkCurve25519, ArkConfig, PolyVariant, Value, VirtualPolynomial};
use lang::id::{Tid, Vid};
use rand::Rng;
use share::Ctx;
use std::{
    fs::OpenOptions,
    io::Write,
    path::Path,
    thread,
    time::{Duration, Instant},
};
use zippel::*;

const WORKER_STACK_BYTES: usize = 256 * 1024 * 1024;

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

fn main() {
    thread::Builder::new()
        .name("spartan-main".into())
        .stack_size(WORKER_STACK_BYTES)
        .spawn(run)
        .expect("failed to spawn worker thread")
        .join()
        .expect("spartan worker thread panicked");
}

#[derive(Clone, Debug)]
struct RunResult {
    m: usize,
    prover: Duration,
    verifier: Duration,
    proof_bytes: usize,
    passed: bool,
}

fn run() {
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

fn hyrax_split(m: usize) -> (usize, usize) {
    let nw = m - 1;
    let l = nw / 2;
    let m_h = nw - l;
    (l, m_h)
}

fn run_one(m: usize, invalid: bool, manual_zippel: Option<&str>) -> RunResult {
    assert!(m >= 3, "M must be >= 3 (Hyrax needs NW = M-1 >= 2 to split L,M_h both >= 1)");

    let zippel_path = if let Some(path) = manual_zippel {
        std::path::PathBuf::from(path)
    } else {
        let proto = generate_proto(m);
        let tmp_dir = std::env::temp_dir().join("zippel_spartan");
        std::fs::create_dir_all(&tmp_dir).expect("create tmp dir");
        let p = tmp_dir.join(format!("spartan_m{m}.zippel"));
        std::fs::write(&p, proto).expect("write generated proto");
        p
    };

    let args = ZippelArgs::new(zippel_path);
    let mut handler: ZippelHandler<ArkCurve25519> = ZippelHandler::new(args);
    let (_l_h, m_h) = hyrax_split(m);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("SC"), &m);
    sizes.insert(&Tid::new("S"), &m_h);
    handler.compile(&sizes);

    let mut inputs = prover_create_inputs(m);
    if invalid {
        type F = <ArkCurve25519 as ArkConfig>::F;
        if let Some(v) = inputs.get(&Vid("az".to_string())) {
            if let Value::VecScalar(mut a) = v.clone() {
                a[0] = a[0] + F::from(7u64);
                inputs.insert(&Vid("az".to_string()), &Value::VecScalar(a));
            }
        }
    }

    let prover_scheduled = handler.default_schedule_prover();
    let prover_start = Instant::now();
    let proof = handler
        .run_prover(prover_scheduled, inputs)
        .expect("run_prover failed");
    let prover_elapsed = prover_start.elapsed();
    let proof_bytes = proof_size_bytes::<ArkCurve25519>(&proof);

    let verifier_scheduled = handler.default_schedule_verifier();
    let verifier_start = Instant::now();
    let verifier_result = handler
        .run_verifier(verifier_scheduled, proof)
        .expect("run_verifier failed");
    let verifier_elapsed = verifier_start.elapsed();
    if std::env::var("SPARTAN_DEBUG_VERIFIES").is_ok() {
        for (i, v) in verifier_result.iter().enumerate() {
            if let Value::Bool(b) = v {
                eprintln!("  verify[{i}] = {b}");
            }
        }
    }
    let passed = check_verification(verifier_result).passed;

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
    let num_vars = w.len() + io.len() + 1;
    assert_eq!(num_vars, m, "z = w ++ io ++ [1] must have length m");

    let mut z = Vec::with_capacity(m);
    z.extend_from_slice(w);
    z.extend_from_slice(io);
    z.push(F::from(1u64));

    let const_col = m - 1;
    const K_NNZ_PER_ROW: usize = 1;
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

        let az_i: F = a_cols.iter().zip(a_vals.iter()).map(|(c, v)| z[*c] * *v).sum();
        let bz_i: F = b_cols.iter().zip(b_vals.iter()).map(|(c, v)| z[*c] * *v).sum();
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
        assert_eq!(az[i] * bz[i], cz[i], "row {i} of random R1CS is unsatisfied");
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
        (Vid("g_evs_d3".to_string()), Value::VecG1Affine(g_evs_d3_aff)),
        (Vid("g_evs_d2".to_string()), Value::VecG1Affine(g_evs_d2_aff)),
        (Vid("h_evs".to_string()), Value::G1(h_evs)),
        (Vid("placeholder_tau".to_string()), Value::VecScalar(placeholder_tau)),
        (Vid("f_one".to_string()), Value::Scalar(one)),
    ])
}

fn generate_proto(m: usize) -> String {
    let m_lit = m;
    let two_m = 1usize << m;
    let two_m_vars = 2 * m;
    let nw = m - 1;
    let two_nw = 1usize << nw;
    let io_len = two_nw - 1;
    let (l, m_h) = hyrax_split(m);
    let nrows = 1usize << l;
    let ncols = 1usize << m_h;
    assert_eq!(nrows * ncols, two_nw);

    format!(r#"fn eq_weights<G: Group, F: Scalar<G>>(public x: [F; 1]) -> [F; 2] {{
    [(1 - x[0]), x[0]]
}}
fn eq_weights<G: Group, F: Scalar<G>, EK: 2..21>(public x: [F; EK]) -> [F; 2^EK] {{
    let x_lo = x[0..(EK-1)];
    let a    = x[EK-1];
    let prev = eq_weights(x_lo);
    (prev * (1 - a)) ++ (prev * a)
}}

fn draw_taus<G: Group, F: Scalar<G>>(public placeholder: [F; 1]) -> [F; 1] {{
    t <- challenge<F>;
    [t]
}}
fn draw_taus<G: Group, F: Scalar<G>, DK: 2..21>(public placeholder: [F; DK]) -> [F; DK] {{
    let prev = draw_taus(placeholder[0..(DK-1)]);
    t <- challenge<F>;
    prev ++ [t]
}}

fn sc_recurse_d3<G: Group, F: Scalar<G>, SC: Size, V: 2..SC>(
    public curr_poly:       Poly<F, V, 3>,
    public points:          [F; 4],
    public prev_challenges: [F; SC - V],
    public prev_eval:       F,
    public round_challenge: F,
    public curr_round:      Fin<SC>,
    public g_evs_d3:        [G; 4],
    public h_evs:           G
) -> {{ final_eval: F, challenges: [F; SC] }} {{
    let cfg = {{| poly: curr_poly, num_variables: SC, max_degree: 3, round: curr_round, challenge: round_challenge |}};
    let out = marginalize(cfg);
    evs <- out.evaluations;
    verify(prev_eval == evs[0] + evs[1]);
    let g = interpolate(points, evs);
    r_next <- challenge<F>;
    let next_vec = eval(g, [r_next]);
    let next_prev = next_vec[0];
    let new_challenges = prev_challenges ++ [r_next];

    let r_poly_sc = random<F>;
    comm_evs <- dot(g_evs_d3, evs) + h_evs * r_poly_sc;
    let r_eval_sc = random<F>;
    comm_eval_sc <- g_evs_d3[0] * next_prev + h_evs * r_eval_sc;
    let d_vec_sc = [random<F> for i in 0..4];
    let r_delta_sc = random<F>;
    let r_beta_sc = random<F>;
    delta_sc <- dot(g_evs_d3, d_vec_sc) + h_evs * r_delta_sc;
    let a_d_dot_sc = dot(d_vec_sc, evs);
    beta_sc <- g_evs_d3[0] * a_d_dot_sc + h_evs * r_beta_sc;
    c_sc <- challenge<F>;
    z_vec_sc <- [c_sc * evs[i] + d_vec_sc[i] for i in 0..4];
    z_delta_sc <- c_sc * r_poly_sc + r_delta_sc;
    z_beta_sc <- c_sc * r_eval_sc + r_beta_sc;
    let zk_check_sc = dot(g_evs_d3, z_vec_sc) + h_evs * z_delta_sc == comm_evs * c_sc + delta_sc;
    verify(zk_check_sc);

    sc_recurse_d3(out.next_poly, points, new_challenges, next_prev, r_next, curr_round + 1, g_evs_d3, h_evs)
}}
fn sc_recurse_d3<G: Group, F: Scalar<G>, SC: Size>(
    public curr_poly:       Poly<F, 1, 3>,
    public points:          [F; 4],
    public prev_challenges: [F; SC - 1],
    public prev_eval:       F,
    public round_challenge: F,
    public curr_round:      Fin<SC>,
    public g_evs_d3:        [G; 4],
    public h_evs:           G
) -> {{ final_eval: F, challenges: [F; SC] }} {{
    let cfg = {{| poly: curr_poly, num_variables: SC, max_degree: 3, round: curr_round, challenge: round_challenge |}};
    let out = marginalize(cfg);
    evs <- out.evaluations;
    verify(prev_eval == evs[0] + evs[1]);
    let g = interpolate(points, evs);
    r_final <- challenge<F>;
    let final_vec = eval(g, [r_final]);
    let final_eval = final_vec[0];

    let r_poly_sc = random<F>;
    comm_evs <- dot(g_evs_d3, evs) + h_evs * r_poly_sc;
    let r_eval_sc = random<F>;
    comm_eval_sc <- g_evs_d3[0] * final_eval + h_evs * r_eval_sc;
    let d_vec_sc = [random<F> for i in 0..4];
    let r_delta_sc = random<F>;
    let r_beta_sc = random<F>;
    delta_sc <- dot(g_evs_d3, d_vec_sc) + h_evs * r_delta_sc;
    let a_d_dot_sc = dot(d_vec_sc, evs);
    beta_sc <- g_evs_d3[0] * a_d_dot_sc + h_evs * r_beta_sc;
    c_sc <- challenge<F>;
    z_vec_sc <- [c_sc * evs[i] + d_vec_sc[i] for i in 0..4];
    z_delta_sc <- c_sc * r_poly_sc + r_delta_sc;
    z_beta_sc <- c_sc * r_eval_sc + r_beta_sc;
    let zk_check_sc = dot(g_evs_d3, z_vec_sc) + h_evs * z_delta_sc == comm_evs * c_sc + delta_sc;
    verify(zk_check_sc);

    {{| final_eval: final_eval, challenges: prev_challenges ++ [r_final] |}}
}}

fn sc_recurse_d2<G: Group, F: Scalar<G>, SC: Size, V: 2..SC>(
    public curr_poly:       Poly<F, V, 2>,
    public points:          [F; 3],
    public prev_challenges: [F; SC - V],
    public prev_eval:       F,
    public round_challenge: F,
    public curr_round:      Fin<SC>,
    public g_evs_d2:        [G; 3],
    public h_evs:           G
) -> {{ final_eval: F, challenges: [F; SC] }} {{
    let cfg = {{| poly: curr_poly, num_variables: SC, max_degree: 2, round: curr_round, challenge: round_challenge |}};
    let out = marginalize(cfg);
    evs <- out.evaluations;
    verify(prev_eval == evs[0] + evs[1]);
    let g = interpolate(points, evs);
    r_next <- challenge<F>;
    let next_vec = eval(g, [r_next]);
    let next_prev = next_vec[0];
    let new_challenges = prev_challenges ++ [r_next];

    let r_poly_sc = random<F>;
    comm_evs <- dot(g_evs_d2, evs) + h_evs * r_poly_sc;
    let r_eval_sc = random<F>;
    comm_eval_sc <- g_evs_d2[0] * next_prev + h_evs * r_eval_sc;
    let d_vec_sc = [random<F> for i in 0..3];
    let r_delta_sc = random<F>;
    let r_beta_sc = random<F>;
    delta_sc <- dot(g_evs_d2, d_vec_sc) + h_evs * r_delta_sc;
    let a_d_dot_sc = dot(d_vec_sc, evs);
    beta_sc <- g_evs_d2[0] * a_d_dot_sc + h_evs * r_beta_sc;
    c_sc <- challenge<F>;
    z_vec_sc <- [c_sc * evs[i] + d_vec_sc[i] for i in 0..3];
    z_delta_sc <- c_sc * r_poly_sc + r_delta_sc;
    z_beta_sc <- c_sc * r_eval_sc + r_beta_sc;
    let zk_check_sc = dot(g_evs_d2, z_vec_sc) + h_evs * z_delta_sc == comm_evs * c_sc + delta_sc;
    verify(zk_check_sc);

    sc_recurse_d2(out.next_poly, points, new_challenges, next_prev, r_next, curr_round + 1, g_evs_d2, h_evs)
}}
fn sc_recurse_d2<G: Group, F: Scalar<G>, SC: Size>(
    public curr_poly:       Poly<F, 1, 2>,
    public points:          [F; 3],
    public prev_challenges: [F; SC - 1],
    public prev_eval:       F,
    public round_challenge: F,
    public curr_round:      Fin<SC>,
    public g_evs_d2:        [G; 3],
    public h_evs:           G
) -> {{ final_eval: F, challenges: [F; SC] }} {{
    let cfg = {{| poly: curr_poly, num_variables: SC, max_degree: 2, round: curr_round, challenge: round_challenge |}};
    let out = marginalize(cfg);
    evs <- out.evaluations;
    verify(prev_eval == evs[0] + evs[1]);
    let g = interpolate(points, evs);
    r_final <- challenge<F>;
    let final_vec = eval(g, [r_final]);
    let final_eval = final_vec[0];

    let r_poly_sc = random<F>;
    comm_evs <- dot(g_evs_d2, evs) + h_evs * r_poly_sc;
    let r_eval_sc = random<F>;
    comm_eval_sc <- g_evs_d2[0] * final_eval + h_evs * r_eval_sc;
    let d_vec_sc = [random<F> for i in 0..3];
    let r_delta_sc = random<F>;
    let r_beta_sc = random<F>;
    delta_sc <- dot(g_evs_d2, d_vec_sc) + h_evs * r_delta_sc;
    let a_d_dot_sc = dot(d_vec_sc, evs);
    beta_sc <- g_evs_d2[0] * a_d_dot_sc + h_evs * r_beta_sc;
    c_sc <- challenge<F>;
    z_vec_sc <- [c_sc * evs[i] + d_vec_sc[i] for i in 0..3];
    z_delta_sc <- c_sc * r_poly_sc + r_delta_sc;
    z_beta_sc <- c_sc * r_eval_sc + r_beta_sc;
    let zk_check_sc = dot(g_evs_d2, z_vec_sc) + h_evs * z_delta_sc == comm_evs * c_sc + delta_sc;
    verify(zk_check_sc);

    {{| final_eval: final_eval, challenges: prev_challenges ++ [r_final] |}}
}}

fn compute_s_vec<G: Group, F: Scalar<G>>(public c: [F; 1], public c_inv: [F; 1]) -> [F; 2] {{
    [c_inv[0], c[0]]
}}
fn compute_s_vec<G: Group, F: Scalar<G>, K: 2..21>(public c: [F; K], public c_inv: [F; K]) -> [F; 2^K] {{
    let curr_c = c[0];
    let curr_c_inv = c_inv[0];
    let c_rest = c[1..K];
    let c_inv_rest = c_inv[1..K];
    let prev = compute_s_vec(c_rest, c_inv_rest);
    (prev * curr_c_inv) ++ (prev * curr_c)
}}

fn bullet_collect<G: Group, F: Scalar<G>>(
    public g_base: G,
    public h_base: G,
    private g_folded: [G; 2],
    private a_folded: [F; 2],
    private x_folded: [F; 2],
    private y_folded: F,
    private r_Upsilon_folded: F
) -> {{ challenges: [F; 1], challenges_inv: [F; 1], Ls: [G; 1], Rs: [G; 1], final_x: F, final_y: F, final_r: F }} {{
    let x_1 = x_folded[0..1];
    let x_2 = x_folded[1..2];
    let a_1 = a_folded[0..1];
    let a_2 = a_folded[1..2];
    let g_1 = g_folded[0..1];
    let g_2 = g_folded[1..2];
    let r_L = random<F>;
    let r_R = random<F>;
    let dot_x1_a2 = dot(x_1, a_2);
    let dot_x2_a1 = dot(x_2, a_1);
    upsilon_neg1 <- h_base * r_L + g_base * dot_x1_a2 + dot(g_2, x_1);
    upsilon_1 <- h_base * r_R + g_base * dot_x2_a1 + dot(g_1, x_2);
    c <- challenge<F>;
    let c_inv = 1 / c;
    let c_sq = c * c;
    let c_inv_sq = c_inv * c_inv;
    let next_x = x_1 * c + x_2 * c_inv;
    let next_y = dot_x1_a2 * c_sq + y_folded + dot_x2_a1 * c_inv_sq;
    let next_r = r_L * c_sq + r_Upsilon_folded + r_R * c_inv_sq;
    {{|
        challenges: [c],
        challenges_inv: [c_inv],
        Ls: [upsilon_neg1],
        Rs: [upsilon_1],
        final_x: next_x[0],
        final_y: next_y,
        final_r: next_r
    |}}
}}

fn bullet_collect<G: Group, F: Scalar<G>, S: Size, N: 2..S+1>(
    public g_base: G,
    public h_base: G,
    private g_folded: [G; 2^N],
    private a_folded: [F; 2^N],
    private x_folded: [F; 2^N],
    private y_folded: F,
    private r_Upsilon_folded: F
) -> {{ challenges: [F; N], challenges_inv: [F; N], Ls: [G; N], Rs: [G; N], final_x: F, final_y: F, final_r: F }} {{
    let x_1 = x_folded[0..2^(N-1)];
    let x_2 = x_folded[2^(N-1)..2^N];
    let a_1 = a_folded[0..2^(N-1)];
    let a_2 = a_folded[2^(N-1)..2^N];
    let g_1 = g_folded[0..2^(N-1)];
    let g_2 = g_folded[2^(N-1)..2^N];
    let r_L = random<F>;
    let r_R = random<F>;
    let dot_x1_a2 = dot(x_1, a_2);
    let dot_x2_a1 = dot(x_2, a_1);
    upsilon_neg1 <- h_base * r_L + g_base * dot_x1_a2 + dot(g_2, x_1);
    upsilon_1 <- h_base * r_R + g_base * dot_x2_a1 + dot(g_1, x_2);
    c <- challenge<F>;
    let c_inv = 1 / c;
    let c_sq = c * c;
    let c_inv_sq = c_inv * c_inv;
    let next_g = g_1 * c_inv + g_2 * c;
    let next_a = a_1 * c_inv + a_2 * c;
    let next_x = x_1 * c + x_2 * c_inv;
    let next_y = dot_x1_a2 * c_sq + y_folded + dot_x2_a1 * c_inv_sq;
    let next_r = r_L * c_sq + r_Upsilon_folded + r_R * c_inv_sq;
    let inner = bullet_collect(g_base, h_base, next_g, next_a, next_x, next_y, next_r);
    {{|
        challenges: [c] ++ inner.challenges,
        challenges_inv: [c_inv] ++ inner.challenges_inv,
        Ls: [upsilon_neg1] ++ inner.Ls,
        Rs: [upsilon_1] ++ inner.Rs,
        final_x: inner.final_x,
        final_y: inner.final_y,
        final_r: inner.final_r
    |}}
}}

proto spartan<G: Group, F: Scalar<G>>(
    public mat_a_t:   Poly<F, {two_m_vars}, 1>,
    public mat_b_t:   Poly<F, {two_m_vars}, 1>,
    public mat_c_t:   Poly<F, {two_m_vars}, 1>,
    public io:        [F; {io_len}],
    private w:        [F; {two_nw}],
    private az:       [F; {two_m}],
    private bz:       [F; {two_m}],
    private cz:       [F; {two_m}],
    public g_vec_w:   [G; {ncols}],
    public g_base_w:  G,
    public h_base_w:  G,
    public g_evs_d3:  [G; 4],
    public g_evs_d2:  [G; 3],
    public h_evs:     G,
    public placeholder_tau: [F; {m_lit}],
    public f_one:     F
) where
    az * bz == cz
{{
    let one  = f_one;
    let zero = f_one - f_one;

    let r_rows = [random<F> for i in 0..{nrows}];
    c_rows <- [
        h_base_w * r_rows[i] + dot(g_vec_w, [w[i*{ncols} + j] for j in 0..{ncols}])
        for i in 0..{nrows}
    ];

    let z = w ++ io ++ [one];

    let f_a = mle(az);
    let f_b = mle(bz);
    let f_c = mle(cz);

    let tau_vec = draw_taus(placeholder_tau);
    let eq_tau_evs = eq_weights(tau_vec);
    let eq_tau     = mle(eq_tau_evs);

    let neg_one = zero - one;
    let g_sub   = f_a * f_b + f_c * neg_one;
    let g_poly  = g_sub * eq_tau;

    let pts3   = [i for i in 0..4];
    let cfg1_0 = {{| poly: g_poly, num_variables: {m_lit}, max_degree: 3, round: 0, challenge: zero |}};
    let out1_0 = marginalize(cfg1_0);
    evs1_0 <- out1_0.evaluations;
    verify(zero == evs1_0[0] + evs1_0[1]);
    let g1_r1     = interpolate(pts3, evs1_0);
    rx0           <- challenge<F>;
    let prev1_vec = eval(g1_r1, [rx0]);
    let prev1     = prev1_vec[0];

    let r_poly_10 = random<F>;
    comm_evs_10 <- dot(g_evs_d3, evs1_0) + h_evs * r_poly_10;
    let r_eval_10 = random<F>;
    comm_eval_10 <- g_evs_d3[0] * prev1 + h_evs * r_eval_10;
    let d_vec_10 = [random<F> for i in 0..4];
    let r_delta_10 = random<F>;
    let r_beta_10  = random<F>;
    delta_10 <- dot(g_evs_d3, d_vec_10) + h_evs * r_delta_10;
    let a_d_dot_10 = dot(d_vec_10, evs1_0);
    beta_10  <- g_evs_d3[0] * a_d_dot_10 + h_evs * r_beta_10;
    c_10     <- challenge<F>;
    z_vec_10   <- [c_10 * evs1_0[i] + d_vec_10[i] for i in 0..4];
    z_delta_10 <- c_10 * r_poly_10 + r_delta_10;
    z_beta_10  <- c_10 * r_eval_10 + r_beta_10;
    let zk_check_10 = dot(g_evs_d3, z_vec_10) + h_evs * z_delta_10 == comm_evs_10 * c_10 + delta_10;
    verify(zk_check_10);

    let sc1 = sc_recurse_d3(out1_0.next_poly, pts3, [rx0], prev1, rx0, 1, g_evs_d3, h_evs);
    let rx  = sc1.challenges;
    let e_x = sc1.final_eval;

    let lx = eq_weights(rx);
    v_a <- dot(lx, az);
    v_b <- dot(lx, bz);
    v_c <- dot(lx, cz);
    let eq_tau_at_rx = dot(lx, eq_tau_evs);
    verify(e_x == (v_a * v_b - v_c) * eq_tau_at_rx);

    let r_va = random<F>;
    let r_vb = random<F>;
    let r_vc = random<F>;
    let r_prod = random<F>;
    comm_va_phase1 <- g_evs_d3[0] * v_a + h_evs * r_va;
    comm_vb_phase1 <- g_evs_d3[0] * v_b + h_evs * r_vb;
    comm_vc_phase1 <- g_evs_d3[0] * v_c + h_evs * r_vc;
    comm_prod_phase1 <- g_evs_d3[0] * (v_a * v_b) + h_evs * r_prod;
    let d1_phase1 = random<F>;
    let d2_phase1 = random<F>;
    let r_d_phase1 = random<F>;
    let r_e_phase1 = random<F>;
    let r_f_phase1 = random<F>;
    alpha_phase1 <- g_evs_d3[0] * d1_phase1 + h_evs * r_d_phase1;
    beta_p1_phase1 <- g_evs_d3[0] * d2_phase1 + h_evs * r_e_phase1;
    delta_phase1 <- comm_va_phase1 * d2_phase1 + h_evs * r_f_phase1;
    c_phase1 <- challenge<F>;
    z1_phase1 <- c_phase1 * v_a + d1_phase1;
    z2_phase1 <- c_phase1 * r_va + r_d_phase1;
    z3_phase1 <- c_phase1 * v_b + d2_phase1;
    z4_phase1 <- c_phase1 * r_vb + r_e_phase1;
    z5_phase1 <- c_phase1 * (r_prod - r_va * v_b) + r_f_phase1;
    let prod_check1 = g_evs_d3[0] * z1_phase1 + h_evs * z2_phase1 == comm_va_phase1 * c_phase1 + alpha_phase1;
    let prod_check2 = g_evs_d3[0] * z3_phase1 + h_evs * z4_phase1 == comm_vb_phase1 * c_phase1 + beta_p1_phase1;
    let prod_check3 = comm_va_phase1 * z3_phase1 + h_evs * z5_phase1 == comm_prod_phase1 * c_phase1 + delta_phase1;
    verify(prod_check1);
    verify(prod_check2);
    verify(prod_check3);
    let t1_pok_vc = random<F>;
    let t2_pok_vc = random<F>;
    alpha_pok_vc <- g_evs_d3[0] * t1_pok_vc + h_evs * t2_pok_vc;
    c_pok_vc <- challenge<F>;
    z1_pok_vc <- v_c * c_pok_vc + t1_pok_vc;
    z2_pok_vc <- r_vc * c_pok_vc + t2_pok_vc;
    let pok_vc_check = g_evs_d3[0] * z1_pok_vc + h_evs * z2_pok_vc == comm_vc_phase1 * c_pok_vc + alpha_pok_vc;
    verify(pok_vc_check);
    let r_postsc_blind = random<F>;
    let r_eq_p1 = random<F>;
    let derived_blind_p1 = eq_tau_at_rx * (r_prod - r_vc);
    comm_postsc_p1 <- g_evs_d3[0] * e_x + h_evs * r_postsc_blind;
    let comm_derived_p1 = (comm_prod_phase1 - comm_vc_phase1) * eq_tau_at_rx;
    alpha_eq_p1 <- h_evs * r_eq_p1;
    c_eq_p1 <- challenge<F>;
    z_eq_p1 <- c_eq_p1 * (r_postsc_blind - derived_blind_p1) + r_eq_p1;
    let eq_check_p1 = h_evs * z_eq_p1 == (comm_postsc_p1 - comm_derived_p1) * c_eq_p1 + alpha_eq_p1;
    verify(eq_check_p1);

    ra <- challenge<F>;
    rb <- challenge<F>;
    rc <- challenge<F>;
    let t2 = ra * v_a + rb * v_b + rc * v_c;

    let partial_a = eval(mat_a_t, rx);
    let partial_b = eval(mat_b_t, rx);
    let partial_c = eval(mat_c_t, rx);

    let l_mle  = partial_a * ra + partial_b * rb + partial_c * rc;
    let z_mle  = mle(z);
    let m_poly = l_mle * z_mle;

    let pts2   = [i for i in 0..3];
    let cfg2_0 = {{| poly: m_poly, num_variables: {m_lit}, max_degree: 2, round: 0, challenge: zero |}};
    let out2_0 = marginalize(cfg2_0);
    evs2_0 <- out2_0.evaluations;
    verify(t2 == evs2_0[0] + evs2_0[1]);
    let g2_r1     = interpolate(pts2, evs2_0);
    ry0           <- challenge<F>;
    let prev2_vec = eval(g2_r1, [ry0]);
    let prev2     = prev2_vec[0];

    let r_poly_20 = random<F>;
    comm_evs_20 <- dot(g_evs_d2, evs2_0) + h_evs * r_poly_20;
    let r_eval_20 = random<F>;
    comm_eval_20 <- g_evs_d2[0] * prev2 + h_evs * r_eval_20;
    let d_vec_20 = [random<F> for i in 0..3];
    let r_delta_20 = random<F>;
    let r_beta_20  = random<F>;
    delta_20 <- dot(g_evs_d2, d_vec_20) + h_evs * r_delta_20;
    let a_d_dot_20 = dot(d_vec_20, evs2_0);
    beta_20  <- g_evs_d2[0] * a_d_dot_20 + h_evs * r_beta_20;
    c_20     <- challenge<F>;
    z_vec_20   <- [c_20 * evs2_0[i] + d_vec_20[i] for i in 0..3];
    z_delta_20 <- c_20 * r_poly_20 + r_delta_20;
    z_beta_20  <- c_20 * r_eval_20 + r_beta_20;
    let zk_check_20 = dot(g_evs_d2, z_vec_20) + h_evs * z_delta_20 == comm_evs_20 * c_20 + delta_20;
    verify(zk_check_20);

    let sc2 = sc_recurse_d2(out2_0.next_poly, pts2, [ry0], prev2, ry0, 1, g_evs_d2, h_evs);
    let ry  = sc2.challenges;
    let e_y = sc2.final_eval;

    let pcs_z   = ry[0..{nw}];
    let ly_lo   = eq_weights(pcs_z);
    let z_col   = pcs_z[0..{m_h}];
    let z_row   = pcs_z[{m_h}..{nw}];
    let l_vec   = eq_weights(z_row);
    let r_vec   = eq_weights(z_col);

    let big_t   = dot(l_vec, c_rows);
    let r_big_t = dot(l_vec, r_rows);
    let u_vec = [
        dot(l_vec, [w[i*{ncols} + j] for i in 0..{nrows}])
        for j in 0..{ncols}
    ];

    let v_w_val = dot(ly_lo, w);
    sent_v_w    <- v_w_val;

    let r_tau = random<F>;
    tau_pcs <- g_base_w * sent_v_w + h_base_w * r_tau;
    rho_pcs <- challenge<F>;
    let upsilon_pcs = big_t + tau_pcs * rho_pcs;
    let r_upsilon_pcs = r_big_t + r_tau * rho_pcs;
    let a_rho_pcs = [r_vec[j] * rho_pcs for j in 0..{ncols}];
    let y_rho_pcs = sent_v_w * rho_pcs;
    let bullet = bullet_collect(g_base_w, h_base_w, g_vec_w, a_rho_pcs, u_vec, y_rho_pcs, r_upsilon_pcs);
    let b_challenges = bullet.challenges;
    let b_challenges_inv = bullet.challenges_inv;
    let b_Ls = bullet.Ls;
    let b_Rs = bullet.Rs;
    let b_final_y = bullet.final_y;
    let b_final_r = bullet.final_r;
    let s_vec = compute_s_vec(b_challenges, b_challenges_inv);
    let g_hat = dot(g_vec_w, s_vec);
    let a_hat = dot(a_rho_pcs, s_vec);
    let c_sq_vec = [b_challenges[i] * b_challenges[i] for i in 0..{m_h}];
    let c_inv_sq_vec = [b_challenges_inv[i] * b_challenges_inv[i] for i in 0..{m_h}];
    let upsilon_combined = upsilon_pcs + dot(b_Ls, c_sq_vec) + dot(b_Rs, c_inv_sq_vec);
    let d_ipa = random<F>;
    let r_delta_ipa = random<F>;
    let r_beta_ipa = random<F>;
    delta_ipa <- g_hat * d_ipa + h_base_w * r_delta_ipa;
    beta_ipa <- g_base_w * d_ipa + h_base_w * r_beta_ipa;
    c_ipa <- challenge<F>;
    z1_ipa <- d_ipa + c_ipa * b_final_y;
    z2_ipa <- a_hat * (c_ipa * b_final_r + r_beta_ipa) + r_delta_ipa;
    let lhs_ipa = (upsilon_combined * c_ipa + beta_ipa) * a_hat + delta_ipa;
    let rhs_ipa = (g_hat + g_base_w * a_hat) * z1_ipa + h_base_w * z2_ipa;
    let ipa_ok = lhs_ipa == rhs_ipa;

    let io_block = io ++ [one];
    let v_io     = dot(ly_lo, io_block);
    let ry_top   = ry[{m_lit} - 1];
    let v_z      = (one - ry_top) * sent_v_w + ry_top * v_io;

    let v1 = eval(partial_a, ry);
    let v2 = eval(partial_b, ry);
    let v3 = eval(partial_c, ry);

    let r_ey   = random<F>;
    let d_p2   = random<F>;
    let r_d_p2 = random<F>;
    comm_ey_p2 <- g_evs_d2[0] * e_y + h_evs * r_ey;
    alpha_p2   <- g_evs_d2[0] * d_p2 + h_evs * r_d_p2;
    c_p2       <- challenge<F>;
    z1_p2 <- c_p2 * e_y + d_p2;
    z2_p2 <- c_p2 * r_ey + r_d_p2;
    let eq_check_p2 = g_evs_d2[0] * z1_p2 + h_evs * z2_p2 == comm_ey_p2 * c_p2 + alpha_p2;
    verify(eq_check_p2);

    verify(ipa_ok);
    verify(e_y == (ra * v1 + rb * v2 + rc * v3) * v_z)
}}
"#,
        m_lit = m_lit,
        two_m = two_m,
        two_m_vars = two_m_vars,
        nw = nw,
        two_nw = two_nw,
        io_len = io_len,
        m_h = m_h,
        nrows = nrows,
        ncols = ncols,
    )
}
