//! Spartan-NIZK example.
//!
//! Composes the info-theoretic Spartan PIOP with the PST13 multilinear
//! PCS, runs prove + verify against a random *square* satisfying R1CS
//! instance with
//!
//!     num_constraints = num_vars = 2^M
//!     |w|  = 2^(M-1)
//!     |io| = 2^(M-1) - 1
//!
//! R1CS matrices are stored sparsely as `Vec<(row, col, F)>` triples
//! and lifted into `PolyVariant::SparseMle` for the partial-eval inside
//! SC #2 (`eval(mat_a_t, rx)` etc.). `az` / `bz` / `cz` are computed in
//! Rust and passed in as **private inputs**, since zippel has no
//! first-class `Mv` primitive that could express the matvec inside the
//! proto. Soundness binding between `az/bz/cz` and the public matrices
//! lives in SC #2: it verifies that v_a/v_b/v_c (which come from SC #1
//! over `mle(az/bz/cz)`) equal Σ_y M_x(rx, y) · z(y), with the final
//! `(ra·M_a + rb·M_b + rc·M_c)·v_z` check at random ry. A prover lying
//! about az/bz/cz can't satisfy that check w.h.p.
//!
//! The proto is generated *per M* by `generate_proto(m)` and written to
//! a temp file before each run, because zippel's helper-function overload
//! resolution can't (currently) bind `[F; K]` overloads of recursive
//! helpers like `eq_weights` / `draw_taus` when the call site has an
//! abstract `[F; M]` argument. Substituting M as a literal sidesteps
//! that limitation: each per-M file is fully concrete and the recursive
//! helpers resolve unambiguously.
//!
//! Args:
//!   --m N        run a single size M = N (default 2)
//!   --sweep A B  iterate M from A through B inclusive
//!   --invalid    corrupt mat_a after the satisfiability check, expect
//!                Verification ✗ FAILED
//!   --csv P      append `m,prover_ms,verifier_ms,proof_bytes,passed`
//!                rows to file P (or "-" for stdout)
//!
//! Scales to M=16+ on a single machine. The native Microsoft Spartan
//! baseline lives at `benchmarks/src/bin/spartan_bench.rs` (NIZK +
//! SNARK variants over the same M range).

use ark_ff::{Field, Zero};
use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, PolyVariant, Value, VirtualPolynomial};
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
    /// If set, use this hand-written .zippel file for the M values in
    /// `sweep` (and skip codegen). The harness still supplies the same
    /// `mat_a / mat_b / mat_c / io / w / ck_n_w / g_gen / h_gen /
    /// alpha_h_w / placeholder_tau / f_one` inputs sized for that M, so
    /// the file's proto signature has to match. Used for localising
    /// codegen bugs by hand-unrolling a specific M (e.g. M=3).
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
        sweep.push(2);
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
        .name("spartan-full-main".into())
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

    println!("=== Spartan-NIZK sparse-inputs (PIOP + PST13 PCS, ArkBls12_381) ===");
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
        println!(
            "M={m:>2}  num_cons={n:>8}  |w|={w:>8}  |io|={io:>8}  prover={prover:>10.2?}  verifier={verifier:>10.2?}  proof={bytes:>7}B  verdict={verdict}",
            n = 1usize << m,
            w = if m >= 1 { 1usize << (m - 1) } else { 0 },
            io = if m >= 1 { (1usize << (m - 1)) - 1 } else { 0 },
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

fn run_one(m: usize, invalid: bool, manual_zippel: Option<&str>) -> RunResult {
    assert!(m >= 2, "M must be >= 2 (Spartan needs at least 2 sum-check rounds)");

    let zippel_path = if let Some(path) = manual_zippel {
        // Skip codegen, use the hand-written proto as-is.
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
    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    // sc_recurse_d{2,3} has a free `SC: Size` generic that the compiler
    // can't solve from `[F; SC - V]` at the call site (only one
    // arg-shape constraint, two unknowns). Pin it externally; for
    // Spartan, SC = M (both sum-checks run M rounds).
    sizes.insert(&Tid::new("SC"), &m);
    handler.compile(&sizes);

    let mut inputs = prover_create_inputs(m);
    if invalid {
        // Corrupt `az` (the prover's claimed A·z). The verifier's
        // SC #2 closing check `e_y == (ra·M_a + rb·M_b + rc·M_c)·v_z`
        // independently re-derives M_a(rx, ry) from the public mat_a_t
        // and ry, so a corrupted az breaks the link and the proof fails
        // — exactly the soundness binding between the (private) az/bz/cz
        // and the (public) matrices.
        type F = <ArkBls12_381 as ArkConfig>::F;
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
    let proof_bytes = proof_size_bytes::<ArkBls12_381>(&proof);

    let verifier_scheduled = handler.default_schedule_verifier();
    let verifier_start = Instant::now();
    let verifier_result = handler
        .run_verifier(verifier_scheduled, proof)
        .expect("run_verifier failed");
    let verifier_elapsed = verifier_start.elapsed();
    // Set SPARTAN_DEBUG_VERIFIES=1 to print per-verify status.
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

/// Sparse R1CS instance: each matrix is stored as a list of `(row, col, val)`
/// triples. Dense storage was O(N²) — at M=15 (N=32K) that's 32 GB per
/// matrix, well past the allocation limit. With K-sparse rows the triple
/// list is O(K · N).
struct R1csInstance<F> {
    mat_a: Vec<(usize, usize, F)>,
    mat_b: Vec<(usize, usize, F)>,
    mat_c: Vec<(usize, usize, F)>,
    io: Vec<F>,
    w: Vec<F>,
}

/// Build a random satisfying square R1CS instance of size m × m, with
/// z = w ++ io ++ [1] of length m. |w| = m/2, |io| = m/2 - 1.
///
/// Strategy: sample A and B fully randomly, sample most of each C row,
/// then solve C's constant column so the row's R1CS holds. Same scheme
/// as the original (pinned) spartan harness; just made parametric.
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
    // K non-zeros per row, matching `microsoft/spartan`'s synthetic
    // R1CS baseline of `nnz = num_cons` (≈ 1 non-zero per row).
    // The constant column `const_col` is always among the K active
    // columns of row C so we can solve for satisfiability.
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

fn prover_create_inputs(m: usize) -> Ctx<Vid, Value<ArkBls12_381>> {
    type F = <ArkBls12_381 as ArkConfig>::F;
    type G1 = <ArkBls12_381 as ArkConfig>::G1;
    type G2 = <ArkBls12_381 as ArkConfig>::G2;

    let num_cons = 1usize << m;
    let witness_len = 1usize << (m - 1);
    let io_len = witness_len - 1;
    let n_w = m - 1;

    let mut rng = rand::rngs::OsRng;
    let one = F::from(1u64);

    let witness: Vec<F> = (0..witness_len).map(|_| F::rand(&mut rng)).collect();
    let instance: Vec<F> = (0..io_len).map(|_| F::rand(&mut rng)).collect();

    let r1cs = random_r1cs::<F, _>(&mut rng, num_cons, &witness, &instance);

    // Build z = w ++ io ++ [1] and compute az = A·z, bz = B·z, cz = C·z
    // natively. These are passed to the proto as PRIVATE inputs so the
    // body doesn't have to unroll the dense MVM into ~N² mul-nodes.
    // We still also do the belt-and-suspenders satisfiability check.
    let mut z: Vec<F> = Vec::with_capacity(num_cons);
    z.extend_from_slice(&witness);
    z.extend_from_slice(&instance);
    z.push(one);

    // Sparse Mv: for each row, accumulate Σ_{(i,c,v) ∈ mat_x : i = row} v·z[c].
    // O(|nnz|) per matrix.
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

    // Build the 2M-variable MLEs for A, B, C in SPARSE evaluation form,
    // directly from the (row, col, val) triples. Column-major LSB-first
    // index `k = c * N + i` puts the row-bits in the low variables,
    // matching zippel's MLE layout. `eval(mat_x_t, rx)` then fixes the
    // low M vars, leaving the col-bits free → exactly partial_x.
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

    // PST13.Setup over N_w variables.
    let g_gen = G1::rand(&mut rng);
    let h_gen = G2::rand(&mut rng);
    let alpha: Vec<F> = (0..n_w).map(|_| F::rand(&mut rng)).collect();

    let ck_scalars: Vec<F> = (0..(1usize << n_w))
        .map(|i| {
            (0..n_w).fold(one, |acc, j| {
                let bit = (i >> j) & 1;
                let factor = if bit == 1 { alpha[j] } else { one - alpha[j] };
                acc * factor
            })
        })
        .collect();
    let ck_n_w: Vec<G1> = ck_scalars.iter().map(|s| g_gen * s).collect();
    let alpha_h_w: Vec<G2> = alpha.iter().map(|a| h_gen * a).collect();

    // `placeholder_tau`: a length-M zero array used purely to give the
    // `draw_taus` recursive helper a concretely-sized argument that
    // resolves unambiguously to its [F; M] specialization. The actual
    // τ challenges are still drawn from the transcript by `draw_taus`.
    let placeholder_tau: Vec<F> = vec![F::from(0u64); m];

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("mat_a_t".to_string()), mat_a_t),
        (Vid("mat_b_t".to_string()), mat_b_t),
        (Vid("mat_c_t".to_string()), mat_c_t),
        (Vid("io".to_string()), Value::VecScalar(r1cs.io)),
        (Vid("w".to_string()), Value::VecScalar(r1cs.w)),
        (Vid("az".to_string()), Value::VecScalar(az)),
        (Vid("bz".to_string()), Value::VecScalar(bz)),
        (Vid("cz".to_string()), Value::VecScalar(cz)),
        (Vid("ck_n_w".to_string()), Value::VecG1(ck_n_w)),
        (Vid("g_gen".to_string()), Value::G1(g_gen)),
        (Vid("h_gen".to_string()), Value::G2(h_gen)),
        (Vid("alpha_h_w".to_string()), Value::VecG2(alpha_h_w)),
        (Vid("placeholder_tau".to_string()), Value::VecScalar(placeholder_tau)),
        (Vid("f_one".to_string()), Value::Scalar(one)),
    ])
}

/// Build the per-M Spartan-NIZK zippel proto as a string. All sizes are
/// substituted as integer literals (no `M`-typed proto generic), so the
/// recursive helpers `eq_weights` / `draw_taus` / `sc_recurse_d{2,3}` /
/// `pst13_open_rounds` resolve unambiguously at the call sites. The
/// only remaining free generic is the sum-check helper's `SC: Size`,
/// which the harness pins via `Ctx::insert("SC", &m)`.
fn generate_proto(m: usize) -> String {
    let m_lit = m;
    let two_m = 1usize << m;
    let two_m_vars = 2 * m;
    let nw = m - 1;
    let two_nw = 1usize << nw;
    let io_len = two_nw - 1;

    // Recursive helper for the dimensional-Lagrange basis at r_x and r_y.
    // For M = 2, the EK = 2..20 recursive case at K = 2 isn't strictly
    // needed (we only call eq_weights at [F; 2] which then descends into
    // the [F; 1] base) — but the compiler is happy to monomorphize it
    // and we don't pay anything at runtime.
    let pst13_helpers = if nw == 1 {
        // NW = 1 → only the PST13 open BASE case is reachable.
        String::from("")
    } else {
        // NW >= 2 → recursive case is needed.
        String::from("")
    };
    let _ = pst13_helpers;

    format!(r#"// Auto-generated Spartan-NIZK proto for M = {m_lit}.
// num_constraints = num_vars = {two_m}; |w| = {two_nw}; |io| = {io_len}.
// Composition: info-theoretic Spartan PIOP + PST13 multilinear PCS,
// the NIZK column of Fig. 5 in Setty CRYPTO 2020.
//
// This file is regenerated per M by examples/spartan/main.rs.

// ===== Lagrange basis at point x ∈ F^K (LSB-first), recursive over K. =====
// All helpers carry the same `F: Scalar<G1, G2>` bound as the outer
// proto — using `F: Field` here would create a subtype mismatch that
// zippel's overload resolution can't disambiguate (multiple [F; K]
// specs match a Scalar-typed [F; M] argument).
fn eq_weights<G1: Group, G2: Group, F: Scalar<G1, G2>>(public x: [F; 1]) -> [F; 2] {{
    [(1 - x[0]), x[0]]
}}
fn eq_weights<G1: Group, G2: Group, F: Scalar<G1, G2>, EK: 2..20>(public x: [F; EK]) -> [F; 2^EK] {{
    let x_lo = x[0..(EK-1)];
    let a    = x[EK-1];
    let prev = eq_weights(x_lo);
    (prev * (1 - a)) ++ (prev * a)
}}

// ===== Draw K Fiat-Shamir challenges, recursive over K. =====
fn draw_taus<G1: Group, G2: Group, F: Scalar<G1, G2>>(public placeholder: [F; 1]) -> [F; 1] {{
    t <- challenge<F>;
    [t]
}}
fn draw_taus<G1: Group, G2: Group, F: Scalar<G1, G2>, DK: 2..20>(public placeholder: [F; DK]) -> [F; DK] {{
    let prev = draw_taus(placeholder[0..(DK-1)]);
    t <- challenge<F>;
    prev ++ [t]
}}

// ===== Sum-check rounds 1..SC-1 plus the base round, deg 3. =====
fn sc_recurse_d3<G1: Group, G2: Group, F: Scalar<G1, G2>, SC: Size, V: 2..SC>(
    public curr_poly:       Poly<F, V, 3>,
    public points:          [F; 4],
    public prev_challenges: [F; SC - V],
    public prev_eval:       F,
    public round_challenge: F,
    public curr_round:      Fin<SC>
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
    sc_recurse_d3(out.next_poly, points, new_challenges, next_prev, r_next, curr_round + 1)
}}
fn sc_recurse_d3<G1: Group, G2: Group, F: Scalar<G1, G2>, SC: Size>(
    public curr_poly:       Poly<F, 1, 3>,
    public points:          [F; 4],
    public prev_challenges: [F; SC - 1],
    public prev_eval:       F,
    public round_challenge: F,
    public curr_round:      Fin<SC>
) -> {{ final_eval: F, challenges: [F; SC] }} {{
    let cfg = {{| poly: curr_poly, num_variables: SC, max_degree: 3, round: curr_round, challenge: round_challenge |}};
    let out = marginalize(cfg);
    evs <- out.evaluations;
    verify(prev_eval == evs[0] + evs[1]);
    let g = interpolate(points, evs);
    r_final <- challenge<F>;
    let final_vec = eval(g, [r_final]);
    let final_eval = final_vec[0];
    {{| final_eval: final_eval, challenges: prev_challenges ++ [r_final] |}}
}}

// ===== Sum-check rounds 1..SC-1 plus the base round, deg 2. =====
fn sc_recurse_d2<G1: Group, G2: Group, F: Scalar<G1, G2>, SC: Size, V: 2..SC>(
    public curr_poly:       Poly<F, V, 2>,
    public points:          [F; 3],
    public prev_challenges: [F; SC - V],
    public prev_eval:       F,
    public round_challenge: F,
    public curr_round:      Fin<SC>
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
    sc_recurse_d2(out.next_poly, points, new_challenges, next_prev, r_next, curr_round + 1)
}}
fn sc_recurse_d2<G1: Group, G2: Group, F: Scalar<G1, G2>, SC: Size>(
    public curr_poly:       Poly<F, 1, 2>,
    public points:          [F; 3],
    public prev_challenges: [F; SC - 1],
    public prev_eval:       F,
    public round_challenge: F,
    public curr_round:      Fin<SC>
) -> {{ final_eval: F, challenges: [F; SC] }} {{
    let cfg = {{| poly: curr_poly, num_variables: SC, max_degree: 2, round: curr_round, challenge: round_challenge |}};
    let out = marginalize(cfg);
    evs <- out.evaluations;
    verify(prev_eval == evs[0] + evs[1]);
    let g = interpolate(points, evs);
    r_final <- challenge<F>;
    let final_vec = eval(g, [r_final]);
    let final_eval = final_vec[0];
    {{| final_eval: final_eval, challenges: prev_challenges ++ [r_final] |}}
}}

// ===== PST13 commit (single call, fixed size). =====
fn pst13_commit_w<G1: Group, G2: Group, F: Scalar<G1, G2>>(
    private p:    [F; {two_nw}],
    public ck_n:  [G1; {two_nw}]
) -> G1 {{
    dot(p, ck_n)
}}

// ===== PST13 open: recursive over the witness-MLE variable count. =====
fn pst13_open_rounds<G1: Group, G2: Group, GT: Pairing<G1, G2>, F: Scalar<G1, G2>>(
    private p_curr:        [F; 2],
    public ck_curr:        [G1; 2],
    public z_curr:         [F; 1],
    public alpha_H_curr:   [G2; 1],
    public h_gen:          G2,
    public rem:            GT
) -> Bool {{
    let ck_lo = ck_curr[0..1];
    let ck_hi = ck_curr[1..2];
    let ck_0  = ck_lo + ck_hi;
    let p_lo = p_curr[0..1];
    let p_hi = p_curr[1..2];
    let q    = p_hi - p_lo;
    pi_last <- dot(q, ck_0);
    rem == pair(pi_last, alpha_H_curr[0] - (h_gen * z_curr[0]))
}}
fn pst13_open_rounds<G1: Group, G2: Group, GT: Pairing<G1, G2>, F: Scalar<G1, G2>, PK: 2..20>(
    private p_curr:        [F; 2^PK],
    public ck_curr:        [G1; 2^PK],
    public z_curr:         [F; PK],
    public alpha_H_curr:   [G2; PK],
    public h_gen:          G2,
    public rem:            GT
) -> Bool {{
    let ck_lo  = ck_curr[0..2^(PK-1)];
    let ck_hi  = ck_curr[2^(PK-1)..2^PK];
    let ck_nxt = ck_lo + ck_hi;
    let p_lo = p_curr[0..2^(PK-1)];
    let p_hi = p_curr[2^(PK-1)..2^PK];
    let q    = p_hi - p_lo;
    pi_curr <- dot(q, ck_nxt);
    let p_red    = p_lo + (q * z_curr[0]);
    let rem_next = rem - pair(pi_curr, alpha_H_curr[0] - (h_gen * z_curr[0]));
    pst13_open_rounds(p_red, ck_nxt, z_curr[1..PK], alpha_H_curr[1..PK], h_gen, rem_next)
}}

// ===== Spartan-NIZK proto (M = {m_lit} hardcoded).
//
// `az` / `bz` / `cz` are PRIVATE inputs — the harness pre-computes
// A·z, B·z, C·z natively in Rust (since zippel has no `Mv` primitive
// that could express the matvec inside the proto) and feeds them in.
// Matrices are still public because `partial_a/b/c` (for SC #2) and
// the SC #2 final R1CS-shape check both need them — but the partial
// eval dispatches to the sparse fast path in PolyVariant::SparseMle,
// so it's O(|nz|·M) rather than O(2^(2M)). =====
proto spartan<G1: Group, G2: Group, GT: Pairing<G1, G2>, F: Scalar<G1, G2>>(
    // 2M-variable MLEs for A, B, C in column-major (LSB-first) layout.
    // Built natively as SparseMle on the Rust side, so `eval(mat_x_t, rx)`
    // dispatches to a sparse partial-eval (O(|nz|·M) vs O(2^(2M)) dense).
    public mat_a_t:   Poly<F, {two_m_vars}, 1>,
    public mat_b_t:   Poly<F, {two_m_vars}, 1>,
    public mat_c_t:   Poly<F, {two_m_vars}, 1>,
    public io:        [F; {io_len}],
    private w:        [F; {two_nw}],
    private az:       [F; {two_m}],
    private bz:       [F; {two_m}],
    private cz:       [F; {two_m}],
    // SRS / proving key: ~6 MB of G1Affine commitment-key points at M=16.
    // Marked `private` so it isn't re-absorbed into the FS sponge on every
    // prove — only the prover graph references it (inside `pst13_commit_w`
    // and the prover branches of `pst13_open_rounds`; the verifier reads
    // `pi_*` from the transcript via `<-` and never touches `ck_n_w`).
    // Soundness binding to the prover's matrices/commitment-key is via the
    // small verification-key items below + the witness commitment c_w that
    // both sides absorb.
    private ck_n_w:   [G1; {two_nw}],
    public g_gen:     G1,
    public h_gen:     G2,
    public alpha_h_w: [G2; {nw}],
    // Concretely-typed placeholder for `draw_taus` — zippel's overload
    // resolution can't disambiguate `draw_taus([F; M])` for an [F; M]
    // built inline from a comprehension, so the harness ships a sized
    // zero array as a proto input. The actual τ challenges are still
    // drawn from the transcript inside `draw_taus`.
    public placeholder_tau: [F; {m_lit}],
    public f_one:     F
) where
    az * bz == cz
{{
    let one  = f_one;
    // Typed zero seeded from f_one (matrices are now Poly, no scalar
    // indexable element available).
    let zero = f_one - f_one;

    // ===== Witness commitment (first prover move). =====
    c_w <- pst13_commit_w(w, ck_n_w);

    // `az`, `bz`, `cz` are private inputs — no dense MVM in body.
    let z  = w ++ io ++ [one];

    let f_a = mle(az);
    let f_b = mle(bz);
    let f_c = mle(cz);

    // ===== V draws τ ∈ F^{m_lit} (via FS inside `draw_taus`). =====
    let tau = draw_taus(placeholder_tau);
    let eq_tau_evs      = eq_weights(tau);
    let eq_tau          = mle(eq_tau_evs);

    let neg_one = zero - one;
    let g_sub   = f_a * f_b + f_c * neg_one;
    let g_poly  = g_sub * eq_tau;

    // ===== Sum-check #1: claimed sum = 0, {m_lit} rounds, degree 3. =====
    let pts3   = [i for i in 0..4];
    let cfg1_0 = {{| poly: g_poly, num_variables: {m_lit}, max_degree: 3, round: 0, challenge: zero |}};
    let out1_0 = marginalize(cfg1_0);
    evs1_0 <- out1_0.evaluations;
    verify(zero == evs1_0[0] + evs1_0[1]);
    let g1_r1     = interpolate(pts3, evs1_0);
    rx0           <- challenge<F>;
    let prev1_vec = eval(g1_r1, [rx0]);
    let prev1     = prev1_vec[0];
    let sc1 = sc_recurse_d3(out1_0.next_poly, pts3, [rx0], prev1, rx0, 1);
    let rx  = sc1.challenges;
    let e_x = sc1.final_eval;

    let lx = eq_weights(rx);
    // v_a, v_b, v_c are derived from az/bz/cz (private), so they must be
    // logged to the transcript so the verifier can use them in the
    // linking check below.
    v_a <- dot(lx, az);
    v_b <- dot(lx, bz);
    v_c <- dot(lx, cz);
    let eq_tau_at_rx = dot(lx, eq_tau_evs);
    verify(e_x == (v_a * v_b - v_c) * eq_tau_at_rx);

    ra <- challenge<F>;
    rb <- challenge<F>;
    rc <- challenge<F>;
    let t2 = ra * v_a + rb * v_b + rc * v_c;

    // partial_x is the partial-evaluation of M_x's 2M-var MLE at rx
    // — i.e., the polynomial f(y) = M_x(rx, y) over the col-bits y.
    // Computing each entry y as `dot(lx, [mat[i*N+y] for i in 0..N])`
    // unrolls into N² mul-nodes per matrix; doing `eval(mle, rx)` with
    // col-major storage collapses it to a single backend op (one
    // DenseMle fix-prefix call). Both halves of zippel (prover and
    // verifier) execute this, so this lift cuts both. We then carry
    // partial_x as a Poly and never materialise the dense vector —
    // `l_mle` is just the poly linear combination, and v1/v2/v3 at
    // the final check are full evaluations at ry.
    let partial_a = eval(mat_a_t, rx);
    let partial_b = eval(mat_b_t, rx);
    let partial_c = eval(mat_c_t, rx);

    let l_mle  = partial_a * ra + partial_b * rb + partial_c * rc;
    let z_mle  = mle(z);
    let m_poly = l_mle * z_mle;

    // ===== Sum-check #2: claimed sum = T_2, {m_lit} rounds, degree 2. =====
    let pts2   = [i for i in 0..3];
    let cfg2_0 = {{| poly: m_poly, num_variables: {m_lit}, max_degree: 2, round: 0, challenge: zero |}};
    let out2_0 = marginalize(cfg2_0);
    evs2_0 <- out2_0.evaluations;
    verify(t2 == evs2_0[0] + evs2_0[1]);
    let g2_r1     = interpolate(pts2, evs2_0);
    ry0           <- challenge<F>;
    let prev2_vec = eval(g2_r1, [ry0]);
    let prev2     = prev2_vec[0];
    let sc2 = sc_recurse_d2(out2_0.next_poly, pts2, [ry0], prev2, ry0, 1);
    let ry  = sc2.challenges;
    let e_y = sc2.final_eval;

    let ly = eq_weights(ry);

    // ===== PCS open at pcs_z = ry first NW entries. =====
    //
    // eq_weights / dot are LSB-first (pcs_z[k] = value of x_k), so
    // sent_v_w = w_mle(pcs_z[0], ..., pcs_z[NW-1]). The PST13 recursion
    // below splits ck/p on contiguous halves, which peels the HIGH bit
    // first, so its round 0 needs the value for the highest variable.
    // Reverse pcs_z and alpha_h_w before passing so the helper's
    // z_curr[0] / alpha_H_curr[0] align with the high-bit fold. At M=2
    // (NW=1) these arrays are length 1 so the reversal is a no-op — which
    // is why the same call site worked at M=2 and failed silently at M>=3.
    let pcs_z       = ry[0..{nw}];
    let pcs_z_rev   = [pcs_z[{nw} - 1 - i] for i in 0..{nw}];
    let alpha_h_rev = [alpha_h_w[{nw} - 1 - i] for i in 0..{nw}];
    let ly_lo   = eq_weights(pcs_z);
    let v_w_val = dot(ly_lo, w);
    sent_v_w    <- v_w_val;

    let pcs_lhs = pair(c_w - (g_gen * sent_v_w), h_gen);
    let pcs_ok  = pst13_open_rounds(w, ck_n_w, pcs_z_rev, alpha_h_rev, h_gen, pcs_lhs);

    // ===== Final R1CS-shape check. =====
    let io_block = io ++ [one];
    let v_io     = dot(ly_lo, io_block);
    let ry_top   = ry[{m_lit} - 1];
    let v_z      = (one - ry_top) * sent_v_w + ry_top * v_io;

    // v_x = M_x(rx, ry) = full eval of partial_x at ry. (`dot(ly, partial_x)`
    // computes the same value via Lagrange weights over the dense vector,
    // but partial_x is a Poly here, so we go through `eval` instead. Full
    // eval (len(points) == num_vars) returns a scalar directly — no [0]
    // indexing.)
    let v1 = eval(partial_a, ry);
    let v2 = eval(partial_b, ry);
    let v3 = eval(partial_c, ry);

    verify(pcs_ok);
    verify(e_y == (ra * v1 + rb * v2 + rc * v3) * v_z)
}}
"#,
        m_lit = m_lit,
        two_m = two_m,
        two_m_vars = two_m_vars,
        nw = nw,
        two_nw = two_nw,
        io_len = io_len,
    )
}
