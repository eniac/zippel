//! Compare Zippel sum-check math with HyperPlonk’s sum-check on the same polynomial.
//!
//! Usage (from repo root `zippel/zippel`):
//!   `cargo run -p sumcheck_compare`              — `both`: FS Zippel + FS HyperPlonk (round 0 only matches)
//!   `cargo run -p sumcheck_compare -- oracle`    — **shared challenges**; all rounds should match
//!   `cargo run -p sumcheck_compare -- zippel|hp` — one backend only
//!
//! **Fiat–Shamir (`both`):** compared as canonical `BigUint` per coefficient; round 0 matches, later rounds differ.
//!
//! **Oracle (`oracle`):** draws `r1..r4` from `SUMCHECK_CHALLENGE_SEED` (HpFr), maps to Zippel `Fr` via
//! compressed serialization, runs `backend::marginalize` vs a vendored HyperPlonk prover round loop (no Merlin).
//! Prover messages use `r1,r2,r3` only; `r4` matches the paper’s last coin (printed for debugging).
//!
//! `SUMCHECK_HEX=1` prints per-coefficient compressed Fr hex.

use std::path::PathBuf;
use std::time::{Duration, Instant};

use ark_ff::Zero;
use ark_poly::DenseMultilinearExtension;
use ark_serialize::{
    CanonicalDeserialize as ZCanonicalDeserialize, CanonicalSerialize as ZCanonicalSerialize,
};
use backend::poly_variant::PolyVariant;
use backend::{ArkBls12_381, ArkConfig, Value, VirtualPolynomial as ZVirtualPolynomial};
use hp_ark_bls12_381::Fr as HpFr;
use hp_ark_poly::DenseMultilinearExtension as HpDenseMle;
use hp_ark_serialize::{
    CanonicalDeserialize as HpCanonicalDeserialize, CanonicalSerialize as HpCanonicalSerialize,
};
use lang::id::{Vid, Tid};
use num_bigint::BigUint;
use rand::rngs::StdRng;
use rand::{RngCore, SeedableRng};
use share::Ctx;
use subroutines::poly_iop::prelude::{IOPProof, PolyIOP, SumCheck};
use zippel::{check_verification, proof_size_bytes, ZippelArgs, ZippelHandler};

use arithmetic::VirtualPolynomial as HpVirtualPolynomial;
use backend::values::marginalize;

mod hp_oracle_prover;
use hp_oracle_prover::HpSumcheckOracle;

type HpVP = HpVirtualPolynomial<HpFr>;
type ZFr = <ArkBls12_381 as ArkConfig>::F;

const DEFAULT_NUM_VARS: usize = 10;
/// Degree bound used by `examples/sumcheck/sumcheck.zippel` in full protocol mode.
const FULL_PROTOCOL_MAX_DEGREE: usize = 10;
const DEFAULT_SEED: u64 = 0x5355_4D43_484B; // "SUMCHK"
/// Default RNG seed for **shared** sum-check challenges (r1..r4), independent of MLE table seed.
const DEFAULT_CHALLENGE_SEED: u64 = 0x4348_414c4c; // "CHALL"

fn zippel_protocol_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../examples/sumcheck/sumcheck.zippel")
}

fn bytes_to_hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn z_fr_compressed_hex(x: &ZFr) -> String {
    let mut v = Vec::new();
    if ZCanonicalSerialize::serialize_compressed(x, &mut v).is_err() {
        return "<serialize error>".into();
    }
    bytes_to_hex(&v)
}

fn hp_fr_compressed_hex(x: &HpFr) -> String {
    let mut v = Vec::new();
    if HpCanonicalSerialize::serialize_compressed(x, &mut v).is_err() {
        return "<serialize error>".into();
    }
    bytes_to_hex(&v)
}

fn z_canonical_uint(z: &ZFr) -> BigUint {
    (*z).into()
}

fn hp_canonical_uint(h: &HpFr) -> BigUint {
    (*h).into()
}

fn hp_fr_to_z_fr(h: &HpFr) -> ZFr {
    let mut b = Vec::new();
    HpCanonicalSerialize::serialize_compressed(h, &mut b).expect("HpFr serialize");
    ZCanonicalDeserialize::deserialize_compressed(b.as_slice()).expect("ZFr deserialize")
}

/// Zippel `marginalize` with the same schedule as HyperPlonk: round 0 uses field zero (no fix);
/// rounds 1.. use `r1, r2, …`.
fn z_oracle_round_messages(
    vp: &ZVirtualPolynomial<ZFr>,
    num_vars: usize,
    max_degree: usize,
    r_fix: &[ZFr],
) -> Vec<Vec<ZFr>> {
    let z0 = ZFr::zero();
    let (m0, mut cur) = marginalize::<ArkBls12_381>(vp, num_vars, max_degree, 0, Some(z0));
    let mut out = vec![m0];
    for i in 0..num_vars - 1 {
        let (m, next) = marginalize::<ArkBls12_381>(
            &cur,
            num_vars,
            max_degree,
            i + 1,
            Some(r_fix[i]),
        );
        out.push(m);
        cur = next;
    }
    out
}

fn hp_oracle_round_messages(poly: &HpVP, r_fix: &[HpFr]) -> Result<Vec<Vec<HpFr>>, String> {
    let mut st = HpSumcheckOracle::init(poly)?;
    let mut out = Vec::with_capacity(poly.aux_info.num_variables);
    out.push(st.prove_round(None)?);
    for r in r_fix {
        out.push(st.prove_round(Some(*r))?);
    }
    Ok(out)
}

fn shared_challenges_hp(challenge_seed: u64, num_vars: usize) -> Vec<HpFr> {
    let mut rng = StdRng::seed_from_u64(challenge_seed);
    (0..num_vars).map(|_| HpFr::from(rng.next_u64())).collect()
}

fn run_oracle_compare(
    num_vars: usize,
    max_degree: usize,
    poly_seed: u64,
    challenge_seed: u64,
    print_hex: bool,
    verbose_diffs: bool,
) {
    if max_degree == 0 {
        eprintln!("SUMCHECK_MAX_DEGREE must be >= 1.");
        std::process::exit(2);
    }
    println!("=== Shared-challenge oracle (Zippel marginalize vs vendored HyperPlonk prover) ===");
    println!("  MLE / polynomial seed: {poly_seed}");
    println!("  Challenge seed:        {challenge_seed}");
    println!("  num_vars:              {num_vars}");
    println!("  polynomial degree:     {max_degree}");

    let z_vp = z_oracle_poly_from_seed(num_vars, poly_seed, max_degree);
    let (hp_poly, _sum) = hp_oracle_poly_from_seed(num_vars, poly_seed, max_degree);

    let r_hp = shared_challenges_hp(challenge_seed, num_vars);
    let challenge_preview = r_hp
        .iter()
        .take(4)
        .map(hp_fr_compressed_hex)
        .collect::<Vec<_>>()
        .join(", ");
    println!("  Challenges r1..r4 (HpFr compressed hex): {challenge_preview}");

    let r_fix_z: Vec<ZFr> = r_hp.iter().take(num_vars - 1).map(hp_fr_to_z_fr).collect();

    let t0 = Instant::now();
    let z_rounds = z_oracle_round_messages(&z_vp, num_vars, max_degree, &r_fix_z);
    let z_oracle_elapsed = t0.elapsed();
    let r_fix_hp: Vec<HpFr> = r_hp.iter().copied().take(num_vars - 1).collect();
    let t1 = Instant::now();
    let hp_rounds = hp_oracle_round_messages(&hp_poly, &r_fix_hp).unwrap_or_else(|e| {
        eprintln!("HyperPlonk oracle: {e}");
        std::process::exit(1);
    });
    let hp_oracle_elapsed = t1.elapsed();
    println!("Zippel oracle prover:     {:.3?}", z_oracle_elapsed);
    println!("HyperPlonk oracle prover: {:.3?}", hp_oracle_elapsed);

    if print_hex {
        print_round_hex_lines_z("Zippel oracle", &z_rounds);
        print_round_hex_lines_hp("HyperPlonk oracle", &hp_rounds);
    }

    compare_rounds(&z_rounds, &hp_rounds, verbose_diffs, true);
}

/// Build the same product-of-3-MLE `VirtualPolynomial` as the sumcheck example (Zippel field).
fn z_oracle_poly_from_seed(num_vars: usize, seed: u64, degree: usize) -> ZVirtualPolynomial<ZFr> {
    let eval_count = 1usize << num_vars;
    let mut rng = StdRng::seed_from_u64(seed);
    let base_evals: Vec<ZFr> = (0..eval_count).map(|_| ZFr::from(rng.next_u64())).collect();
    let base = ZVirtualPolynomial::from_poly(PolyVariant::DenseMle(
        DenseMultilinearExtension::from_evaluations_vec(num_vars, base_evals),
    ));

    let mut poly = base.clone();
    for _ in 1..degree {
        poly = poly.poly_mul(&base).expect("poly*base");
    }
    poly
}

fn extract_zippel_round_scalars(proof: &[Value<ArkBls12_381>]) -> Vec<Vec<ZFr>> {
    let mut out = Vec::new();
    for v in proof {
        match v {
            Value::VecScalar(s) => out.push(s.clone()),
            Value::Record(map) => {
                let mut pairs: Vec<_> = map
                    .iter()
                    .map(|(k, v)| (k.clone(), v.clone()))
                    .collect();
                pairs.sort_by(|a, b| a.0.cmp(&b.0));
                for (_k, inner) in pairs {
                    if let Value::VecScalar(s) = inner {
                        out.push(s);
                    }
                }
            }
            _ => {}
        }
    }
    out
}

/// `IOPProverMessage` is a single `evaluations` field; ark 0.4 serializes it like `Vec<HpFr>`.
fn decode_hp_prover_message<M: HpCanonicalSerialize>(msg: &M) -> Result<Vec<HpFr>, String> {
    let mut buf = Vec::new();
    HpCanonicalSerialize::serialize_compressed(msg, &mut buf)
        .map_err(|e| format!("serialize msg: {e:?}"))?;
    let v: Vec<HpFr> = HpCanonicalDeserialize::deserialize_compressed(buf.as_slice())
        .map_err(|e| format!("deserialize Vec<Fr>: {e:?}"))?;
    Ok(v)
}

fn extract_hp_round_scalars(proof: &IOPProof<HpFr>) -> Result<Vec<Vec<HpFr>>, String> {
    proof
        .proofs
        .iter()
        .enumerate()
        .map(|(i, m)| decode_hp_prover_message(m).map_err(|e| format!("round {i}: {e}")))
        .collect()
}

fn print_round_hex_lines_z(label: &str, rounds: &[Vec<ZFr>]) {
    println!("--- {label} (compressed canonical Fr hex) ---");
    for (r, coeffs) in rounds.iter().enumerate() {
        for (i, x) in coeffs.iter().enumerate() {
            println!("  r{r} c{i}: {}", z_fr_compressed_hex(x));
        }
    }
}

fn print_round_hex_lines_hp(label: &str, rounds: &[Vec<HpFr>]) {
    println!("--- {label} (compressed canonical Fr hex) ---");
    for (r, coeffs) in rounds.iter().enumerate() {
        for (i, x) in coeffs.iter().enumerate() {
            println!("  r{r} c{i}: {}", hp_fr_compressed_hex(x));
        }
    }
}

fn compare_rounds(
    z: &[Vec<ZFr>],
    h: &[Vec<HpFr>],
    verbose_diffs: bool,
    shared_challenges: bool,
) {
    println!("--- Cross-backend comparison (canonical `BigUint` mod p) ---");
    if shared_challenges {
        println!("Shared-challenge mode: **all rounds** should match (same r1..r3 in prover state).");
    } else {
        println!(
            "Fiat–Shamir mode: only round **0** is expected to match; later rounds use different transcripts."
        );
    }
    println!(
        "Per-coefficient DIFF lines for rounds ≥1: {} (set SUMCHECK_VERBOSE=1 to print all).",
        if verbose_diffs { "on" } else { "off" }
    );
    if z.len() != h.len() {
        println!(
            "Round count mismatch: zippel {} vs hyperplonk {}",
            z.len(),
            h.len()
        );
    }
    let rounds = z.len().min(h.len());
    let mut ok = 0usize;
    let mut bad = 0usize;
    let mut bad_r0 = 0usize;
    for r in 0..rounds {
        let zr = &z[r];
        let hr = &h[r];
        if zr.len() != hr.len() {
            println!(
                "  r{r}: length mismatch zippel {} vs hyperplonk {}",
                zr.len(),
                hr.len()
            );
            bad += zr.len().max(hr.len());
            continue;
        }
        for i in 0..zr.len() {
            let zu = z_canonical_uint(&zr[i]);
            let hu = hp_canonical_uint(&hr[i]);
            if zu == hu {
                ok += 1;
            } else {
                if r == 0 {
                    bad_r0 += 1;
                }
                if r == 0 || verbose_diffs {
                    println!(
                        "  r{r} c{i}: DIFF\n    z {}\n    h {}\n    z_hex {}\n    h_hex {}",
                        zu,
                        hu,
                        z_fr_compressed_hex(&zr[i]),
                        hp_fr_compressed_hex(&hr[i])
                    );
                }
                bad += 1;
            }
        }
    }
    if bad_r0 == 0 && !z.is_empty() && !h.is_empty() && z[0].len() == h[0].len() {
        println!(
            "Round 0: all {} univariate evaluation points match (same polynomial / sum).",
            z[0].len()
        );
    } else if bad_r0 > 0 {
        println!(
            "Round 0: {bad_r0} mismatch(es) — Zippel marginalize vs HyperPlonk round-0 message differs."
        );
    }
    if shared_challenges {
        println!("Summary: {ok} matching coefficients; {bad} differing (oracle expects 0 differing).");
    } else {
        println!("Summary: {ok} matching coefficients; {bad} differing (expected for r≥1 under separate FS).");
    }
}

fn print_prover_timing_comparison(z: Duration, h: Duration) {
    let (faster, slower, faster_name, slower_name) = if z <= h {
        (z, h, "Zippel", "HyperPlonk")
    } else {
        (h, z, "HyperPlonk", "Zippel")
    };
    let ratio = slower.as_secs_f64() / faster.as_secs_f64();
    println!("--- Prover timing comparison (same polynomial seed) ---");
    println!("Zippel prover:     {:.3?}", z);
    println!("HyperPlonk prover: {:.3?}", h);
    println!(
        "{faster_name} is faster by {:.2}x over {slower_name}.",
        ratio
    );
}

fn run_zippel(
    num_vars: usize,
    max_degree: usize,
    seed: u64,
    print_hex: bool,
) -> (Vec<Vec<ZFr>>, Duration, Duration) {
    println!("=== Zippel sumcheck (Bls12-381, git ark) ===");
    let args = ZippelArgs::new(zippel_protocol_path());
    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("S"), &10);
    handler.compile(&sizes);

    let inputs = zippel_inputs_from_seed(num_vars, max_degree, seed);
    let prover_scheduled = handler.default_schedule_prover();
    let t0 = Instant::now();
    let proof = handler.run_prover(prover_scheduled, inputs);
    let prover_elapsed = t0.elapsed();
    println!("Prover time:    {:.2?}", prover_elapsed);
    println!(
        "Proof size:     {} bytes ({} top-level values)",
        proof_size_bytes::<ArkBls12_381>(&proof),
        proof.len()
    );

    let rounds = extract_zippel_round_scalars(&proof);
    if print_hex {
        print_round_hex_lines_z("Zippel", &rounds);
    }

    let verifier_scheduled = handler.default_schedule_verifier();
    let t1 = Instant::now();
    let verifier_result = handler.run_verifier(verifier_scheduled, proof);
    let verifier_elapsed = t1.elapsed();
    println!("Verifier time:  {:.2?}", verifier_elapsed);
    let result = check_verification(verifier_result);
    if result.passed {
        println!("Verification:   ✓ PASSED");
    } else {
        println!("Verification:   ✗ FAILED");
        std::process::exit(1);
    }
    (rounds, prover_elapsed, verifier_elapsed)
}

fn zippel_inputs_from_seed(
    num_vars: usize,
    degree: usize,
    seed: u64,
) -> Ctx<Vid, Value<ArkBls12_381>> {
    let eval_count = 1usize << num_vars;
    let mut rng = StdRng::seed_from_u64(seed);
    if degree == 0 {
        eprintln!("SUMCHECK_MAX_DEGREE must be >= 1 for full mode.");
        std::process::exit(2);
    }

    let base_evals: Vec<ZFr> = (0..eval_count).map(|_| ZFr::from(rng.next_u64())).collect();
    let claimed_sum: ZFr = base_evals
        .iter()
        .map(|x| (0..degree).fold(ZFr::from(1u64), |acc, _| acc * *x))
        .fold(ZFr::zero(), |acc, val| acc + val);

    let base = ZVirtualPolynomial::from_poly(PolyVariant::DenseMle(
        DenseMultilinearExtension::from_evaluations_vec(num_vars, base_evals),
    ));
    let mut full_poly = base.clone();
    for _ in 1..degree {
        full_poly = full_poly.poly_mul(&base).expect("poly*base");
    }
    let poly = Value::Poly(full_poly);
    Ctx::from_iter([
        (Vid("claimed_sum".to_string()), Value::Scalar(claimed_sum)),
        (Vid("poly".to_string()), poly),
    ])
}

fn run_hyperplonk(
    num_vars: usize,
    max_degree: usize,
    seed: u64,
    print_hex: bool,
) -> (Vec<Vec<HpFr>>, HpFr, Duration, Duration) {
    println!("=== HyperPlonk sum-check (Bls12-381 Fr, ark 0.4) ===");
    let (poly, claimed_sum) = hp_full_protocol_poly_from_seed(num_vars, seed, max_degree);
    println!("claimed_sum (compressed hex): {}", hp_fr_compressed_hex(&claimed_sum));

    let mut transcript = <PolyIOP<HpFr> as SumCheck<HpFr>>::init_transcript();
    let t0 = Instant::now();
    let proof = match <PolyIOP<HpFr> as SumCheck<HpFr>>::prove(&poly, &mut transcript) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("HyperPlonk prove error: {e:?}");
            std::process::exit(1);
        }
    };
    let prover_elapsed = t0.elapsed();
    println!("Prover time:    {:.2?}", prover_elapsed);

    let rounds = extract_hp_round_scalars(&proof).unwrap_or_else(|e| {
        eprintln!("decode hyperplonk rounds: {e}");
        std::process::exit(1);
    });
    if print_hex {
        print_round_hex_lines_hp("HyperPlonk", &rounds);
    }

    println!(
        "Fiat–Shamir challenges ({}): first {}",
        proof.point.len(),
        proof
            .point
            .first()
            .map(hp_fr_compressed_hex)
            .unwrap_or_default()
    );

    let aux = poly.aux_info.clone();
    let mut v_transcript = <PolyIOP<HpFr> as SumCheck<HpFr>>::init_transcript();
    let t1 = Instant::now();
    let subclaim = match <PolyIOP<HpFr> as SumCheck<HpFr>>::verify(
        claimed_sum,
        &proof,
        &aux,
        &mut v_transcript,
    ) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("HyperPlonk verify error: {e:?}");
            std::process::exit(1);
        }
    };
    let verifier_elapsed = t1.elapsed();
    println!("Verifier time:  {:.2?}", verifier_elapsed);

    let eval_at = poly.evaluate(&subclaim.point).unwrap_or_else(|e| {
        eprintln!("evaluate at subclaim point: {e:?}");
        std::process::exit(1);
    });
    if eval_at == subclaim.expected_evaluation {
        println!("Verification:   ✓ PASSED (eval at r matches subclaim)");
    } else {
        eprintln!(
            "Verification:   ✗ FAILED: eval={eval_at:?} expected={:?}",
            subclaim.expected_evaluation
        );
        std::process::exit(1);
    }
    (rounds, claimed_sum, prover_elapsed, verifier_elapsed)
}

fn hp_oracle_poly_from_seed(num_vars: usize, seed: u64, max_degree: usize) -> (HpVP, HpFr) {
    let eval_count = 1usize << num_vars;
    let mut rng = StdRng::seed_from_u64(seed);

    let base: Vec<HpFr> = (0..eval_count).map(|_| HpFr::from(rng.next_u64())).collect();

    let mut sum = HpFr::from(0u64);
    for value in &base {
        sum += (0..max_degree).fold(HpFr::from(1u64), |acc, _| acc * *value);
    }

    let m = std::sync::Arc::new(HpDenseMle::from_evaluations_vec(num_vars, base));
    let mles = (0..max_degree).map(|_| m.clone()).collect::<Vec<_>>();

    let mut poly = HpVP::new(num_vars);
    poly.add_mle_list(mles, HpFr::from(1u64))
        .expect("add_mle_list");

    poly.aux_info.max_degree = max_degree;

    (poly, sum)
}

fn hp_full_protocol_poly_from_seed(num_vars: usize, seed: u64, max_degree: usize) -> (HpVP, HpFr) {
    let eval_count = 1usize << num_vars;
    let mut rng = StdRng::seed_from_u64(seed);
    if max_degree == 0 {
        eprintln!("SUMCHECK_MAX_DEGREE must be >= 1 for full mode.");
        std::process::exit(2);
    }

    let base: Vec<HpFr> = (0..eval_count).map(|_| HpFr::from(rng.next_u64())).collect();

    let mut sum = HpFr::from(0u64);
    for value in &base {
        sum += (0..max_degree).fold(HpFr::from(1u64), |acc, _| acc * *value);
    }

    let m = std::sync::Arc::new(HpDenseMle::from_evaluations_vec(num_vars, base));
    let mles = (0..max_degree).map(|_| m.clone()).collect::<Vec<_>>();

    let mut poly = HpVP::new(num_vars);
    poly.add_mle_list(mles, HpFr::from(1u64))
        .expect("add_mle_list");
    poly.aux_info.max_degree = max_degree;
    (poly, sum)
}

fn main() {
    let num_vars = std::env::var("SUMCHECK_NUM_VARS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(DEFAULT_NUM_VARS);
    let max_degree = std::env::var("SUMCHECK_MAX_DEGREE")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(FULL_PROTOCOL_MAX_DEGREE);
    let seed = std::env::var("SUMCHECK_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(DEFAULT_SEED);

    let print_hex = std::env::var("SUMCHECK_HEX")
        .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
        .unwrap_or(false);

    let arg = std::env::args().nth(1);
    match arg.as_deref() {
        Some("zippel") | Some("z") => {
            run_zippel(num_vars, max_degree, seed, print_hex);
        }
        Some("hp") | Some("hyperplonk") => {
            run_hyperplonk(num_vars, max_degree, seed, print_hex);
        }
        Some("help") | Some("-h") | Some("--help") => {
            println!(
                "Usage: cargo run -p sumcheck_compare -- [zippel|hp|oracle|both]\n\
                 Modes:\n\
                   both    Zippel FS + HyperPlonk FS (default); round 0 only matches\n\
                   oracle  Same MLE seed + same explicit r1..r4; all rounds should match\n\
                 Env: SUMCHECK_SEED (u64, default {DEFAULT_SEED}) — MLE tables / polynomial\n\
                     SUMCHECK_NUM_VARS (usize, default {DEFAULT_NUM_VARS}) — number of variables\n\
                     SUMCHECK_MAX_DEGREE (usize, default {FULL_PROTOCOL_MAX_DEGREE}) — degree bound\n\
                      SUMCHECK_CHALLENGE_SEED (u64, default {DEFAULT_CHALLENGE_SEED}) — oracle challenges\n\
                      SUMCHECK_HEX=1       per-coefficient compressed Fr hex\n\
                      SUMCHECK_VERBOSE=1   print every differing coeff\n\
                 Oracle uses Zippel `marginalize` vs a vendored HyperPlonk prover (no Merlin)."
            );
        }
        None | Some("both") => {
            let verbose_diffs = std::env::var("SUMCHECK_VERBOSE")
                .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
                .unwrap_or(false);
            let (z_rounds, z_prover, _z_verifier) = run_zippel(num_vars, max_degree, seed, print_hex);
            println!();
            let (hp_rounds, _, hp_prover, _hp_verifier) =
                run_hyperplonk(num_vars, max_degree, seed, print_hex);
            println!();
            compare_rounds(&z_rounds, &hp_rounds, verbose_diffs, false);
            println!();
            print_prover_timing_comparison(z_prover, hp_prover);
        }
        Some("oracle") | Some("shared") => {
            let poly_seed = std::env::var("SUMCHECK_SEED")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(DEFAULT_SEED);
            let challenge_seed = std::env::var("SUMCHECK_CHALLENGE_SEED")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(DEFAULT_CHALLENGE_SEED);
            let verbose_diffs = std::env::var("SUMCHECK_VERBOSE")
                .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
                .unwrap_or(false);
            run_oracle_compare(
                num_vars,
                max_degree,
                poly_seed,
                challenge_seed,
                print_hex,
                verbose_diffs,
            );
        }
        Some(other) => {
            eprintln!("Unknown mode {other:?}. Use zippel, hp, both, oracle, or --help.");
            std::process::exit(2);
        }
    }
}
