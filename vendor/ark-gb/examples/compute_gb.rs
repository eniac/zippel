//! Minimal usage example for `ark_gb::compute_gb`.
//!
//! Builds the cyclic-3 ideal in `Fr[x, y, z]` (BLS12-381 scalar field)
//! under degrevlex, runs [`ark_gb::compute_gb`], and prints the reduced
//! Gröbner basis in a Singular-ish textual form.
//!
//! Also prints timings for cyclic-3, cyclic-4, and cyclic-5 so the
//! example doubles as the task's performance-sanity run:
//!
//! ```console
//! $ cargo run --release --example compute_gb
//! ```

use std::sync::Arc;
use std::time::Instant;

use ark_bls12_381::Fr;
use ark_ff::{One, Zero};
use ark_gb::compute_gb;
use ark_gb::monomial::{GrevLexTerm, MonoTerm, Monomial};
use ark_gb::poly::Poly;
use ark_gb::ring::Ring;

fn mk_ring(nvars: u32) -> Arc<Ring<Fr>> {
    Arc::new(Ring::<Fr>::new(nvars).unwrap())
}

fn mono(r: &Ring<Fr>, e: &[u32]) -> GrevLexTerm {
    GrevLexTerm::from(MonoTerm::from_exponents(r, e).unwrap())
}

/// Render one polynomial as a Singular-ish string using the supplied
/// variable names. Good enough for human inspection; not a parser-
/// compatible round-trip (see the fixture parser in the tests for
/// that).
fn poly_to_string(p: &Poly<Fr, GrevLexTerm>, ring: &Ring<Fr>, var_names: &[&str]) -> String {
    if p.is_zero() {
        return "0".to_string();
    }
    let mut out = String::new();
    for (i, (c, m)) in p.iter().enumerate() {
        let is_neg_one = c == -Fr::one();
        let is_one = c == Fr::one();
        if i == 0 {
            if is_neg_one {
                out.push('-');
            }
        } else if is_neg_one {
            out.push('-');
        } else {
            out.push('+');
        }

        let exps = m.exponents(ring);
        let mono_is_one = exps.iter().all(|&e| e == 0);
        let print_coeff = (!is_one && !is_neg_one) || mono_is_one;
        if print_coeff {
            out.push_str(&format!("{}", c));
        }
        if !mono_is_one {
            let mut first_var = true;
            for (vi, &e) in exps.iter().enumerate() {
                if e == 0 {
                    continue;
                }
                if !first_var || print_coeff {
                    out.push('*');
                }
                out.push_str(var_names[vi]);
                if e > 1 {
                    out.push('^');
                    out.push_str(&e.to_string());
                }
                first_var = false;
            }
        }
    }
    let _ = Fr::zero(); // keep Zero import used
    out
}

fn run_cyclic(
    ring: Arc<Ring<Fr>>,
    name: &str,
    input: Vec<Poly<Fr, GrevLexTerm>>,
    var_names: &[&str],
) {
    println!("=== {} ===", name);
    let t = Instant::now();
    let gb = compute_gb(Arc::clone(&ring), input);
    let elapsed = t.elapsed();
    println!("basis size: {}", gb.len());
    println!("time:       {:?}", elapsed);
    for (i, p) in gb.iter().enumerate() {
        println!("  [{:>2}] {}", i, poly_to_string(p, &ring, var_names));
    }
    println!();
}

fn cyclic3() {
    let r = mk_ring(3);
    let m = |e: &[u32]| mono(&r, e);
    let one = Fr::one();
    let neg_one = -Fr::one();
    let gens = vec![
        Poly::from_terms(
            &r,
            vec![
                (one, m(&[1, 0, 0])),
                (one, m(&[0, 1, 0])),
                (one, m(&[0, 0, 1])),
            ],
        ),
        Poly::from_terms(
            &r,
            vec![
                (one, m(&[1, 1, 0])),
                (one, m(&[0, 1, 1])),
                (one, m(&[1, 0, 1])),
            ],
        ),
        Poly::from_terms(&r, vec![(one, m(&[1, 1, 1])), (neg_one, m(&[0, 0, 0]))]),
    ];
    run_cyclic(r, "cyclic-3 over Fr (BLS12-381)", gens, &["x", "y", "z"]);
}

fn cyclic4() {
    let r = mk_ring(4);
    let m = |e: &[u32]| mono(&r, e);
    let one = Fr::one();
    let neg_one = -Fr::one();
    let gens = vec![
        Poly::from_terms(
            &r,
            vec![
                (one, m(&[1, 0, 0, 0])),
                (one, m(&[0, 1, 0, 0])),
                (one, m(&[0, 0, 1, 0])),
                (one, m(&[0, 0, 0, 1])),
            ],
        ),
        Poly::from_terms(
            &r,
            vec![
                (one, m(&[1, 1, 0, 0])),
                (one, m(&[0, 1, 1, 0])),
                (one, m(&[0, 0, 1, 1])),
                (one, m(&[1, 0, 0, 1])),
            ],
        ),
        Poly::from_terms(
            &r,
            vec![
                (one, m(&[1, 1, 1, 0])),
                (one, m(&[0, 1, 1, 1])),
                (one, m(&[1, 0, 1, 1])),
                (one, m(&[1, 1, 0, 1])),
            ],
        ),
        Poly::from_terms(
            &r,
            vec![(one, m(&[1, 1, 1, 1])), (neg_one, m(&[0, 0, 0, 0]))],
        ),
    ];
    run_cyclic(
        r,
        "cyclic-4 over Fr (BLS12-381)",
        gens,
        &["a", "b", "c", "d"],
    );
}

fn cyclic5() {
    let r = mk_ring(5);
    let m = |e: &[u32]| mono(&r, e);
    let one = Fr::one();
    let neg_one = -Fr::one();
    let gens = vec![
        Poly::from_terms(
            &r,
            vec![
                (one, m(&[1, 0, 0, 0, 0])),
                (one, m(&[0, 1, 0, 0, 0])),
                (one, m(&[0, 0, 1, 0, 0])),
                (one, m(&[0, 0, 0, 1, 0])),
                (one, m(&[0, 0, 0, 0, 1])),
            ],
        ),
        Poly::from_terms(
            &r,
            vec![
                (one, m(&[1, 1, 0, 0, 0])),
                (one, m(&[0, 1, 1, 0, 0])),
                (one, m(&[0, 0, 1, 1, 0])),
                (one, m(&[0, 0, 0, 1, 1])),
                (one, m(&[1, 0, 0, 0, 1])),
            ],
        ),
        Poly::from_terms(
            &r,
            vec![
                (one, m(&[1, 1, 1, 0, 0])),
                (one, m(&[0, 1, 1, 1, 0])),
                (one, m(&[0, 0, 1, 1, 1])),
                (one, m(&[1, 0, 0, 1, 1])),
                (one, m(&[1, 1, 0, 0, 1])),
            ],
        ),
        Poly::from_terms(
            &r,
            vec![
                (one, m(&[1, 1, 1, 1, 0])),
                (one, m(&[0, 1, 1, 1, 1])),
                (one, m(&[1, 0, 1, 1, 1])),
                (one, m(&[1, 1, 0, 1, 1])),
                (one, m(&[1, 1, 1, 0, 1])),
            ],
        ),
        Poly::from_terms(
            &r,
            vec![(one, m(&[1, 1, 1, 1, 1])), (neg_one, m(&[0, 0, 0, 0, 0]))],
        ),
    ];
    run_cyclic(
        r,
        "cyclic-5 over Fr (BLS12-381)",
        gens,
        &["a", "b", "c", "d", "e"],
    );
}

fn main() {
    cyclic3();
    cyclic4();
    cyclic5();
}
