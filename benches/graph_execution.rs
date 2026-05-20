//! Criterion benchmarks for graph execution (prover and verifier).
//!
//! These benchmarks measure the end-to-end execution time of `run_graph`
//! via the public `ZippelHandler` API. They are useful for comparing
//! different `run_graph` implementations and tracking performance regressions.
//!
//! Run with: cargo bench --bench graph_execution

use criterion::{Criterion, criterion_group, criterion_main};
use std::path::PathBuf;

use ark_ff::Field;
use ark_std::UniformRand;
use backend::{ATyp, ArkBls12_381, ArkConfig, ArkGroupOps, ArkPairingOps, ArkSecp256k1, Value};
use lang::id::{Tid, Vid};
use share::Ctx;
use zippel::*;

// ---------------------------------------------------------------------------
// Schnorr protocol (ArkBls12_381) — small, fast, exercises full transcript
// ---------------------------------------------------------------------------

fn schnorr_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;
    let x = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let g = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let h_affines = <ArkBls12_381 as ArkConfig>::G1Ops::vec_mul(&g, &vec![x]);
    let h = h_affines.into_iter().next().unwrap();
    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("x".to_string()), Value::Scalar(x)),
        (Vid("g".to_string()), Value::G1(g)),
        (Vid("h".to_string()), Value::G1Affine(h)),
    ])
}

fn bench_schnorr_prover(c: &mut Criterion) {
    let mut group = c.benchmark_group("schnorr");
    group.sample_size(10);

    // Compile once outside the benchmark loop.
    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(ZippelArgs::new(
        PathBuf::from("examples/schnorr/schnorr.zippel"),
    ));
    handler.compile(&Ctx::new());
    let inputs = schnorr_inputs();

    group.bench_function("prover", |b| {
        b.iter(|| {
            let scheduled = handler.default_schedule_prover();
            handler
                .run_prover(scheduled, inputs.clone())
                .expect("run_prover failed")
        })
    });

    group.finish();
}

fn bench_schnorr_verifier(c: &mut Criterion) {
    let mut group = c.benchmark_group("schnorr");
    group.sample_size(10);

    // Compile and produce a proof outside the benchmark loop.
    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(ZippelArgs::new(
        PathBuf::from("examples/schnorr/schnorr.zippel"),
    ));
    handler.compile(&Ctx::new());
    let inputs = schnorr_inputs();
    let prover_scheduled = handler.default_schedule_prover();
    let proof = handler
        .run_prover(prover_scheduled, inputs)
        .expect("run_prover failed");

    group.bench_function("verifier", |b| {
        b.iter(|| {
            let scheduled = handler.default_schedule_verifier();
            handler
                .run_verifier(scheduled, proof.clone())
                .expect("run_verifier failed")
        })
    });

    group.finish();
}

// ---------------------------------------------------------------------------
// Hadamard protocol (ArkSecp256k1) — different curve, tiny graph
// ---------------------------------------------------------------------------

#[allow(non_snake_case)]
fn hadamard_inputs() -> Ctx<Vid, Value<ArkSecp256k1>> {
    use ark_ff::{One, Zero};

    let mut rng = rand::rngs::OsRng;
    let n: usize = 4;

    // Random univariate polynomials p_A, p_B, p_C of degree < N.
    let mut p_a_coeffs = Vec::with_capacity(n);
    let mut p_b_coeffs = Vec::with_capacity(n);
    let mut p_c_coeffs = Vec::with_capacity(n);
    for _ in 0..n {
        let a_i: Value<ArkSecp256k1> =
            Value::<ArkSecp256k1>::random(&mut rng, &backend::ATyp::scalar());
        let b_i: Value<ArkSecp256k1> =
            Value::<ArkSecp256k1>::random(&mut rng, &backend::ATyp::scalar());
        let c_i: Value<ArkSecp256k1> =
            Value::<ArkSecp256k1>::random(&mut rng, &backend::ATyp::scalar());
        p_a_coeffs.push(a_i.into_scalar());
        p_b_coeffs.push(b_i.into_scalar());
        p_c_coeffs.push(c_i.into_scalar());
    }
    let p_A = Value::<ArkSecp256k1>::VecScalar(p_a_coeffs).value_poly();
    let p_B = Value::<ArkSecp256k1>::VecScalar(p_b_coeffs).value_poly();
    let p_C = Value::<ArkSecp256k1>::VecScalar(p_c_coeffs).value_poly();

    // v_H = 1 (constant polynomial), so any poly is divisible by v_H.
    let zero = <ArkSecp256k1 as ArkConfig>::F::zero();
    let one = <ArkSecp256k1 as ArkConfig>::F::one();
    let mut v_h_coeffs = Vec::with_capacity(n);
    v_h_coeffs.push(one);
    v_h_coeffs.extend(std::iter::repeat_n(zero, n));
    let v_H = Value::<ArkSecp256k1>::VecScalar(v_h_coeffs).value_poly();

    Ctx::<Vid, Value<ArkSecp256k1>>::from_iter([
        (Vid("p_A".to_string()), p_A),
        (Vid("p_B".to_string()), p_B),
        (Vid("p_C".to_string()), p_C),
        (Vid("v_H".to_string()), v_H),
    ])
}

fn bench_hadamard_prover(c: &mut Criterion) {
    use lang::id::Tid;

    let mut group = c.benchmark_group("hadamard");

    let mut handler: ZippelHandler<ArkSecp256k1> = ZippelHandler::new(ZippelArgs::new(
        PathBuf::from("examples/hadamard/hadamard.zippel"),
    ));
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("S"), &4usize);
    handler.compile(&sizes);
    let inputs = hadamard_inputs();

    group.bench_function("prover", |b| {
        b.iter(|| {
            let scheduled = handler.default_schedule_prover();
            handler
                .run_prover(scheduled, inputs.clone())
                .expect("run_prover failed")
        })
    });

    group.finish();
}

fn bench_hadamard_verifier(c: &mut Criterion) {
    use lang::id::Tid;

    let mut group = c.benchmark_group("hadamard");

    let mut handler: ZippelHandler<ArkSecp256k1> = ZippelHandler::new(ZippelArgs::new(
        PathBuf::from("examples/hadamard/hadamard.zippel"),
    ));
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("S"), &4usize);
    handler.compile(&sizes);
    let inputs = hadamard_inputs();
    let prover_scheduled = handler.default_schedule_prover();
    let proof = handler
        .run_prover(prover_scheduled, inputs)
        .expect("run_prover failed");

    group.bench_function("verifier", |b| {
        b.iter(|| {
            let scheduled = handler.default_schedule_verifier();
            handler
                .run_verifier(scheduled, proof.clone())
                .expect("run_verifier failed")
        })
    });

    group.finish();
}

// ---------------------------------------------------------------------------
// Map comprehension benchmark (ArkBls12_381) — various sizes N = 4, 16, 64
// ---------------------------------------------------------------------------

fn map_comp_inputs(n: usize) -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;

    let g_vec: Value<ArkBls12_381> = Value::random(&mut rng, &ATyp::vec(&ATyp::g1(), n));
    let x_vec: Value<ArkBls12_381> = Value::random(&mut rng, &ATyp::vec_scalar(n));

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("g_vec".to_string()), g_vec),
        (Vid("x_vec".to_string()), x_vec),
    ])
}

fn bench_map_comp_prover(c: &mut Criterion) {
    let mut group = c.benchmark_group("map_comp");
    group.sample_size(10);

    for &n in [4usize, 16, 64].iter() {
        let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(ZippelArgs::new(
            PathBuf::from("examples/map_comp_bench/map_comp_bench.zippel"),
        ));
        let mut sizes = Ctx::new();
        sizes.insert(&Tid::new("S"), &n);
        handler.compile(&sizes);
        let inputs = map_comp_inputs(n);

        group.bench_function(format!("prover/N={}", n).as_str(), |b| {
            b.iter(|| {
                let scheduled = handler.default_schedule_prover();
                handler
                    .run_prover(scheduled, inputs.clone())
                    .expect("run_prover failed")
            })
        });
    }

    group.finish();
}

fn bench_map_comp_verifier(c: &mut Criterion) {
    let mut group = c.benchmark_group("map_comp");
    group.sample_size(10);

    for &n in [4usize, 16, 64].iter() {
        let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(ZippelArgs::new(
            PathBuf::from("examples/map_comp_bench/map_comp_bench.zippel"),
        ));
        let mut sizes = Ctx::new();
        sizes.insert(&Tid::new("S"), &n);
        handler.compile(&sizes);
        let inputs = map_comp_inputs(n);
        let prover_scheduled = handler.default_schedule_prover();
        let proof = handler
            .run_prover(prover_scheduled, inputs)
            .expect("run_prover failed");

        group.bench_function(format!("verifier/N={}", n).as_str(), |b| {
            b.iter(|| {
                let scheduled = handler.default_schedule_verifier();
                handler
                    .run_verifier(scheduled, proof.clone())
                    .expect("run_verifier failed")
            })
        });
    }

    group.finish();
}

// ---------------------------------------------------------------------------
// Pedersen commitment equality (ArkBls12_381) — classic ZK primitive
// ---------------------------------------------------------------------------

fn pedersen_eq_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    use std::ops::Mul;

    let mut rng = rand::rngs::OsRng;

    let x = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let r1 = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let r2 = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let g = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let h = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);

    let c1 = g.mul(x) + h.mul(r1);
    let c2 = g.mul(x) + h.mul(r2);

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("x".to_string()), Value::Scalar(x)),
        (Vid("r1".to_string()), Value::Scalar(r1)),
        (Vid("r2".to_string()), Value::Scalar(r2)),
        (Vid("g".to_string()), Value::G1(g)),
        (Vid("h".to_string()), Value::G1(h)),
        (Vid("c1".to_string()), Value::G1(c1)),
        (Vid("c2".to_string()), Value::G1(c2)),
    ])
}

fn bench_pedersen_eq_prover(c: &mut Criterion) {
    let mut group = c.benchmark_group("pedersen_eq");
    group.sample_size(10);

    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(ZippelArgs::new(
        PathBuf::from("examples/commitment_equality/commitment_equality.zippel"),
    ));
    handler.compile(&Ctx::new());
    let inputs = pedersen_eq_inputs();

    group.bench_function("prover", |b| {
        b.iter(|| {
            let scheduled = handler.default_schedule_prover();
            handler
                .run_prover(scheduled, inputs.clone())
                .expect("run_prover failed")
        })
    });

    group.finish();
}

fn bench_pedersen_eq_verifier(c: &mut Criterion) {
    let mut group = c.benchmark_group("pedersen_eq");
    group.sample_size(10);

    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(ZippelArgs::new(
        PathBuf::from("examples/commitment_equality/commitment_equality.zippel"),
    ));
    handler.compile(&Ctx::new());
    let inputs = pedersen_eq_inputs();
    let prover_scheduled = handler.default_schedule_prover();
    let proof = handler
        .run_prover(prover_scheduled, inputs)
        .expect("run_prover failed");

    group.bench_function("verifier", |b| {
        b.iter(|| {
            let scheduled = handler.default_schedule_verifier();
            handler
                .run_verifier(scheduled, proof.clone())
                .expect("run_verifier failed")
        })
    });

    group.finish();
}

// ---------------------------------------------------------------------------
// IPA (Inner Product Argument) — ArkSecp256k1, exercises recursive protocol
// Instance size: 2^S elements.  Default S=10 (fast); increase to 15 for
// a more stressful benchmark (but expect long runtimes).
// ---------------------------------------------------------------------------

fn ipa_inputs(s: usize) -> Ctx<Vid, Value<ArkSecp256k1>> {
    let mut rng = rand::rngs::OsRng;
    let n_val_const = 1usize << s;

    let u_aux_base: Value<ArkSecp256k1> = Value::<ArkSecp256k1>::random(&mut rng, &ATyp::g1());
    let g_vec: Value<ArkSecp256k1> =
        Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec(&ATyp::g1(), n_val_const));
    let h_vec: Value<ArkSecp256k1> =
        Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec(&ATyp::g1(), n_val_const));
    let a_vec_witness: Value<ArkSecp256k1> =
        Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec_scalar(n_val_const));
    let b_vec_witness: Value<ArkSecp256k1> =
        Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec_scalar(n_val_const));
    let ip_val_claimed: Value<ArkSecp256k1> = a_vec_witness.clone().dot(b_vec_witness.clone());
    let p_initial_commitment: Value<ArkSecp256k1> =
        g_vec.clone().dot(a_vec_witness.clone()) + h_vec.clone().dot(b_vec_witness.clone());
    let sum_vec: Value<ArkSecp256k1> =
        Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec_scalar(n_val_const));

    Ctx::<Vid, Value<ArkSecp256k1>>::from_iter([
        (Vid("g_vec".to_string()), g_vec),
        (Vid("h_vec".to_string()), h_vec),
        (
            Vid("p_initial_commitment".to_string()),
            p_initial_commitment,
        ),
        (Vid("ip_val_claimed".to_string()), ip_val_claimed),
        (Vid("u_aux_base".to_string()), u_aux_base),
        (Vid("a_vec_witness".to_string()), a_vec_witness),
        (Vid("b_vec_witness".to_string()), b_vec_witness),
        (Vid("sum_vec".to_string()), sum_vec),
    ])
}

const IPA_S: usize = 15;

fn bench_ipa_prover(c: &mut Criterion) {
    let mut group = c.benchmark_group("ipa");
    group.sample_size(10);

    let mut handler: ZippelHandler<ArkSecp256k1> =
        ZippelHandler::new(ZippelArgs::new(PathBuf::from("examples/ipa/ipa.zippel")));
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("S"), &IPA_S);
    handler.compile(&sizes);
    let inputs = ipa_inputs(IPA_S);

    group.bench_function(format!("prover/S={}", IPA_S).as_str(), |b| {
        b.iter(|| {
            let scheduled = handler.default_schedule_prover();
            handler
                .run_prover(scheduled, inputs.clone())
                .expect("run_prover failed")
        })
    });

    group.finish();
}

fn bench_ipa_verifier(c: &mut Criterion) {
    let mut group = c.benchmark_group("ipa");
    group.sample_size(10);

    let mut handler: ZippelHandler<ArkSecp256k1> =
        ZippelHandler::new(ZippelArgs::new(PathBuf::from("examples/ipa/ipa.zippel")));
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("S"), &IPA_S);
    handler.compile(&sizes);
    let inputs = ipa_inputs(IPA_S);
    let prover_scheduled = handler.default_schedule_prover();
    let proof = handler
        .run_prover(prover_scheduled, inputs)
        .expect("run_prover failed");

    group.bench_function(format!("verifier/S={}", IPA_S).as_str(), |b| {
        b.iter(|| {
            let scheduled = handler.default_schedule_verifier();
            handler
                .run_verifier(scheduled, proof.clone())
                .expect("run_verifier failed")
        })
    });

    group.finish();
}

// ---------------------------------------------------------------------------
// Hyrax IPA (Log-of-Dot-Product) — ArkBls12_381
// Instance size: 2^S elements.  Default S=10.
// ---------------------------------------------------------------------------

fn hyrax_ipa_inputs(s: usize) -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;
    let n_val_const = 1usize << s;

    let x_vec = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(n_val_const));
    let a_vec = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(n_val_const));
    let y = x_vec.clone().dot(a_vec.clone());

    let r_xi = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let r_tau = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);

    let g_vec = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec(&ATyp::g1(), n_val_const));
    let g_base = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let h_base = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);

    let tau_val = match y.clone() {
        Value::Scalar(y_scalar) => g_base * y_scalar + h_base * r_tau,
        _ => unreachable!(),
    };

    let gx_dot = g_vec.clone().dot(x_vec.clone());
    let xi_val = match gx_dot {
        Value::G1(gx_sum) => h_base * r_xi + gx_sum,
        _ => unreachable!(),
    };

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("xi".to_string()), Value::G1(xi_val)),
        (Vid("tau".to_string()), Value::G1(tau_val)),
        (Vid("a_vec_public".to_string()), a_vec),
        (Vid("g_vec_public".to_string()), g_vec),
        (Vid("g_base".to_string()), Value::G1(g_base)),
        (Vid("h_base".to_string()), Value::G1(h_base)),
        (Vid("x_vec_private".to_string()), x_vec),
        (Vid("y_private".to_string()), y),
        (Vid("r_xi_private".to_string()), Value::Scalar(r_xi)),
        (Vid("r_tau_private".to_string()), Value::Scalar(r_tau)),
    ])
}

const HYRAX_IPA_S: usize = 15;

fn bench_hyrax_ipa_prover(c: &mut Criterion) {
    let mut group = c.benchmark_group("hyrax_ipa");
    group.sample_size(10);

    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(ZippelArgs::new(
        PathBuf::from("examples/hyrax_ipa/hyrax_ipa.zippel"),
    ));
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("S"), &HYRAX_IPA_S);
    handler.compile(&sizes);
    let inputs = hyrax_ipa_inputs(HYRAX_IPA_S);

    group.bench_function(format!("prover/S={}", HYRAX_IPA_S).as_str(), |b| {
        b.iter(|| {
            let scheduled = handler.default_schedule_prover();
            handler
                .run_prover(scheduled, inputs.clone())
                .expect("run_prover failed")
        })
    });

    group.finish();
}

fn bench_hyrax_ipa_verifier(c: &mut Criterion) {
    let mut group = c.benchmark_group("hyrax_ipa");
    group.sample_size(10);

    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(ZippelArgs::new(
        PathBuf::from("examples/hyrax_ipa/hyrax_ipa.zippel"),
    ));
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("S"), &HYRAX_IPA_S);
    handler.compile(&sizes);
    let inputs = hyrax_ipa_inputs(HYRAX_IPA_S);
    let prover_scheduled = handler.default_schedule_prover();
    let proof = handler
        .run_prover(prover_scheduled, inputs)
        .expect("run_prover failed");

    group.bench_function(format!("verifier/S={}", HYRAX_IPA_S).as_str(), |b| {
        b.iter(|| {
            let scheduled = handler.default_schedule_verifier();
            handler
                .run_verifier(scheduled, proof.clone())
                .expect("run_verifier failed")
        })
    });

    group.finish();
}

// ---------------------------------------------------------------------------
// Dory (Evaluation Proof with Bilinear Pairings) — ArkBls12_381
// Instance size: 2^LOG_N elements.  Default LOG_N=10.
// ---------------------------------------------------------------------------

fn dory_inputs(log_n: usize) -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;
    let n = 1usize << log_n;

    let u_vec = <ArkBls12_381 as ArkConfig>::G1Ops::vec_rand(&mut rng, n);
    let g_vec = <ArkBls12_381 as ArkConfig>::G2Ops::vec_rand(&mut rng, n);

    let gamma1 = <ArkBls12_381 as ArkConfig>::G1Ops::vec_rand(&mut rng, n);
    let gamma2 = <ArkBls12_381 as ArkConfig>::G2Ops::vec_rand(&mut rng, n);

    let gamma1_prime = <ArkBls12_381 as ArkConfig>::G1Ops::vec_rand(&mut rng, n / 2);
    let gamma2_prime = <ArkBls12_381 as ArkConfig>::G2Ops::vec_rand(&mut rng, n / 2);

    let c1 = <ArkBls12_381 as ArkConfig>::POps::billinear_vec_dot(&u_vec, &g_vec);
    let c2 = <ArkBls12_381 as ArkConfig>::POps::billinear_vec_dot(&u_vec, &gamma2);
    let c3 = <ArkBls12_381 as ArkConfig>::POps::billinear_vec_dot(&gamma1, &g_vec);

    let mut hash1_l_vec = Vec::new();
    let mut hash1_r_vec = Vec::new();
    let mut hash2_l_vec = Vec::new();
    let mut hash2_r_vec = Vec::new();
    let mut gamma_pair_ipp_vec = Vec::new();

    let mut current_n = n;
    let mut cur_gamma1 = gamma1.clone();
    let mut cur_gamma2 = gamma2.clone();

    while current_n > 1 {
        let half_n = current_n / 2;

        let g1_l = cur_gamma1[0..half_n].to_vec();
        let g1_r = cur_gamma1[half_n..current_n].to_vec();
        let g2_l = cur_gamma2[0..half_n].to_vec();
        let g2_r = cur_gamma2[half_n..current_n].to_vec();

        let cur_g1_prime = gamma1_prime[0..half_n].to_vec();
        let cur_g2_prime = gamma2_prime[0..half_n].to_vec();

        let h1_l = <ArkBls12_381 as ArkConfig>::POps::billinear_vec_dot(&g1_l, &cur_g2_prime);
        let h1_r = <ArkBls12_381 as ArkConfig>::POps::billinear_vec_dot(&g1_r, &cur_g2_prime);
        let h2_l = <ArkBls12_381 as ArkConfig>::POps::billinear_vec_dot(&cur_g1_prime, &g2_l);
        let h2_r = <ArkBls12_381 as ArkConfig>::POps::billinear_vec_dot(&cur_g1_prime, &g2_r);
        let ipp = <ArkBls12_381 as ArkConfig>::POps::billinear_vec_dot(&cur_gamma1, &cur_gamma2);

        hash1_l_vec.push(h1_l);
        hash1_r_vec.push(h1_r);
        hash2_l_vec.push(h2_l);
        hash2_r_vec.push(h2_r);
        gamma_pair_ipp_vec.push(ipp);

        cur_gamma1 = cur_g1_prime;
        cur_gamma2 = cur_g2_prime;
        current_n = half_n;
    }

    let final_gamma1 = cur_gamma1[0];
    let final_gamma2 = cur_gamma2[0];

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("c1".to_string()), Value::GT(c1)),
        (Vid("c2".to_string()), Value::GT(c2)),
        (Vid("c3".to_string()), Value::GT(c3)),
        (Vid("hash1_l_vec".to_string()), Value::VecGT(hash1_l_vec)),
        (Vid("hash1_r_vec".to_string()), Value::VecGT(hash1_r_vec)),
        (Vid("hash2_l_vec".to_string()), Value::VecGT(hash2_l_vec)),
        (Vid("hash2_r_vec".to_string()), Value::VecGT(hash2_r_vec)),
        (
            Vid("gamma_pair_ipp_vec".to_string()),
            Value::VecGT(gamma_pair_ipp_vec),
        ),
        (Vid("final_gamma1".to_string()), Value::G1(final_gamma1)),
        (Vid("final_gamma2".to_string()), Value::G2(final_gamma2)),
        (Vid("gamma1".to_string()), Value::VecG1(gamma1)),
        (Vid("gamma2".to_string()), Value::VecG2(gamma2)),
        (Vid("gamma1_prime".to_string()), Value::VecG1(gamma1_prime)),
        (Vid("gamma2_prime".to_string()), Value::VecG2(gamma2_prime)),
        (Vid("u_vec".to_string()), Value::VecG1(u_vec)),
        (Vid("g_vec".to_string()), Value::VecG2(g_vec)),
    ])
}

const DORY_LOG_N: usize = 10;

fn bench_dory_prover(c: &mut Criterion) {
    let mut group = c.benchmark_group("dory");
    group.sample_size(10);

    let mut handler: ZippelHandler<ArkBls12_381> =
        ZippelHandler::new(ZippelArgs::new(PathBuf::from("examples/dory/dory.zippel")));
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("S"), &DORY_LOG_N);
    handler.compile(&sizes);
    let inputs = dory_inputs(DORY_LOG_N);

    group.bench_function(format!("prover/S={}", DORY_LOG_N).as_str(), |b| {
        b.iter(|| {
            let scheduled = handler.default_schedule_prover();
            handler
                .run_prover(scheduled, inputs.clone())
                .expect("run_prover failed")
        })
    });

    group.finish();
}

fn bench_dory_verifier(c: &mut Criterion) {
    let mut group = c.benchmark_group("dory");
    group.sample_size(10);

    let mut handler: ZippelHandler<ArkBls12_381> =
        ZippelHandler::new(ZippelArgs::new(PathBuf::from("examples/dory/dory.zippel")));
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("S"), &DORY_LOG_N);
    handler.compile(&sizes);
    let inputs = dory_inputs(DORY_LOG_N);
    let prover_scheduled = handler.default_schedule_prover();
    let proof = handler
        .run_prover(prover_scheduled, inputs)
        .expect("run_prover failed");

    group.bench_function(format!("verifier/S={}", DORY_LOG_N).as_str(), |b| {
        b.iter(|| {
            let scheduled = handler.default_schedule_verifier();
            handler
                .run_verifier(scheduled, proof.clone())
                .expect("run_verifier failed")
        })
    });

    group.finish();
}

// ---------------------------------------------------------------------------
// KZG (Kate-Zaverucha-Goldberg) — ArkBls12_381, pairing-based polynomial commit
// ---------------------------------------------------------------------------

fn kzg_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    use ark_std::UniformRand;

    let mut rng = rand::rngs::OsRng;
    let n_size = 2;

    let g_input = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let g: Value<ArkBls12_381> = Value::G1(g_input);

    let h_input = <ArkBls12_381 as ArkConfig>::G2::rand(&mut rng);
    let h: Value<ArkBls12_381> = Value::G2(h_input);

    let p: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(n_size));
    let z: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());
    let tau_input = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let tau: Value<ArkBls12_381> = Value::Scalar(tau_input);

    let ss_g: Value<ArkBls12_381> = Value::VecG1((0..n_size).map(|_| g_input).collect());
    let ss_index = Value::VecScalar((0..n_size).map(|i| tau_input.pow([i as u64])).collect());
    let ss = ss_g.clone() * ss_index.clone();
    let _s = Value::G1(<ArkBls12_381 as ArkConfig>::G1::rand(&mut rng)) * tau.clone();

    let z_val: Value<ArkBls12_381> =
        Value::Vec((0..n_size).map(|i| z.clone() ^ Value::Index(i)).collect());
    let y: Value<ArkBls12_381> = p.clone().dot(z_val.clone());
    let h_val: Value<ArkBls12_381> = Value::G2(h_input * tau_input);

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("p".to_string()), p),
        (Vid("g".to_string()), g),
        (Vid("h".to_string()), h),
        (Vid("z".to_string()), z),
        (Vid("y".to_string()), y),
        (Vid("ss".to_string()), ss),
        (Vid("h_val".to_string()), h_val),
    ])
}

fn bench_kzg_prover(c: &mut Criterion) {
    let mut group = c.benchmark_group("kzg");
    group.sample_size(10);

    let mut handler: ZippelHandler<ArkBls12_381> =
        ZippelHandler::new(ZippelArgs::new(PathBuf::from("examples/kzg/kzg.zippel")));
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("S"), &2usize);
    handler.compile(&sizes);
    let inputs = kzg_inputs();

    group.bench_function("prover", |b| {
        b.iter(|| {
            let scheduled = handler.default_schedule_prover();
            handler
                .run_prover(scheduled, inputs.clone())
                .expect("run_prover failed")
        })
    });

    group.finish();
}

fn bench_kzg_verifier(c: &mut Criterion) {
    let mut group = c.benchmark_group("kzg");
    group.sample_size(10);

    let mut handler: ZippelHandler<ArkBls12_381> =
        ZippelHandler::new(ZippelArgs::new(PathBuf::from("examples/kzg/kzg.zippel")));
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("S"), &2usize);
    handler.compile(&sizes);
    let inputs = kzg_inputs();

    // Extract public inputs (everything except "p") for the verifier.
    let public_inputs = inputs
        .clone()
        .into_iter()
        .filter(|(vid, _)| vid.0 != "p")
        .collect::<Ctx<Vid, Value<ArkBls12_381>>>();

    let prover_scheduled = handler.default_schedule_prover();
    let proof = handler
        .run_prover(prover_scheduled, inputs)
        .expect("run_prover failed");

    group.bench_function("verifier", |b| {
        b.iter(|| {
            let mut verifier_handler: ZippelHandler<ArkBls12_381> =
                ZippelHandler::new(ZippelArgs::new(PathBuf::from("examples/kzg/kzg.zippel")));
            verifier_handler.compile(&sizes);
            verifier_handler.set_public_inputs(public_inputs.clone());
            let scheduled = verifier_handler.default_schedule_verifier();
            verifier_handler
                .run_verifier(scheduled, proof.clone())
                .expect("run_verifier failed")
        })
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_schnorr_prover,
    bench_schnorr_verifier,
    bench_hadamard_prover,
    bench_hadamard_verifier,
    bench_map_comp_prover,
    bench_map_comp_verifier,
    bench_pedersen_eq_prover,
    bench_pedersen_eq_verifier,
    bench_ipa_prover,
    bench_ipa_verifier,
    bench_hyrax_ipa_prover,
    bench_hyrax_ipa_verifier,
    bench_dory_prover,
    bench_dory_verifier,
    bench_kzg_prover,
    bench_kzg_verifier,
);
criterion_main!(benches);
