//! Criterion benchmarks comparing arkworks Groth16 prover/verifier with Zippel's
//! across different circuit sizes (2^10 to 2^13 constraints).
//!
//! Supports both noh (matvec + FFT inside zippel) and opt (h_coeffs external) modes.
//!
//! Run with: `cargo bench --bench groth16`

use ark_bls12_381::{Bls12_381, Fr, G1Projective, G2Projective};
use ark_ec::AffineRepr;
use ark_ff::{FftField, One, UniformRand, Zero};
use ark_groth16::Groth16;
use ark_groth16::r1cs_to_qap::{LibsnarkReduction, R1CSToQAP};
use ark_poly::EvaluationDomain;
use ark_poly::GeneralEvaluationDomain;
use ark_relations::gr1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, LinearCombination,
    R1CS_PREDICATE_LABEL, SynthesisMode,
};
use backend::{ArkBls12_381, Value};
use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use lang::id::{Tid, Vid};
use share::Ctx;
use std::path::PathBuf;
use std::time::Duration;
use zippel::*;

type E = Bls12_381;
type F = Fr;

#[derive(Clone)]
struct BenchCircuit {
    num_constraints: usize,
}

impl ConstraintSynthesizer<F> for BenchCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> ark_relations::gr1cs::Result<()> {
        let num_cons = self.num_constraints;
        let mut witness_vars = Vec::new();
        for _ in 0..(2 * num_cons) {
            let val = F::rand(&mut rand::rngs::OsRng);
            let w = cs.new_witness_variable(|| Ok(val))?;
            witness_vars.push((w, val));
        }
        for i in 0..num_cons {
            let (w1, v1) = witness_vars[2 * i];
            let (w2, v2) = witness_vars[2 * i + 1];
            let out_val = v1 * v2;
            let out = cs.new_input_variable(|| Ok(out_val))?;
            cs.enforce_constraint_arity_3(
                R1CS_PREDICATE_LABEL,
                || LinearCombination::from(w1),
                || LinearCombination::from(w2),
                || LinearCombination::from(out),
            )?;
        }
        Ok(())
    }
}

struct BenchData {
    pk: ark_groth16::ProvingKey<E>,
    vk: ark_groth16::VerifyingKey<E>,
    instance_assignment: Vec<F>,
    witness_assignment: Vec<F>,
    h_coeffs: Vec<F>,
    matrices: Vec<ark_relations::gr1cs::Matrix<F>>,
    num_inputs: usize,
    num_constraints: usize,
    n: usize,
    m: usize,
    l: usize,
    h_size: usize,
    domain_size: usize,
}

fn build_dense_matrix_a(
    sparse: &ark_relations::gr1cs::Matrix<F>,
    num_constraints: usize,
    num_inputs: usize,
    domain_size: usize,
    n: usize,
) -> Vec<F> {
    let mut dense = vec![F::zero(); domain_size * n];
    for (i, row) in sparse.iter().enumerate() {
        for (coeff, col) in row {
            dense[i * n + col] = *coeff;
        }
    }
    for i in 0..num_inputs {
        let row = num_constraints + i;
        dense[row * n + i] = F::one();
    }
    dense
}

fn build_dense_matrix_bc(
    sparse: &ark_relations::gr1cs::Matrix<F>,
    domain_size: usize,
    n: usize,
) -> Vec<F> {
    let mut dense = vec![F::zero(); domain_size * n];
    for (i, row) in sparse.iter().enumerate() {
        for (coeff, col) in row {
            dense[i * n + col] = *coeff;
        }
    }
    dense
}

fn setup_bench(num_constraints: usize) -> BenchData {
    let mut rng = rand::rngs::OsRng;
    let circuit = BenchCircuit { num_constraints };
    let pk =
        Groth16::<E>::generate_random_parameters_with_reduction(circuit.clone(), &mut rng).unwrap();
    let vk = pk.vk.clone();

    let cs = ConstraintSystem::<F>::new_ref();
    cs.set_mode(SynthesisMode::Prove {
        construct_matrices: true,
        generate_lc_assignments: false,
    });
    circuit.clone().generate_constraints(cs.clone()).unwrap();
    cs.finalize();

    let cs_borrowed = cs.borrow().unwrap();
    let matrices_map = cs_borrowed.to_matrices().unwrap();
    let matrices: Vec<_> = matrices_map
        .get(R1CS_PREDICATE_LABEL)
        .cloned()
        .unwrap_or_default();
    let num_inputs = cs_borrowed.num_instance_variables();
    let num_cons = cs_borrowed.num_constraints();
    let instance_assignment: Vec<F> = cs_borrowed.instance_assignment().unwrap().to_vec();
    let witness_assignment: Vec<F> = cs_borrowed.witness_assignment().unwrap().to_vec();
    let full_assignment: Vec<F> =
        [instance_assignment.clone(), witness_assignment.clone()].concat();

    type D<FF> = GeneralEvaluationDomain<FF>;
    let h_coeffs = LibsnarkReduction::witness_map_from_matrices::<F, D<F>>(
        &matrices,
        num_inputs,
        num_cons,
        &full_assignment,
    )
    .unwrap();

    let domain = D::<F>::new(num_cons + num_inputs).unwrap();
    let domain_size = domain.size();

    let n = pk.a_query.len();
    let m = vk.gamma_abc_g1.len();
    let l = pk.l_query.len();
    let h_size = pk.h_query.len();

    BenchData {
        pk,
        vk,
        instance_assignment,
        witness_assignment,
        h_coeffs,
        matrices,
        num_inputs,
        num_constraints: num_cons,
        n,
        m,
        l,
        h_size,
        domain_size,
    }
}

fn groth16_bench(c: &mut Criterion) {
    let sizes: Vec<usize> = vec![1024, 2048, 4096];

    let mut group = c.benchmark_group("groth16");
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(30));

    for &size in &sizes {
        let data = setup_bench(size);

        // Arkworks prover
        group.bench_with_input(
            BenchmarkId::new("arkworks_prover", size),
            &data,
            |b, data| {
                let circuit = BenchCircuit {
                    num_constraints: size,
                };
                b.iter(|| {
                    Groth16::<E>::create_random_proof_with_reduction(
                        circuit.clone(),
                        &data.pk,
                        &mut rand::rngs::OsRng,
                    )
                    .unwrap()
                });
            },
        );

        // Arkworks verifier
        group.bench_with_input(
            BenchmarkId::new("arkworks_verifier", size),
            &data,
            |b, data| {
                let pvk = ark_groth16::prepare_verifying_key(&data.vk);
                let circuit = BenchCircuit {
                    num_constraints: size,
                };
                let proof = Groth16::<E>::create_random_proof_with_reduction(
                    circuit,
                    &data.pk,
                    &mut rand::rngs::OsRng,
                )
                .unwrap();
                let public_inputs = &data.instance_assignment[1..data.num_inputs];
                b.iter(|| Groth16::<E>::verify_proof(&pvk, &proof, public_inputs).unwrap());
            },
        );

        // --- Zippel opt mode prover ---
        {
            let alpha_g1: G1Projective = data.pk.vk.alpha_g1.into_group();
            let beta_g1: G1Projective = data.pk.beta_g1.into_group();
            let beta_g2: G2Projective = data.pk.vk.beta_g2.into_group();
            let gamma_g2: G2Projective = data.pk.vk.gamma_g2.into_group();
            let delta_g1: G1Projective = data.pk.delta_g1.into_group();
            let delta_g2: G2Projective = data.pk.vk.delta_g2.into_group();

            let a_query_proj: Vec<G1Projective> =
                data.pk.a_query.iter().map(|p| p.into_group()).collect();
            let b_g1_query_proj: Vec<G1Projective> =
                data.pk.b_g1_query.iter().map(|p| p.into_group()).collect();
            let b_g2_query_proj: Vec<G2Projective> =
                data.pk.b_g2_query.iter().map(|p| p.into_group()).collect();
            let h_query_proj: Vec<G1Projective> =
                data.pk.h_query.iter().map(|p| p.into_group()).collect();
            let l_query_proj: Vec<G1Projective> =
                data.pk.l_query.iter().map(|p| p.into_group()).collect();
            let gamma_abc_g1_proj: Vec<G1Projective> = data
                .vk
                .gamma_abc_g1
                .iter()
                .map(|p| p.into_group())
                .collect();

            let mut h_coeffs_padded = data.h_coeffs.clone();
            h_coeffs_padded.resize(data.h_size, F::zero());

            let zippel_inputs = Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
                (Vid("alpha_g1".to_string()), Value::G1(alpha_g1)),
                (Vid("beta_g2".to_string()), Value::G2(beta_g2)),
                (Vid("gamma_g2".to_string()), Value::G2(gamma_g2)),
                (Vid("delta_g2".to_string()), Value::G2(delta_g2)),
                (
                    Vid("gamma_abc_g1".to_string()),
                    Value::VecG1(gamma_abc_g1_proj),
                ),
                (Vid("beta_g1".to_string()), Value::G1(beta_g1)),
                (Vid("delta_g1".to_string()), Value::G1(delta_g1)),
                (Vid("a_query".to_string()), Value::VecG1(a_query_proj)),
                (Vid("b_g1_query".to_string()), Value::VecG1(b_g1_query_proj)),
                (Vid("b_g2_query".to_string()), Value::VecG2(b_g2_query_proj)),
                (Vid("h_query".to_string()), Value::VecG1(h_query_proj)),
                (Vid("l_query".to_string()), Value::VecG1(l_query_proj)),
                (
                    Vid("instance_assignment".to_string()),
                    Value::VecScalar(data.instance_assignment.clone()),
                ),
                (
                    Vid("witness_assignment".to_string()),
                    Value::VecScalar(data.witness_assignment.clone()),
                ),
                (
                    Vid("h_coeffs".to_string()),
                    Value::VecScalar(h_coeffs_padded),
                ),
            ]);

            let m = data.m;
            let l = data.l;
            let h = data.h_size;

            // Zippel opt prover
            group.bench_with_input(
                BenchmarkId::new("zippel_opt_prover", size),
                &(m, l, h),
                |b, dims| {
                    let args =
                        ZippelArgs::new(PathBuf::from("examples/groth16/groth16-opt.zippel"));
                    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
                    let mut sizes = Ctx::new();
                    sizes.insert(&Tid::new("M"), &dims.0);
                    sizes.insert(&Tid::new("L"), &dims.1);
                    sizes.insert(&Tid::new("H"), &dims.2);
                    handler.compile(&sizes);
                    let scheduled = handler.default_schedule_prover();
                    b.iter(|| {
                        handler
                            .run_prover(scheduled.clone(), zippel_inputs.clone())
                            .unwrap()
                    });
                },
            );

            // Zippel opt verifier
            {
                let args = ZippelArgs::new(PathBuf::from("examples/groth16/groth16-opt.zippel"));
                let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
                let mut sizes = Ctx::new();
                sizes.insert(&Tid::new("M"), &m);
                sizes.insert(&Tid::new("L"), &l);
                sizes.insert(&Tid::new("H"), &h);
                handler.compile(&sizes);

                let public_input_names = [
                    "alpha_g1",
                    "beta_g2",
                    "gamma_g2",
                    "delta_g2",
                    "gamma_abc_g1",
                    "beta_g1",
                    "delta_g1",
                    "a_query",
                    "b_g1_query",
                    "b_g2_query",
                    "h_query",
                    "l_query",
                    "instance_assignment",
                ];
                let public_inputs_ctx: Ctx<Vid, Value<ArkBls12_381>> = zippel_inputs
                    .clone()
                    .into_iter()
                    .filter(|(vid, _)| public_input_names.contains(&vid.0.as_str()))
                    .collect();
                handler.set_public_inputs(public_inputs_ctx);
                let scheduled_prover = handler.default_schedule_prover();
                let proof = handler
                    .run_prover(scheduled_prover, zippel_inputs.clone())
                    .unwrap();
                let scheduled_verifier = handler.default_schedule_verifier();

                group.bench_with_input(
                    BenchmarkId::new("zippel_opt_verifier", size),
                    &(),
                    |b, _| {
                        b.iter(|| {
                            handler
                                .run_verifier(scheduled_verifier.clone(), proof.clone())
                                .unwrap()
                        });
                    },
                );
            }
        }

        // --- Zippel noh mode prover ---
        {
            let alpha_g1: G1Projective = data.pk.vk.alpha_g1.into_group();
            let beta_g1: G1Projective = data.pk.beta_g1.into_group();
            let beta_g2: G2Projective = data.pk.vk.beta_g2.into_group();
            let gamma_g2: G2Projective = data.pk.vk.gamma_g2.into_group();
            let delta_g1: G1Projective = data.pk.delta_g1.into_group();
            let delta_g2: G2Projective = data.pk.vk.delta_g2.into_group();

            let a_query_proj: Vec<G1Projective> =
                data.pk.a_query.iter().map(|p| p.into_group()).collect();
            let b_g1_query_proj: Vec<G1Projective> =
                data.pk.b_g1_query.iter().map(|p| p.into_group()).collect();
            let b_g2_query_proj: Vec<G2Projective> =
                data.pk.b_g2_query.iter().map(|p| p.into_group()).collect();
            let h_query_proj: Vec<G1Projective> =
                data.pk.h_query.iter().map(|p| p.into_group()).collect();
            let l_query_proj: Vec<G1Projective> =
                data.pk.l_query.iter().map(|p| p.into_group()).collect();
            let gamma_abc_g1_proj: Vec<G1Projective> = data
                .vk
                .gamma_abc_g1
                .iter()
                .map(|p| p.into_group())
                .collect();

            let mat_a_flat = build_dense_matrix_a(
                &data.matrices[0],
                data.num_constraints,
                data.num_inputs,
                data.domain_size,
                data.n,
            );
            let mat_b_flat = build_dense_matrix_bc(&data.matrices[1], data.domain_size, data.n);
            let mat_c_flat = build_dense_matrix_bc(&data.matrices[2], data.domain_size, data.n);
            let coset_offset = F::GENERATOR;

            let noh_inputs = Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
                (Vid("alpha_g1".to_string()), Value::G1(alpha_g1)),
                (Vid("beta_g2".to_string()), Value::G2(beta_g2)),
                (Vid("gamma_g2".to_string()), Value::G2(gamma_g2)),
                (Vid("delta_g2".to_string()), Value::G2(delta_g2)),
                (
                    Vid("gamma_abc_g1".to_string()),
                    Value::VecG1(gamma_abc_g1_proj),
                ),
                (Vid("beta_g1".to_string()), Value::G1(beta_g1)),
                (Vid("delta_g1".to_string()), Value::G1(delta_g1)),
                (Vid("a_query".to_string()), Value::VecG1(a_query_proj)),
                (Vid("b_g1_query".to_string()), Value::VecG1(b_g1_query_proj)),
                (Vid("b_g2_query".to_string()), Value::VecG2(b_g2_query_proj)),
                (Vid("h_query".to_string()), Value::VecG1(h_query_proj)),
                (Vid("l_query".to_string()), Value::VecG1(l_query_proj)),
                (
                    Vid("instance_assignment".to_string()),
                    Value::VecScalar(data.instance_assignment.clone()),
                ),
                (
                    Vid("witness_assignment".to_string()),
                    Value::VecScalar(data.witness_assignment.clone()),
                ),
                (Vid("mat_a".to_string()), Value::VecScalar(mat_a_flat)),
                (Vid("mat_b".to_string()), Value::VecScalar(mat_b_flat)),
                (Vid("mat_c".to_string()), Value::VecScalar(mat_c_flat)),
                (Vid("omega".to_string()), Value::Scalar(coset_offset)),
            ]);

            let m = data.m;
            let l = data.l;
            let c = data.num_constraints;
            let d = data.domain_size;

            // Zippel noh prover
            group.bench_with_input(
                BenchmarkId::new("zippel_noh_prover", size),
                &(m, l, c, d),
                |b, dims| {
                    let args = ZippelArgs::new(PathBuf::from("examples/groth16/groth16.zippel"));
                    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
                    let mut sizes = Ctx::new();
                    sizes.insert(&Tid::new("M"), &dims.0);
                    sizes.insert(&Tid::new("L"), &dims.1);
                    sizes.insert(&Tid::new("C"), &dims.2);
                    sizes.insert(&Tid::new("D"), &dims.3);
                    handler.compile(&sizes);
                    let scheduled = handler.default_schedule_prover();
                    b.iter(|| {
                        handler
                            .run_prover(scheduled.clone(), noh_inputs.clone())
                            .unwrap()
                    });
                },
            );

            // Zippel noh verifier
            {
                let args = ZippelArgs::new(PathBuf::from("examples/groth16/groth16.zippel"));
                let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
                let mut sizes = Ctx::new();
                sizes.insert(&Tid::new("M"), &m);
                sizes.insert(&Tid::new("L"), &l);
                sizes.insert(&Tid::new("C"), &c);
                sizes.insert(&Tid::new("D"), &d);
                handler.compile(&sizes);

                let public_input_names = [
                    "alpha_g1",
                    "beta_g2",
                    "gamma_g2",
                    "delta_g2",
                    "gamma_abc_g1",
                    "beta_g1",
                    "delta_g1",
                    "a_query",
                    "b_g1_query",
                    "b_g2_query",
                    "h_query",
                    "l_query",
                    "instance_assignment",
                    "mat_a",
                    "mat_b",
                    "mat_c",
                    "omega",
                ];
                let public_inputs_ctx: Ctx<Vid, Value<ArkBls12_381>> = noh_inputs
                    .clone()
                    .into_iter()
                    .filter(|(vid, _)| public_input_names.contains(&vid.0.as_str()))
                    .collect();
                handler.set_public_inputs(public_inputs_ctx);
                let scheduled_prover = handler.default_schedule_prover();
                let proof = handler
                    .run_prover(scheduled_prover, noh_inputs.clone())
                    .unwrap();
                let scheduled_verifier = handler.default_schedule_verifier();

                group.bench_with_input(
                    BenchmarkId::new("zippel_noh_verifier", size),
                    &(),
                    |b, _| {
                        b.iter(|| {
                            handler
                                .run_verifier(scheduled_verifier.clone(), proof.clone())
                                .unwrap()
                        });
                    },
                );
            }
        }
    }

    group.finish();
}

criterion_group!(benches, groth16_bench);
criterion_main!(benches);
