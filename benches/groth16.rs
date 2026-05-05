//! Criterion benchmarks comparing arkworks Groth16 prover/verifier with Zippel's
//! across different circuit sizes (2^10 to 2^15 constraints).
//!
//! Uses a simple R1CS circuit with multiplication constraints.
//!
//! Run with: `cargo bench --bench groth16`

use ark_bls12_381::{Bls12_381, Fr, G1Projective, G2Projective};
use ark_ec::AffineRepr;
use ark_ff::{One, UniformRand, Zero};
use ark_groth16::Groth16;
use ark_poly::GeneralEvaluationDomain;
use ark_relations::gr1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, LinearCombination,
    SynthesisMode, R1CS_PREDICATE_LABEL,
};
use ark_groth16::r1cs_to_qap::{LibsnarkReduction, R1CSToQAP};
use backend::{ArkBls12_381, Value};
use lang::id::{Tid, Vid};
use share::Ctx;
use std::path::PathBuf;
use std::time::Duration;
use zippel::*;
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};

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
            let w = cs.new_witness_variable(|| Ok(F::rand(&mut rand::rngs::OsRng)))?;
            witness_vars.push(w);
        }
        let mut output_vars = Vec::new();
        for _ in 0..num_cons {
            let o = cs.new_input_variable(|| Ok(F::rand(&mut rand::rngs::OsRng)))?;
            output_vars.push(o);
        }
        for i in 0..num_cons {
            let w1 = witness_vars[2 * i];
            let w2 = witness_vars[2 * i + 1];
            let out = output_vars[i];
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
    full_assignment: Vec<F>,
    witness_assignment: Vec<F>,
    h_coeffs: Vec<F>,
    r: F,
    s: F,
    num_inputs: usize,
    n: usize,
    m: usize,
    l: usize,
    h_size: usize,
}

fn setup_bench(num_constraints: usize) -> BenchData {
    let mut rng = rand::rngs::OsRng;
    let circuit = BenchCircuit { num_constraints };
    let pk = Groth16::<E>::generate_random_parameters_with_reduction(circuit.clone(), &mut rng).unwrap();
    let vk = pk.vk.clone();
    let r = F::rand(&mut rng);
    let s = F::rand(&mut rng);

    let cs = ConstraintSystem::<F>::new_ref();
    cs.set_mode(SynthesisMode::Prove { construct_matrices: true, generate_lc_assignments: false });
    circuit.clone().generate_constraints(cs.clone()).unwrap();
    cs.finalize();

    let cs_borrowed = cs.borrow().unwrap();
    let matrices_map = cs_borrowed.to_matrices().unwrap();
    let matrices: Vec<_> = matrices_map.get(R1CS_PREDICATE_LABEL).cloned().unwrap_or_default();
    let num_inputs = cs_borrowed.num_instance_variables();
    let num_cons = cs_borrowed.num_constraints();
    let instance_assignment: Vec<F> = cs_borrowed.instance_assignment().unwrap().to_vec();
    let witness_assignment: Vec<F> = cs_borrowed.witness_assignment().unwrap().to_vec();
    let full_assignment: Vec<F> = [instance_assignment, witness_assignment.clone()].concat();

    type D<FF> = GeneralEvaluationDomain<FF>;
    let h_coeffs = LibsnarkReduction::witness_map_from_matrices::<F, D<F>>(
        &matrices, num_inputs, num_cons, &full_assignment,
    ).unwrap();

    BenchData {
        pk, vk, full_assignment, witness_assignment, h_coeffs, r, s,
        num_inputs, n: 0, m: 0, l: 0, h_size: 0,
    }
}

fn groth16_bench(c: &mut Criterion) {
    let sizes: Vec<usize> = vec![1024, 2048, 4096];

    let mut group = c.benchmark_group("groth16");
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(30));

    for &size in &sizes {
        let mut data = setup_bench(size);
        data.n = data.pk.a_query.len();
        data.m = data.vk.gamma_abc_g1.len();
        data.l = data.pk.l_query.len();
        data.h_size = data.pk.h_query.len();

        // Arkworks prover
        group.bench_with_input(BenchmarkId::new("arkworks_prover", size), &data, |b, data| {
            let circuit = BenchCircuit { num_constraints: size };
            b.iter(|| {
                Groth16::<E>::create_random_proof_with_reduction(
                    circuit.clone(), &data.pk, &mut rand::rngs::OsRng
                ).unwrap()
            });
        });

        // Arkworks verifier
        group.bench_with_input(BenchmarkId::new("arkworks_verifier", size), &data, |b, data| {
            let pvk = ark_groth16::prepare_verifying_key(&data.vk);
            let circuit = BenchCircuit { num_constraints: size };
            let proof = Groth16::<E>::create_random_proof_with_reduction(circuit, &data.pk, &mut rand::rngs::OsRng).unwrap();
            let public_inputs = &data.full_assignment[1..data.num_inputs];
            b.iter(|| {
                Groth16::<E>::verify_proof(&pvk, &proof, public_inputs).unwrap()
            });
        });

        // Zippel prover
        let alpha_g1: G1Projective = data.pk.vk.alpha_g1.into_group();
        let beta_g1: G1Projective = data.pk.beta_g1.into_group();
        let beta_g2: G2Projective = data.pk.vk.beta_g2.into_group();
        let gamma_g2: G2Projective = data.pk.vk.gamma_g2.into_group();
        let delta_g1: G1Projective = data.pk.delta_g1.into_group();
        let delta_g2: G2Projective = data.pk.vk.delta_g2.into_group();

        let a_query_proj: Vec<G1Projective> = data.pk.a_query.iter().map(|p| p.into_group()).collect();
        let b_g1_query_proj: Vec<G1Projective> = data.pk.b_g1_query.iter().map(|p| p.into_group()).collect();
        let b_g2_query_proj: Vec<G2Projective> = data.pk.b_g2_query.iter().map(|p| p.into_group()).collect();
        let h_query_proj: Vec<G1Projective> = data.pk.h_query.iter().map(|p| p.into_group()).collect();
        let l_query_proj: Vec<G1Projective> = data.pk.l_query.iter().map(|p| p.into_group()).collect();
        let gamma_abc_g1_proj: Vec<G1Projective> = data.vk.gamma_abc_g1.iter().map(|p| p.into_group()).collect();

        let public_inputs_raw = &data.full_assignment[1..data.num_inputs];
        let mut public_inputs_padded: Vec<F> = vec![F::one()];
        public_inputs_padded.extend_from_slice(public_inputs_raw);

        let mut full_assignment_padded = data.full_assignment.clone();
        full_assignment_padded.resize(data.n, F::zero());
        let mut h_coeffs_padded = data.h_coeffs.clone();
        h_coeffs_padded.resize(data.h_size, F::zero());
        let mut aux_assignment_padded = data.witness_assignment.clone();
        aux_assignment_padded.resize(data.l, F::zero());

        let zippel_inputs = Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
            (Vid("alpha_g1".to_string()), Value::G1(alpha_g1)),
            (Vid("beta_g2".to_string()), Value::G2(beta_g2)),
            (Vid("gamma_g2".to_string()), Value::G2(gamma_g2)),
            (Vid("delta_g2".to_string()), Value::G2(delta_g2)),
            (Vid("gamma_abc_g1".to_string()), Value::VecG1(gamma_abc_g1_proj)),
            (Vid("beta_g1".to_string()), Value::G1(beta_g1)),
            (Vid("delta_g1".to_string()), Value::G1(delta_g1)),
            (Vid("a_query".to_string()), Value::VecG1(a_query_proj)),
            (Vid("b_g1_query".to_string()), Value::VecG1(b_g1_query_proj)),
            (Vid("b_g2_query".to_string()), Value::VecG2(b_g2_query_proj)),
            (Vid("h_query".to_string()), Value::VecG1(h_query_proj)),
            (Vid("l_query".to_string()), Value::VecG1(l_query_proj)),
            (Vid("public_inputs".to_string()), Value::VecScalar(public_inputs_padded)),
            (Vid("r".to_string()), Value::Scalar(data.r)),
            (Vid("s".to_string()), Value::Scalar(data.s)),
            (Vid("full_assignment".to_string()), Value::VecScalar(full_assignment_padded)),
            (Vid("h_coeffs".to_string()), Value::VecScalar(h_coeffs_padded)),
            (Vid("aux_assignment".to_string()), Value::VecScalar(aux_assignment_padded)),
        ]);

        let n = data.n;
        let m = data.m;
        let l = data.l;
        let h = data.h_size;

        group.bench_with_input(BenchmarkId::new("zippel_prover", size), &(n, m, l, h), |b, dims| {
            let args = ZippelArgs::new(PathBuf::from("examples/groth16/groth16.zippel"));
            let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
            let mut sizes = Ctx::new();
            sizes.insert(&Tid::new("N"), &dims.0);
            sizes.insert(&Tid::new("M"), &dims.1);
            sizes.insert(&Tid::new("L"), &dims.2);
            sizes.insert(&Tid::new("H"), &dims.3);
            handler.compile(&sizes);
            let scheduled = handler.default_schedule_prover();
            b.iter(|| {
                handler.run_prover(scheduled.clone(), zippel_inputs.clone())
            });
        });
    }

    group.finish();
}

criterion_group!(benches, groth16_bench);
criterion_main!(benches);