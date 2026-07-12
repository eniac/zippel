use ark_bls12_381::{Bls12_381, Fr, G1Projective, G2Projective};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{UniformRand, Zero};
use ark_groth16::Groth16;
use ark_groth16::r1cs_to_qap::{LibsnarkReduction, R1CSToQAP};
use ark_poly::GeneralEvaluationDomain;
use ark_relations::gr1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, LinearCombination,
    R1CS_PREDICATE_LABEL, SynthesisMode,
};
use backend::{ArkBls12_381, Value};
use lang::id::{Tid, Vid};
use share::Ctx;
use std::{path::PathBuf, time::Instant};
use zippel::*;

type E = Bls12_381;
type F = Fr;

const CONSTRAINT_SIZE: usize = 1 << 5;

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

struct Groth16Params {
    alpha_g1: G1Projective,
    beta_g1: G1Projective,
    beta_g2: G2Projective,
    gamma_g2: G2Projective,
    delta_g1: G1Projective,
    delta_g2: G2Projective,
    a_query: Vec<G1Projective>,
    b_g1_query: Vec<G1Projective>,
    b_g2_query: Vec<G2Projective>,
    h_query: Vec<G1Projective>,
    l_query: Vec<G1Projective>,
    gamma_abc_g1: Vec<G1Projective>,
}

impl Groth16Params {
    fn from_keys(pk: &ark_groth16::ProvingKey<E>, vk: &ark_groth16::VerifyingKey<E>) -> Self {
        Self {
            alpha_g1: pk.vk.alpha_g1.into_group(),
            beta_g1: pk.beta_g1.into_group(),
            beta_g2: vk.beta_g2.into_group(),
            gamma_g2: vk.gamma_g2.into_group(),
            delta_g1: pk.delta_g1.into_group(),
            delta_g2: pk.vk.delta_g2.into_group(),
            a_query: pk.a_query.iter().map(|p| p.into_group()).collect(),
            b_g1_query: pk.b_g1_query.iter().map(|p| p.into_group()).collect(),
            b_g2_query: pk.b_g2_query.iter().map(|p| p.into_group()).collect(),
            h_query: pk.h_query.iter().map(|p| p.into_group()).collect(),
            l_query: pk.l_query.iter().map(|p| p.into_group()).collect(),
            gamma_abc_g1: vk.gamma_abc_g1.iter().map(|p| p.into_group()).collect(),
        }
    }

    fn common_inputs(
        &self,
        instance_assignment: &[F],
        witness_assignment: &[F],
    ) -> Vec<(Vid, Value<ArkBls12_381>)> {
        vec![
            (Vid("alpha_g1".to_string()), Value::G1(self.alpha_g1)),
            (Vid("beta_g2".to_string()), Value::G2(self.beta_g2)),
            (Vid("gamma_g2".to_string()), Value::G2(self.gamma_g2)),
            (Vid("delta_g2".to_string()), Value::G2(self.delta_g2)),
            (
                Vid("gamma_abc_g1".to_string()),
                Value::VecG1(self.gamma_abc_g1.clone()),
            ),
            (Vid("beta_g1".to_string()), Value::G1(self.beta_g1)),
            (Vid("delta_g1".to_string()), Value::G1(self.delta_g1)),
            (
                Vid("a_query".to_string()),
                Value::VecG1(self.a_query.clone()),
            ),
            (
                Vid("b_g1_query".to_string()),
                Value::VecG1(self.b_g1_query.clone()),
            ),
            (
                Vid("b_g2_query".to_string()),
                Value::VecG2(self.b_g2_query.clone()),
            ),
            (
                Vid("h_query".to_string()),
                Value::VecG1(self.h_query.clone()),
            ),
            (
                Vid("l_query".to_string()),
                Value::VecG1(self.l_query.clone()),
            ),
            (
                Vid("instance_assignment".to_string()),
                Value::VecScalar(instance_assignment.to_vec()),
            ),
            (
                Vid("witness_assignment".to_string()),
                Value::VecScalar(witness_assignment.to_vec()),
            ),
        ]
    }
}

fn zippel_proof_to_ark(proof: &[Value<ArkBls12_381>]) -> ark_groth16::Proof<E> {
    ark_groth16::Proof {
        a: match &proof[0] {
            Value::G1(p) => p.into_affine(),
            _ => panic!("expected G1 for a_proof"),
        },
        b: match &proof[1] {
            Value::G2(p) => p.into_affine(),
            _ => panic!("expected G2 for b_proof"),
        },
        c: match &proof[2] {
            Value::G1(p) => p.into_affine(),
            _ => panic!("expected G1 for c_proof"),
        },
    }
}

fn run_and_verify(
    zippel_path: &str,
    sizes: &Ctx<Tid, usize>,
    inputs: &Ctx<Vid, Value<ArkBls12_381>>,
    public_input_names: &[&str],
    vk: &ark_groth16::VerifyingKey<E>,
    instance_assignment: &[F],
) {
    let public_inputs_ctx: Ctx<Vid, Value<ArkBls12_381>> = inputs
        .clone()
        .into_iter()
        .filter(|(vid, _)| public_input_names.contains(&vid.0.as_str()))
        .collect();

    let args = ZippelArgs::new(PathBuf::from(zippel_path));
    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    handler.compile(sizes);
    let prover_start = Instant::now();
    let proof = handler.run_prover(inputs).unwrap();
    let prover_elapsed = prover_start.elapsed();
    let proof_bytes = proof_size_bytes::<ArkBls12_381>(&proof);
    println!("Zippel prover time:    {prover_elapsed:.2?}");
    println!(
        "Proof size:           {proof_bytes} bytes ({} elements)",
        proof.len()
    );

    let verifier_args = ZippelArgs::new(PathBuf::from(zippel_path));
    let mut verifier_handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(verifier_args);
    verifier_handler.compile(sizes);
    verifier_handler.set_public_inputs(public_inputs_ctx);
    let verifier_start = Instant::now();
    let verifier_result = verifier_handler.run_verifier(&proof).unwrap();
    let verifier_elapsed = verifier_start.elapsed();
    let passed = check_verification(&verifier_result);
    println!("Zippel verifier time: {verifier_elapsed:.2?}");
    if passed {
        println!("Verification:         ✓ PASSED");
    } else {
        println!("Verification:         ✗ FAILED");
        std::process::exit(1);
    }

    let pvk = ark_groth16::prepare_verifying_key(vk);
    let proof_ark = zippel_proof_to_ark(&proof);
    let ark_verify =
        Groth16::<E>::verify_proof(&pvk, &proof_ark, &instance_assignment[1..]).unwrap();
    println!(
        "\nArkworks cross-verification (zippel proof → arkworks verifier): {}",
        if ark_verify {
            "✓ PASSED"
        } else {
            "✗ FAILED"
        }
    );
}

fn run_groth16(
    pk: &ark_groth16::ProvingKey<E>,
    vk: &ark_groth16::VerifyingKey<E>,
    h_coeffs: &[F],
    instance_assignment: &[F],
    witness_assignment: &[F],
) {
    let params = Groth16Params::from_keys(pk, vk);
    let m = vk.gamma_abc_g1.len();
    let l = pk.l_query.len();
    let h_size = pk.h_query.len();

    let h_coeffs_padded = {
        let mut v = h_coeffs.to_vec();
        v.resize(h_size, F::zero());
        v
    };

    let mut entries = params.common_inputs(instance_assignment, witness_assignment);
    entries.push((
        Vid("h_coeffs".to_string()),
        Value::VecScalar(h_coeffs_padded),
    ));

    // Relation-only trapdoor witnesses (a_evs, b_evs, c_evs, tau, t_at_tau).
    // The proto body and verifier never reference these; they exist so the
    // `where` clause can express the QAP identity at the trusted-setup
    // trapdoor τ. Zeros are fine at runtime — the static analyzer is where
    // they matter, and it consumes them via the where clause without needing
    // cryptographically-meaningful values.
    let n_total = m + l;
    let a_evs = vec![F::zero(); n_total];
    let b_evs = vec![F::zero(); n_total];
    let c_evs = vec![F::zero(); n_total];
    entries.push((Vid("a_evs".to_string()), Value::VecScalar(a_evs)));
    entries.push((Vid("b_evs".to_string()), Value::VecScalar(b_evs)));
    entries.push((Vid("c_evs".to_string()), Value::VecScalar(c_evs)));
    entries.push((Vid("tau".to_string()), Value::Scalar(F::zero())));
    entries.push((Vid("t_at_tau".to_string()), Value::Scalar(F::zero())));

    let inputs: Ctx<Vid, Value<ArkBls12_381>> = Ctx::from_iter(entries);

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

    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("M"), &m);
    sizes.insert(&Tid::new("L"), &l);
    sizes.insert(&Tid::new("H"), &h_size);

    run_and_verify(
        "examples/groth16/groth16.zippel",
        &sizes,
        &inputs,
        &public_input_names,
        vk,
        instance_assignment,
    );
}

fn main() {
    type D<FF> = GeneralEvaluationDomain<FF>;
    println!("=== Groth16 (ArkBls12_381) — constraints: {CONSTRAINT_SIZE} ===");

    let circuit = BenchCircuit {
        num_constraints: CONSTRAINT_SIZE,
    };
    let mut rng = rand::rngs::OsRng;

    let pk =
        Groth16::<E>::generate_random_parameters_with_reduction(circuit.clone(), &mut rng).unwrap();
    let vk = pk.vk.clone();

    let cs = ConstraintSystem::<F>::new_ref();
    cs.set_mode(SynthesisMode::Prove {
        construct_matrices: true,
        generate_lc_assignments: false,
    });
    circuit.generate_constraints(cs.clone()).unwrap();
    cs.finalize();

    let cs_borrowed = cs.borrow().unwrap();
    let num_constraints = cs_borrowed.num_constraints();
    let num_inputs = cs_borrowed.num_instance_variables();
    let matrices_map = cs_borrowed.to_matrices().unwrap();
    let matrices: Vec<_> = matrices_map
        .get(R1CS_PREDICATE_LABEL)
        .cloned()
        .unwrap_or_default();
    let instance_assignment: Vec<F> = cs_borrowed.instance_assignment().unwrap().to_vec();
    let witness_assignment: Vec<F> = cs_borrowed.witness_assignment().unwrap().to_vec();

    println!("num_constraints={num_constraints} num_inputs={num_inputs}");
    println!(
        "N={} M={} L={} H={}",
        pk.a_query.len(),
        vk.gamma_abc_g1.len(),
        pk.l_query.len(),
        pk.h_query.len()
    );

    let full_assignment: Vec<F> =
        [instance_assignment.clone(), witness_assignment.clone()].concat();
    let h_coeffs = LibsnarkReduction::witness_map_from_matrices::<F, D<F>>(
        &matrices,
        num_inputs,
        num_constraints,
        &full_assignment,
    )
    .unwrap();

    run_groth16(
        &pk,
        &vk,
        &h_coeffs,
        &instance_assignment,
        &witness_assignment,
    );
}
