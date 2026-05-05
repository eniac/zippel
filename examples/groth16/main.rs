use ark_bls12_381::{Bls12_381, Fr, G1Projective, G2Projective};
use ark_ec::AffineRepr;
use ark_ff::{One, UniformRand, Zero};
use ark_groth16::Groth16;
use ark_relations::gr1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, LinearCombination,
    SynthesisMode, R1CS_PREDICATE_LABEL,
};
use backend::{ArkBls12_381, Value};
use lang::id::{Tid, Vid};
use share::Ctx;
use std::{path::PathBuf, time::Instant};
use zippel::*;

type E = Bls12_381;
type F = Fr;

#[derive(Clone)]
struct MultiplyCircuit {
    a: Option<F>,
    b: Option<F>,
}

impl ConstraintSynthesizer<F> for MultiplyCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> ark_relations::gr1cs::Result<()> {
        let a_var = cs.new_witness_variable(|| {
            self.a.ok_or(ark_relations::gr1cs::SynthesisError::AssignmentMissing)
        })?;
        let b_var = cs.new_witness_variable(|| {
            self.b.ok_or(ark_relations::gr1cs::SynthesisError::AssignmentMissing)
        })?;
        let c_var = cs.new_input_variable(|| {
            self.a.and_then(|a| self.b.map(|b| a * b))
                .ok_or(ark_relations::gr1cs::SynthesisError::AssignmentMissing)
        })?;
        cs.enforce_constraint_arity_3(
            R1CS_PREDICATE_LABEL,
            || LinearCombination::from(a_var),
            || LinearCombination::from(b_var),
            || LinearCombination::from(c_var),
        )?;
        Ok(())
    }
}

fn main() {
    println!("=== Groth16 (ArkBls12_381) ===");
    let mut rng = rand::rngs::OsRng;

    let a_val = F::rand(&mut rng);
    let b_val = F::rand(&mut rng);
    let circuit = MultiplyCircuit { a: Some(a_val), b: Some(b_val) };

    let pk = Groth16::<E>::generate_random_parameters_with_reduction(circuit.clone(), &mut rng)
        .unwrap();
    let vk = pk.vk.clone();

    let r = F::rand(&mut rng);
    let s = F::rand(&mut rng);

    let cs = ConstraintSystem::<F>::new_ref();
    cs.set_mode(SynthesisMode::Prove {
        construct_matrices: true,
        generate_lc_assignments: false,
    });
    circuit.clone().generate_constraints(cs.clone()).unwrap();
    cs.finalize();

    let cs_borrowed = cs.borrow().unwrap();
    let matrices_map = cs_borrowed.to_matrices().unwrap();
    let matrices: Vec<_> = matrices_map.get(R1CS_PREDICATE_LABEL).cloned().unwrap_or_default();
    let num_inputs = cs_borrowed.num_instance_variables();
    let num_constraints = cs_borrowed.num_constraints();
    let instance_assignment: Vec<F> = cs_borrowed.instance_assignment().unwrap().to_vec();
    let witness_assignment: Vec<F> = cs_borrowed.witness_assignment().unwrap().to_vec();
    let full_assignment_raw: Vec<F> = [instance_assignment.clone(), witness_assignment.clone()].concat();

    use ark_groth16::r1cs_to_qap::{LibsnarkReduction, R1CSToQAP};
    use ark_poly::GeneralEvaluationDomain;
    type D<F> = GeneralEvaluationDomain<F>;
    let h_coeffs = LibsnarkReduction::witness_map_from_matrices::<F, D<F>>(
        &matrices, num_inputs, num_constraints, &full_assignment_raw,
    ).unwrap();

    let n = pk.a_query.len();
    let m = vk.gamma_abc_g1.len();
    let l = pk.l_query.len();
    let h_size = pk.h_query.len();

    // Convert CRS affine -> projective
    let alpha_g1 = pk.vk.alpha_g1.into_group();
    let beta_g1 = pk.beta_g1.into_group();
    let beta_g2 = pk.vk.beta_g2.into_group();
    let gamma_g2 = pk.vk.gamma_g2.into_group();
    let delta_g1 = pk.delta_g1.into_group();
    let delta_g2 = pk.vk.delta_g2.into_group();

    let a_query_proj: Vec<G1Projective> = pk.a_query.iter().map(|p| p.into_group()).collect();
    let b_g1_query_proj: Vec<G1Projective> = pk.b_g1_query.iter().map(|p| p.into_group()).collect();
    let b_g2_query_proj: Vec<G2Projective> = pk.b_g2_query.iter().map(|p| p.into_group()).collect();
    let h_query_proj: Vec<G1Projective> = pk.h_query.iter().map(|p| p.into_group()).collect();
    let l_query_proj: Vec<G1Projective> = pk.l_query.iter().map(|p| p.into_group()).collect();
    let gamma_abc_g1_proj: Vec<G1Projective> = vk.gamma_abc_g1.iter().map(|p| p.into_group()).collect();

    // Build padded vectors
    let public_inputs_raw = &full_assignment_raw[1..num_inputs];
    let mut public_inputs_padded: Vec<F> = vec![F::one()];
    public_inputs_padded.extend_from_slice(public_inputs_raw);

    let full_assignment_padded = {
        let mut v = full_assignment_raw.clone();
        v.resize(n, F::zero());
        v
    };
    let h_coeffs_padded = {
        let mut v = h_coeffs.clone();
        v.resize(h_size, F::zero());
        v
    };
    let aux_assignment_padded = {
        let mut v = witness_assignment.clone();
        v.resize(l, F::zero());
        v
    };

    let inputs = Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
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
        (Vid("r".to_string()), Value::Scalar(r)),
        (Vid("s".to_string()), Value::Scalar(s)),
        (Vid("full_assignment".to_string()), Value::VecScalar(full_assignment_padded)),
        (Vid("h_coeffs".to_string()), Value::VecScalar(h_coeffs_padded)),
        (Vid("aux_assignment".to_string()), Value::VecScalar(aux_assignment_padded)),
    ]);

    let public_input_names = [
        "alpha_g1", "beta_g2", "gamma_g2", "delta_g2", "gamma_abc_g1",
        "beta_g1", "delta_g1", "a_query", "b_g1_query", "b_g2_query",
        "h_query", "l_query", "public_inputs",
    ];
    let public_inputs_ctx: Ctx<Vid, Value<ArkBls12_381>> = inputs
        .clone()
        .into_iter()
        .filter(|(vid, _)| public_input_names.contains(&vid.0.as_str()))
        .collect();

    // Zippel prover
    let args = ZippelArgs::new(PathBuf::from("examples/groth16/groth16.zippel"));
    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("N"), &n);
    sizes.insert(&Tid::new("M"), &m);
    sizes.insert(&Tid::new("L"), &l);
    sizes.insert(&Tid::new("H"), &h_size);
    handler.compile(&sizes);

    let prover_scheduled = handler.default_schedule_prover();
    let prover_start = Instant::now();
    let proof = handler.run_prover(prover_scheduled, inputs);
    let prover_elapsed = prover_start.elapsed();
    let proof_bytes = proof_size_bytes::<ArkBls12_381>(&proof);
    println!("Zippel prover time:    {prover_elapsed:.2?}");
    println!("Proof size:           {proof_bytes} bytes ({} elements)", proof.len());

    // Zippel verifier
    let verifier_args = ZippelArgs::new(PathBuf::from("examples/groth16/groth16.zippel"));
    let mut verifier_handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(verifier_args);
    verifier_handler.compile(&sizes);
    verifier_handler.set_public_inputs(public_inputs_ctx);
    let verifier_scheduled = verifier_handler.default_schedule_verifier();
    let verifier_start = Instant::now();
    let verifier_result = verifier_handler.run_verifier(verifier_scheduled, proof);
    let verifier_elapsed = verifier_start.elapsed();
    let result = check_verification(verifier_result);
    println!("Zippel verifier time: {verifier_elapsed:.2?}");
    if result.passed {
        println!("Verification:         ✓ PASSED");
    } else {
        println!("Verification:         ✗ FAILED");
        std::process::exit(1);
    }

    // Arkworks reference verification
    let proof_ark = Groth16::<E>::create_random_proof_with_reduction(circuit, &pk, &mut rng).unwrap();
    let pvk = ark_groth16::prepare_verifying_key(&vk);
    let ark_verify = Groth16::<E>::verify_proof(&pvk, &proof_ark, &full_assignment_raw[1..num_inputs]).unwrap();
    println!("\nArkworks reference verification: {}", if ark_verify { "✓ PASSED" } else { "✗ FAILED" });
}