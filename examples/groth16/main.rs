use ark_bls12_381::{Bls12_381, Fr, G1Projective, G2Projective};
use ark_ec::AffineRepr;
use ark_ff::{FftField, One, UniformRand, Zero};
use ark_groth16::Groth16;
use ark_poly::EvaluationDomain;
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

#[derive(Clone)]
struct MultiplyCircuit {
    a: Option<F>,
    b: Option<F>,
}

impl ConstraintSynthesizer<F> for MultiplyCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> ark_relations::gr1cs::Result<()> {
        let a_var = cs.new_witness_variable(|| {
            self.a
                .ok_or(ark_relations::gr1cs::SynthesisError::AssignmentMissing)
        })?;
        let b_var = cs.new_witness_variable(|| {
            self.b
                .ok_or(ark_relations::gr1cs::SynthesisError::AssignmentMissing)
        })?;
        let c_var = cs.new_input_variable(|| {
            self.a
                .and_then(|a| self.b.map(|b| a * b))
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

#[derive(Clone)]
struct DoubleMulCircuit {
    a: Option<F>,
    b: Option<F>,
    d: Option<F>,
}

impl ConstraintSynthesizer<F> for DoubleMulCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> ark_relations::gr1cs::Result<()> {
        let a_var = cs.new_witness_variable(|| {
            self.a
                .ok_or(ark_relations::gr1cs::SynthesisError::AssignmentMissing)
        })?;
        let b_var = cs.new_witness_variable(|| {
            self.b
                .ok_or(ark_relations::gr1cs::SynthesisError::AssignmentMissing)
        })?;
        let d_var = cs.new_witness_variable(|| {
            self.d
                .ok_or(ark_relations::gr1cs::SynthesisError::AssignmentMissing)
        })?;
        let c1_var = cs.new_input_variable(|| {
            self.a
                .and_then(|a| self.b.map(|b| a * b))
                .ok_or(ark_relations::gr1cs::SynthesisError::AssignmentMissing)
        })?;
        let c2_var = cs.new_input_variable(|| {
            self.a
                .and_then(|a| self.d.map(|d| a * d))
                .ok_or(ark_relations::gr1cs::SynthesisError::AssignmentMissing)
        })?;
        cs.enforce_constraint_arity_3(
            R1CS_PREDICATE_LABEL,
            || LinearCombination::from(a_var),
            || LinearCombination::from(b_var),
            || LinearCombination::from(c1_var),
        )?;
        cs.enforce_constraint_arity_3(
            R1CS_PREDICATE_LABEL,
            || LinearCombination::from(a_var),
            || LinearCombination::from(d_var),
            || LinearCombination::from(c2_var),
        )?;
        Ok(())
    }
}

#[derive(Clone)]
struct TripleMulCircuit {
    a: Option<F>,
    b: Option<F>,
    d: Option<F>,
    e: Option<F>,
}

impl ConstraintSynthesizer<F> for TripleMulCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> ark_relations::gr1cs::Result<()> {
        let a_var = cs.new_witness_variable(|| {
            self.a
                .ok_or(ark_relations::gr1cs::SynthesisError::AssignmentMissing)
        })?;
        let b_var = cs.new_witness_variable(|| {
            self.b
                .ok_or(ark_relations::gr1cs::SynthesisError::AssignmentMissing)
        })?;
        let d_var = cs.new_witness_variable(|| {
            self.d
                .ok_or(ark_relations::gr1cs::SynthesisError::AssignmentMissing)
        })?;
        let e_var = cs.new_witness_variable(|| {
            self.e
                .ok_or(ark_relations::gr1cs::SynthesisError::AssignmentMissing)
        })?;
        let c1_var = cs.new_input_variable(|| {
            self.a
                .and_then(|a| self.b.map(|b| a * b))
                .ok_or(ark_relations::gr1cs::SynthesisError::AssignmentMissing)
        })?;
        let c2_var = cs.new_input_variable(|| {
            self.a
                .and_then(|a| self.d.map(|d| a * d))
                .ok_or(ark_relations::gr1cs::SynthesisError::AssignmentMissing)
        })?;
        let c3_var = cs.new_input_variable(|| {
            self.b
                .and_then(|b| self.e.map(|e| b * e))
                .ok_or(ark_relations::gr1cs::SynthesisError::AssignmentMissing)
        })?;
        cs.enforce_constraint_arity_3(
            R1CS_PREDICATE_LABEL,
            || LinearCombination::from(a_var),
            || LinearCombination::from(b_var),
            || LinearCombination::from(c1_var),
        )?;
        cs.enforce_constraint_arity_3(
            R1CS_PREDICATE_LABEL,
            || LinearCombination::from(a_var),
            || LinearCombination::from(d_var),
            || LinearCombination::from(c2_var),
        )?;
        cs.enforce_constraint_arity_3(
            R1CS_PREDICATE_LABEL,
            || LinearCombination::from(b_var),
            || LinearCombination::from(e_var),
            || LinearCombination::from(c3_var),
        )?;
        Ok(())
    }
}

#[derive(Clone)]
struct ComplexCircuit {
    a: Option<F>,
    b: Option<F>,
    c: Option<F>,
    d: Option<F>,
    e: Option<F>,
    f: Option<F>,
    g: Option<F>,
    h: Option<F>,
    p: Option<F>,
    q: Option<F>,
}

impl ConstraintSynthesizer<F> for ComplexCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> ark_relations::gr1cs::Result<()> {
        let alloc = |opt: Option<F>| {
            opt.ok_or(ark_relations::gr1cs::SynthesisError::AssignmentMissing)
        };
        let a = cs.new_witness_variable(|| alloc(self.a))?;
        let b = cs.new_witness_variable(|| alloc(self.b))?;
        let c = cs.new_witness_variable(|| alloc(self.c))?;
        let d = cs.new_witness_variable(|| alloc(self.d))?;
        let e = cs.new_witness_variable(|| alloc(self.e))?;
        let f = cs.new_witness_variable(|| alloc(self.f))?;
        let g = cs.new_witness_variable(|| alloc(self.g))?;
        let h = cs.new_witness_variable(|| alloc(self.h))?;
        let p = cs.new_witness_variable(|| alloc(self.p))?;
        let q = cs.new_witness_variable(|| alloc(self.q))?;
        let mul2 = |x: Option<F>, y: Option<F>| {
            x.and_then(|x| y.map(|y| x * y))
                .ok_or(ark_relations::gr1cs::SynthesisError::AssignmentMissing)
        };
        let o1 = cs.new_input_variable(|| mul2(self.a, self.b))?;
        let o2 = cs.new_input_variable(|| mul2(self.c, self.d))?;
        let o3 = cs.new_input_variable(|| mul2(self.e, self.f))?;
        let o4 = cs.new_input_variable(|| mul2(self.g, self.h))?;
        let o5 = cs.new_input_variable(|| mul2(self.a, self.c))?;
        let o6 = cs.new_input_variable(|| mul2(self.b, self.e))?;
        let o7 = cs.new_input_variable(|| mul2(self.d, self.g))?;
        let o8 = cs.new_input_variable(|| mul2(self.f, self.h))?;
        let o9 = cs.new_input_variable(|| mul2(self.p, self.q))?;
        let o10 = cs.new_input_variable(|| mul2(self.a, self.p))?;
        let o11 = cs.new_input_variable(|| mul2(self.e, self.p))?;
        let o12 = cs.new_input_variable(|| mul2(self.h, self.q))?;
        cs.enforce_constraint_arity_3(R1CS_PREDICATE_LABEL, || LinearCombination::from(a), || LinearCombination::from(b), || LinearCombination::from(o1))?;
        cs.enforce_constraint_arity_3(R1CS_PREDICATE_LABEL, || LinearCombination::from(c), || LinearCombination::from(d), || LinearCombination::from(o2))?;
        cs.enforce_constraint_arity_3(R1CS_PREDICATE_LABEL, || LinearCombination::from(e), || LinearCombination::from(f), || LinearCombination::from(o3))?;
        cs.enforce_constraint_arity_3(R1CS_PREDICATE_LABEL, || LinearCombination::from(g), || LinearCombination::from(h), || LinearCombination::from(o4))?;
        cs.enforce_constraint_arity_3(R1CS_PREDICATE_LABEL, || LinearCombination::from(a), || LinearCombination::from(c), || LinearCombination::from(o5))?;
        cs.enforce_constraint_arity_3(R1CS_PREDICATE_LABEL, || LinearCombination::from(b), || LinearCombination::from(e), || LinearCombination::from(o6))?;
        cs.enforce_constraint_arity_3(R1CS_PREDICATE_LABEL, || LinearCombination::from(d), || LinearCombination::from(g), || LinearCombination::from(o7))?;
        cs.enforce_constraint_arity_3(R1CS_PREDICATE_LABEL, || LinearCombination::from(f), || LinearCombination::from(h), || LinearCombination::from(o8))?;
        cs.enforce_constraint_arity_3(R1CS_PREDICATE_LABEL, || LinearCombination::from(p), || LinearCombination::from(q), || LinearCombination::from(o9))?;
        cs.enforce_constraint_arity_3(R1CS_PREDICATE_LABEL, || LinearCombination::from(a), || LinearCombination::from(p), || LinearCombination::from(o10))?;
        cs.enforce_constraint_arity_3(R1CS_PREDICATE_LABEL, || LinearCombination::from(e), || LinearCombination::from(p), || LinearCombination::from(o11))?;
        cs.enforce_constraint_arity_3(R1CS_PREDICATE_LABEL, || LinearCombination::from(h), || LinearCombination::from(q), || LinearCombination::from(o12))?;
        Ok(())
    }
}

fn run_opt<C: ConstraintSynthesizer<F> + Clone>(
    pk: &ark_groth16::ProvingKey<E>,
    vk: &ark_groth16::VerifyingKey<E>,
    h_coeffs: &[F],
    full_assignment_raw: &[F],
    num_inputs: usize,
    circuit: C,
) {
    let mut rng = rand::rngs::OsRng;
    let r = F::rand(&mut rng);
    let s = F::rand(&mut rng);

    let n = pk.a_query.len();
    let m = vk.gamma_abc_g1.len();
    let l = pk.l_query.len();
    let h_size = pk.h_query.len();

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
    let gamma_abc_g1_proj: Vec<G1Projective> =
        vk.gamma_abc_g1.iter().map(|p| p.into_group()).collect();

    let public_inputs_raw = &full_assignment_raw[1..num_inputs];
    let mut public_inputs_padded: Vec<F> = vec![F::one()];
    public_inputs_padded.extend_from_slice(public_inputs_raw);

    let full_assignment_padded = {
        let mut v = full_assignment_raw.to_vec();
        v.resize(n, F::zero());
        v
    };
    let h_coeffs_padded = {
        let mut v = h_coeffs.to_vec();
        v.resize(h_size, F::zero());
        v
    };

    let inputs = Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
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
            Vid("public_inputs".to_string()),
            Value::VecScalar(public_inputs_padded),
        ),
        (Vid("r".to_string()), Value::Scalar(r)),
        (Vid("s".to_string()), Value::Scalar(s)),
        (
            Vid("full_assignment".to_string()),
            Value::VecScalar(full_assignment_padded),
        ),
        (
            Vid("h_coeffs".to_string()),
            Value::VecScalar(h_coeffs_padded),
        ),
    ]);

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
        "public_inputs",
    ];

    let args = ZippelArgs::new(PathBuf::from("examples/groth16/groth16-opt.zippel"));
    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("M"), &m);
    sizes.insert(&Tid::new("L"), &l);
    sizes.insert(&Tid::new("H"), &h_size);
    handler.compile(&sizes);

    let public_inputs_ctx: Ctx<Vid, Value<ArkBls12_381>> = inputs
        .clone()
        .into_iter()
        .filter(|(vid, _)| public_input_names.contains(&vid.0.as_str()))
        .collect();

    let prover_scheduled = handler.default_schedule_prover();
    let prover_start = Instant::now();
    let proof = handler.run_prover(prover_scheduled, inputs);
    let prover_elapsed = prover_start.elapsed();
    let proof_bytes = proof_size_bytes::<ArkBls12_381>(&proof);
    println!("Zippel prover time:    {prover_elapsed:.2?}");
    println!(
        "Proof size:           {proof_bytes} bytes ({} elements)",
        proof.len()
    );

    let verifier_args = ZippelArgs::new(PathBuf::from("examples/groth16/groth16-opt.zippel"));
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

    let proof_ark =
        Groth16::<E>::create_random_proof_with_reduction(circuit, pk, &mut rng).unwrap();
    let pvk = ark_groth16::prepare_verifying_key(vk);
    let ark_verify =
        Groth16::<E>::verify_proof(&pvk, &proof_ark, &full_assignment_raw[1..num_inputs]).unwrap();
    println!(
        "\nArkworks reference verification: {}",
        if ark_verify {
            "✓ PASSED"
        } else {
            "✗ FAILED"
        }
    );

    // run_analysis("examples/groth16/groth16-opt.zippel", "opt");
}

#[allow(dead_code)]
fn run_analysis(zippel_file: &str, mode_name: &str) {
    println!("\n--- Static Analysis ({mode_name}) ---");
    let analysis_start = Instant::now();
    let analysis_result = std::panic::catch_unwind(|| {
        let analysis_args = ZippelArgs::new(PathBuf::from(zippel_file));
        let mut analysis_handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(analysis_args);
        analysis_handler.minimal_analysis()
    });
    let analysis_elapsed = analysis_start.elapsed();
    match analysis_result {
        Ok(analysis) => {
            match &analysis.completeness {
                Ok(()) => println!("Completeness:   ✓"),
                Err(e) => println!("Completeness:   ✗ {}", e),
            }
            match &analysis.zk {
                Ok(()) => println!("ZK:             ✓"),
                Err(e) => println!("ZK:             ✗ {}", e),
            }
        }
        Err(_) => println!("Analysis:       ⚠ not supported (non-polynomial operations)"),
    }
    println!("Analysis time:  {analysis_elapsed:.2?}");
}

fn run_noh<C: ConstraintSynthesizer<F> + Clone>(
    pk: &ark_groth16::ProvingKey<E>,
    vk: &ark_groth16::VerifyingKey<E>,
    matrices: &[ark_relations::gr1cs::Matrix<F>],
    full_assignment_raw: &[F],
    num_inputs: usize,
    num_constraints: usize,
    circuit: C,
) {
    use ark_poly::GeneralEvaluationDomain;

    let mut rng = rand::rngs::OsRng;
    let r = F::rand(&mut rng);
    let s = F::rand(&mut rng);

    let n = pk.a_query.len();
    let m = vk.gamma_abc_g1.len();
    let l = pk.l_query.len();

    type Dm<FF> = GeneralEvaluationDomain<FF>;
    let domain = Dm::<F>::new(num_constraints + num_inputs).unwrap();
    let domain_size = domain.size();

    // Build flat D×N dense matrices from sparse R1CS matrices
    // Rows 0..num_constraints: constraint rows (sparse, padded with zeros)
    // Rows num_constraints..num_constraints+num_inputs: identity rows (A only) or zeros
    // Rows num_constraints+num_inputs..domain_size: zeros
    // Note: arkworks adds identity rows for A only (for input variables), not B or C.
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
        _num_constraints: usize,
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

    let mat_a_flat =
        build_dense_matrix_a(&matrices[0], num_constraints, num_inputs, domain_size, n);
    let mat_b_flat = build_dense_matrix_bc(&matrices[1], num_constraints, domain_size, n);
    let mat_c_flat = build_dense_matrix_bc(&matrices[2], num_constraints, domain_size, n);

    // Coset offset: omega = F::GENERATOR
    // Shift vectors and v_inv are computed inside zippel from omega
    let coset_offset = F::GENERATOR;

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
    let gamma_abc_g1_proj: Vec<G1Projective> =
        vk.gamma_abc_g1.iter().map(|p| p.into_group()).collect();

    let public_inputs_raw = &full_assignment_raw[1..num_inputs];
    let mut public_inputs_padded: Vec<F> = vec![F::one()];
    public_inputs_padded.extend_from_slice(public_inputs_raw);

    let full_assignment_padded = {
        let mut v = full_assignment_raw.to_vec();
        v.resize(n, F::zero());
        v
    };

    let inputs = Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
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
            Vid("public_inputs".to_string()),
            Value::VecScalar(public_inputs_padded),
        ),
        (Vid("r".to_string()), Value::Scalar(r)),
        (Vid("s".to_string()), Value::Scalar(s)),
        (
            Vid("full_assignment".to_string()),
            Value::VecScalar(full_assignment_padded),
        ),
        (Vid("mat_a".to_string()), Value::VecScalar(mat_a_flat)),
        (Vid("mat_b".to_string()), Value::VecScalar(mat_b_flat)),
        (Vid("mat_c".to_string()), Value::VecScalar(mat_c_flat)),
        (Vid("omega".to_string()), Value::Scalar(coset_offset)),
    ]);

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
        "public_inputs",
    ];

    let public_inputs_ctx: Ctx<Vid, Value<ArkBls12_381>> = inputs
        .clone()
        .into_iter()
        .filter(|(vid, _)| public_input_names.contains(&vid.0.as_str()))
        .collect();

    let args = ZippelArgs::new(PathBuf::from("examples/groth16/groth16.zippel"));
    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("M"), &m);
    sizes.insert(&Tid::new("L"), &l);
    sizes.insert(&Tid::new("C"), &num_constraints);
    sizes.insert(&Tid::new("D"), &domain_size);
    handler.compile(&sizes);

    let prover_scheduled = handler.default_schedule_prover();
    let prover_start = Instant::now();
    let proof = handler.run_prover(prover_scheduled, inputs);
    let prover_elapsed = prover_start.elapsed();
    let proof_bytes = proof_size_bytes::<ArkBls12_381>(&proof);
    println!("Zippel prover time:    {prover_elapsed:.2?}");
    println!(
        "Proof size:           {proof_bytes} bytes ({} elements)",
        proof.len()
    );

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

    let proof_ark =
        Groth16::<E>::create_random_proof_with_reduction(circuit, pk, &mut rng).unwrap();
    let pvk = ark_groth16::prepare_verifying_key(vk);
    let ark_verify =
        Groth16::<E>::verify_proof(&pvk, &proof_ark, &full_assignment_raw[1..num_inputs]).unwrap();
    println!(
        "\nArkworks reference verification: {}",
        if ark_verify {
            "✓ PASSED"
        } else {
            "✗ FAILED"
        }
    );

    // run_analysis("examples/groth16/groth16.zippel", "noh");
}

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_else(|| "noh".to_string());
    let circuit_name = std::env::args()
        .nth(2)
        .unwrap_or_else(|| "single".to_string());
    println!("=== Groth16 (ArkBls12_381) — mode: {mode}, circuit: {circuit_name} ===");
    let mut rng = rand::rngs::OsRng;

    if circuit_name == "double" {
        let a_val = F::rand(&mut rng);
        let b_val = F::rand(&mut rng);
        let d_val = F::rand(&mut rng);
        let circuit = DoubleMulCircuit {
            a: Some(a_val),
            b: Some(b_val),
            d: Some(d_val),
        };
        setup_and_run(circuit, mode);
    } else if circuit_name == "triple" {
        let a_val = F::rand(&mut rng);
        let b_val = F::rand(&mut rng);
        let d_val = F::rand(&mut rng);
        let e_val = F::rand(&mut rng);
        let circuit = TripleMulCircuit {
            a: Some(a_val),
            b: Some(b_val),
            d: Some(d_val),
            e: Some(e_val),
        };
        setup_and_run(circuit, mode);
    } else if circuit_name == "complex" {
        let circuit = ComplexCircuit {
            a: Some(F::rand(&mut rng)),
            b: Some(F::rand(&mut rng)),
            c: Some(F::rand(&mut rng)),
            d: Some(F::rand(&mut rng)),
            e: Some(F::rand(&mut rng)),
            f: Some(F::rand(&mut rng)),
            g: Some(F::rand(&mut rng)),
            h: Some(F::rand(&mut rng)),
            p: Some(F::rand(&mut rng)),
            q: Some(F::rand(&mut rng)),
        };
        setup_and_run(circuit, mode);
    } else {
        let a_val = F::rand(&mut rng);
        let b_val = F::rand(&mut rng);
        let circuit = MultiplyCircuit {
            a: Some(a_val),
            b: Some(b_val),
        };
        setup_and_run(circuit, mode);
    }
}

fn setup_and_run<C: ConstraintSynthesizer<F> + Clone>(circuit: C, mode: String) {
    let mut rng = rand::rngs::OsRng;

    let pk =
        Groth16::<E>::generate_random_parameters_with_reduction(circuit.clone(), &mut rng).unwrap();
    let vk = pk.vk.clone();

    let n = pk.a_query.len();
    let m = vk.gamma_abc_g1.len();
    let l = pk.l_query.len();
    let h = pk.h_query.len();

    let cs = ConstraintSystem::<F>::new_ref();
    cs.set_mode(SynthesisMode::Prove {
        construct_matrices: true,
        generate_lc_assignments: false,
    });
    circuit.clone().generate_constraints(cs.clone()).unwrap();
    cs.finalize();

    let cs_borrowed = cs.borrow().unwrap();
    let num_constraints = cs_borrowed.num_constraints();
    let num_inputs = cs_borrowed.num_instance_variables();
    let num_witness = cs_borrowed.num_witness_variables();
    println!("num_constraints={num_constraints} num_inputs={num_inputs} num_witness={num_witness}");
    println!("N={n} M={m} L={l} H={h}");

    let cs_borrowed = cs.borrow().unwrap();
    let matrices_map = cs_borrowed.to_matrices().unwrap();
    let matrices: Vec<_> = matrices_map
        .get(R1CS_PREDICATE_LABEL)
        .cloned()
        .unwrap_or_default();
    let num_inputs = cs_borrowed.num_instance_variables();
    let num_constraints = cs_borrowed.num_constraints();
    let instance_assignment: Vec<F> = cs_borrowed.instance_assignment().unwrap().to_vec();
    let witness_assignment: Vec<F> = cs_borrowed.witness_assignment().unwrap().to_vec();
    let full_assignment_raw: Vec<F> = [instance_assignment, witness_assignment].concat();

    use ark_groth16::r1cs_to_qap::{LibsnarkReduction, R1CSToQAP};
    use ark_poly::GeneralEvaluationDomain;
    type D<FF> = GeneralEvaluationDomain<FF>;

    if mode == "opt" {
        let h_coeffs = LibsnarkReduction::witness_map_from_matrices::<F, D<F>>(
            &matrices,
            num_inputs,
            num_constraints,
            &full_assignment_raw,
        )
        .unwrap();

        run_opt(
            &pk,
            &vk,
            &h_coeffs,
            &full_assignment_raw,
            num_inputs,
            circuit,
        );
    } else {
        run_noh(
            &pk,
            &vk,
            &matrices,
            &full_assignment_raw,
            num_inputs,
            num_constraints,
            circuit,
        );
    }
}
