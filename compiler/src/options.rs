#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CodegenMode {
    Prover,
    Verifier,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RustTarget {
    pub curve_crate: &'static str,
    pub scalar_type: &'static str,
    pub g1_type: &'static str,
    pub g2_type: &'static str,
    pub pairing_type: &'static str,
}

impl RustTarget {
    pub fn ark_bls12_381() -> Self {
        Self {
            curve_crate: "ark_bls12_381",
            scalar_type: "ark_bls12_381::Fr",
            g1_type: "ark_bls12_381::G1Projective",
            g2_type: "ark_bls12_381::G2Projective",
            pairing_type: "ark_bls12_381::Bls12_381",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CodegenOptions {
    pub mode: CodegenMode,
    pub target: RustTarget,
    pub session: String,
    pub proof_type_path: String,
}

impl CodegenOptions {
    pub fn prover() -> Self {
        Self::default()
    }

    pub fn verifier() -> Self {
        Self {
            mode: CodegenMode::Verifier,
            ..Self::default()
        }
    }
}

impl Default for CodegenOptions {
    fn default() -> Self {
        Self {
            mode: CodegenMode::Prover,
            target: RustTarget::ark_bls12_381(),
            session: "examples/schnorr/schnorr.zippel".to_string(),
            proof_type_path: "crate::prover::Proof".to_string(),
        }
    }
}
