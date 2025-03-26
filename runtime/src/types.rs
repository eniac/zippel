use lang::typ::Typ;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Field {
    Bls12377(ark_bls12_377::Fr),
    Bls12381(ark_bls12_381::Fr),
    EdOnCp6_782(ark_ed_on_cp6_782::Fr),
    Bn254(ark_bn254::Fr),
    MNT4_298(ark_mnt4_298::Fr),
    MNT4_753(ark_mnt4_753::Fr),
    Pallas(ark_pallas::Fr),
    Secp256k1(ark_secp256k1::Fr),
    Curve25519(ark_curve25519::Fr)
}

pub enum Group {
    Bls12377G1(ark_bls12_377::g1::G1Affine),
    Bls12377G2(ark_bls12_377::g2::G2Affine),
    Bls12377Gt(ark_bls12_377::G1TEAffine),
    Bls12381G1(ark_bls12_381::g1::G1Affine),
    Bls12381G2(ark_bls12_381::g2::G2Affine),
    EdOnCp6_782(ark_ed_on_cp6_782::EdwardsAffine),
    Bn254G1(ark_bn254::g1::G1Affine),
    Bn254G2(ark_bn254::g2::G2Affine),
    MNT4_298G1(ark_mnt4_298::g1::G1Affine),
    MNT4_298G2(ark_mnt4_298::g2::G2Affine),
    MNT4_753G1(ark_mnt4_753::g1::G1Affine),
    MNT4_753G2(ark_mnt4_753::g2::G2Affine),
    Pallas(ark_pallas::Affine),
    Vesta(ark_vesta::Affine),
    Secp256k1(ark_secp256k1::Affine),
    Curve25519(ark_curve25519::EdwardsAffine),
}

pub enum ArkType {
    Field(Field),
    Group(Group),
}

/// A Zippel type specialized to arkworks types
pub type ATyp = Typ<ArkType, usize>;


