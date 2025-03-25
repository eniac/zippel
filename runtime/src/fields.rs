use ark_bls12_377::Fr as Bls12377;
use ark_bls12_381::Fr as Bls12381;
use ark_ed_on_cp6_782::Fr as EdOnCp6_782;
use ark_bn254::Fr as Bn254;
use ark_mnt4_298::Fr as MNT4_298;
use ark_mnt4_753::Fr as MNT4_753;
use ark_pallas::Fr as Pallas;
use ark_secp256k1::Fr as Secp256k1;
use ark_curve25519::Fr as Curve25519;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Field {
    Bls12377(Bls12377),
    Bls12381(Bls12381),
    EdOnCp6_782(EdOnCp6_782),
    Bn254(Bn254),
    MNT4_298(MNT4_298),
    MNT4_753(MNT4_753),
    Pallas(Pallas),
    Secp256k1(Secp256k1),
    Curve25519(Curve25519)
}

