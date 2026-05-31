use ark_bls12_381::Fr;
use ark_gb::monomial::MonoTerm;
use ark_gb::ring::Ring;

#[inline(never)]
#[unsafe(no_mangle)]
pub extern "C" fn probe_mul(a: &MonoTerm, b: &MonoTerm, ring: &Ring<Fr>, out: &mut MonoTerm) {
    *out = a.mul(b, ring);
}

fn main() {
    let ring = Ring::<Fr>::new(25).unwrap();
    let a = MonoTerm::from_exponents(&ring, &[1u32; 25]).unwrap();
    let b = MonoTerm::from_exponents(&ring, &[2u32; 25]).unwrap();
    let mut out = MonoTerm::one(&ring);
    probe_mul(&a, &b, &ring, &mut out);
    eprintln!("{:?}", out.exponents(&ring));
}
