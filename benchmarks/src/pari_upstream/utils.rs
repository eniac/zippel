use super::data_structures::VerifyingKey;
use ark_ec::pairing::Pairing;

#[cfg(not(feature = "sol"))]
pub fn compute_chall<E: Pairing>(
    vk: &VerifyingKey<E>,
    public_input: &[E::ScalarField],
    t_g: &E::G1Affine,
) -> E::ScalarField {
    use super::transcript::IOPTranscript;
    let mut transcript = IOPTranscript::<E::ScalarField>::new(super::Pari::<E>::SNARK_NAME);
    let _ = transcript.append_serializable_element(b"vk", vk);
    let _ = transcript.append_serializable_element(b"input", &public_input.to_vec());
    let _ = transcript.append_serializable_element(b"comm", t_g);
    let challenge = transcript.get_and_append_challenge("r".as_bytes()).unwrap();
    challenge
}
#[cfg(feature = "sol")]
use ark_ec::AffineRepr;
#[cfg(feature = "sol")]
use ark_ff::PrimeField;

#[cfg(feature = "sol")]
pub fn compute_chall<E: Pairing>(
    vk: &VerifyingKey<E>,
    public_input: &[E::ScalarField],
    t_g: &E::G1Affine,
) -> E::ScalarField
where
    E::BaseField: PrimeField,
    <E::G1Affine as AffineRepr>::BaseField: PrimeField,
{
    use ark_ff::Field;
    use tiny_keccak::{Hasher, Keccak};
    let mut hasher = Keccak::v256();
    let mut output = [0u8; 32];

    let binding = vk.h.x().unwrap();
    let mut vk_h_x = binding.to_base_prime_field_elements();
    let binding = vk.h.y().unwrap();
    let mut vk_h_y = binding.to_base_prime_field_elements();

    let binding = vk.delta_two_h.x().unwrap();
    let mut vk_delta_h_x = binding.to_base_prime_field_elements();
    let binding = vk.delta_two_h.y().unwrap();
    let mut vk_delta_h_y = binding.to_base_prime_field_elements();

    let binding = vk.tau_h.x().unwrap();
    let mut vk_tau_h_x = binding.to_base_prime_field_elements();
    let binding = vk.tau_h.y().unwrap();
    let mut vk_tau_h_y = binding.to_base_prime_field_elements();

    hasher.update(&encode_packed(t_g.x().unwrap()));
    hasher.update(&encode_packed(t_g.y().unwrap()));
    hasher.update(&encode_packed(E::ScalarField::from(1)));
    for elem in public_input.iter() {
        hasher.update(&encode_packed(*elem));
    }

    hasher.update(&encode_packed(vk.g.x().unwrap()));
    hasher.update(&encode_packed(vk.g.y().unwrap()));
    hasher.update(&encode_packed(vk.alpha_g.x().unwrap()));
    hasher.update(&encode_packed(vk.alpha_g.y().unwrap()));
    hasher.update(&encode_packed(vk.beta_g.x().unwrap()));
    hasher.update(&encode_packed(vk.beta_g.y().unwrap()));
    hasher.update(&encode_packed(vk_h_x.next().unwrap()));
    hasher.update(&encode_packed(vk_h_x.next().unwrap()));
    hasher.update(&encode_packed(vk_h_y.next().unwrap()));
    hasher.update(&encode_packed(vk_h_y.next().unwrap()));
    hasher.update(&encode_packed(vk_delta_h_x.next().unwrap()));
    hasher.update(&encode_packed(vk_delta_h_x.next().unwrap()));
    hasher.update(&encode_packed(vk_delta_h_y.next().unwrap()));
    hasher.update(&encode_packed(vk_delta_h_y.next().unwrap()));
    hasher.update(&encode_packed(vk_tau_h_x.next().unwrap()));
    hasher.update(&encode_packed(vk_tau_h_x.next().unwrap()));
    hasher.update(&encode_packed(vk_tau_h_y.next().unwrap()));
    hasher.update(&encode_packed(vk_tau_h_y.next().unwrap()));
    hasher.finalize(&mut output);
    E::ScalarField::from_be_bytes_mod_order(&output)
}

#[cfg(feature = "sol")]
fn encode_packed<F: PrimeField>(field_element: F) -> Vec<u8> {
    use num_bigint::BigUint;

    let a: BigUint = field_element.into();
    let mut b = a.to_bytes_be();

    if b.len() < 32 {
        let mut padded = vec![0u8; 32 - b.len()];
        padded.extend_from_slice(&b);
        b = padded;
    }

    b
}
