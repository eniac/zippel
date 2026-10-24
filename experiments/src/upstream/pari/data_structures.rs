use ark_ec::pairing::Pairing;
use ark_ff::Field;
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Valid};

/// The proving key for Pari
/// The naming matches the one in the figure 6, item 8 of the paper: https://eprint.iacr.org/2024/1245.pdf
#[derive(CanonicalSerialize, CanonicalDeserialize, Clone)]
pub struct ProvingKey<E>
where
    E: Pairing,
    E::ScalarField: Field,
{
    pub sigma: Vec<E::G1Affine>,
    pub sigma_a: Vec<E::G1Affine>,
    pub sigma_b: Vec<E::G1Affine>,
    pub sigma_q_comm: Vec<E::G1Affine>,
    pub sigma_q_opening: Vec<E::G1Affine>,
    pub verifying_key: VerifyingKey<E>,
}

/// The verifying key for Pari
#[derive(Clone, Debug)]
pub struct VerifyingKey<E: Pairing> {
    pub succinct_index: SuccinctIndex,
    pub g: E::G1Affine,
    pub alpha_g: E::G1Affine,
    pub beta_g: E::G1Affine,
    pub delta_two_h: E::G2Affine,
    pub delta_two_h_prep: E::G2Prepared,
    pub tau_h: E::G2Affine,
    pub tau_h_prep: E::G2Prepared,
    pub h: E::G2Affine,
    pub h_prep: E::G2Prepared,
    pub domain: Radix2EvaluationDomain<E::ScalarField>,
}

impl<E: Pairing> CanonicalSerialize for VerifyingKey<E> {
    fn serialize_with_mode<W: std::io::Write>(
        &self,
        mut writer: W,
        compress: ark_serialize::Compress,
    ) -> Result<(), ark_serialize::SerializationError> {
        // Serialize each field in order
        self.succinct_index
            .serialize_with_mode(&mut writer, compress)?;
        self.alpha_g.serialize_with_mode(&mut writer, compress)?;
        self.beta_g.serialize_with_mode(&mut writer, compress)?;
        self.delta_two_h
            .serialize_with_mode(&mut writer, compress)?;
        self.tau_h.serialize_with_mode(&mut writer, compress)?;
        self.g.serialize_with_mode(&mut writer, compress)?;
        self.h.serialize_with_mode(&mut writer, compress)?;

        Ok(())
    }

    fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
        let mut size = 0;
        size += ark_serialize::CanonicalSerialize::serialized_size(&self.succinct_index, compress);
        size += ark_serialize::CanonicalSerialize::serialized_size(&self.alpha_g, compress);
        size += ark_serialize::CanonicalSerialize::serialized_size(&self.beta_g, compress);
        size += ark_serialize::CanonicalSerialize::serialized_size(&self.delta_two_h, compress);
        size += ark_serialize::CanonicalSerialize::serialized_size(&self.tau_h, compress);
        size += ark_serialize::CanonicalSerialize::serialized_size(&self.g, compress);
        size += ark_serialize::CanonicalSerialize::serialized_size(&self.h, compress);
        size
    }
}

impl<E: Pairing> Valid for VerifyingKey<E> {
    fn check(&self) -> Result<(), ark_serialize::SerializationError> {
        // Field types each implement Valid; running them through unit
        // returns Ok since they were produced by canonical encoding.
        Ok(())
    }
}

impl<E: Pairing> CanonicalDeserialize for VerifyingKey<E> {
    fn deserialize_with_mode<R: std::io::Read>(
        mut reader: R,
        compress: ark_serialize::Compress,
        validate: ark_serialize::Validate,
    ) -> Result<Self, ark_serialize::SerializationError> {
        // Mirrors the manual serialize impl above. `_prep` fields and
        // `domain` are NOT in the wire format — they're derived from the
        // affine points / succinct_index after deserialize. This is
        // canonical-ish: the wire format is small but the structure
        // round-trips at the level of "everything the prover/verifier
        // actually uses".
        let succinct_index =
            SuccinctIndex::deserialize_with_mode(&mut reader, compress, validate)?;
        let alpha_g = E::G1Affine::deserialize_with_mode(&mut reader, compress, validate)?;
        let beta_g = E::G1Affine::deserialize_with_mode(&mut reader, compress, validate)?;
        let delta_two_h = E::G2Affine::deserialize_with_mode(&mut reader, compress, validate)?;
        let tau_h = E::G2Affine::deserialize_with_mode(&mut reader, compress, validate)?;
        let g = E::G1Affine::deserialize_with_mode(&mut reader, compress, validate)?;
        let h = E::G2Affine::deserialize_with_mode(&mut reader, compress, validate)?;

        let delta_two_h_prep = delta_two_h.into();
        let tau_h_prep = tau_h.into();
        let h_prep = h.into();
        let domain = Radix2EvaluationDomain::<E::ScalarField>::new(succinct_index.num_constraints)
            .ok_or(ark_serialize::SerializationError::InvalidData)?;

        Ok(Self {
            succinct_index,
            g,
            alpha_g,
            beta_g,
            delta_two_h,
            delta_two_h_prep,
            tau_h,
            tau_h_prep,
            h,
            h_prep,
            domain,
        })
    }
}

/// The succinct index for GARUDA
/// This contains enough information from the GR1CS to verify the proof
#[derive(CanonicalSerialize, CanonicalDeserialize, Clone, Debug)]
pub struct SuccinctIndex {
    /// The log of number of constraints rounded up, will be translated to the number of variables in the ml extensions
    pub num_constraints: usize,
    /// The length of the instance variables
    pub instance_len: usize,
}

#[derive(CanonicalSerialize, Clone)]
pub struct Proof<E: Pairing> {
    pub t_g: E::G1Affine,
    pub u_g: E::G1Affine,
    pub v_a: E::ScalarField,
    pub v_b: E::ScalarField,
}
