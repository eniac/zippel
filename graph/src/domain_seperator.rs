use ark_serialize::CanonicalSerialize;
use backend::{ABase, ATyp, ArkConfig, ArkPairingOps};
use spongefish::{
    ByteDomainSeparator, DomainSeparator, DuplexSpongeInterface,
};
use crate::Dag;

#[cfg(test)] use backend::ArkBls12_381;
#[cfg(test)] use lang::ast::UModule;
#[cfg(test)] use share::unwrap;
#[cfg(test)] use crate::UDags;
#[cfg(test)] use spongefish::DefaultHash;

/// Extend the domain separator with the Schnorr protocol.
pub struct ZippelDomainSeparator<H: DuplexSpongeInterface> (
    pub DomainSeparator<H>
);

impl<H> ZippelDomainSeparator<H>
where
    H: DuplexSpongeInterface
{
    pub fn new<C: ArkConfig, A>(domsep: &str, dag: &Dag<C, A>) -> Self {
        let mut ds = Self(DomainSeparator::<H>::new(domsep));
        ds.init_from_dag(dag);
        ds
    }

    fn from_input_node<C: ArkConfig, A>(mut self, node: &crate::Node<C, A>) -> Self {
        
        match &node {
            crate::Node::Inp(_c, prefs) => {
                for pref in prefs.iter() {
                    if pref.qualifier.is_public() && !pref.from_transcript {
                        self.init_absorb_type::<C>(&pref.typ);
                    }
                }
            }
            _ => {
                panic!("Not an input node")
            }
        }
            self
        }

    fn init_absorb_bytes(&mut self, byte_len: usize, label: &str) {
        self.0 = self.0.add_bytes(byte_len, label);
    }

    fn init_absorb_type<C: ArkConfig>(&mut self, typ: &ATyp) {
        match typ {
            ATyp::Base(ABase::G1) => self.init_absorb_bytes(C::G1::default().compressed_size(), "G1"),
            ATyp::Base(ABase::G2) => self.init_absorb_bytes(C::G2::default().compressed_size(), "G2"),
            ATyp::Base(ABase::GT) => self.init_absorb_bytes(C::POps::zero().compressed_size(), "GT"),
            ATyp::Base(ABase::Scalar) => self.init_absorb_bytes(C::F::default().compressed_size(), "F"),
            ATyp::Base(ABase::Bool) => self.init_absorb_bytes(1, "Bool"),
            ATyp::Vec(inner_typ, size) => (0..*size).for_each(|_| self.init_absorb_type::<C>(inner_typ)),
            ATyp::Uni(ndegree) => panic!("TODO: Need ATyp to tell me Dense/Sparse and Uni/Multivariate so I can serialize properly"),
            ATyp::Mle(ndegree) => panic!("TODO: Need ATyp to tell me Dense/Sparse and Uni/Multivariate so I can serialize properly"),
        }
    }

    fn init_squeeze_bytes(&mut self, size: usize, label: &str) {
        self.0 = self.0.squeeze(size, label);
    }

    fn init_from_dag<C: ArkConfig, A>(&mut self, dag: &Dag<C, A>) {
        let input_node_index = dag.input_node();
        let node = &dag.0[input_node_index];
        self.from_input_node(&node);

        let transcript_nodes = dag.transcript_nodes();
           
        for (position, transcript_node_index) in transcript_nodes.iter().enumerate() {
            if dag[*transcript_node_index].is_challenge() {
                self.init_squeeze_bytes(
                    C::F::default().compressed_size(),
                    &format!("chall{}", position),
                );
            } else {
                let atyp = dag[*transcript_node_index].typ().unwrap();
                self.init_absorb_type::<C>(&atyp);
            }
        }       
    }
}

#[test]
fn test_domain_separator() {
    let ex = r#"
    proto schnorr<G: Group, F: Scalar<G>>(private x: F, public g: G, public h: G) where h == g*x {
        let r = random<F>;
        u <- g*r;
        c <- challenge<F>;
        z <- r + x*c;
        verify(g*z == u + h*c);
    }
"#;
    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
    let domain_seperator = ZippelDomainSeparator::<DefaultHash>::new(
        "test_domain_separator",
        &gs[0],
    );
    println!("Domain Seperator: {:?}", domain_seperator.0);
}
