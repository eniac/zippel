use ark_serialize::CanonicalSerialize;
use backend::{ABase, ATyp, ArkConfig};
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
    pub fn new_zippel_domain_seperator<C: ArkConfig, A>(domsep: &str, dag: &Dag<C, A>) -> Self {
        Self(DomainSeparator::<H>::new(domsep)).from_dag(dag)
    }

    pub fn from_input_node<C: ArkConfig, A>(mut self, node: &crate::Node<C, A>) -> Self {
        
        match &node {
            crate::Node::Inp(_c, prefs) => {
                for pref in prefs.clone() {
                    if pref.qualifier.is_public() && !pref.from_transcript {
                        self = Self::from_atyp::<C>(self,pref.typ);
                    }
                }
            }
            _ => {
                panic!("Not an input node")
            }
        }
        self
    }

    pub fn from_challenge_node<C: ArkConfig, A>(mut self, node: &crate::Node<C, A>, label: usize) -> Self {
        match &node {
            crate::Node::Transcr(c, _) => match c {
                crate::Op::Challenge(_typ, _) => {
                    // println!("Challenge node: {}", label);
                    // println!("Size {}", C::F::default().compressed_size());
                    self = Self(self.0.squeeze(
                        C::F::default().compressed_size(),
                        &format!("chall{}", label),
                    ));

                },
                _ => {}
            },
            _ => {

            }
        }
        self
    }

    pub fn from_transcript_node<C: ArkConfig, A>(mut self, node: &crate::Node<C, A>, _label: usize) -> Self {
        match &node {
            crate::Node::Transcr(c, _) => {
                let typ: ATyp = c.typ();
                self = Self::from_atyp::<C>(self,typ);
            },
            _ => {
                panic!("Not a transcript node")
            }
        }
        self
    }

    pub fn from_atyp<C: ArkConfig>(mut self, typ: ATyp) -> Self {
        match typ {
            ATyp::Base(base) => match base {
                ABase::G1 => {
                    // println!("Adding G1");
                    // println!("Size {}", C::G1::default().compressed_size());
                    self = Self(self.0.add_bytes(C::G1::default().compressed_size(), "G1"));
                }
                ABase::G2 => {
                    // println!("Adding G2");
                    // println!("Size {}", C::G2::default().compressed_size());
                    self = Self(self.0.add_bytes(C::G2::default().compressed_size(), "G2"));
                }
                ABase::GT => {
                    // println!("Adding GT");
                    // println!("Size {}", C::G2::default().compressed_size());
                    self = Self(self.0.add_bytes(C::G2::default().compressed_size(), "GT"));
                }
                ABase::Scalar => {
                    // println!("Adding Scalar");
                    // println!("Size {}", C::F::default().compressed_size());
                    self = Self(self.0.add_bytes(C::F::default().compressed_size(), "F"));
                }
                _ => {
                    panic!("Cannot add this base element to transcript");
                }
            },
            ATyp::Vec(another_typ, size) => {
                for _ in 0..size {
                    self =
                    Self::from_atyp::<C>(self, *another_typ.clone());
                }
            }
            _ => {
                panic!("Cannot add this type to transcript");
            }
        }
        self
    }

    pub fn from_dag<C: ArkConfig, A>(mut self, dag: &Dag<C, A>) -> Self {
        let input_node_index = dag.input_node();
        let node = &dag.0[input_node_index];
        self = self.from_input_node(&node);

        let transcript_nodes = dag.transcript_nodes();
           
        for (position, transcript_node_index) in transcript_nodes.iter().enumerate() {
            self = self.from_challenge_node(&dag.0[*transcript_node_index], position);
            self = self
            .from_transcript_node(&dag.0[*transcript_node_index], position);
        }       

        
        Self(self.0.clone())
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
    let domain_seperator = ZippelDomainSeparator::<DefaultHash>::new_zippel_domain_seperator(
        "test_domain_separator",
        &gs[0],
    );
    println!("Domain Seperator: {:?}", domain_seperator.0);
}
