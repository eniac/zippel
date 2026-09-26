use std::cmp::Ordering;
use std::fmt;

/// Visibility qualifier attached to every protocol variable and DAG node.
///
/// The four qualifiers form a total order `Witness <= Local <= Extra <= Instance`,
/// from "known only to the prover" up to "known to everyone". Qualifier
/// propagation in `graph` joins the qualifiers of an operation's children, and the
/// result decides whether a node is projected into the prover subgraph, the
/// verifier subgraph, or both.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Qualifier {
    /// Secret prover input (surface keyword `witness`); never revealed to the verifier.
    Witness,
    /// The default for an unannotated argument or a compiler-introduced intermediate:
    /// a value local to the party that computes it, not part of the transcript.
    Local,
    /// Transcript material (surface keyword `extra`): computed by the prover and sent
    /// to the verifier as part of the proof.
    Extra,
    /// Public statement data (surface keyword `instance`) known to prover and verifier alike.
    Instance,
}

impl Qualifier {
    /// Returns `true` for [`Qualifier::Witness`].
    pub fn is_witness(&self) -> bool {
        matches!(self, Qualifier::Witness)
    }
    /// Returns `true` for [`Qualifier::Local`].
    pub fn is_local(&self) -> bool {
        matches!(self, Qualifier::Local)
    }
    /// Returns `true` for [`Qualifier::Extra`].
    pub fn is_extra(&self) -> bool {
        matches!(self, Qualifier::Extra)
    }
    /// Returns `true` for [`Qualifier::Instance`].
    pub fn is_instance(&self) -> bool {
        matches!(self, Qualifier::Instance)
    }
    /// Joins two qualifiers in the secrecy lattice, yielding the least (most secret)
    /// of the two.
    ///
    /// This is the propagation rule: a value derived from a `witness` is itself a
    /// witness, and only a value derived exclusively from `instance` data stays
    /// `Instance`.
    pub fn join(&self, other: &Self) -> Self {
        match (self, other) {
            // Witness ≤ Local ≤ Extra ≤ Instance (join = min in the lattice)
            (Qualifier::Witness, _) | (_, Qualifier::Witness) => Qualifier::Witness,
            (Qualifier::Local, _) | (_, Qualifier::Local) => Qualifier::Local,
            (Qualifier::Extra, _) | (_, Qualifier::Extra) => Qualifier::Extra,
            (Qualifier::Instance, Qualifier::Instance) => Qualifier::Instance,
        }
    }
}

/// Witness <= Local <= Extra <= Instance
impl PartialOrd for Qualifier {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Qualifier {
    fn cmp(&self, other: &Self) -> Ordering {
        let rank = |q: &Qualifier| -> u8 {
            match q {
                Qualifier::Witness => 0,
                Qualifier::Local => 1,
                Qualifier::Extra => 2,
                Qualifier::Instance => 3,
            }
        };
        rank(self).cmp(&rank(other))
    }
}

impl fmt::Display for Qualifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Qualifier::Witness => "witness ",
            Qualifier::Local => "local ",
            Qualifier::Extra => "extra ",
            Qualifier::Instance => "instance ",
        })
    }
}

#[test]
fn qualifier_join_lattice_consistency() {
    use Qualifier::*;
    let all = [Witness, Local, Extra, Instance];
    for &a in &all {
        for &b in &all {
            let j = a.join(&b);
            // join(a,b) == min(a,b) in the ordering
            assert_eq!(
                j,
                a.min(b),
                "join({:?}, {:?}) = {:?}, expected {:?}",
                a,
                b,
                j,
                a.min(b)
            );
            // Commutativity
            assert_eq!(
                a.join(&b),
                b.join(&a),
                "join is not commutative for {:?}, {:?}",
                a,
                b
            );
        }
    }
}
