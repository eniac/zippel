use crate::{Op, Node, Dag, UDag, Dep};
use petgraph::{
    graph::{EdgeReference, NodeIndex},
    visit::EdgeRef,
    Graph,
    Direction,
};
use lang::id::Vid;
use lang::ast::{BinOp, CArg};
use share::{Ctx, Pretty, BoxAllocator, DocAllocator, DocBuilder};
use backend::ArkConfig;
use std::fmt;

/// Assign a principal to graph nodes
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Principal {
    Verifier,
    Prover,
    Any
}

/// A greater than zero constraint on an operand
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum GtZ {
    Node(NodeIndex),
    Var(Vid)
}

impl GtZ {
    pub fn var(v: Vid) -> Self {
        GtZ::Var(v)
    }
    pub fn node(n: NodeIndex) -> Self {
        GtZ::Node(n)
    }
}


/// Graph with principals
#[derive(Clone)]
pub struct PrincipalDag<C: ArkConfig>(Dag<C, Principal>);

impl<C: ArkConfig> PrincipalDag<C> {
    pub fn new(dag: &UDag<C>) -> Self where C: Clone {
        PrincipalDag(Dag(dag.0.map(|_, n|
                match n {
                    Node::Op(Op::Gen(t), _) => Node::Op(Op::Gen(t.clone()), Principal::Verifier),
                    Node::Op(Op::Challenge(t), _) => Node::Op(Op::Challenge(t.clone()), Principal::Verifier),
                    Node::Op(op, _) => Node::Op(op.clone(), Principal::Any),
                    Node::Transcr(op, _) => Node::Transcr(op.clone(), Principal::Verifier),
                    Node::Inp(fid, sig) => Node::Inp(fid.clone(), sig.clone())
                },
                |_, e| e.clone())))
    }

    pub fn invert(&mut self) -> (Vec<Vid>, Vec<GtZ>) {
        let mut leaks = Vec::new();
        let mut ctrs = Vec::new();

        let mut next: Vec<NodeIndex> = self.0.0.node_indices().collect();
        let mut empty_twice = false;
        loop {
            next = next.iter()
                .flat_map(|n| self.bidirectional(*n, &mut leaks, &mut ctrs))
                .collect();
            if empty_twice {
                break;
            } else if next.is_empty() {
                next = self.0.0.node_indices().collect();
                empty_twice = true;
            }
        }
        return (leaks, ctrs);
    }

    /// Check if an edge leads to a verifier state or public argument
    pub fn is_public_edge<'a>(&'a self, e: &EdgeReference<'a, Dep>, dir: Direction) -> bool {
        match dir {
            Direction::Incoming => self.is_public_node(e.source(), e.weight().get_var()),
            Direction::Outgoing => self.is_public_node(e.target(), e.weight().get_var()),
        }
    }

    pub fn is_public_node(&self, n: NodeIndex, var: Option<Vid>) -> bool {
        match &self.0.0[n] {
            Node::Op(_, Principal::Verifier) => true,
            Node::Transcr(_, Principal::Verifier) => true,
            Node::Inp(_, sig) =>
                if let Some(var) = var {
                    sig.get(&var)
                        .map(|(q, _)| q.is_public())
                        .unwrap()
                } else {
                    true
                },
            _ => false
        }
    }

    /// Check if an edge leads to a prover state or private argument
    pub fn is_private_edge<'a>(&'a self, e: &EdgeReference<'a, Dep>, dir: Direction) -> bool {
        !self.is_public_edge(e, dir)
    }

    pub fn is_private_node(&self, n: NodeIndex, var: Option<Vid>) -> bool {
        !self.is_public_node(n, var)
    }

    pub fn publicize(&mut self, node: NodeIndex, var: Option<Vid>, leaks: &mut Vec<Vid>) {
        match self.0.0.node_weight_mut(node).unwrap() {
            Node::Op(_, ann)
            | Node::Transcr(_, ann) =>
                *ann = Principal::Verifier,
            // Let's see if there is a leak
            Node::Inp(_, sig) => {
                if let Some((v, q)) = var.and_then(|v| Some((v.clone(), sig.get(&v)?.0))) {
                    if q.is_private() {
                        // Leak!
                        leaks.push(v)
                    }
                }
            }
        }
    }

    pub fn bidirectional(&mut self, n: NodeIndex, leaks: &mut Vec<Vid>, ctrs: &mut Vec<GtZ>) -> Vec<NodeIndex> {
        self.forwards(n, leaks, ctrs).into_iter()
            .chain(self.backwards(n, leaks, ctrs))
            .collect()
    }

    pub fn forwards(&mut self, n: NodeIndex, leaks: &mut Vec<Vid>, ctrs: &mut Vec<GtZ>) -> Vec<NodeIndex> {
        let immself = self.0.0.clone();
        // Get the incoming edges and separate in public and private edges
        let epub =
            immself
            .edges_directed(n, Direction::Incoming)
            .filter(|e| self.is_public_edge(e, Direction::Incoming) && e.weight().is_data())
            .collect::<Vec<_>>();


        match &immself[n] {
            Node::Op(op, Principal::Prover | Principal::Any) =>
                match op {
                    Op::Underscore(prev, _) if epub.len() > 0 => {
                        self.publicize(n, None, leaks);
                        vec![*prev]
                    },
                    Op::Var(v, prev, _) if epub.len() > 0 => {
                        self.publicize(n, Some(v.clone()), leaks);
                        self.forwards(n, leaks, ctrs);
                        vec![*prev]
                    },
                    Op::Bin(op, box a, box b, typ) if epub.len() > 1 => {
                        // Two public incoming edges, that means the result is public
                        self.publicize(n, None, leaks);
                        return immself.edges_directed(n, Direction::Outgoing)
                            .filter(|e| self.is_private_edge(e, Direction::Outgoing))
                            .map(|e| e.target())
                            .collect();
                    },
                    op => vec![]
                }
            _ => vec![]
        }
    }

    pub fn get_constr(&self, dep: Dep, node: NodeIndex) -> GtZ {
        match self.0.0[node] {
            Node::Inp(_, _) => GtZ::Var(dep.get_var().unwrap()),
            _ => GtZ::node(node)
        }
    }

    /// Invert an operation
    pub fn backwards(&mut self, n: NodeIndex, leaks: &mut Vec<Vid>, ctrs: &mut Vec<GtZ>) -> Vec<NodeIndex> {
        let immself = self.0.0.clone();

        // Get the incoming edges and separate in public and private edges
        let epub =
            immself
            .edges_directed(n, Direction::Incoming)
            .filter(|e| self.is_public_edge(e, Direction::Incoming) && e.weight().is_data())
            .collect::<Vec<_>>();


        let epriv =
            immself
            .edges_directed(n, Direction::Incoming)
            .filter(|e| self.is_private_edge(e, Direction::Incoming))
            .collect::<Vec<_>>();

        match &immself[n] {
            Node::Op(op, Principal::Verifier) | Node::Transcr(op, _) =>
                match op {
                    Op::Underscore(n, _) if epriv.len() > 0 => {
                        self.publicize(*n, None, leaks);
                        vec![*n]
                    },
                    Op::Var(v, n, _) if epriv.len() > 0 => {
                        self.publicize(*n, Some(v.clone()), leaks);
                        vec![*n]
                    },
                    Op::Bin(op, box a, box b, typ) if epriv.len() == epub.len() => {
                        // Must be exactly one public and one private incoming edge

                        let epub = epub[0];
                        let epriv = epriv[0];

                        match op {
                            BinOp::Add | BinOp::Sub | BinOp::Equ => {
                                self.publicize(epriv.source(), epriv.weight().get_var(), leaks);
                            },
                            BinOp::Mul => {
                                // TODO: Add exceptions for group * scalar multiplication which is
                                // computationally hard to invert
                                // Add a constraint that pub * priv is invertible if only pub > 0
                                ctrs.push(self.get_constr(epub.weight().clone(), epub.source()));
                                self.publicize(epriv.source(), epriv.weight().get_var(), leaks);
                            },
                            _ => {}
                        };
                        // Next inversions will be the sources of the ones inverted here
                        immself.edges_directed(epriv.source(), Direction::Outgoing)
                            .filter(|e| self.is_private_edge(e, Direction::Outgoing))
                            .map(|e| e.target())
                            .collect()
                    },
                    _ => vec![]
                },
            Node::Op(_, Principal::Prover | Principal::Any) => vec![],
            Node::Inp(_, _) => vec![]
        }
    }
}

/// Principal basic trait implementations
impl Default for Principal {
    fn default() -> Self {
        Principal::Any
    }
}

impl<'a, D, A> Pretty<'a, D, A> for Principal
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        match self {
            Principal::Prover => allocator.text("Prover"),
            Principal::Verifier => allocator.text("Verifier"),
            Principal::Any => allocator.text("Any"),
        }
    }
    fn is_nil(&self) -> bool {
        false
    }
}

impl<'a> fmt::Display for Principal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Principal as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(20, f)
    }
}

impl<'a> fmt::Display for GtZ {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            GtZ::Node(n) => write!(f, "Node({}) > 0", n.index()),
            GtZ::Var(v) => write!(f, "Var({}) > 0", v),
        }
    }
}
#[cfg(test)] use share::unwrap;
#[cfg(test)] use lang::ast::UModule;
#[cfg(test)] use backend::ArkBls12_381;
#[test]
fn principal_foo() {
    let ex = r#"
        proto foo<F: Field>(private s: F, private s': F) where s == s {
            let r = random<F>;
            c <- challenge<F>;
            a <- r + s;
            b <- r + s';
            verify(b == b);
        }"#;
    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    println!("{}", m);
    let g = unwrap!(UDag::<ArkBls12_381>::from_module(m));

    // Test zk closure....
    let mut pdag = PrincipalDag::new(&g);
    let (leaks, ctrs) = pdag.invert();

    // Print leaks and constraints
    println!("Leaks: \n{:?}\n", leaks);
    println!("Constraints: \n");
    for c in &ctrs {
        match c {
            GtZ::Node(n) => println!("{} ({})", c, g.0[*n]),
            GtZ::Var(_) => println!("{}", c)
        }
    }
    // Output graph
    pdag.0.write_pdf("graph_foo").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });
}

#[test]
fn principal_bar() {
    let ex = r#"
        proto bar<F: Field>(private s: Fin<0..10>) where s == s {
            let r = random<F>;
            c <- challenge<F>;
            a <- r * s;
            b <- r + s + c;
            verify(a == b);
        }"#;
    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    println!("{}", m);
    let g = unwrap!(UDag::<ArkBls12_381>::from_module(m));

    // Test zk closure....
    let mut pdag = PrincipalDag::new(&g);
    let (leaks, ctrs) = pdag.invert();

    // Print leaks and constraints
    println!("Leaks: \n{:?}\n", leaks);
    println!("Constraints: \n");
    for c in &ctrs {
        match c {
            GtZ::Node(n) => println!("{} ({})", c, g.0[*n]),
            GtZ::Var(_) => println!("{}", c)
        }
    }
    // Output graph
    pdag.0.write_pdf("graph_foo").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });
}
