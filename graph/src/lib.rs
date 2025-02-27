mod node;
mod edge;
mod principal;

pub use node::{Op, Node};
pub use edge::{Dependency, Edge};

use share::{Pretty, BoxAllocator};
use lang::exp::{TAExp, TBExp, TExp};
use lang::id::{Vid, Fid};
use lang::module::TModule;
use thiserror::Error;
use petgraph::{dot::Dot, graph::NodeIndex, Direction, Graph};
use std::process::Command;

/// Represents graphs in the Zippel language
/// graph intermediate representation (Graph IR)
/// It is parameterized by types `A` representing a
/// node annotation like costs, schedules etc.
pub struct Dag<A>(pub Graph<Node<A>, Edge>);

impl<A> Dag<A> {
    /// Get the number of nodes in the graph
    pub fn node_count(&self) -> usize {
        self.0.node_count()
    }

    /// Edge deduplication
    fn add_edge(&mut self, source: NodeIndex, sink: NodeIndex, edge: Edge) {
        self.0.update_edge(source, sink, edge);
    }

    /// Write graph to PDF
    pub fn write_pdf<'a>(&self, filename: &str) -> std::io::Result<()>
    where
        A: Clone + Pretty<'a, BoxAllocator, ()>,
    {
        // Write graphviz file
        let fdot: String = format!("{}.dot", filename.to_string());
        // Create graphviz object
        let graphviz =  Dot::with_attr_getters(
                &self.0,
                &[],
                &|_, e|
                        match e.weight().dep {
                            Dependency::Data => "[color = \"black\"]",
                            Dependency::Transcript => "[color = \"red\"]",
                            Dependency::Implicit => "[color = \"blue\"]"
                        }.to_string(),
                &|_, _| String::new()
            );

        // Write to file
        std::fs::write(fdot.clone(), graphviz.to_string())?;
        let fpdf: String = format!("{}.pdf", filename.to_string());

        // Convert to pdf
        Command::new("dot")
            .arg("-Tpdf")
            .arg(fdot.clone())
            .arg("-o")
            .arg(fpdf.clone())
            .spawn()
            .expect("[dot] CLI failed to convert DAG to [pdf] file")
            .wait()?;

        // Remove DOT file
        std::fs::remove_file(fdot)?;

        // Print success
        println!("Wrote {}.pdf", filename);
        Ok(())
    }

    fn add_init(&mut self, fid: &Fid, args: &Args) -> NodeIndex {
        let node = Node::Init(fid.clone(), args.clone());
        self.0.add_node(node)
    }
}

#[derive(Error, PartialEq, Debug)]
pub enum DepError {
    #[error("Variable not found {0}")]
    VarNotFound(Vid),
    #[error("Function not found {0}")]
    FuncNotFound(Fid),
    #[error("Protocol {0} cannot be called here")]
    ProtoNotCallable(Fid),
    #[error("Function {0} cannot be called here")]
    FuncNotCallable(Fid),
    #[error("Cannot infer structural recursive argument for {0}")]
    FuncRecArg(Fid),
    #[error("Duplicate argument name {0} in function {1}")]
    DuplicateArg(Vid, Fid),
}

impl DepError {
    pub fn duplicate_arg(arg: &Arg, fid: &Fid) -> Self {
        DepError::DuplicateArg(arg.clone(), fid.clone())
    }
}

impl Dag<TExp> {
    fn find_exp(&self, exp: &TExp) -> Option<NodeIndex> {
        self.0.node_indices().find(|i| &self.0[*i].ann == exp)
    }

    fn add_module(&mut self, m: &TModule) -> Result<(), DepError> {
        // For every declaration, add it to the graph
        for ((fid, args), decl) in m.0 {

            // Initialize new variable-to-node context
            let mut vars = Ctx::new();

            // Add the arguments to the graph as [Node::Init]
            let n = dag.add_init(&fid, &args);

            // Add arguments to variable context pointing, to [Init] node [n]
            for arg in args {
                vars.insert_with(arg.id, n, &mut |_, _| Err(DepError::duplicate_arg(&arg.id, &fid)))?;
            }

            // Add function body to Graph
            self.add_decl(m, &mut vars, n, decl)?;
        }
    }

    fn add_decl(&mut self, m: &TModule, vars: &mut Ctx<Vid, NodeIndex>, n: NodeIndex, decl: &Decl) -> Result<(), DepError> {

                         let node = Node::Var(v);
                let v = dag.0.add_node(node);
                dag.add_edge(n, v, Edge {
                    var: Some(v),
                    non_zero: vec![],
                    dep: Dependency::Data
                });
            }

        let mut dag = Dag(Graph::new());
        let mut vars = Ctx::new();
        for (fid, f) in m.funcs.iter() {
            let fnode = dag.add_func(m, vars, fid, f)?;
            for (aid, a) in f.args.iter() {
                let anode = dag.add_aexp(m, vars, a)?;
                dag.add_edge(fnode, anode, Edge {
                    var: None,
                    non_zero: vec![],
                    dep: Dependency::Data
                });
            }
            let rnode = dag.add_aexp(m, vars, &f.ret)?;
            dag.add_edge(fnode, rnode, Edge {
                var: None,
                non_zero: vec![],
                dep: Dependency::Data
            });
        }
        Ok(dag)
    }
    fn add_aexp(&mut self, m: &TModule, vars: &mut Ctx<Vid, NodeIndex>, aexp: &TAExp) -> NodeIndex {
        match aexp {
            TAExp::Var(v) => {
                let node = Node::Var(v.clone());
                self.0.add_node(node)
            }
        let node = Node::AExp(aexp);
        self.0.add_node(node)
    }
}

