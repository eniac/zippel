use backend::ArkConfig;
use grb::expr::GurobiSum;
use grb::ModelSense::Minimize;
use grb::{add_binvar, add_intvar, attr, c, Expr, Model, Status, Var};
use petgraph::algo;

use crate::{Dag, UDag, Ref, Node, WritePdf};
use crate::scheduler::{TDag, CostModel, Scheduler, ThreadAlloc};
use grb::parameter::DoubleParam;

#[derive(Debug)]
struct LpSolution {
    pub maping: Vec<Vec<bool>>,
}

/// Use Gurobi ILP solver to schedule num_tasks in num_threads
pub struct GurobiScheduler {
    num_threads: usize,
    num_tasks: usize,
    cost_map: Vec<Vec<f64>>,
    miip_gap: f64,
    flow_map: Vec<Vec<bool>>,
}

impl<C: ArkConfig> WritePdf for Dag<C, ThreadAlloc> {
    fn write_pdf<'a, 'b>(&'a self, filename: &'b str) -> std::io::Result<()> {
        self.map_annotations(&|_, a| a.to_string()).write_pdf(filename)
    }
}

impl GurobiScheduler {
    pub fn new_with_system<C: ArkConfig, CM: CostModel<C, Ref>>(dag: &UDag<C>, cost_model: &CM, miip_gap: f64) -> Self {
        let num_threads: usize = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(1);
        Self::new(num_threads - 1, dag, cost_model, miip_gap)
    }

    pub fn new<C: ArkConfig, CM: CostModel<C, Ref>>(num_threads: usize, dag: &UDag<C>, cost_model: &CM, miip_gap: f64) -> Self {
        // Create cost map from the DAG
        let mut cost_map: Vec<Vec<f64>> = vec![vec![0.0; num_threads]; dag.node_count()];
        for i in dag.node_indices() {
            for j in 0..num_threads {
                cost_map[i.index()][j] =
                    match &dag.0[i] {
                        Node::Inp(_, _) | Node::Rel(_, _) => 0.0,
                        Node::Op(op, _)
                        | Node::Transcr(op, _) =>
                            (cost_model.cost(op, j + 1).0 / 100.0).round(), // Round to the nearest integer
                    }
            }
        }
        println!("Cost map extracted from the dag: {:?}", cost_map);

        // Create flow map from the DAG
        let mut flow_map: Vec<Vec<bool>> = vec![vec![false; dag.node_count()]; dag.node_count()];
        for i in dag.node_indices() {
            for j in dag.node_indices() {
                if algo::has_path_connecting(&dag.0, i, j, None) && i != j
                {
                    flow_map[i.index()][j.index()] = true;
                }
            }
        }
        println!("Flow map extracted from the dag: {:?}", flow_map);
        GurobiScheduler { num_threads, num_tasks: dag.node_count(), cost_map, miip_gap, flow_map }
    }

    pub fn default<C: ArkConfig, CM: CostModel<C, Ref>>(dag: &UDag<C>, cost_model: &CM, miip_gap: f64) -> Self {
        let num_threads: usize = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(1);
        Self::new(num_threads, dag, cost_model, miip_gap)
    }

    pub fn num_threads(&self) -> usize {
        self.num_threads
    }

    /// Solve the ILP problem for the execution time using Gurobi ILP solver
    fn optimize_runtime(self, miip_gap: f64) -> LpSolution { 
        let mut model: Model = Model::new("zippel").unwrap();
        model.set_param(DoubleParam::MIPGap, miip_gap).unwrap();
        // TODO: compute the maximum big_m for each zippel file
        let big_m: f64 = 10000000.0;
        let cores_mat_var: Vec<Vec<Var>> = (0..self.num_tasks)
            .map(|_| {
                (0..self.num_threads)
                    .map(|_| add_binvar!(model).unwrap())
                    .collect()
            })
            .collect();

        let map_mat_var: Vec<Vec<Var>> = (0..self.num_tasks)
            .map(|_| {
                (0..self.num_threads)
                    .map(|_| add_binvar!(model).unwrap())
                    .collect()
            })
            .collect();

        let duration_vec_var: Vec<Var> = (0..self.num_tasks)
            .map(|_| add_intvar!(model, bounds: 0..).unwrap())
            .collect();

        let start_vec_var: Vec<Var> = (0..self.num_tasks)
            .map(|_| add_intvar!(model, bounds: 0..).unwrap())
            .collect();

        let finish_vec_var: Vec<Var> = (0..self.num_tasks)
            .map(|_| add_intvar!(model, bounds: 0..).unwrap())
            .collect();

        let max_finish_var: Var = add_intvar!(model, bounds: 0..).unwrap();

        for i in 0..self.num_tasks {
            model
                .add_constr(
                    &format!("c{:?}", i),
                    c!(&max_finish_var >= &finish_vec_var[i]),
                )
                .unwrap();
        }

        for i in 0..self.num_tasks {
            model
                .add_constr(
                    &format!("d{:?}", i),
                    c!(cores_mat_var[i].iter().grb_sum() == 1),
                )
                .unwrap();
        }

        for i in 0..self.num_tasks {
            model
                .add_constr(
                    &format!("e{:?}", i),
                    c!(map_mat_var[i].iter().grb_sum()
                        == cores_mat_var[i]
                            .iter()
                            .enumerate()
                            .map(|(k, cores)| ((k + 1) as f64) * *cores)
                            .grb_sum()),
                )
                .unwrap();
        }

        for i in 0..self.num_tasks {
            model
                .add_constr(
                    &format!("f{:?}", i),
                    c!(duration_vec_var[i]
                        == cores_mat_var[i]
                            .iter()
                            .zip(self.cost_map[i].iter())
                            .fold(Expr::default(), |acc, (&core, &time)| { acc + core * time })),
                )
                .unwrap();
        }

        for i in 0..self.num_tasks {
            model
                .add_constr(
                    &format!("g{:?}", i),
                    c!(finish_vec_var[i] == start_vec_var[i] + duration_vec_var[i]),
                )
                .unwrap();
        }

        for i1 in 0..self.num_tasks {
            for i2 in 0..self.num_tasks {
                if i1 != i2 {
                    for j in 0..self.num_threads {
                        let z1: Var = add_binvar!(model).unwrap();
                        let z2: Var = add_binvar!(model).unwrap();
                        let z3: Var = add_binvar!(model).unwrap();
                        model
                            .add_constr(&format!("h{:?}", i1), c!(z1 + z2 + z3 >= 1))
                            .unwrap();
                        model
                            .add_constr(
                                &format!("i{:?}{:?}{:?}", i1, i2, j),
                                c!(map_mat_var[i1][j] + map_mat_var[i2][j] - (big_m * (1 - z1))
                                    <= 1),
                            )
                            .unwrap();

                        model
                            .add_constr(
                                &format!("j{:?}{:?}{:?}", i1, i2, j),
                                c!(finish_vec_var[i1] - start_vec_var[i2] - (big_m * (1 - z2))
                                    <= 0),
                            )
                            .unwrap();

                        model
                            .add_constr(
                                &format!("k{:?}{:?}{:?}", i1, i2, j),
                                c!(finish_vec_var[i2] - start_vec_var[i1] - (big_m * (1 - z3))
                                    <= 0),
                            )
                            .unwrap();
                    }
                    if self.flow_map[i1][i2] == true {
                        model
                            .add_constr(
                                &format!("l{:?}{:?}", i1, i2),
                                c!(finish_vec_var[i1] <= start_vec_var[i2]),
                            )
                            .unwrap();
                    }
                }
            }
        }

        model.set_objective(max_finish_var, Minimize).unwrap();
        model.optimize().unwrap();
        assert_eq!(model.status().unwrap(), Status::Optimal);


        let map_lpunit: Vec<Vec<f64>> = map_mat_var
            .iter()
            .map(|v| model.get_obj_attr_batch(attr::X, v.clone()).unwrap())
            .collect();
        println!("mapings: {:?}", map_lpunit);

        let mut map_binary: Vec<Vec<bool>> = Vec::new();
        for map_vec in map_lpunit {
            let mut map_vec_binary: Vec<bool> = Vec::new();
            for map in map_vec {
                map_vec_binary.push(map != 0 as f64);
            }
            map_binary.push(map_vec_binary);
        }

        LpSolution {
            maping: map_binary,
        }
        // dbg!(model.get_obj_attr(attr::X, &max_finish_var));
        // dbg!(model.get_obj_attr_batch(attr::X, start_vec_var));
        // dbg!(model.get_obj_attr_batch(attr::X, finish_vec_var));
        // dbg!(model.get_obj_attr_batch(attr::X, duration_vec_var));
        // todo!()
    }
}

impl Scheduler for GurobiScheduler {
    fn schedule<C: ArkConfig>(self, dag: UDag<C>) -> TDag<C> {
        let num_threads = self.num_threads;
        let miip_gap = self.miip_gap;

        // Call Gurobi and solve the ILP problem
        let lp_solution = self.optimize_runtime(miip_gap);

        // Extract the task thread map from the LP solution
        let mut output = vec![Vec::new(); dag.node_count()];
        for i in 0..dag.node_count() {
            for j in 0..num_threads {
                if lp_solution.maping[i][j] {
                    output[i].push(j);
                }
            }
        }
        Dag(
            dag.0.map(
                |a, n| n.with_annotation(ThreadAlloc(output[a.index()].len())),
                |_, e| e.clone(),
            )
        )
    }
}

#[cfg(test)] use lang::ast::UModule;
#[cfg(test)] use share::{Ctx, unwrap};
#[cfg(test)] use crate::UDags;
#[cfg(test)] use backend::ArkBls12_381;
#[cfg(test)] use crate::scheduler::AsymptoticCost;
#[ignore = "Gurobi license for CI bot does not work due to HostID"]
#[test]
fn gurobi_e2e() {
    let ex =
      r#"fn test<F: Field>(private a: [F; 20]) -> F {
       let r = random<F>;
       (r * a) . (r * a)
      }"#;


    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

    // AsymptoticCost is a cost model for zippel operations
    let cost_model = AsymptoticCost::new();

    // Pick the first graph
    let g = gs[0].clone();

    // Create a new Gurobi ILP solver
    let solver = GurobiScheduler::new(4, &g, &cost_model, 0.20);

    g.map_annotations(&|op, _|
        (1..5).map(|i| format!("{}: {}", i, cost_model.cost(op, i)))
        .collect::<Vec<_>>()
        .join(", ")
    ).write_pdf("ilp_test").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });

    // Run the gurobi solver
    let tg = solver.schedule(g);

    tg.write_pdf("scheduler_test").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });
}
