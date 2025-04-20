use backend::ArkConfig;
use grb::{attribute::VarDoubleAttr::X, prelude::*};
use grb::expr::GurobiSum;
use grb::ModelSense::Minimize;
use grb::{add_binvar, add_intvar, attr, c, Expr, Model, Status, Var, INFINITY};
use petgraph::algo;
use petgraph::graph::NodeIndex;
use log::debug;

use crate::scheduler::cost::Cost;
use crate::Dag;
use crate::scheduler::{CDag, TDag, ThreadAlloc, Scheduler};
use crate::lang::types::Nothing;

#[derive(Debug)]
struct LpSolution {
    pub start_times: Vec<f64>,
    pub finish_times: Vec<f64>,
    pub durations: Vec<f64>,
    pub cores: Vec<Vec<bool>>,
    pub maping: Vec<Vec<bool>>,
    pub max_finish_time: f64
}

/// Use Gurobi ILP solver to schedule num_tasks in num_threads
pub struct GurobiRuntimeSolver {
    num_threads: usize
}

impl GurobiRuntimeSolver {
    pub fn new(num_threads: usize) -> Self {
        GurobiRuntimeSolver { num_threads }
    }

    pub fn default() -> Self {
        let num_threads: usize = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(1);
        Self::new(num_threads)
    }

    pub fn num_threads(&self) -> usize {
        self.num_threads
    }

    /// Solve the ILP problem for the execution time using Gurobi ILP solver
    fn solve_for_exec_time(
        &self,
        num_tasks: usize,
        cost_map: Vec<Vec<f64>>,
        flow_map: Vec<Vec<bool>>,
    ) -> LpSolution {
        let mut model: Model = Model::new("zippel").unwrap();
        // TODO: compute the maximum big_m for each zippel file
        let big_m: f64 = 10000000.0;
        let cores_mat_var: Vec<Vec<Var>> = (0..num_tasks)
            .map(|_| {
                (0..self.num_threads)
                    .map(|_| add_binvar!(model).unwrap())
                    .collect()
            })
            .collect();

        let map_mat_var: Vec<Vec<Var>> = (0..num_tasks)
            .map(|_| {
                (0..self.num_threads)
                    .map(|_| add_binvar!(model).unwrap())
                    .collect()
            })
            .collect();

        let duration_vec_var: Vec<Var> = (0..num_tasks)
            .map(|_| add_intvar!(model, bounds: 0..).unwrap())
            .collect();

        let start_vec_var: Vec<Var> = (0..num_tasks)
            .map(|_| add_intvar!(model, bounds: 0..).unwrap())
            .collect();

        let finish_vec_var: Vec<Var> = (0..num_tasks)
            .map(|_| add_intvar!(model, bounds: 0..).unwrap())
            .collect();

        let max_finish_var: Var = add_intvar!(model, bounds: 0..).unwrap();

        for i in 0..num_tasks {
            model
                .add_constr(
                    &format!("c{:?}", i),
                    c!(&max_finish_var >= &finish_vec_var[i]),
                )
                .unwrap();
        }

        for i in 0..num_tasks {
            model
                .add_constr(
                    &format!("d{:?}", i),
                    c!(cores_mat_var[i].iter().grb_sum() == 1),
                )
                .unwrap();
        }

        for i in 0..num_tasks {
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

        for i in 0..num_tasks {
            model
                .add_constr(
                    &format!("f{:?}", i),
                    c!(duration_vec_var[i]
                        == cores_mat_var[i]
                            .iter()
                            .zip(cost_map[i].iter())
                            .fold(Expr::default(), |acc, (&core, &time)| { acc + core * time })),
                )
                .unwrap();
        }

        for i in 0..num_tasks {
            model
                .add_constr(
                    &format!("g{:?}", i),
                    c!(finish_vec_var[i] == start_vec_var[i] + duration_vec_var[i]),
                )
                .unwrap();
        }

        for i1 in 0..num_tasks {
            for i2 in 0..num_tasks {
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
                    if flow_map[i1][i2] == true {
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

        let cores_lpunit: Vec<Vec<f64>> = cores_mat_var
            .iter()
            .map(|v| model.get_obj_attr_batch(attr::X, v.clone()).unwrap())
            .collect();
        let mut cores_binary: Vec<Vec<bool>> = Vec::new();
        for core_vec in cores_lpunit {
            let mut core_vec_binary: Vec<bool> = Vec::new();
            for core in core_vec {
                core_vec_binary.push(core != 0 as f64);
            }
            cores_binary.push(core_vec_binary);
        }

        let cores_lpunit: Vec<Vec<f64>> = cores_mat_var
            .iter()
            .map(|v| model.get_obj_attr_batch(attr::X, v.clone()).unwrap())
            .collect();
        let mut cores_binary: Vec<Vec<bool>> = Vec::new();
        for core_vec in cores_lpunit {
            let mut core_vec_binary: Vec<bool> = Vec::new();
            for core in core_vec {
                core_vec_binary.push(core != 0 as f64);
            }
            cores_binary.push(core_vec_binary);
        }

        let map_lpunit: Vec<Vec<f64>> = map_mat_var
            .iter()
            .map(|v| model.get_obj_attr_batch(attr::X, v.clone()).unwrap())
            .collect();
        debug!("mapings: {:?}", map_lpunit);

        let mut map_binary: Vec<Vec<bool>> = Vec::new();
        for map_vec in map_lpunit {
            let mut map_vec_binary: Vec<bool> = Vec::new();
            for map in map_vec {
                map_vec_binary.push(map != 0 as f64);
            }
            map_binary.push(map_vec_binary);
        }

        LpSolution {
            start_times: model.get_obj_attr_batch(attr::X, start_vec_var).unwrap(),
            finish_times: model.get_obj_attr_batch(attr::X, finish_vec_var).unwrap(),
            durations: model.get_obj_attr_batch(attr::X, duration_vec_var).unwrap(),
            cores: cores_binary,
            maping: map_binary,
            max_finish_time: model.get_obj_attr(attr::X, &max_finish_var).unwrap(),
        }
        // dbg!(model.get_obj_attr(attr::X, &max_finish_var));
        // dbg!(model.get_obj_attr_batch(attr::X, start_vec_var));
        // dbg!(model.get_obj_attr_batch(attr::X, finish_vec_var));
        // dbg!(model.get_obj_attr_batch(attr::X, duration_vec_var));
        // todo!()
    }
}

impl Scheduler for GurobiRuntimeSolver {
    fn schedule<C: ArkConfig>(&self, dag: CDag<C>) -> TDag<C> {
        // Create cost map from the DAG
        let mut cost_map: Vec<Vec<f64>> = vec![vec![0.0; self.num_threads]; dag.num_nodes()];
        for i in 0..dag.num_nodes() {
            for j in 0..self.num_threads {
                cost_map[i][j] = dag
                    .0
                    .node_weight(NodeIndex::new(i))
                    .unwrap()
                    .0
                    .runtime(j + 1);
            }
        }
        debug!("Cost map extracted from the dag: {:?}", cost_map);

        // Create flow map from the DAG
        let mut flow_map: Vec<Vec<bool>> = vec![vec![false; dag.num_nodes()]; dag.num_nodes()];
        for i in 0..dag.num_nodes() {
            for j in 0..dag.num_nodes() {
                if algo::has_path_connecting(&dag.0, NodeIndex::new(i), NodeIndex::new(j), None) && i != j
                {
                    flow_map[i][j] = true;
                }
            }
        }
        debug!("Flow map extracted from the dag: {:?}", flow_map);

        // Call Gurobi and solve the ILP problem
        let lp_solution = self.solve_for_exec_time(dag.num_nodes(), cost_map, flow_map);

        // Extract the task thread map from the LP solution
        let mut output = vec![Vec::new(); dag.num_nodes()];
        for i in 0..dag.num_nodes() {
            for j in 0..self.num_threads {
                if lp_solution.maping[i][j] {
                    output[i].push(j);
                }
            }
        }
        Dag(
            dag.0.map(
                |a, (exp, _)|
                  (exp.clone(), ThreadAlloc(output[a.index()].clone())),
                |_, _| (),
            )
        )
    }
}

#[cfg(test)] use lang::ast::UModule;
#[cfg(test)] use crate::UDag;
#[cfg(test)] use share::unwrap;
#[cfg(test)] use backend::ArkBls12_381;
#[test]
fn test_gurobi_e2e() {
    let ex =
      r#"fn test<F: Field>(a: [F; 20], b: [F; 10]) -> F {
       let x = a . a + b . b;
       r <- random<F>;
       let y = b . b + r;
       (x * y)
      }"#;

    env_logger::builder()
        .filter_level(log::LevelFilter::max())
        .is_test(true)
        .try_init();

    let solver = GurobiRuntimeSolver::default();

    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    let g = unwrap!(UDag::<ArkBls12_381>::from_module(m));

    let tg = solver.schedule(&g);
    tg.write_pdf("scheduler_test").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });
}
