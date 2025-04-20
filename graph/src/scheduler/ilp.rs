use backend::ArkConfig;
use grb::{attribute::VarDoubleAttr::X, prelude::*};
use grb::expr::GurobiSum;
use grb::ModelSense::Minimize;
use grb::{add_binvar, add_intvar, attr, c, Expr, Model, Status, Var, INFINITY};
use petgraph::algo;
use petgraph::graph::NodeIndex;

use crate::{Dag, UDag, Node};
use crate::scheduler::{TDag, CostModel, Scheduler, ThreadAlloc};

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
pub struct GurobiScheduler<C: ArkConfig, CM: CostModel<C>> {
    num_threads: usize,
    _marker: std::marker::PhantomData<CM>,
    _marker2: std::marker::PhantomData<C>
}

impl<C: ArkConfig, CM: CostModel<C>> GurobiScheduler<C, CM> {
    pub fn new(num_threads: usize) -> Self {
        GurobiScheduler { num_threads , _marker: std::marker::PhantomData, _marker2: std::marker::PhantomData }
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

impl<C: ArkConfig, CM: CostModel<C>> Scheduler<C> for GurobiScheduler<C, CM> {
    type CM = CM;
    fn schedule(&self, dag: UDag<C>, cost_model: Self::CM) -> TDag<C> {
        // Create cost map from the DAG
        let mut cost_map: Vec<Vec<f64>> = vec![vec![0.0; self.num_threads]; dag.node_count()];
        for i in dag.node_indices() {
            for j in 0..self.num_threads {
                cost_map[i.index()][j] =
                    match &dag.0[i] {
                        Node::Inp(_, _) => 0.0,
                        Node::Op(op, _)
                        | Node::Transcr(op, _) => cost_model.cost(&op, j + 1).0,
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

        // Call Gurobi and solve the ILP problem
        let lp_solution = self.solve_for_exec_time(dag.node_count(), cost_map, flow_map);

        // Extract the task thread map from the LP solution
        let mut output = vec![Vec::new(); dag.node_count()];
        for i in 0..dag.node_count() {
            for j in 0..self.num_threads {
                if lp_solution.maping[i][j] {
                    output[i].push(j);
                }
            }
        }
        Dag(
            dag.0.map(
                |a, n| n.with_annotation(ThreadAlloc(output[a.index()].clone())),
                |_, e| e.clone(),
            )
        )
    }
}

#[cfg(test)] use lang::ast::UModule;
#[cfg(test)] use share::{Ctx, unwrap};
#[cfg(test)] use backend::ArkBls12_381;
#[cfg(test)] use crate::scheduler::AsymptoticCost;
#[test]
fn gurobi_e2e() {
    let ex =
      r#"fn test<F: Field>(private a: [F; 20]) -> F {
       let r = random<F>;
       (r * a) . (r * a)
      }"#;

    let solver = GurobiScheduler::new(4);

    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    let g = unwrap!(UDag::<ArkBls12_381>::from_module(m));

    let cost_model = AsymptoticCost::new();
    g.map_annotations(|op, _|
        (1..5).map(|i| (i, cost_model.cost(op, i))).collect::<Ctx<_, _>>()
    ).write_pdf("ilp_test").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });

    let tg = solver.schedule(g, cost_model);
    tg.write_pdf("scheduler_test").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });
}
