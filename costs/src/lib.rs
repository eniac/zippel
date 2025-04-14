pub mod bench_info;

// Import all the curves
use ark_bls12_377::Bls12_377;
use ark_bls12_381::Bls12_381;
use ark_bn254::Bn254;
use ark_bw6_761::BW6_761;
use ark_bw6_767::BW6_767;
use ark_cp6_782::CP6_782;
use ark_ec::pairing::Pairing;
use ark_ff::UniformRand;
use ark_ff::batch_inversion;
use ark_mnt4_298::MNT4_298;
use ark_mnt4_753::MNT4_753;
use ark_mnt6_298::MNT6_298;
use ark_mnt6_753::MNT6_753;

use bench_info::BenchEntry;
use bench_info::BenchParameters;
use bench_info::BenchedTask;
use bench_info::BenchmarkResult;
use bench_info::Curve;
use bench_info::RawBenchmark;
use bench_info::TaskLoad;
//////////////////////////////////////////
use criterion::Criterion;
use criterion::SamplingMode;
use rayon::ThreadPoolBuilder;
use std::collections::HashMap;
use std::fs;
use std::str::FromStr;
use std::time::Duration;
use strum::IntoEnumIterator;
use walkdir::WalkDir;

pub struct Benchmarker {
    num_available_threads: usize,
    criterion: Criterion,
    bench_dir: String,
}

impl Benchmarker {
    pub fn build_bench_entries(&self) -> Vec<BenchEntry> {
        Curve::iter()
            .zip(1..self.num_available_threads)
            .flat_map(|(curve, num_threads)| {
                //////////////// Binary Tasks ////////////////
                let mut entries: Vec<BenchEntry> =
                    [BenchedTask::FAddition, BenchedTask::FMultiplication]
                        .iter()
                        .map(move |task| BenchEntry {
                            task: *task,
                            parameters: BenchParameters {
                                num_threads,
                                curve,
                                input_size: 2,
                            },
                        })
                        .collect();

                // Extend with FInversion tasks
                entries.extend((1..=3).map(move |exp| BenchEntry {
                    task: BenchedTask::FInversion,
                    parameters: BenchParameters {
                        num_threads,
                        curve,
                        input_size: 1 << exp,
                    },
                }));

                entries
            })
            .collect()
    }

    pub fn with_criterion(c: Criterion) -> Self {
        Self {
            criterion: c,
            num_available_threads: rayon::current_num_threads(),
            bench_dir: "../target/criterion".to_string(),
        }
    }

    pub fn run_benches(&mut self) {
        for bench_entry in self.build_bench_entries() {
            match bench_entry.parameters.curve {
                Curve::Bls12_381 => self.bench_field_with_curve::<Bls12_381>(&bench_entry),
                Curve::Bls12_377 => self.bench_field_with_curve::<Bls12_377>(&bench_entry),
                Curve::Mnt4_298 => self.bench_field_with_curve::<MNT4_298>(&bench_entry),
                Curve::Mnt4_753 => self.bench_field_with_curve::<MNT4_753>(&bench_entry),
                Curve::Mnt6_298 => self.bench_field_with_curve::<MNT6_298>(&bench_entry),
                Curve::Mnt6_753 => self.bench_field_with_curve::<MNT6_753>(&bench_entry),
                Curve::Bw6_761 => self.bench_field_with_curve::<BW6_761>(&bench_entry),
                Curve::Bw6_767 => self.bench_field_with_curve::<BW6_767>(&bench_entry),
                Curve::Cp6_782 => self.bench_field_with_curve::<CP6_782>(&bench_entry),
                Curve::Bn254 => self.bench_field_with_curve::<Bn254>(&bench_entry),
            }
        }
    }

    pub fn load_from_criterion(&self) -> HashMap<BenchEntry, BenchmarkResult> {
        let mut cost_map = HashMap::new();
        for entry in WalkDir::new(&self.bench_dir)
            .into_iter()
            .filter_map(Result::ok)
            .filter(|e| e.file_type().is_dir() && e.path().ends_with("new"))
        {
            let benchmark_path = entry.path().join("benchmark.json");
            let estimates_path = entry.path().join("estimates.json");

            let benchmark_contents = fs::read_to_string(&benchmark_path).unwrap();
            let estimates_contents = fs::read_to_string(&estimates_path).unwrap();
            let bench_results =
                serde_json::from_str::<BenchmarkResult>(&estimates_contents).unwrap();
            let raw: RawBenchmark = serde_json::from_str(&benchmark_contents).unwrap();
            let task = BenchedTask::from_str(&raw.group_id).unwrap();
            let bench_param: BenchParameters = BenchParameters::from_str(&raw.function_id).unwrap();
            let bench_entry: BenchEntry = BenchEntry {
                task,
                parameters: bench_param,
            };
            cost_map.insert(bench_entry, bench_results);
        }
        cost_map
    }

    pub fn bench_field_with_curve<E: Pairing>(&mut self, bench_entry: &BenchEntry) {
        let pool = ThreadPoolBuilder::new()
            .num_threads(bench_entry.parameters.num_threads)
            .build()
            .unwrap();

        let mut bench_group = self.criterion.benchmark_group(bench_entry.task.to_string());

        match bench_entry.task.load() {
            TaskLoad::Light => {
                bench_group
                    .sample_size(100)
                    .measurement_time(Duration::from_secs(1))
                    .sampling_mode(SamplingMode::Flat);
            }
            TaskLoad::Medium => {
                bench_group
                    .sample_size(10)
                    .measurement_time(Duration::from_secs(1))
                    .sampling_mode(SamplingMode::Flat);
            }
            TaskLoad::Heavy => {
                bench_group
                    .sample_size(1)
                    .measurement_time(Duration::from_secs(1))
                    .sampling_mode(SamplingMode::Flat);
            }
        }

        match bench_entry.task {
            BenchedTask::FAddition => {
                bench_group.bench_function(bench_entry.parameters.to_string(), |b| {
                    b.iter_batched(
                        || Self::rand_input::<E::ScalarField>(bench_entry.parameters.input_size),
                        |input| {
                            pool.install(|| {
                                let _ = input[0] + input[1];
                            })
                        },
                        criterion::BatchSize::SmallInput,
                    )
                });
            }

            BenchedTask::FMultiplication => {
                bench_group.bench_function(bench_entry.parameters.to_string(), |b| {
                    b.iter_batched(
                        || Self::rand_input::<E::ScalarField>(bench_entry.parameters.input_size),
                        |input| {
                            pool.install(|| {
                                let _ = input[0] * input[1];
                            })
                        },
                        criterion::BatchSize::SmallInput,
                    )
                });
            }

            BenchedTask::FInversion => {
                bench_group.bench_function(bench_entry.parameters.to_string(), |b| {
                    b.iter_batched(
                        || Self::rand_input::<E::ScalarField>(bench_entry.parameters.input_size),
                        |mut input| {
                            pool.install(|| {
                                batch_inversion(&mut input);
                            })
                        },
                        criterion::BatchSize::SmallInput,
                    )
                });
            }

            BenchedTask::G1Addition => {
                bench_group.bench_function(bench_entry.parameters.to_string(), |b| {
                    b.iter_batched(
                        || Self::rand_input::<E::G1>(bench_entry.parameters.input_size),
                        |input| {
                            pool.install(|| {
                                let _ = input[0] + input[1];
                            })
                        },
                        criterion::BatchSize::SmallInput,
                    )
                });
            }

            BenchedTask::G2Addition => {
                bench_group.bench_function(bench_entry.parameters.to_string(), |b| {
                    b.iter_batched(
                        || Self::rand_input::<E::G2>(bench_entry.parameters.input_size),
                        |input| {
                            pool.install(|| {
                                let _ = input[0] + input[1];
                            })
                        },
                        criterion::BatchSize::SmallInput,
                    )
                });
            }
        }

        bench_group.finish();
    }

    fn rand_input<F: UniformRand>(size: usize) -> Vec<F> {
        let mut rng = ark_std::test_rng();
        (0..size).map(|_| F::rand(&mut rng)).collect()
    }
}
