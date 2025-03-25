use costs::Benchmarker;
use criterion::{BenchmarkId, Criterion};
use std::{fs::{self, File}, io::Write, path::Path};
use walkdir::WalkDir;
fn main() {
    // // You can call your benchmark function directly from anywhere
    let criterion = Criterion::default().with_output_color(true);
    let mut benchmarker = Benchmarker::with_criterion(criterion);
    // benchmarker.run_benches();
    let cost_map = benchmarker.load_from_criterion();
    let json = serde_json::to_string_pretty(&cost_map).unwrap();
    let mut file = File::create("map_output.json").unwrap();
    file.write_all(json.as_bytes()).unwrap();
}
