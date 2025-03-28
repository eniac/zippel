use core::fmt;
use std::str::FromStr;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use strum_macros::{Display, EnumIter, EnumString};

#[derive(Debug, Deserialize, Serialize)]
pub struct BenchmarkResult {
    pub mean: Estimate,
    pub median: Estimate,
    pub median_abs_dev: Estimate,
    pub slope: Option<Estimate>,
    pub std_dev: Estimate,
}

#[derive(Debug, Deserialize, Serialize)]
pub struct Estimate {
    pub point_estimate: f64,
    pub standard_error: f64,
    pub confidence_interval: ConfidenceInterval,
}

#[derive(Debug, Deserialize, Serialize)]
pub struct ConfidenceInterval {
    pub confidence_level: f64,
    pub lower_bound: f64,
    pub upper_bound: f64,
}

#[derive(serde::Deserialize, Debug, Serialize)]
pub struct RawBenchmark {
    pub group_id: String,
    pub function_id: String,
    // other fields are ignored
}

#[allow(non_camel_case_types)]
#[derive(EnumIter, EnumString, Debug, Clone, Copy, Hash, Eq, PartialEq, Display)]
pub enum Curve {
    Bls12_381,
    Bls12_377,
    Bn254,
    Bw6_761,
    Bw6_767,
    Cp6_782,
    Mnt4_298,
    Mnt4_753,
    Mnt6_753,
    Mnt6_298,
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub struct BenchParameters {
    pub num_threads: usize,
    pub curve: Curve,
    pub input_size: usize,
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub struct BenchEntry {
    pub task: BenchedTask,
    pub parameters: BenchParameters,
}

/*
 *
Replace BenchEntry with the following:

type DynType = Typ<ZippelType, usize>;

Map<(Op<DynType, ZippelType>, usize), f64> // Bench

Map::from([
    ((Op::Bin(BinOp::Add, Typ::Base(ZippelType::Curve25519_Field), Typ::Base(ZippelType::Curve25519_Field)), 1) -> 128.0),
    ((Op::challenge(ZippelType::Curve25519_Field) -> 1.0),

*/

#[derive(EnumIter, EnumString, Debug, Clone, Copy, Hash, Eq, PartialEq, Display)]
pub enum BenchedTask {
    FAddition,
    FMultiplication,
    FInversion,
    G1Addition,
    G2Addition,
}
impl BenchedTask {
    pub fn load(&self) -> TaskLoad {
        match self {
            BenchedTask::FAddition => TaskLoad::Light,
            BenchedTask::FMultiplication => TaskLoad::Light,
            BenchedTask::FInversion => TaskLoad::Medium,
            BenchedTask::G1Addition => TaskLoad::Light,
            BenchedTask::G2Addition => TaskLoad::Light,
        }
    }
}

pub enum TaskLoad {
    Light,
    Medium,
    Heavy,
}

impl fmt::Display for BenchParameters {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}:{}", self.num_threads, self.curve, self.input_size)
    }
}

impl fmt::Display for BenchEntry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.task, self.parameters)
    }
}

impl FromStr for BenchParameters {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let parts: Vec<&str> = s.split(':').collect();
        if parts.len() != 3 {
            return Err("Expected exactly 3 parts".to_string());
        }
        Ok(BenchParameters {
            num_threads: parts[0].parse().map_err(|_| "Invalid number of threads")?,
            curve: parts[1].parse().map_err(|_| "Invalid curve")?,
            input_size: parts[2].parse().map_err(|_| "Invalid input size")?,
        })
    }
}

impl Serialize for BenchParameters {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&self.to_string())
    }
}

impl<'de> Deserialize<'de> for BenchParameters {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        BenchParameters::from_str(&s).map_err(serde::de::Error::custom)
    }
}

// Serialize BenchEntry as "Task|Params"
impl Serialize for BenchEntry {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let combined = format!("{}|{}", self.task, self.parameters);
        serializer.serialize_str(&combined)
    }
}

impl<'de> Deserialize<'de> for BenchEntry {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        let parts: Vec<&str> = s.split('|').collect();
        if parts.len() != 2 {
            return Err(serde::de::Error::custom("Expected format Task|Params"));
        }
        Ok(BenchEntry {
            task: parts[0].parse().map_err(serde::de::Error::custom)?,
            parameters: parts[1].parse().map_err(serde::de::Error::custom)?,
        })
    }
}
