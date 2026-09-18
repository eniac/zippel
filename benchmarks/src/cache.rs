//! On-disk cache for SRS-style setup artifacts.
//!
//! Every system's prove/verify-key generation depends only on (system,
//! log_size, seeded rng) — not on `RAYON_NUM_THREADS` or anything else
//! that changes across thread-sweep iterations. The sweep wrapper
//! restarts the binary per thread count so rayon's global pool can be
//! re-pinned, but re-running keygen each time wastes hours at log_size=20
//! (groth16 / pari / kzg keygens are minutes apiece).
//!
//! `load_or_build_canonical` (for arkworks types) and
//! `load_or_build_bincode` (for libspartan / serde types) check
//! `artifacts/<name>_log<n>.bin`: hit → deserialize and return, miss →
//! invoke `build`, serialize, then return. Either way the call happens
//! OUTSIDE the timed region (callers wrap setup phase in
//! `setup_pool().install`), so cache I/O never enters a measured
//! number.
//!
//! Override the directory with `BENCH_ARTIFACTS_DIR`; default is
//! `./artifacts` relative to the cwd of `bench_all` (= repo root when
//! invoked via `run_all.sh`).

use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, Validate};
use std::fs::File;
use std::io::{BufReader, Read, Write};
use std::path::PathBuf;

/// Directory that setup artifacts are cached in, creating it if needed.
///
/// Reads `BENCH_ARTIFACTS_DIR`, defaulting to `artifacts` relative to the
/// current working directory. Directory-creation failures are swallowed —
/// a missing directory simply turns every later cache probe into a miss
/// plus a failed write, which surfaces at the call site instead.
pub fn artifacts_dir() -> PathBuf {
    let dir = std::env::var("BENCH_ARTIFACTS_DIR").unwrap_or_else(|_| "artifacts".to_string());
    let path = PathBuf::from(dir);
    std::fs::create_dir_all(&path).ok();
    path
}

/// Path of the cache entry for `name` at the given `log_size`, of the form
/// `<artifacts_dir>/<name>_log<log_size>.bin`.
///
/// `log_size` is part of the key because every cached artifact (SRS,
/// universal parameters, committer keys, generated witnesses) is sized by
/// the sweep's log-size parameter.
pub fn artifact_path(name: &str, log_size: usize) -> PathBuf {
    artifacts_dir().join(format!("{name}_log{log_size}.bin"))
}

/// Load `T` from `artifacts/<name>_log<log_size>.bin` if present;
/// otherwise call `build`, save the result, and return it. `T` uses
/// arkworks `CanonicalSerialize` / `CanonicalDeserialize` (compressed
/// encoding, no validation — these are our own outputs, no need to
/// re-validate point subgroups).
pub fn load_or_build_canonical<T>(name: &str, log_size: usize, build: impl FnOnce() -> T) -> T
where
    T: CanonicalSerialize + CanonicalDeserialize,
{
    let path = artifact_path(name, log_size);
    if path.exists() {
        eprintln!("  [cache hit ] {}", path.display());
        let f = File::open(&path).expect("open artifact");
        let mut reader = BufReader::new(f);
        let mut bytes = Vec::new();
        reader.read_to_end(&mut bytes).expect("read artifact");
        return T::deserialize_with_mode(&bytes[..], Compress::Yes, Validate::No)
            .expect("deserialize artifact");
    }
    eprintln!(
        "  [cache miss] building {} (rayon threads = {})",
        path.display(),
        rayon::current_num_threads()
    );
    let t = build();
    let mut bytes = Vec::with_capacity(1 << 16);
    t.serialize_with_mode(&mut bytes, Compress::Yes)
        .expect("serialize artifact");
    let mut f = File::create(&path).expect("create artifact");
    f.write_all(&bytes).expect("write artifact");
    f.sync_all().ok();
    t
}

/// Bincode/serde variant for libspartan types that don't implement
/// arkworks' canonical traits (Instance, Assignment, NIZKGens).
pub fn load_or_build_bincode<T>(name: &str, log_size: usize, build: impl FnOnce() -> T) -> T
where
    T: serde::Serialize + serde::de::DeserializeOwned,
{
    let path = artifact_path(name, log_size);
    if path.exists() {
        eprintln!("  [cache hit ] {}", path.display());
        let bytes = std::fs::read(&path).expect("read artifact");
        return bincode::deserialize(&bytes).expect("deserialize artifact (bincode)");
    }
    eprintln!("  [cache miss] building {}", path.display());
    let t = build();
    let bytes = bincode::serialize(&t).expect("serialize artifact (bincode)");
    std::fs::write(&path, &bytes).expect("write artifact");
    t
}
