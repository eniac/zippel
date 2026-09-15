//! GB snapshot tests: `completeness::*` and `soundness::*` trials assert
//! the actual analysis passes (`CompletenessAnalysis::run` /
//! `SpecialSoundnessAnalysis::run`) and, on success, snapshot the computed
//! Gröbner basis for regression detection. `knowledge::*` trials only
//! snapshot the basis — see `knowledge::trials` for why that group is
//! always ignored.
//!
//! The test harness always uses Singular for GB computation. If Singular
//! is not on `PATH`, the test prints a warning and passes (skips the GB
//! computation). This allows local development without Singular, while CI
//! installs Singular explicitly.
//!
//! When `INSTA_UPDATE` is set (snapshot regeneration mode), Singular is
//! always used. If Singular is not on `PATH` during regeneration, the test
//! prints a warning and passes without updating.
//!
//! To (re)generate snapshots:
//! ```sh
//! INSTA_UPDATE=always cargo test -p analyses --test gb_snapshots
//! ```
//! To verify in CI (Singular required for meaningful verification):
//! ```sh
//! cargo test -p analyses --test gb_snapshots
//! ```
//!
//! Adding a new analysis to this suite: add a `<analysis>.rs` module with
//! its own entry list/struct, a `run_<analysis>_snapshot` function, and a
//! `trials()` builder (`completeness.rs` and `soundness.rs` are the
//! templates — `knowledge.rs` shows how to reuse another module's entry
//! list instead of defining its own), then wire `trials()` into `main()`
//! below.

mod common;
mod completeness;
mod knowledge;
mod soundness;

fn main() {
    // If Singular is missing, force-ignore all trials and warn once up
    // front — test trial output is captured by the harness and would
    // hide per-test warnings.
    let singular_ok = common::singular();
    if !singular_ok {
        eprintln!(
            "WARNING: Singular is not on PATH — GB snapshot tests will be \
             skipped (ignored). Install Singular to run them."
        );
    }
    let force_ignored = !singular_ok;

    let mut trials = Vec::new();
    trials.extend(completeness::trials(force_ignored));
    trials.extend(knowledge::trials());
    trials.extend(soundness::trials(force_ignored));

    libtest_mimic::run(&libtest_mimic::Arguments::from_args(), trials).exit();
}
