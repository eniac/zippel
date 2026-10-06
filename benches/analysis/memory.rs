//! The `--memory-limit-mb` window (see `LIMIT_ACTIVE`) and peak-memory
//! measurement.

use std::io::Write as _;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicBool, Ordering};

/// True while the analysis runs under a memory limit — the
/// memory-constrained window, from `build_inputs` (ideal construction,
/// which alone can exhaust memory, e.g. a `where`-clause grand product)
/// through `run`. Parsing, concretizing and DAG construction before it are
/// unbounded: a failure there is unambiguously a real bug. Read by `main`'s
/// panic catch to decide `"crashed"` (panic outside this window) vs
/// `"oom"` (inside it). Under the limit, running out of memory can also
/// surface as a panic, e.g. a Singular that cannot start or dies trips the
/// backend's `expect`, so the window's panics are all `"oom"`.
static LIMIT_ACTIVE: AtomicBool = AtomicBool::new(false);

/// The final JSON line to print on a hard allocator abort, pre-built (while
/// allocation still works) before the memory limit goes into effect. The
/// allocation-error hook below must not allocate, so this is the only way
/// it can report anything.
static OOM_LINE: OnceLock<Vec<u8>> = OnceLock::new();

/// Whether a memory limit is in effect (see `LIMIT_ACTIVE`).
pub fn limit_active() -> bool {
    LIMIT_ACTIVE.load(Ordering::SeqCst)
}

/// Installs [`oom_alloc_error_hook`].
pub fn install_oom_hook() {
    std::alloc::set_alloc_error_hook(oom_alloc_error_hook);
}

/// Allocation-error hook: writes the pre-built [`OOM_LINE`] (if any) with no
/// further allocation, then aborts — same as the default hook, but leaves a
/// real status line on stdout for `analysis_all` to pick up instead of a
/// silent death.
fn oom_alloc_error_hook(_layout: std::alloc::Layout) {
    if let Some(line) = OOM_LINE.get() {
        let mut out = std::io::stdout();
        let _ = out.write_all(line);
        let _ = out.write_all(b"\n");
        let _ = out.flush();
    }
    std::process::abort();
}

/// Cap the process's virtual address space at `limit_mb` megabytes
/// (`RLIMIT_AS`), inherited by child processes (e.g. Singular). Only
/// lowers the *soft* limit, leaving the hard limit untouched, so it can be
/// raised back via [`restore_memory_limit`] — lowering both would be a
/// one-way ratchet. Returns the previous soft limit on success, `None` if
/// the limit wasn't applied.
#[cfg(unix)]
fn apply_memory_limit(limit_mb: u64) -> Option<u64> {
    let bytes = limit_mb.saturating_mul(1024 * 1024) as libc::rlim_t;

    let mut current = libc::rlimit {
        rlim_cur: 0,
        rlim_max: 0,
    };
    if unsafe { libc::getrlimit(libc::RLIMIT_AS, &raw mut current) } != 0 {
        eprintln!(
            "warning: failed to read current memory limit: {}",
            std::io::Error::last_os_error()
        );
        return None;
    }

    let limit = libc::rlimit {
        rlim_cur: bytes.min(current.rlim_max),
        rlim_max: current.rlim_max,
    };
    if unsafe { libc::setrlimit(libc::RLIMIT_AS, &raw const limit) } == 0 {
        Some(current.rlim_cur)
    } else {
        eprintln!(
            "warning: failed to set {limit_mb} MB memory limit: {}",
            std::io::Error::last_os_error()
        );
        None
    }
}

#[cfg(not(unix))]
fn apply_memory_limit(limit_mb: u64) -> Option<u64> {
    eprintln!("warning: --memory-limit-mb is only supported on unix; ignoring {limit_mb} MB limit");
    None
}

/// Restore a soft `RLIMIT_AS` previously returned by [`apply_memory_limit`].
/// Best-effort: if it fails, the process just stays under the tighter
/// limit for the rest of its (already nearly-finished) run.
#[cfg(unix)]
fn restore_memory_limit(previous_soft: u64) {
    let mut current = libc::rlimit {
        rlim_cur: 0,
        rlim_max: 0,
    };
    if unsafe { libc::getrlimit(libc::RLIMIT_AS, &raw mut current) } != 0 {
        return;
    }
    let limit = libc::rlimit {
        rlim_cur: previous_soft as libc::rlim_t,
        rlim_max: current.rlim_max,
    };
    let _ = unsafe { libc::setrlimit(libc::RLIMIT_AS, &raw const limit) };
}

#[cfg(not(unix))]
fn restore_memory_limit(_previous_soft: u64) {}

/// The memory-constrained window (see `LIMIT_ACTIVE`), open while the
/// analysis runs.
pub struct MemoryWindow {
    /// The soft limit to restore on close, if a limit was applied.
    previous: Option<u64>,
}

impl MemoryWindow {
    /// Applies `limit_mb`, if any, after storing `oom_line` for the
    /// allocation-error hook to print.
    pub fn open(limit_mb: Option<u64>, oom_line: String) -> Self {
        let Some(limit_mb) = limit_mb else {
            return Self { previous: None };
        };
        let _ = OOM_LINE.set(oom_line.into_bytes());

        let previous = apply_memory_limit(limit_mb);
        if previous.is_some() {
            LIMIT_ACTIVE.store(true, Ordering::SeqCst);
        }
        Self { previous }
    }

    /// Restores the previous limit.
    pub fn close(&mut self) {
        if let Some(previous) = self.previous.take() {
            restore_memory_limit(previous);
            LIMIT_ACTIVE.store(false, Ordering::SeqCst);
        }
    }
}

/// Peak resident memory in MiB, from `getrusage`'s `ru_maxrss`: of this
/// process, or with `children` of its largest finished child (a Singular
/// run), `None` while no child has finished.
#[cfg(unix)]
pub fn peak_rss_mib(children: bool) -> Option<u64> {
    let who = if children {
        libc::RUSAGE_CHILDREN
    } else {
        libc::RUSAGE_SELF
    };
    let mut usage: libc::rusage = unsafe { std::mem::zeroed() };
    if unsafe { libc::getrusage(who, &raw mut usage) } != 0 {
        return None;
    }
    let maxrss = u64::try_from(usage.ru_maxrss).ok()?;
    if children && maxrss == 0 {
        return None;
    }
    // `ru_maxrss` is in bytes on macOS and in KiB elsewhere.
    let bytes = if cfg!(target_os = "macos") {
        maxrss
    } else {
        maxrss * 1024
    };
    Some(bytes / (1024 * 1024))
}

#[cfg(not(unix))]
pub fn peak_rss_mib(_children: bool) -> Option<u64> {
    None
}
