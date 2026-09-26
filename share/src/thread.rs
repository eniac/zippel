//! Run a closure on a scoped thread with a larger-than-default stack.
//!
//! Several compiler entry points (`zippel-check`, `ZippelHandler::compile`,
//! the inline benchmark, the GB snapshot tests) spawn a worker thread with a
//! bigger stack because this compiler's recursive passes can overflow the
//! default 8MiB thread stack, then block until it finishes. This module
//! holds that pattern once.

use std::thread;

/// Stack size given to every thread spawned by [`run`]/[`run_or_panic`]. Large enough for the
/// deepest recursive pass in the workspace (the inline benchmark and GB snapshot tests already
/// needed 256MiB); callers don't get to pick their own, so there's only ever one value to reason
/// about.
const STACK_SIZE: usize = 256 * 1024 * 1024;

/// Run `f` to completion on a new thread named `name` with a larger-than-default stack,
/// blocking the caller until it finishes.
///
/// Returns `f`'s value on success, or the panic payload if `f` panicked, so
/// the caller can decide how to handle it (see [`run_or_panic`] for the
/// common case of propagating it as-is).
///
/// # Panics
/// If the OS refuses to spawn the thread.
pub fn run<T, F>(name: &str, f: F) -> thread::Result<T>
where
    F: FnOnce() -> T + Send,
    T: Send,
{
    thread::scope(|scope| {
        thread::Builder::new()
            .name(name.to_string())
            .stack_size(STACK_SIZE)
            .spawn_scoped(scope, f)
            .expect("failed to spawn thread")
            .join()
    })
}

/// Like [`run`], but resumes the worker thread's panic on the caller thread
/// instead of returning it.
///
/// # Panics
/// If the OS refuses to spawn the thread, or if `f` panics.
pub fn run_or_panic<T, F>(name: &str, f: F) -> T
where
    F: FnOnce() -> T + Send,
    T: Send,
{
    match run(name, f) {
        Ok(value) => value,
        Err(payload) => std::panic::resume_unwind(payload),
    }
}
