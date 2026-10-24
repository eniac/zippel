//! Callgrind controls confined to the CI harness.

use std::collections::HashMap;
use std::ffi::CString;
use std::sync::{LazyLock, Mutex};

static DIRECTORY: LazyLock<Option<std::path::PathBuf>> =
    LazyLock::new(|| std::env::var_os("ZIPPEL_BENCH_PROFILE_DIR").map(std::path::PathBuf::from));

/// Samples already measured per region name, so repeated regions dump apart.
static SAMPLES: LazyLock<Mutex<HashMap<String, usize>>> = LazyLock::new(Mutex::default);

/// Run a named region, collecting all threads when Callgrind is enabled.
pub fn measure<T>(name: &str, f: impl FnOnce() -> T) -> T {
    let Some(directory) = DIRECTORY.as_ref() else {
        return f();
    };
    let index = *SAMPLES
        .lock()
        .expect("profile sample counter")
        .entry(name.to_owned())
        .and_modify(|index| *index += 1)
        .or_insert(0);
    // `name.index` labels the dump and attributes Singular children to it.
    let label = format!("{name}.{index}");
    std::fs::write(directory.join("phase"), &label).expect("write profile phase");
    request(0x4354_0001, 0); // CALLGRIND_ZERO_STATS
    request(0x4354_0004, 0); // CALLGRIND_START_INSTRUMENTATION
    let result = f();
    request(0x4354_0005, 0); // CALLGRIND_STOP_INSTRUMENTATION
    let label = CString::new(label).expect("profile label");
    request(0x4354_0003, label.as_ptr() as usize); // CALLGRIND_DUMP_STATS_AT
    result
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn request(code: usize, argument: usize) {
    let args = [code, argument, 0, 0, 0, 0];
    // Valgrind's amd64 client-request ABI (valgrind.h). The rotations restore
    // rdi; the marker is a no-op when the executable runs without Valgrind.
    unsafe {
        std::arch::asm!(
            "rol rdi, 3", "rol rdi, 13", "rol rdi, 61", "rol rdi, 51",
            "xchg rbx, rbx",
            in("rax") args.as_ptr(),
            inout("rdx") 0usize => _,
            lateout("rdi") _,
            options(nostack),
        );
    }
}

#[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
fn request(_: usize, _: usize) {
    panic!("instruction profiling requires Linux x86_64");
}
