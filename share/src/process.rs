//! Launching an external program so that it dies with the process that
//! launched it.
//!
//! Use [`ContainedChild`] for any program a library starts on its caller's
//! behalf (Singular, for the Gröbner-basis backend): it must not keep running
//! after the caller panics, errors out, or is killed.

use std::io::{Read, Write};
use std::process::{Child, Command, Output};

/// A child process that dies with ours, however ours ends.
///
/// - Dropping the guard kills and reaps the child, unless it has already been
///   waited for (through [`Self::wait_with_output`] or the [`Child`] the guard
///   derefs to): an error or a panic does not leave it running.
/// - On Linux the child gets `PR_SET_PDEATHSIG(SIGKILL)`: the kernel kills it
///   when our process dies, even by `SIGKILL` or an abort, which skip `Drop`.
///   Strictly, when the thread that spawned it dies: keep that thread alive
///   for as long as the child should run.
/// - On Windows the child is in a Job Object with kill-on-close: the job's
///   handle closes, killing the child, whenever our process exits.
/// - Elsewhere (macOS, the BSDs) the kernel has no such hook: only `Drop`.
///
/// The child stays in our process group, so a terminal's Ctrl-C or a caller's
/// group kill still reaches it.
pub struct ContainedChild {
    child: Child,
    /// `None` if the child could not be put in a job (see [`Self::spawn`]).
    #[cfg(windows)]
    _job: Option<job::KillOnCloseJob>,
}

impl ContainedChild {
    /// Spawns `command` (its program, arguments and stdio as the caller set
    /// them) contained.
    ///
    /// On Windows, if the child cannot be put in a job (before Windows 8, or
    /// inside a job that sets UI restrictions, where jobs do not nest), it
    /// runs without one, and a warning is logged once: only `Drop` then kills
    /// it.
    ///
    /// # Errors
    /// As [`Command::spawn`].
    pub fn spawn(
        #[cfg_attr(not(target_os = "linux"), allow(unused_mut))] mut command: Command,
    ) -> std::io::Result<Self> {
        #[cfg(target_os = "linux")]
        {
            use std::os::unix::process::CommandExt;
            let parent = std::process::id();
            // SAFETY: the hook runs in the forked child before `exec` and
            // only makes async-signal-safe calls (`prctl`, `getppid`).
            unsafe {
                command.pre_exec(move || {
                    if libc::prctl(libc::PR_SET_PDEATHSIG, libc::SIGKILL) == -1 {
                        return Err(std::io::Error::last_os_error());
                    }
                    // We may have died before the `prctl`: then nothing
                    // would kill the child, so it must not start.
                    if libc::getppid().cast_unsigned() != parent {
                        return Err(std::io::Error::from_raw_os_error(libc::ESRCH));
                    }
                    Ok(())
                });
            }
        }
        let child = command.spawn()?;
        #[cfg(windows)]
        let job = job::KillOnCloseJob::containing(&child)
            .inspect_err(|e| {
                static WARNED: std::sync::Once = std::sync::Once::new();
                WARNED.call_once(|| {
                    log::warn!(
                        "a launched program will not die with this process: \
                         no kill-on-close job ({e})"
                    );
                });
            })
            .ok();
        Ok(Self {
            child,
            #[cfg(windows)]
            _job: job,
        })
    }

    /// Writes `input` to the child's stdin, closes it, reads stdout and stderr
    /// to their ends (stderr on a second thread, so neither pipe can fill and
    /// block the child), and waits for the child to exit. A stream the caller
    /// did not pipe is skipped (and comes back empty).
    ///
    /// # Errors
    /// If writing, reading or waiting fails; the guard then still kills the
    /// child when dropped.
    ///
    /// # Panics
    /// If the stderr reader thread panics.
    pub fn wait_with_output(&mut self, input: &[u8]) -> std::io::Result<Output> {
        if let Some(mut stdin) = self.child.stdin.take() {
            stdin.write_all(input)?;
        }
        let stdout_pipe = self.child.stdout.take();
        let stderr_pipe = self.child.stderr.take();
        let (stdout, stderr) = std::thread::scope(|scope| {
            let stderr = scope.spawn(move || {
                let mut buf = Vec::new();
                stderr_pipe
                    .map_or(Ok(0), |mut pipe| pipe.read_to_end(&mut buf))
                    .map(|_| buf)
            });
            let mut stdout = Vec::new();
            let read = stdout_pipe.map_or(Ok(0), |mut pipe| pipe.read_to_end(&mut stdout));
            let stderr = stderr.join().expect("stderr reader panicked");
            read.and(stderr.map(|stderr| (stdout, stderr)))
        })?;
        let status = self.child.wait()?;
        Ok(Output {
            status,
            stdout,
            stderr,
        })
    }
}

impl std::ops::Deref for ContainedChild {
    type Target = Child;

    fn deref(&self) -> &Child {
        &self.child
    }
}

impl std::ops::DerefMut for ContainedChild {
    fn deref_mut(&mut self) -> &mut Child {
        &mut self.child
    }
}

impl Drop for ContainedChild {
    fn drop(&mut self) {
        // Both are no-ops for a child already waited for: `Child` then
        // never signals, as its pid may have been reused.
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

/// A Windows Job Object with `JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE`: closing
/// its handle, which happens when our process exits however it exits, kills
/// every process in it.
#[cfg(windows)]
mod job {
    use std::os::windows::io::AsRawHandle;
    use windows_sys::Win32::Foundation::{CloseHandle, HANDLE};
    use windows_sys::Win32::System::JobObjects::{
        AssignProcessToJobObject, CreateJobObjectW, JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE,
        JOBOBJECT_EXTENDED_LIMIT_INFORMATION, JobObjectExtendedLimitInformation,
        SetInformationJobObject,
    };

    pub(super) struct KillOnCloseJob(HANDLE);

    // SAFETY: a kernel handle is valid in every thread of the process; this
    // keeps `ContainedChild` `Send` on Windows as it is elsewhere.
    unsafe impl Send for KillOnCloseJob {}

    impl KillOnCloseJob {
        /// A new kill-on-close job holding `child`. The child runs briefly
        /// before it is assigned; a process it starts in that window is not
        /// in the job (Singular starts none).
        pub(super) fn containing(child: &std::process::Child) -> std::io::Result<Self> {
            // SAFETY: plain Win32 calls on handles we own (the job) or borrow
            // for the call (the child's process handle).
            unsafe {
                let handle = CreateJobObjectW(std::ptr::null(), std::ptr::null());
                if handle.is_null() {
                    return Err(std::io::Error::last_os_error());
                }
                let job = Self(handle);
                let mut info = JOBOBJECT_EXTENDED_LIMIT_INFORMATION::default();
                info.BasicLimitInformation.LimitFlags = JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE;
                let size = u32::try_from(std::mem::size_of_val(&info))
                    .expect("the limit information fits in a u32");
                if SetInformationJobObject(
                    job.0,
                    JobObjectExtendedLimitInformation,
                    (&raw const info).cast(),
                    size,
                ) == 0
                {
                    return Err(std::io::Error::last_os_error());
                }
                if AssignProcessToJobObject(job.0, child.as_raw_handle().cast()) == 0 {
                    return Err(std::io::Error::last_os_error());
                }
                Ok(job)
            }
        }
    }

    impl Drop for KillOnCloseJob {
        fn drop(&mut self) {
            // SAFETY: we own the handle; closing it kills the job's processes.
            unsafe { CloseHandle(self.0) };
        }
    }
}

#[cfg(all(test, target_os = "linux"))]
mod tests {
    use super::ContainedChild;
    use std::io::{BufRead, BufReader};
    use std::process::{Command, Stdio};
    use std::time::{Duration, Instant};

    /// Whether `pid` is a live process (a zombie awaiting its reaper is not).
    fn alive(pid: u32) -> bool {
        std::fs::read_to_string(format!("/proc/{pid}/stat")).is_ok_and(|stat| {
            stat.rsplit(')')
                .next()
                .is_some_and(|s| !s.trim_start().starts_with('Z'))
        })
    }

    /// `sleep 1000`: a child that outlives any test unless killed. Its stdio
    /// is null, so a survivor cannot hold the test's output pipes open.
    fn sleeper() -> Command {
        let mut command = Command::new("sleep");
        command
            .arg("1000")
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null());
        command
    }

    /// Waits up to five seconds for `pid` to die; whether it did.
    fn dies(pid: u32) -> bool {
        let deadline = Instant::now() + Duration::from_secs(5);
        while alive(pid) && Instant::now() < deadline {
            std::thread::sleep(Duration::from_millis(10));
        }
        !alive(pid)
    }

    #[test]
    fn dropping_a_contained_child_kills_it() {
        let child = ContainedChild::spawn(sleeper()).unwrap();
        let pid = child.id();
        assert!(alive(pid));
        drop(child);
        assert!(!alive(pid), "the child survived its guard");
    }

    #[test]
    fn a_contained_child_runs_to_completion() {
        let mut command = Command::new("cat");
        command.stdin(Stdio::piped()).stdout(Stdio::piped());
        let mut child = ContainedChild::spawn(command).unwrap();
        let output = child.wait_with_output(b"to stdout").unwrap();
        assert!(output.status.success());
        assert_eq!(output.stdout, b"to stdout");
    }

    const HELPER: &str = "ZIPPEL_CONTAINED_CHILD_HELPER";

    /// A contained child dies when its parent is `SIGKILL`ed, which skips
    /// `Drop`. The parent is this test binary re-run as a helper: it spawns
    /// the child, prints its pid, and waits to be killed.
    #[test]
    fn a_contained_child_dies_with_its_parent() {
        if std::env::var_os(HELPER).is_some() {
            let child = ContainedChild::spawn(sleeper()).unwrap();
            println!("child pid {}", child.id());
            std::thread::sleep(Duration::from_secs(1000));
            return;
        }
        let mut helper = Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "process::tests::a_contained_child_dies_with_its_parent",
                "--nocapture",
            ])
            .env(HELPER, "1")
            .stdout(Stdio::piped())
            .spawn()
            .unwrap();
        let pid: u32 = BufReader::new(helper.stdout.take().unwrap())
            .lines()
            .find_map(|line| line.unwrap().strip_prefix("child pid ")?.parse().ok())
            .expect("the helper reports its child");
        assert!(alive(pid));
        helper.kill().unwrap();
        helper.wait().unwrap();
        assert!(dies(pid), "the child survived its parent");
    }
}
