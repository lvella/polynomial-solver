//! This benchmark executes all test cases we have for all the binaries, and for
//! each case outputs its execution statistics, like outcome (timeout, success,
//! panic, etc), runtime, maximum memory usage, etc.
//!
//! Intended to be execute on every new version to track performance evolution
//! and detect serious regressions.
//!
//! Uses libc for wait4, that is Linux only, use nix for everything else.

#![feature(local_key_cell_methods)]

use lazy_static::lazy_static;
use nix::{
    sys::{
        signal::{
            killpg, sigaction, sigprocmask, SaFlags, SigAction, SigHandler, SigmaskHow,
            Signal::{SIGABRT, SIGHUP, SIGINT, SIGKILL, SIGTERM},
        },
        signalfd::SigSet,
    },
    unistd::Pid,
};
use regex::Regex;
use serde::Serialize;
use std::{
    ffi::OsStr,
    io::{self, BufRead, BufReader},
    mem::MaybeUninit,
    os::unix::process::{CommandExt, ExitStatusExt},
    path::Path,
    process::{ChildStdout, Command, ExitStatus, Stdio},
    sync::{
        atomic::{AtomicU32, Ordering::Relaxed},
        mpsc::sync_channel,
    },
    time::{Duration, Instant},
};

const TIMEOUT: Duration = Duration::from_secs(300);

/// Instant this process started. This is initialized at the very beginning of
/// main(), so the variable is always initialized and safe to read through the
/// execution.
static mut START_TIME: MaybeUninit<Instant> = MaybeUninit::uninit();

fn get_secs_since_start() -> u64 {
    (Instant::now() - unsafe { *START_TIME.assume_init_ref() }).as_secs()
}

macro_rules! tprintln {
    ($($arg:tt)*) => {
        eprintln!(
            "[{:06}] {}",
            get_secs_since_start(),
            format!($($arg)*)
        );
    };
}

/// The child group currently executing (if different from zero). This is used
/// to propagate signals, in case this process is interrupted.
static CHILD_PGID: AtomicU32 = AtomicU32::new(0);

thread_local! {
    /// List of signals to be propagated
    static DEATH_SIGNALS: SigSet = death_signals_set();
}

fn main() {
    unsafe {
        START_TIME.write(Instant::now());
    }

    // Register signal handler that propagates death signals to children.
    DEATH_SIGNALS.with(|death_signals| {
        let action = SigAction::new(
            SigHandler::Handler(death_signal_dispatcher),
            SaFlags::empty(),
            *death_signals,
        );

        for signal in death_signals.iter() {
            unsafe { sigaction(signal, &action) }.unwrap();
        }
    });

    // Set the working directory to a convenient place.
    std::env::set_current_dir(concat!(env!("CARGO_MANIFEST_DIR"), "/monitoring-cases")).unwrap();

    let mut wtr = csv::Writer::from_writer(io::stdout());

    // Walk through the cases directory and execute for all known extensions.
    let walk = walkdir::WalkDir::new(".")
        .follow_links(true)
        .sort_by_file_name();
    for entry in walk {
        match entry {
            Ok(e) => {
                if e.file_type().is_file() {
                    let path = e.path().strip_prefix(".").unwrap();
                    let ext = path.extension();
                    if Some(OsStr::new("maple")) == ext {
                        // Run maple-like cases. Each file may have multiple cases:
                        for i in 0.. {
                            match grobner_basis_runner(PolysolverInput::MapleLike(path, i)) {
                                Some(r) => {
                                    wtr.serialize(r).unwrap();
                                    wtr.flush().unwrap();
                                }
                                None => break,
                            }
                        }
                    } else if Some(OsStr::new("r1cs")) == ext {
                        // Run r1cs determinism check:
                        wtr.serialize(determinism_runner(path)).unwrap();
                        wtr.flush().unwrap();
                    } else if Some(OsStr::new("zok_bin")) == ext {
                        // Run the zokrates case:
                        wtr.serialize(
                            grobner_basis_runner(PolysolverInput::ZokratesBin(path)).unwrap(),
                        )
                        .unwrap();
                        wtr.flush().unwrap();
                    }
                }
            }
            Err(e) => {
                eprintln!("Error traversing Maple-like cases: {}", e);
            }
        }
    }
}

/// A polysolver input problem locator, to be executed.
enum PolysolverInput<'a> {
    ZokratesBin(&'a Path),
    MapleLike(&'a Path, u32),
}

/// Execution result
#[derive(Debug, PartialEq, Eq, Serialize)]
enum RunOutcome {
    Success,
    Timedout,
    Unknown,
}

/// All the recorded statistics of a run
#[derive(Debug, Serialize)]
struct RunStatistics {
    case_name: String,
    outcome: RunOutcome,
    self_reported_time: Option<f64>,
    user_time: f64,
    system_time: f64,
    max_progress: u32,
    max_memory_kb: i64,
    exit_status: Option<i32>,
    exit_signal: Option<i32>,
}

fn grobner_basis_runner(case: PolysolverInput) -> Option<RunStatistics> {
    // Path of the executable being benchmarked
    const GB_BIN: &'static str = env!("CARGO_BIN_EXE_grobner-basis");

    lazy_static! {
        static ref TIME_RE: Regex =
            Regex::new(r"^### Gröbner Base calculation time: (\d*\.\d+|\d+) s").unwrap();
        static ref WRONG_IDX: Regex =
            Regex::new(r"^Index too large, benchmark file only has \d+ systems.").unwrap();
    }

    let mut cmd = Command::new(GB_BIN);
    let case_name: String;
    match case {
        PolysolverInput::ZokratesBin(filename) => {
            cmd.arg("-z").arg(filename);
            case_name = filename.to_string_lossy().into();
        }
        PolysolverInput::MapleLike(filename, index) => {
            cmd.arg("-m").arg(filename).arg("-i").arg(index.to_string());
            case_name = format!("{}:{index}", filename.to_string_lossy());
        }
    }

    let mut wrong_idx = false;

    let run_result = child_runner(case_name, cmd, |output| {
        let (spairs, last_line) = count_spairs(output);

        // Check if the index is valid.
        if let PolysolverInput::MapleLike(_, _) = case {
            if WRONG_IDX.is_match(&last_line) {
                wrong_idx = true;
                return (RunOutcome::Unknown, None, 0);
            }
        }

        // Try to get the self reported time, which is available if the run was successful.
        let self_reported = TIME_RE
            .captures(&last_line)
            .map(|caps| caps.get(1).unwrap().as_str().parse::<f64>().unwrap());

        let outcome = if let Some(_) = &self_reported {
            RunOutcome::Success
        } else {
            RunOutcome::Unknown
        };

        (outcome, self_reported, spairs)
    });

    if wrong_idx {
        None
    } else {
        Some(run_result)
    }
}

fn determinism_runner(input: &Path) -> RunStatistics {
    // Path of the executable being benchmarked
    const CHECK_DETERMINISM_BIN: &'static str = env!("CARGO_BIN_EXE_check-determinism");

    let mut cmd = Command::new(CHECK_DETERMINISM_BIN);
    cmd.arg(input);

    child_runner(input.to_string_lossy().into(), cmd, |output| {
        let (spairs, last_line) = count_spairs(output);

        lazy_static! {
            static ref OUTCOME_RE: Regex =
                Regex::new(r"^(DETERMINISTIC|NON DETERMINISTIC|UNKNOWN)").unwrap();
        }

        let outcome = if OUTCOME_RE.is_match(&last_line) {
            RunOutcome::Success
        } else {
            RunOutcome::Unknown
        };

        (outcome, None, spairs)
    })
}

fn count_spairs(output: impl BufRead) -> (u32, String) {
    lazy_static! {
        static ref PROGRESS_RE: Regex = Regex::new(r"^#\(p: (\d+), s: \d+\)").unwrap();
    }

    // Update the execution progress as output is written:
    let mut spairs = 0u32;
    let mut last_line = String::new();
    for line in output.lines() {
        last_line = line.unwrap();
        if PROGRESS_RE.is_match(&last_line) {
            spairs += 1;
        }
    }

    (spairs, last_line)
}

fn child_runner(
    case_name: String,
    mut command: Command,
    output_processor: impl FnOnce(BufReader<ChildStdout>) -> (RunOutcome, Option<f64>, u32),
) -> RunStatistics {
    tprintln!("Starting {}", case_name);
    let command = command
        .process_group(0)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped());

    // Blocks death signals while we fork, so that the child PGID is stored
    // so that those signals can be propagated by our signal handler.
    let child;
    {
        let prev_mask = mask_death_signals();
        child = unsafe {
            command.pre_exec(move || {
                prev_mask.restore();
                Ok(())
            })
        }
        .spawn()
        .map(|child| {
            let old_pgid = CHILD_PGID.swap(child.id(), Relaxed);
            (child, old_pgid)
        });
        prev_mask.restore();
    }
    let (mut child, old_pgid) = child.unwrap();
    assert_eq!(old_pgid, 0);

    // We don't need stdin, so drop it:
    child.stdin.take();

    // Read the output one line at a time
    let output = BufReader::new(child.stdout.take().unwrap());

    // Create a thread to kill child on timeout
    let (signal_timeout, waiter) = sync_channel::<()>(0);
    let timeout_watcher = std::thread::spawn(move || {
        // Block for at most TIMEOUT, but may be unblocked early by the
        // other thread.
        tprintln!("Waiting for case to finish");
        let unblock_reason = waiter.recv_timeout(TIMEOUT).unwrap_err();

        // Kill the whole child process group 😢. Child might be a zombie at
        // this point, but should not have been collected yet.
        tprintln!("Done waiting, sending kill signal");
        killpg(Pid::from_raw(child.id() as libc::pid_t), SIGKILL).unwrap();

        match unblock_reason {
            std::sync::mpsc::RecvTimeoutError::Timeout => true,
            std::sync::mpsc::RecvTimeoutError::Disconnected => false,
        }
    });

    // Parse child output:
    let (outcome, self_reported_time, max_progress) = output_processor(output);

    // All output was parsed and stdout is closed. So the process is either dead
    // or dying, and we don't need the timeout thread anymore:
    drop(signal_timeout);
    let timed_out = timeout_watcher.join().unwrap();
    let outcome = match timed_out {
        true => RunOutcome::Timedout,
        false => outcome,
    };

    // Instead of waiting child from std::process interface, we use wait4 from
    // libc to get child's resource usage information. This is safe because
    // std::process::Child does not automatically wait for the child when
    // dropped.
    let (usage, wait_status) = unsafe {
        use libc::{c_int, pid_t, rusage, wait4};

        // We no longer have to propagate the signals to this process, because
        // it was already signaled to die.
        let pid = CHILD_PGID.swap(0, Relaxed) as pid_t;
        let mut status = MaybeUninit::<c_int>::uninit();
        let mut rusage = MaybeUninit::<rusage>::uninit();

        tprintln!("Collecting the case's zombie process (PID {})", pid);
        let err = wait4(pid, status.as_mut_ptr(), 0, rusage.as_mut_ptr());
        assert_ne!(err, -1);

        (rusage.assume_init(), status.assume_init())
    };

    let status = ExitStatus::from_raw(wait_status);

    RunStatistics {
        case_name,
        outcome,
        self_reported_time,
        max_progress,
        user_time: parse_timeval(&usage.ru_utime),
        system_time: parse_timeval(&usage.ru_stime),
        max_memory_kb: usage.ru_maxrss,
        exit_status: status.code(),
        exit_signal: status.signal(),
    }
}

fn parse_timeval(duration: &libc::timeval) -> f64 {
    duration.tv_sec as f64 + (duration.tv_usec as f64 / 1e6)
}

fn death_signals_set() -> SigSet {
    let mut sigset = SigSet::empty();
    sigset.add(SIGABRT);
    sigset.add(SIGHUP);
    sigset.add(SIGINT);
    sigset.add(SIGTERM);
    sigset
}

/// Signal handler that forwards various killing signals from this process to
/// child.
extern "C" fn death_signal_dispatcher(signal: libc::c_int) {
    unsafe {
        let pid = CHILD_PGID.load(Relaxed) as libc::pid_t;
        if pid != 0 {
            libc::killpg(pid as i32, signal);
        }
        // It seems to be some convention to finish with this exit code.
        libc::_exit(128 + signal);
    }
}

fn mask_death_signals() -> PrevSigMask {
    let mut prev = SigSet::empty();
    DEATH_SIGNALS.with(|death_signals| {
        sigprocmask(SigmaskHow::SIG_BLOCK, Some(death_signals), Some(&mut prev)).unwrap()
    });

    PrevSigMask(prev)
}

#[derive(Debug, Clone, Copy)]
struct PrevSigMask(SigSet);

impl PrevSigMask {
    fn restore(&self) {
        sigprocmask(SigmaskHow::SIG_SETMASK, Some(&self.0), None).unwrap();
    }
}
