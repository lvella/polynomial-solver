//! This benchmark executes all test cases we have for all the binaries, and for
//! each case outputs its execution statistics, like outcome (timeout, success,
//! panic, etc), runtime, maximum memory usage, etc.
//!
//! Intended to be execute on every new version to track performance evolution
//! and detect serious regressions.

use lazy_static::lazy_static;
use libc::timeval;
use regex::Regex;
use serde::Serialize;
use std::{
    io::{self, BufRead, BufReader},
    mem::MaybeUninit,
    os::unix::process::ExitStatusExt,
    path::Path,
    process::{ChildStdout, Command, ExitStatus, Stdio},
    sync::mpsc::sync_channel,
    time::Duration,
};

const TIMEOUT: Duration = Duration::from_secs(300);

fn main() {
    // Set the working directory to a convenient place.
    std::env::set_current_dir(concat!(env!("CARGO_MANIFEST_DIR"), "/monitoring-cases")).unwrap();

    let mut wtr = csv::Writer::from_writer(io::stdout());

    // Run the maple-like cases:
    let walk = walkdir::WalkDir::new("maple-like")
        .follow_links(true)
        .sort_by_file_name();
    for entry in walk {
        match entry {
            Ok(e) => {
                // Each maple-like file may have multiple cases
                if e.file_type().is_file() {
                    for i in 0.. {
                        match polysolver_runner(PolysolverInput::MapleLike(e.path(), i)) {
                            Some(r) => {
                                wtr.serialize(r).unwrap();
                                wtr.flush().unwrap();
                            }
                            None => break,
                        }
                    }
                }
            }
            Err(e) => {
                eprintln!("Error traversing Maple-like cases: {}", e);
            }
        }
    }

    // Run the zokrates cases:
    let walk = walkdir::WalkDir::new("zokrates-bin")
        .follow_links(true)
        .sort_by_file_name();
    for entry in walk {
        match entry {
            Ok(e) => {
                if e.file_type().is_file() {
                    wtr.serialize(
                        polysolver_runner(PolysolverInput::ZokratesBin(e.path())).unwrap(),
                    )
                    .unwrap();
                    wtr.flush().unwrap();
                }
            }
            Err(e) => {
                eprintln!("Error traversing Zokrates cases: {}", e);
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
#[derive(Debug, Serialize)]
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

fn polysolver_runner(case: PolysolverInput) -> Option<RunStatistics> {
    // Executable of the polysolver being benchmarked
    const POLYSOLVER_BIN: &'static str = env!("CARGO_BIN_EXE_polysolver");

    lazy_static! {
        static ref PROGRESS_RE: Regex = Regex::new(r"^#\(p: (\d+), s: \d+\)").unwrap();
        static ref TIME_RE: Regex =
            Regex::new(r"^### Gröbner Base calculation time: (\d*\.\d+|\d+) s").unwrap();
        static ref WRONG_IDX: Regex =
            Regex::new(r"^Index too large, benchmark file only has \d+ systems.").unwrap();
    }

    let mut cmd = Command::new(POLYSOLVER_BIN);
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
        // Update the execution progress as output is written:
        let mut spairs = 0u32;
        let mut last_line = String::new();
        for line in output.lines() {
            last_line = line.unwrap();
            if let Some(caps) = PROGRESS_RE.captures(&last_line) {
                spairs = caps.get(1).unwrap().as_str().parse().unwrap();
            }
        }

        // Check if the index is valid.
        if let PolysolverInput::MapleLike(_, _) = case {
            if WRONG_IDX.is_match(&last_line) {
                wrong_idx = true;
                return (None, 0);
            }
        }

        // Try to get the self reported time, which is available if the run was successful.
        let self_reported = TIME_RE
            .captures(&last_line)
            .map(|caps| caps.get(1).unwrap().as_str().parse::<f64>().unwrap());

        (self_reported, spairs)
    });

    if wrong_idx {
        None
    } else {
        Some(run_result)
    }
}

fn child_runner(
    case_name: String,
    mut command: Command,
    output_processor: impl FnOnce(BufReader<ChildStdout>) -> (Option<f64>, u32),
) -> RunStatistics {
    let mut child = command
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();

    let child_pid = child.id();

    // We don't need stdin, so drop it:
    child.stdin.take();

    // Read the output one line at a time
    let output = BufReader::new(child.stdout.take().unwrap());

    // Create a thread to kill child on timeout
    let (signal_timeout, waiter) = sync_channel::<()>(0);
    let timeout_watcher = std::thread::spawn(move || {
        // Block for at most TIMEOUT, but may be unblocked early by the
        // other thread.
        let unblock_reason = waiter.recv_timeout(TIMEOUT).unwrap_err();

        // Kill the child process 😢. Might be a zombie at this point, but
        // should not have been collected yet.
        let _ = child.kill();

        match unblock_reason {
            std::sync::mpsc::RecvTimeoutError::Timeout => true,
            std::sync::mpsc::RecvTimeoutError::Disconnected => false,
        }
    });

    // Parse child output:
    let (self_reported_time, max_progress) = output_processor(output);

    // Stdout is closed. The process is either dead or dying, so we don't need
    // the timeout thread anymore:
    drop(signal_timeout);
    let timed_out = timeout_watcher.join().unwrap();

    // Instead of waiting child from std::process interface, we use wait4 from
    // libc to get child's resource usage information. This is safe because
    // std::process::Child does not automatically wait for the child when
    // dropped.
    let (usage, wait_status) = unsafe {
        use libc::{c_int, pid_t, rusage};

        let pid: pid_t = std::mem::transmute(child_pid);
        let mut status = MaybeUninit::<c_int>::uninit();
        let mut rusage = MaybeUninit::<rusage>::uninit();

        libc::wait4(pid, status.as_mut_ptr(), 0, rusage.as_mut_ptr());

        (rusage.assume_init(), status.assume_init())
    };

    // Detect if execution was a success by parsing self reported time
    let outcome = if let Some(_) = &self_reported_time {
        RunOutcome::Success
    } else if timed_out {
        RunOutcome::Timedout
    } else {
        RunOutcome::Unknown
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

fn parse_timeval(duration: &timeval) -> f64 {
    duration.tv_sec as f64 + (duration.tv_usec as f64 / 1e6)
}
