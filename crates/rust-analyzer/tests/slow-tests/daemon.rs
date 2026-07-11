//! End-to-end tests of the daemonized server: proxy spawn and reuse, control commands,
//! stale endpoint recovery, idle shutdown, and crash exit codes.
//!
//! Every test gets a hermetic daemon discovery directory via `RA_DAEMON_DIR`, so the
//! daemons spawned here never interfere with each other or with a developer's real
//! daemon.

use std::{
    fs,
    io::Write,
    net::TcpStream,
    path::{Path, PathBuf},
    process::{Command, Output, Stdio},
    thread,
    time::{Duration, Instant},
};

use test_utils::skip_slow_tests;

use crate::testdir::TestDir;

const WAIT_TIMEOUT: Duration = Duration::from_secs(30);

#[test]
fn daemon_session_roundtrip_and_reuse() {
    if skip_slow_tests() {
        return;
    }
    let dir = TestDir::new();
    let daemon = DaemonGuard::new(&dir);

    let output = scripted_session(daemon.dir());
    assert!(output.status.success(), "first session failed: {output:?}");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains(r#""capabilities""#), "no initialize response in: {stdout}");

    let first_pid = endpoint_json(daemon.dir())["pid"].as_u64().unwrap();

    let output = scripted_session(daemon.dir());
    assert!(output.status.success(), "second session failed: {output:?}");
    let second_pid = endpoint_json(daemon.dir())["pid"].as_u64().unwrap();
    assert_eq!(first_pid, second_pid, "the second session did not reuse the daemon");

    assert!(wait_until(|| {
        let status = daemon.control(&["daemon", "status"]);
        status.status.success() && {
            let json: serde_json::Value =
                serde_json::from_slice(&status.stdout).expect("status is not json");
            json["pid"].as_u64() == Some(first_pid)
                && json["sessions"].as_array().is_some_and(Vec::is_empty)
        }
    }));

    let stop = daemon.control(&["daemon", "stop"]);
    assert!(stop.status.success(), "stop failed: {stop:?}");
    assert!(wait_until(|| endpoint_path(daemon.dir()).is_none()));
}

#[test]
fn daemon_idle_shutdown() {
    if skip_slow_tests() {
        return;
    }
    let dir = TestDir::new();
    let daemon = DaemonGuard::new(&dir);

    let mut child = ra_command(daemon.dir())
        .args(["daemon", "run", "--idle-timeout", "1"])
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();

    assert!(wait_until(|| endpoint_path(daemon.dir()).is_some()), "daemon never published");
    assert!(
        wait_until(|| child.try_wait().unwrap().is_some()),
        "daemon did not shut down when idle"
    );
    assert!(child.wait().unwrap().success());
    assert!(endpoint_path(daemon.dir()).is_none(), "endpoint file was left behind");
}

#[test]
fn daemon_stale_endpoint_recovery() {
    if skip_slow_tests() {
        return;
    }
    let dir = TestDir::new();
    let daemon = DaemonGuard::new(&dir);

    let mut child = ra_command(daemon.dir())
        .args(["daemon", "run", "--idle-timeout", "600"])
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();
    assert!(wait_until(|| endpoint_path(daemon.dir()).is_some()), "daemon never published");
    let stale_pid = endpoint_json(daemon.dir())["pid"].as_u64().unwrap();

    child.kill().unwrap();
    child.wait().unwrap();
    assert!(endpoint_path(daemon.dir()).is_some(), "kill should leave the endpoint behind");

    let output = scripted_session(daemon.dir());
    assert!(output.status.success(), "session across a stale endpoint failed: {output:?}");
    let fresh_pid = endpoint_json(daemon.dir())["pid"].as_u64().unwrap();
    assert_ne!(stale_pid, fresh_pid, "a fresh daemon should have replaced the stale one");
}

#[test]
fn daemon_stop_disconnects_sessions_with_failure_exit() {
    if skip_slow_tests() {
        return;
    }
    let dir = TestDir::new();
    let daemon = DaemonGuard::new(&dir);

    let mut session = ra_command(daemon.dir())
        .arg("--use-daemon")
        .stdin(Stdio::piped())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();
    let mut stdin = session.stdin.take().unwrap();
    stdin
        .write_all(
            format!(
                "{}{}",
                frame(
                    r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{}}}"#
                ),
                frame(r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#),
            )
            .as_bytes(),
        )
        .unwrap();

    assert!(
        wait_until(|| {
            let status = daemon.control(&["daemon", "status"]);
            status.status.success()
                && serde_json::from_slice::<serde_json::Value>(&status.stdout)
                    .is_ok_and(|json| json["sessions"].as_array().is_some_and(|s| s.len() == 1))
        }),
        "the session never showed up in the status report"
    );

    let stop = daemon.control(&["daemon", "stop"]);
    assert!(stop.status.success(), "stop failed: {stop:?}");

    let status = session.wait().unwrap();
    assert!(!status.success(), "a killed daemon must look like a crash to the client");
    drop(stdin);
}

#[test]
fn daemon_rejects_bad_token_and_version() {
    if skip_slow_tests() {
        return;
    }
    let dir = TestDir::new();
    let daemon = DaemonGuard::new(&dir);

    let mut child = ra_command(daemon.dir())
        .args(["daemon", "run", "--idle-timeout", "600"])
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();
    assert!(wait_until(|| endpoint_path(daemon.dir()).is_some()), "daemon never published");
    let endpoint = endpoint_json(daemon.dir());
    let addr = endpoint["addr"].as_str().unwrap().to_owned();
    let token = endpoint["token"].as_str().unwrap().to_owned();

    let bad_token = r#"{"token":"deadbeef","version":"0.0.0","kind":"control"}"#;
    assert!(
        handshake_response(&addr, bad_token).contains("rejected"),
        "an invalid token must be rejected"
    );

    let bad_version =
        format!(r#"{{"token":"{token}","version":"not-a-version","kind":"control"}}"#);
    let response = handshake_response(&addr, &bad_version);
    assert!(
        response.contains("rejected") && response.contains("version mismatch"),
        "a version mismatch must be rejected, got: {response}"
    );

    child.kill().unwrap();
    child.wait().unwrap();
}

struct DaemonGuard {
    dir: PathBuf,
}

impl DaemonGuard {
    fn new(dir: &TestDir) -> DaemonGuard {
        DaemonGuard { dir: dir.path().as_std_path().to_owned() }
    }

    fn dir(&self) -> &Path {
        &self.dir
    }

    fn control(&self, args: &[&str]) -> Output {
        ra_command(&self.dir).args(args).output().unwrap()
    }
}

impl Drop for DaemonGuard {
    fn drop(&mut self) {
        let _ = self.control(&["daemon", "stop"]);
    }
}

fn ra_command(daemon_dir: &Path) -> Command {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_rust-analyzer"));
    // The daemon directory doubles as the working directory: sessions in these tests
    // provide no `rootUri`, and an empty cwd keeps workspace discovery from loading
    // this very repository into every scripted session.
    cmd.env("RA_DAEMON_DIR", daemon_dir).current_dir(daemon_dir);
    cmd
}

fn frame(body: &str) -> String {
    format!("Content-Length: {}\r\n\r\n{body}", body.len())
}

/// Runs a full scripted LSP session (initialize through exit) through the proxy.
fn scripted_session(daemon_dir: &Path) -> Output {
    let mut child = ra_command(daemon_dir)
        .arg("--use-daemon")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let script = format!(
        "{}{}{}{}",
        frame(r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{}}}"#),
        frame(r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#),
        frame(r#"{"jsonrpc":"2.0","id":2,"method":"shutdown"}"#),
        frame(r#"{"jsonrpc":"2.0","method":"exit"}"#),
    );
    child.stdin.take().unwrap().write_all(script.as_bytes()).unwrap();
    child.wait_with_output().unwrap()
}

/// Locates the single instance directory's endpoint file, if it exists.
fn endpoint_path(daemon_dir: &Path) -> Option<PathBuf> {
    let entries = fs::read_dir(daemon_dir).ok()?;
    entries
        .filter_map(Result::ok)
        .map(|entry| entry.path().join("endpoint"))
        .find(|path| path.exists())
}

fn endpoint_json(daemon_dir: &Path) -> serde_json::Value {
    let path = endpoint_path(daemon_dir).expect("no endpoint file");
    serde_json::from_slice(&fs::read(path).unwrap()).unwrap()
}

/// Performs a raw handshake and returns the response line.
fn handshake_response(addr: &str, hello: &str) -> String {
    let mut stream = TcpStream::connect(addr).unwrap();
    stream.set_read_timeout(Some(WAIT_TIMEOUT)).unwrap();
    stream.write_all(format!("{hello}\n").as_bytes()).unwrap();
    let mut response = String::new();
    std::io::BufRead::read_line(&mut std::io::BufReader::new(&stream), &mut response).unwrap();
    response
}

fn wait_until(mut condition: impl FnMut() -> bool) -> bool {
    let deadline = Instant::now() + WAIT_TIMEOUT;
    while Instant::now() < deadline {
        if condition() {
            return true;
        }
        thread::sleep(Duration::from_millis(200));
    }
    false
}
