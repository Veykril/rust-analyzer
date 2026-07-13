//! The client-facing proxy: relays an LSP session between stdio and the daemon.
//!
//! The proxy never interprets the session beyond LSP framing: client bytes are
//! forwarded unmodified frame by frame (peeking only at whether a frame is the `exit`
//! notification, to tell a clean daemon-side close from a crash), daemon bytes are
//! forwarded verbatim.
#![allow(
    clippy::print_stderr,
    reason = "the proxy's stderr is the client's server-output log, where connection-phase \
              failures belong"
)]

use std::{
    env, fs,
    io::{self, BufRead, Write},
    net::{Shutdown, TcpStream},
    process::{self, ExitCode, Stdio},
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    },
    thread,
    time::{Duration, Instant},
};

use serde_derive::Deserialize;

use crate::daemon::{
    endpoint::{Endpoint, InstanceDir, InstanceKey, Transport},
    protocol::{self, ConnectionKind, Hello, HelloResponse},
};

const CONNECT_TIMEOUT: Duration = Duration::from_secs(1);
const HANDSHAKE_TIMEOUT: Duration = Duration::from_secs(10);
const SPAWN_WAIT_TIMEOUT: Duration = Duration::from_secs(10);
const SPAWN_POLL_INTERVAL: Duration = Duration::from_millis(200);

/// Connects to the daemon for this build (spawning one if none is running) and relays
/// the LSP session between stdio and the daemon until either side disconnects.
///
/// Returns [`ExitCode::SUCCESS`] when the session ended on the client's initiative
/// (`exit` notification or closed stdin), and [`ExitCode::FAILURE`] when the daemon
/// disconnected unexpectedly, so that the client's crash-restart handling kicks in.
///
/// # Errors
///
/// Fails only while no stdio traffic has been consumed yet; the caller may then safely
/// run the session in-process instead.
pub fn run_proxy() -> anyhow::Result<ExitCode> {
    let stream = connect_or_spawn()?;
    Ok(pump(stream))
}

fn connect_or_spawn() -> anyhow::Result<TcpStream> {
    let key = InstanceKey::from_build_info()?;
    let dir = InstanceDir::new(&key)?;

    if let Some(stream) = try_connect(&dir)? {
        return Ok(stream);
    }

    let lock = dir.lock()?;
    if let Some(stream) = try_connect(&dir)? {
        return Ok(stream);
    }

    spawn_daemon(&dir)?;
    let deadline = Instant::now() + SPAWN_WAIT_TIMEOUT;
    while Instant::now() < deadline {
        thread::sleep(SPAWN_POLL_INTERVAL);
        if let Some(stream) = try_connect(&dir)? {
            drop(lock);
            return Ok(stream);
        }
    }
    anyhow::bail!("spawned a daemon, but could not connect to it within {SPAWN_WAIT_TIMEOUT:?}")
}

/// Attempts to connect to the currently published endpoint.
///
/// `Ok(None)` means there is no live daemon (no endpoint, or connecting failed) and
/// spawning one is warranted. An explicit rejection by a live daemon is an error;
/// spawning a competing daemon would not help.
fn try_connect(dir: &InstanceDir) -> anyhow::Result<Option<TcpStream>> {
    let Some(endpoint) = dir.read_endpoint() else {
        return Ok(None);
    };
    match connect_handshake(&endpoint) {
        Ok(stream) => Ok(Some(stream)),
        Err(HandshakeError::Unreachable(err)) => {
            tracing::info!("no live daemon behind the published endpoint: {err}");
            Ok(None)
        }
        Err(HandshakeError::Rejected(reason)) => {
            anyhow::bail!("the daemon rejected the connection: {reason}")
        }
    }
}

enum HandshakeError {
    /// No live daemon answered; a new one may be spawned.
    Unreachable(io::Error),
    /// A live daemon refused us; do not spawn another.
    Rejected(String),
}

impl From<io::Error> for HandshakeError {
    fn from(err: io::Error) -> HandshakeError {
        HandshakeError::Unreachable(err)
    }
}

fn connect_handshake(endpoint: &Endpoint) -> Result<TcpStream, HandshakeError> {
    let Transport::Tcp { addr } = endpoint.transport;
    let stream = TcpStream::connect_timeout(&addr, CONNECT_TIMEOUT)?;
    stream.set_read_timeout(Some(HANDSHAKE_TIMEOUT))?;
    stream.set_write_timeout(Some(HANDSHAKE_TIMEOUT))?;
    let hello = Hello {
        token: endpoint.token.clone(),
        version: crate::version().to_string(),
        kind: ConnectionKind::Session {
            client_pid: process::id(),
            env_fingerprint: protocol::env_fingerprint(),
        },
    };
    protocol::write_line_message(&stream, &hello)?;
    match protocol::read_line_message::<HelloResponse>(&stream)? {
        HelloResponse::Accepted => {
            stream.set_read_timeout(None)?;
            stream.set_write_timeout(None)?;
            Ok(stream)
        }
        HelloResponse::Rejected { reason } => Err(HandshakeError::Rejected(reason)),
    }
}

fn spawn_daemon(dir: &InstanceDir) -> anyhow::Result<()> {
    #[cfg(windows)]
    prevent_std_handle_inheritance();
    let exe = env::current_exe()?;
    // Give the daemon a neutral working directory instead of inheriting whichever
    // directory this proxy happens to run in (and thereby pinning it).
    let mut cmd = toolchain::command(exe, dir.path(), &rustc_hash::FxHashMap::default());
    cmd.arg("--log-file")
        .arg(dir.log_path())
        .args(["daemon", "run"])
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(fs::File::create(dir.stderr_path())?);
    #[cfg(unix)]
    {
        // Put the daemon in its own session so that an editor tearing down the proxy's
        // process group does not take the daemon with it.
        // SAFETY: `setsid` is async-signal-safe.
        unsafe {
            std::os::unix::process::CommandExt::pre_exec(&mut cmd, || {
                libc::setsid();
                Ok(())
            });
        }
    }
    #[cfg(windows)]
    {
        use std::os::windows::process::CommandExt;
        const CREATE_NEW_PROCESS_GROUP: u32 = 0x0000_0200;
        const CREATE_NO_WINDOW: u32 = 0x0800_0000;
        cmd.creation_flags(CREATE_NEW_PROCESS_GROUP | CREATE_NO_WINDOW);
    }
    let child = cmd.spawn()?;
    tracing::info!(pid = child.id(), "spawned a daemon");
    Ok(())
}

/// Stops the daemon from inheriting the proxy's standard handles.
///
/// The client talks to the proxy through pipes it created as inheritable; without this,
/// the detached daemon inherits stray copies of them and keeps them open long after the
/// proxy exited, so the client would never observe EOF on the proxy's stdout. Unix is
/// unaffected as the standard library marks descriptors close-on-exec.
#[cfg(windows)]
fn prevent_std_handle_inheritance() {
    use windows_sys::Win32::{
        Foundation::{HANDLE_FLAG_INHERIT, INVALID_HANDLE_VALUE, SetHandleInformation},
        System::Console::{GetStdHandle, STD_ERROR_HANDLE, STD_INPUT_HANDLE, STD_OUTPUT_HANDLE},
    };
    for kind in [STD_INPUT_HANDLE, STD_OUTPUT_HANDLE, STD_ERROR_HANDLE] {
        // SAFETY: Querying our own standard handles and flipping their inheritance flag
        // does not invalidate them; the proxy keeps using them afterwards.
        unsafe {
            let handle = GetStdHandle(kind);
            if handle != INVALID_HANDLE_VALUE && !handle.is_null() {
                SetHandleInformation(handle, HANDLE_FLAG_INHERIT, 0);
            }
        }
    }
}

fn pump(stream: TcpStream) -> ExitCode {
    let clean_shutdown = Arc::new(AtomicBool::new(false));

    let write_stream = match stream.try_clone() {
        Ok(it) => it,
        Err(err) => {
            eprintln!("rust-analyzer proxy failed to clone the daemon stream: {err}");
            return ExitCode::FAILURE;
        }
    };
    let flag = Arc::clone(&clean_shutdown);
    thread::spawn(move || {
        let mut write_stream = write_stream;
        match relay_frames(io::stdin().lock(), &mut write_stream, &flag) {
            Ok(()) => flag.store(true, Ordering::SeqCst),
            Err(err) => tracing::info!("client to daemon relay ended: {err}"),
        }
        let _ = write_stream.shutdown(Shutdown::Write);
    });

    let mut read_stream = stream;
    let mut stdout = io::stdout().lock();
    let _ = io::copy(&mut read_stream, &mut stdout);
    let _ = stdout.flush();

    if clean_shutdown.load(Ordering::SeqCst) {
        ExitCode::SUCCESS
    } else {
        eprintln!("the rust-analyzer daemon closed the connection unexpectedly");
        ExitCode::FAILURE
    }
}

/// Forwards LSP frames from `reader` to `writer` byte for byte, flagging `saw_exit`
/// when the `exit` notification passes through. Returns `Ok(())` on a clean EOF at a
/// frame boundary.
fn relay_frames(
    mut reader: impl BufRead,
    writer: &mut impl Write,
    saw_exit: &AtomicBool,
) -> io::Result<()> {
    loop {
        let mut header = Vec::new();
        loop {
            let read = reader.read_until(b'\n', &mut header)?;
            if read == 0 {
                if header.is_empty() {
                    return Ok(());
                }
                return Err(io::ErrorKind::UnexpectedEof.into());
            }
            if header.ends_with(b"\r\n\r\n") {
                break;
            }
        }
        let body_len = content_length(&header)?;
        let mut body = vec![0; body_len];
        reader.read_exact(&mut body)?;

        #[derive(Deserialize)]
        struct Method<'a> {
            method: Option<&'a str>,
        }
        if let Ok(Method { method: Some("exit") }) = serde_json::from_slice::<Method<'_>>(&body) {
            saw_exit.store(true, Ordering::SeqCst);
        }

        writer.write_all(&header)?;
        writer.write_all(&body)?;
        writer.flush()?;
    }
}

fn content_length(header: &[u8]) -> io::Result<usize> {
    for line in header.split(|&b| b == b'\n') {
        let line = String::from_utf8_lossy(line);
        let Some((name, value)) = line.split_once(':') else {
            continue;
        };
        if name.eq_ignore_ascii_case("content-length") {
            return value.trim().parse().map_err(|_| {
                io::Error::new(io::ErrorKind::InvalidData, "malformed Content-Length header")
            });
        }
    }
    Err(io::Error::new(io::ErrorKind::InvalidData, "missing Content-Length header"))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn frame(body: &str) -> Vec<u8> {
        format!("Content-Length: {}\r\n\r\n{body}", body.len()).into_bytes()
    }

    #[test]
    fn relays_frames_verbatim() {
        let mut input = frame(r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#);
        input.extend(frame(r#"{"jsonrpc":"2.0","method":"exit"}"#));

        let saw_exit = AtomicBool::new(false);
        let mut output = Vec::new();
        relay_frames(input.as_slice(), &mut output, &saw_exit).unwrap();

        assert_eq!(output, input);
        assert!(saw_exit.load(Ordering::SeqCst));
    }

    #[test]
    fn exit_is_not_flagged_for_other_methods() {
        let input = frame(r#"{"jsonrpc":"2.0","method":"shutdown","id":2}"#);
        let saw_exit = AtomicBool::new(false);
        let mut output = Vec::new();
        relay_frames(input.as_slice(), &mut output, &saw_exit).unwrap();
        assert_eq!(output, input);
        assert!(!saw_exit.load(Ordering::SeqCst));
    }

    #[test]
    fn eof_mid_frame_is_an_error() {
        let input = &frame("{}")[..10];
        let saw_exit = AtomicBool::new(false);
        let mut output = Vec::new();
        assert!(relay_frames(input, &mut output, &saw_exit).is_err());
    }
}
