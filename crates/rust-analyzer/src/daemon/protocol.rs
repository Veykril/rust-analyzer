//! The handshake spoken on a freshly established daemon connection, before any LSP
//! traffic.
//!
//! The connecting side sends a single [`Hello`] line and *must not* send anything else
//! until it has received the [`HelloResponse`] line; both sides use buffered readers, so
//! bytes sent early could be swallowed by the handshake's read-ahead. After an
//! [`HelloResponse::Accepted`], the stream carries plain LSP framing (for session
//! connections) or further line-delimited JSON (for control connections).

use std::{collections::BTreeMap, env, io};

use serde::de::DeserializeOwned;
use serde_derive::{Deserialize, Serialize};

use crate::daemon::endpoint::Token;

/// The first message on any daemon connection, sent by the connecting side.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Hello {
    /// The shared secret from the endpoint file.
    pub token: Token,
    /// The connecting build's full version string; must match the daemon's exactly.
    pub version: String,
    /// What this connection is for.
    #[serde(flatten)]
    pub kind: ConnectionKind,
}

/// The purpose of a daemon connection.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum ConnectionKind {
    /// An LSP session; the stream carries LSP traffic after the handshake.
    Session {
        /// Process id of the proxy, for diagnostics.
        client_pid: u32,
        /// The proxy's [`env_fingerprint`], compared against the daemon's to detect
        /// clients running under a different environment than the daemon.
        env_fingerprint: BTreeMap<String, Option<String>>,
    },
    /// A control connection (`daemon status` / `daemon stop`).
    Control,
}

/// The daemon's reply to a [`Hello`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "result", rename_all = "kebab-case")]
pub enum HelloResponse {
    /// The connection may proceed.
    Accepted,
    /// The connection is refused and the daemon will close the stream.
    Rejected {
        /// Human-readable refusal reason.
        reason: String,
    },
}

/// A command sent on an accepted control connection.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "cmd", rename_all = "kebab-case")]
pub enum ControlRequest {
    /// Requests a [`StatusResponse`].
    Status,
    /// Asks the daemon to shut down, force-dropping all live sessions. Answered with a
    /// [`StopAck`] just before the daemon exits.
    Stop,
}

/// The daemon's answer to [`ControlRequest::Status`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StatusResponse {
    /// The daemon's full version string.
    pub version: String,
    /// Process id of the daemon.
    pub pid: u32,
    /// Seconds since the daemon started.
    pub uptime_secs: u64,
    /// Human-readable amount of memory currently allocated by the daemon.
    pub memory: String,
    /// The currently connected sessions.
    pub sessions: Vec<SessionStatus>,
}

/// A live session, as reported in a [`StatusResponse`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SessionStatus {
    /// Process id of the session's proxy.
    pub client_pid: u32,
    /// Seconds since the session connected.
    pub uptime_secs: u64,
    /// Whether the session's client environment differed from the daemon's.
    pub env_mismatch: bool,
}

/// The daemon's answer to [`ControlRequest::Stop`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StopAck {
    /// Process id of the exiting daemon.
    pub pid: u32,
}

/// Environment variables that affect toolchain discovery and command execution.
///
/// Sessions run with the daemon's process environment; a client whose fingerprint
/// differs from the daemon's may observe different toolchain behavior than it would
/// with an in-process server, which the daemon calls out in its log.
const FINGERPRINT_VARS: &[&str] = &["PATH", "RUSTUP_HOME", "RUSTUP_TOOLCHAIN", "CARGO_HOME"];

/// Captures the current process's [`FINGERPRINT_VARS`].
pub fn env_fingerprint() -> BTreeMap<String, Option<String>> {
    FINGERPRINT_VARS.iter().map(|&var| (var.to_owned(), env::var(var).ok())).collect()
}

const MAX_LINE_LEN: u64 = 64 * 1024;

/// Reads one newline-terminated JSON message.
///
/// # Errors
///
/// Returns [`io::Error`] if the stream ends before a newline, the line exceeds a sanity
/// limit, or the line is not valid JSON for `T`.
///
/// [`io::Error`]: io::Error
pub fn read_line_message<T: DeserializeOwned>(reader: impl io::Read) -> io::Result<T> {
    let mut reader = io::BufReader::new(reader.take(MAX_LINE_LEN));
    let mut line = String::new();
    io::BufRead::read_line(&mut reader, &mut line)?;
    if !line.ends_with('\n') {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "message not terminated by a newline",
        ));
    }
    serde_json::from_str(&line).map_err(|err| io::Error::new(io::ErrorKind::InvalidData, err))
}

/// Writes one newline-terminated JSON message and flushes.
///
/// # Errors
///
/// Returns [`io::Error`] if the message cannot be written.
///
/// [`io::Error`]: io::Error
pub fn write_line_message<T: serde::Serialize>(
    mut writer: impl io::Write,
    message: &T,
) -> io::Result<()> {
    let mut buf = serde_json::to_vec(message).map_err(io::Error::other)?;
    buf.push(b'\n');
    writer.write_all(&buf)?;
    writer.flush()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hello_roundtrip() {
        let hello = Hello {
            token: Token::generate(),
            version: "0.0.0".to_owned(),
            kind: ConnectionKind::Session { client_pid: 42, env_fingerprint: env_fingerprint() },
        };
        let mut buf = Vec::new();
        write_line_message(&mut buf, &hello).unwrap();
        assert_eq!(buf.iter().filter(|&&b| b == b'\n').count(), 1);
        let read: Hello = read_line_message(buf.as_slice()).unwrap();
        assert_eq!(read, hello);
    }

    #[test]
    fn response_roundtrip() {
        for response in
            [HelloResponse::Accepted, HelloResponse::Rejected { reason: "no".to_owned() }]
        {
            let mut buf = Vec::new();
            write_line_message(&mut buf, &response).unwrap();
            let read: HelloResponse = read_line_message(buf.as_slice()).unwrap();
            assert_eq!(read, response);
        }
    }

    #[test]
    fn unterminated_line_is_rejected() {
        let err = read_line_message::<HelloResponse>(&b"{\"result\":\"accepted\"}"[..]);
        assert!(err.is_err());
    }

    #[test]
    fn garbage_is_rejected() {
        let err = read_line_message::<HelloResponse>(&b"hello there\n"[..]);
        assert!(err.is_err());
    }
}
