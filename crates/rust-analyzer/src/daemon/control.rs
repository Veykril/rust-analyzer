//! Client side of daemon control connections: `rust-analyzer daemon status` / `stop`.

use std::{net::TcpStream, process::ExitCode, time::Duration};

use crate::daemon::{
    endpoint::{Endpoint, InstanceDir, InstanceKey, Transport},
    protocol::{
        self, ConnectionKind, ControlRequest, Hello, HelloResponse, StatusResponse, StopAck,
    },
};

const CONTROL_TIMEOUT: Duration = Duration::from_secs(10);

/// Prints the running daemon's status as JSON to stdout.
///
/// Exits with failure when no daemon is running for this build.
///
/// # Errors
///
/// Returns an error if a daemon is running but cannot be queried.
pub fn status() -> anyhow::Result<ExitCode> {
    let Some(stream) = connect()? else {
        eprintln!("no rust-analyzer daemon is running for this build");
        return Ok(ExitCode::FAILURE);
    };
    protocol::write_line_message(&stream, &ControlRequest::Status)?;
    let status: StatusResponse = protocol::read_line_message(&stream)?;
    println!("{}", serde_json::to_string_pretty(&status)?);
    Ok(ExitCode::SUCCESS)
}

/// Stops the running daemon, force-dropping all of its live sessions.
///
/// Succeeds when no daemon is running (stopping is idempotent).
///
/// # Errors
///
/// Returns an error if a daemon is running but cannot be told to stop.
pub fn stop() -> anyhow::Result<ExitCode> {
    let Some(stream) = connect()? else {
        println!("no rust-analyzer daemon is running for this build");
        return Ok(ExitCode::SUCCESS);
    };
    protocol::write_line_message(&stream, &ControlRequest::Stop)?;
    let ack: StopAck = protocol::read_line_message(&stream)?;
    println!("stopped the rust-analyzer daemon (pid {})", ack.pid);
    Ok(ExitCode::SUCCESS)
}

/// Opens a control connection to the daemon of this build, if one is running.
///
/// # Errors
///
/// Returns an error if the build's identity cannot be established or a live daemon
/// rejects the connection.
fn connect() -> anyhow::Result<Option<TcpStream>> {
    let key = InstanceKey::from_build_info()?;
    let dir = InstanceDir::new(&key)?;
    let Some(endpoint) = dir.read_endpoint() else {
        return Ok(None);
    };

    let Endpoint { transport: Transport::Tcp { addr }, token, .. } = &endpoint;
    let Ok(stream) = TcpStream::connect_timeout(addr, CONTROL_TIMEOUT) else {
        return Ok(None);
    };
    stream.set_read_timeout(Some(CONTROL_TIMEOUT))?;
    stream.set_write_timeout(Some(CONTROL_TIMEOUT))?;

    let hello = Hello {
        token: token.clone(),
        version: crate::version().to_string(),
        kind: ConnectionKind::Control,
    };
    if protocol::write_line_message(&stream, &hello).is_err() {
        return Ok(None);
    }
    match protocol::read_line_message::<HelloResponse>(&stream) {
        Ok(HelloResponse::Accepted) => Ok(Some(stream)),
        Ok(HelloResponse::Rejected { reason }) => {
            anyhow::bail!("the daemon rejected the control connection: {reason}")
        }
        Err(_) => Ok(None),
    }
}
