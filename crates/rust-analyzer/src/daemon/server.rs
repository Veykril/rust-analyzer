//! The daemon process: accepts proxy connections and hosts one LSP session per proxy.

use std::{
    collections::BTreeMap,
    io,
    net::{Ipv4Addr, TcpListener, TcpStream},
    panic::{self, AssertUnwindSafe},
    process,
    sync::{Arc, Mutex},
    thread,
    time::{Duration, Instant},
};

use crossbeam_channel::bounded;
use lsp_server::{Connection, Message};
use stdx::thread::{Builder, ThreadIntent};

use rustc_hash::FxHashMap;

use crate::{
    SharedServices,
    daemon::{
        endpoint::{Endpoint, InstanceDir, InstanceKey, Token, Transport},
        protocol::{
            self, ConnectionKind, ControlRequest, Hello, HelloResponse, SessionStatus,
            StatusResponse, StopAck,
        },
    },
    session::{IoThreads, run_session},
    version::version,
};

const STACK_SIZE: usize = 1024 * 1024 * 8;
const HANDSHAKE_TIMEOUT: Duration = Duration::from_secs(10);
const PROBE_TIMEOUT: Duration = Duration::from_secs(1);

/// Runs the daemon in the foreground until it is idle for `idle_timeout`.
///
/// Publishes an endpoint for the current build's [`InstanceKey`], then serves every
/// accepted connection on its own thread. Refuses to start if a live daemon has already
/// published an endpoint for this build.
///
/// # Errors
///
/// Returns an error if another daemon is running, or if the endpoint cannot be
/// published or listened on.
pub fn run(idle_timeout: Duration) -> anyhow::Result<()> {
    let key = InstanceKey::from_build_info()?;
    let dir = InstanceDir::new(&key)?;

    if let Some(endpoint) = dir.read_endpoint()
        && daemon_is_alive(&endpoint)
    {
        anyhow::bail!(
            "a daemon for this rust-analyzer build is already running (pid {})",
            endpoint.pid
        );
    }

    let listener = TcpListener::bind((Ipv4Addr::LOCALHOST, 0))?;
    let addr = listener.local_addr()?;
    let token = Token::generate();
    dir.write_endpoint(&Endpoint {
        transport: Transport::Tcp { addr },
        token: token.clone(),
        pid: process::id(),
        version: version().to_string(),
    })?;

    rayon::ThreadPoolBuilder::new()
        .thread_name(|ix| format!("RayonWorker{ix}"))
        .build_global()
        .unwrap();

    let state = Arc::new(DaemonState {
        token,
        env_fingerprint: protocol::env_fingerprint(),
        started: Instant::now(),
        dir,
        shared: Arc::new(SharedServices::default()),
        connections: Mutex::new(Connections {
            live: 0,
            last_activity: Instant::now(),
            sessions: FxHashMap::default(),
        }),
    });

    tracing::info!(%addr, pid = process::id(), version = %version(), "daemon is listening");

    let watcher_state = Arc::clone(&state);
    Builder::new(ThreadIntent::Worker, "IdleWatcher")
        .allow_leak(true)
        .spawn(move || idle_watch(&watcher_state, idle_timeout))?;

    let mut next_connection_id = 0u64;
    for stream in listener.incoming() {
        let stream = match stream {
            Ok(it) => it,
            Err(err) => {
                tracing::warn!("failed to accept a connection: {err}");
                continue;
            }
        };
        let id = next_connection_id;
        next_connection_id += 1;
        state.connections.lock().unwrap().live += 1;
        let state = Arc::clone(&state);
        Builder::new(ThreadIntent::LatencySensitive, format!("Connection{id}"))
            .stack_size(STACK_SIZE)
            .allow_leak(true)
            .spawn(move || handle_connection(&state, stream, id))?;
    }
    Ok(())
}

struct DaemonState {
    token: Token,
    env_fingerprint: BTreeMap<String, Option<String>>,
    started: Instant,
    dir: InstanceDir,
    shared: Arc<SharedServices>,
    connections: Mutex<Connections>,
}

struct Connections {
    live: u32,
    last_activity: Instant,
    sessions: FxHashMap<u64, SessionInfo>,
}

struct SessionInfo {
    client_pid: u32,
    connected_at: Instant,
    env_mismatch: bool,
}

fn idle_watch(state: &DaemonState, idle_timeout: Duration) {
    let poll_interval =
        (idle_timeout / 10).clamp(Duration::from_millis(100), Duration::from_secs(5));
    loop {
        thread::sleep(poll_interval);
        let connections = state.connections.lock().unwrap();
        if connections.live == 0 && connections.last_activity.elapsed() >= idle_timeout {
            drop(connections);
            tracing::info!("no clients for {idle_timeout:?}, shutting down");
            shutdown(state);
        }
    }
}

fn shutdown(state: &DaemonState) -> ! {
    if let Err(err) = state.dir.remove_endpoint() {
        tracing::warn!("failed to remove the endpoint file: {err}");
    }
    process::exit(0);
}

fn handle_connection(state: &DaemonState, stream: TcpStream, id: u64) {
    struct Disconnect<'a>(&'a DaemonState, u64);
    impl Drop for Disconnect<'_> {
        fn drop(&mut self) {
            let mut connections = self.0.connections.lock().unwrap();
            connections.live -= 1;
            connections.last_activity = Instant::now();
            connections.sessions.remove(&self.1);
        }
    }
    let _guard = Disconnect(state, id);
    let _span = tracing::info_span!("connection", id).entered();

    if let Err(err) = try_handle_connection(state, stream, id) {
        tracing::error!("connection terminated: {err:#}");
    }
}

fn try_handle_connection(state: &DaemonState, stream: TcpStream, id: u64) -> anyhow::Result<()> {
    stream.set_read_timeout(Some(HANDSHAKE_TIMEOUT))?;
    stream.set_write_timeout(Some(HANDSHAKE_TIMEOUT))?;
    let hello: Hello = protocol::read_line_message(&stream)?;

    if hello.token != state.token {
        protocol::write_line_message(
            &stream,
            &HelloResponse::Rejected { reason: "invalid token".to_owned() },
        )?;
        anyhow::bail!("connection presented an invalid token");
    }
    let daemon_version = version().to_string();
    if hello.version != daemon_version {
        protocol::write_line_message(
            &stream,
            &HelloResponse::Rejected {
                reason: format!(
                    "version mismatch: daemon is {daemon_version}, client is {}",
                    hello.version
                ),
            },
        )?;
        anyhow::bail!("connection version {} does not match {daemon_version}", hello.version);
    }

    match hello.kind {
        ConnectionKind::Session { client_pid, env_fingerprint } => {
            let _span = tracing::info_span!("session", client_pid).entered();
            let env_mismatch = env_fingerprint != state.env_fingerprint;
            if env_mismatch {
                tracing::warn!(
                    client_env = ?env_fingerprint,
                    daemon_env = ?state.env_fingerprint,
                    "client environment differs from the daemon's; toolchain discovery \
                     and command execution use the daemon's environment"
                );
            }
            protocol::write_line_message(&stream, &HelloResponse::Accepted)?;
            stream.set_read_timeout(None)?;
            stream.set_write_timeout(None)?;
            state
                .connections
                .lock()
                .unwrap()
                .sessions
                .insert(id, SessionInfo { client_pid, connected_at: Instant::now(), env_mismatch });
            tracing::info!("session connected");

            let (connection, io_threads) = socket_connection(stream)?;
            let shared = Arc::clone(&state.shared);
            match panic::catch_unwind(AssertUnwindSafe(|| {
                run_session(connection, io_threads, None, shared)
            })) {
                Ok(Ok(())) => tracing::info!("session finished"),
                Ok(Err(err)) => tracing::error!("session errored: {err:#}"),
                Err(panic) => tracing::error!("session panicked: {}", panic_message(&panic)),
            }
            Ok(())
        }
        ConnectionKind::Control => {
            protocol::write_line_message(&stream, &HelloResponse::Accepted)?;
            match protocol::read_line_message(&stream)? {
                ControlRequest::Status => {
                    let status = {
                        let connections = state.connections.lock().unwrap();
                        StatusResponse {
                            version: daemon_version,
                            pid: process::id(),
                            uptime_secs: state.started.elapsed().as_secs(),
                            memory: profile::memory_usage().allocated.to_string(),
                            sessions: connections
                                .sessions
                                .values()
                                .map(|session| SessionStatus {
                                    client_pid: session.client_pid,
                                    uptime_secs: session.connected_at.elapsed().as_secs(),
                                    env_mismatch: session.env_mismatch,
                                })
                                .collect(),
                        }
                    };
                    protocol::write_line_message(&stream, &status)?;
                    Ok(())
                }
                ControlRequest::Stop => {
                    tracing::info!("shutting down on control request");
                    protocol::write_line_message(&stream, &StopAck { pid: process::id() })?;
                    shutdown(state);
                }
            }
        }
    }
}

/// Probes whether the daemon behind `endpoint` is alive by performing a handshake.
///
/// Any parseable [`HelloResponse`] proves a live daemon; connection failures or garbage
/// replies (a foreign process squatting on a reused port) count as dead.
fn daemon_is_alive(endpoint: &Endpoint) -> bool {
    let Transport::Tcp { addr } = endpoint.transport;
    let Ok(stream) = TcpStream::connect_timeout(&addr, PROBE_TIMEOUT) else {
        return false;
    };
    if stream.set_read_timeout(Some(PROBE_TIMEOUT)).is_err()
        || stream.set_write_timeout(Some(PROBE_TIMEOUT)).is_err()
    {
        return false;
    }
    let hello = Hello {
        token: endpoint.token.clone(),
        version: endpoint.version.clone(),
        kind: ConnectionKind::Control,
    };
    if protocol::write_line_message(&stream, &hello).is_err() {
        return false;
    }
    protocol::read_line_message::<HelloResponse>(&stream).is_ok()
}

/// Builds an LSP [`Connection`] on top of an established, handshaken stream.
fn socket_connection(stream: TcpStream) -> io::Result<(Connection, IoThreads)> {
    let reader_stream = stream.try_clone()?;
    let (reader_sender, receiver) = bounded::<Message>(0);
    let reader = thread::spawn(move || {
        let mut reader_stream = io::BufReader::new(reader_stream);
        while let Some(msg) = Message::read(&mut reader_stream)? {
            let is_exit = matches!(&msg, Message::Notification(n) if n.method == "exit");
            if reader_sender.send(msg).is_err() {
                break;
            }
            if is_exit {
                break;
            }
        }
        Ok(())
    });

    let (sender, writer_receiver) = bounded::<Message>(0);
    let mut writer_stream = stream;
    let writer = thread::spawn(move || {
        writer_receiver.into_iter().try_for_each(|msg| msg.write(&mut writer_stream))
    });

    Ok((Connection { sender, receiver }, IoThreads::Socket(vec![reader, writer])))
}

fn panic_message(panic: &Box<dyn std::any::Any + Send>) -> &str {
    match panic.downcast_ref::<String>() {
        Some(it) => it,
        None => panic.downcast_ref::<&'static str>().copied().unwrap_or("unknown panic payload"),
    }
}
