//! Daemonized rust-analyzer.
//!
//! One daemon process serves all clients running the same rust-analyzer build: each
//! client spawns a `rust-analyzer lsp-server --use-daemon` process that acts as a thin
//! proxy between the client's stdio and a session inside the daemon. Sessions are
//! isolated from each other; the daemon exists to share process-wide resources between
//! them (proc-macro servers, and eventually the VFS and analysis results).

pub mod control;
pub mod endpoint;
pub mod protocol;
pub mod proxy;
pub mod server;
