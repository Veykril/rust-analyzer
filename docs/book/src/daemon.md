# Daemon Mode (Experimental)

When several clients analyze projects on the same machine — multiple editor windows,
or agent harnesses running many concurrent sessions — each `rust-analyzer` process
duplicates a lot of work and memory. Daemon mode deduplicates this by hosting all
sessions of the same rust-analyzer build inside a single shared daemon process, with
each client talking to it through a thin proxy.

Daemon mode is experimental and currently opt-in per client: start the server with

```bash
rust-analyzer --use-daemon
```

The proxy transparently relays the LSP session to the daemon, spawning the daemon
first if none is running. When the daemon cannot be reached (for example in sandboxes
that block local sockets), the proxy falls back to running the session in-process and
notifies the client with a warning. The daemon exits on its own after ten minutes
without any connected client.

Details worth knowing:

- One daemon exists per rust-analyzer build (version and commit). Upgrading
  rust-analyzer strands the old daemon, which idles out on its own.
- Sessions run with the environment of whichever client spawned the daemon first. If
  another client connects with a different `PATH`, `RUSTUP_HOME`, `RUSTUP_TOOLCHAIN`,
  or `CARGO_HOME`, toolchain discovery and command execution still use the daemon's
  environment; the daemon logs a warning when this happens.
- If the daemon dies, all of its clients see their server "crash" simultaneously and
  restart it through their usual server-restart handling.

## Inspecting and stopping the daemon

```bash
rust-analyzer daemon status  # prints the daemon's sessions and memory usage as JSON
rust-analyzer daemon stop    # stops the daemon, disconnecting all of its clients
```

`daemon stop` is the escape hatch if the daemon ever wedges; clients reconnect (or
respawn a fresh daemon) when their session restarts.

The daemon's discovery state and log live in a per-user directory, keyed by build:
the platform runtime or cache directory under `rust-analyzer/daemon/`, overridable
with the `RA_DAEMON_DIR` environment variable. The daemon's log file is written next
to its endpoint file in that directory.
