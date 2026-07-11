//! Discovery of a running rust-analyzer daemon.
//!
//! A daemon serves exactly one rust-analyzer build: proxies and daemons find each other
//! through a per-user, per-build [`InstanceDir`] containing
//!
//! - `endpoint`: the [`Endpoint`] of the running daemon, atomically replaced on publish,
//! - `lock`: an advisory file lock serializing daemon spawn attempts between proxies,
//! - `log`: the daemon's log output.
//!
//! A leftover `endpoint` file of a dead daemon is detected by failing to connect to it;
//! the proxy that wins the spawn lock replaces it.

use std::{
    env, fmt, fs,
    hash::{Hash, Hasher},
    io,
    net::SocketAddr,
    path::{Path, PathBuf},
};

use rustc_hash::FxHasher;
use serde_derive::{Deserialize, Serialize};

use crate::version::version;

/// Identity of a rust-analyzer build, keying the daemon instance a proxy may talk to.
///
/// Released builds are keyed by version, channel, and commit so that all copies of a
/// release share one daemon. Dev builds carry no commit info (their version is plain
/// `0.0.0`), so they are keyed by binary identity (path and mtime) instead, ensuring a
/// rebuild never talks to a stale daemon.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstanceKey(String);

impl InstanceKey {
    /// Computes the instance key of the currently running build.
    ///
    /// # Errors
    ///
    /// Returns [`io::Error`] if this is a dev build and the current executable cannot
    /// be inspected to establish its identity.
    pub fn from_build_info() -> io::Result<InstanceKey> {
        let version = version();
        let key = match &version.commit_info {
            Some(commit_info) => format!(
                "{}-{}-{}",
                version.version,
                version.release_channel.unwrap_or("unknown"),
                commit_info.short_commit_hash
            ),
            None => {
                let exe = env::current_exe()?;
                let metadata = fs::metadata(&exe)?;
                let mut hasher = FxHasher::default();
                exe.hash(&mut hasher);
                metadata.len().hash(&mut hasher);
                if let Ok(mtime) = metadata.modified() {
                    mtime.hash(&mut hasher);
                }
                format!("dev-{:016x}", hasher.finish())
            }
        };
        let key = key
            .chars()
            .map(
                |c| if c.is_ascii_alphanumeric() || matches!(c, '.' | '-' | '_') { c } else { '_' },
            )
            .collect();
        Ok(InstanceKey(key))
    }
}

impl AsRef<str> for InstanceKey {
    fn as_ref(&self) -> &str {
        &self.0
    }
}

/// Per-user directory holding the discovery state for one daemon instance.
#[derive(Debug)]
pub struct InstanceDir {
    path: PathBuf,
}

impl InstanceDir {
    /// Resolves and creates the instance directory for `key`.
    ///
    /// The parent directory is taken from the `RA_DAEMON_DIR` environment variable if
    /// set (hermetic tests, unusual setups), and otherwise placed in the platform's
    /// runtime or cache directory.
    ///
    /// # Errors
    ///
    /// Returns [`io::Error`] if no base directory can be determined or the directory
    /// cannot be created.
    pub fn new(key: &InstanceKey) -> io::Result<InstanceDir> {
        let base = match env::var_os("RA_DAEMON_DIR") {
            Some(dir) => PathBuf::from(dir),
            None => dirs::runtime_dir()
                .or_else(dirs::cache_dir)
                .ok_or_else(|| {
                    io::Error::other("neither a runtime nor a cache directory is available")
                })?
                .join("rust-analyzer")
                .join("daemon"),
        };
        InstanceDir::create(base.join(key.as_ref()))
    }

    fn create(path: PathBuf) -> io::Result<InstanceDir> {
        fs::create_dir_all(&path)?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&path, fs::Permissions::from_mode(0o700))?;
        }
        Ok(InstanceDir { path })
    }

    /// Returns the path of the daemon's log file.
    pub fn log_path(&self) -> PathBuf {
        self.path.join("log")
    }

    /// Returns the path the daemon's stderr is redirected to (panics and other output
    /// bypassing the log).
    pub fn stderr_path(&self) -> PathBuf {
        self.path.join("stderr")
    }

    fn endpoint_path(&self) -> PathBuf {
        self.path.join("endpoint")
    }

    /// Reads the endpoint published by a (presumably) running daemon.
    ///
    /// Returns `None` if no endpoint is published or the file cannot be parsed (a stale
    /// or foreign leftover). Whether the daemon behind an endpoint is actually alive can
    /// only be established by connecting to it.
    pub fn read_endpoint(&self) -> Option<Endpoint> {
        let contents = fs::read(self.endpoint_path()).ok()?;
        serde_json::from_slice(&contents).ok()
    }

    /// Atomically publishes `endpoint`, replacing any previously published one.
    ///
    /// # Errors
    ///
    /// Returns [`io::Error`] if the endpoint file cannot be written.
    pub fn write_endpoint(&self, endpoint: &Endpoint) -> io::Result<()> {
        let tmp = self.path.join("endpoint.tmp");
        write_private(&tmp, &serde_json::to_vec_pretty(endpoint).unwrap())?;
        fs::rename(&tmp, self.endpoint_path())
    }

    /// Removes the published endpoint, if any.
    ///
    /// # Errors
    ///
    /// Returns [`io::Error`] if the endpoint file exists but cannot be removed.
    pub fn remove_endpoint(&self) -> io::Result<()> {
        match fs::remove_file(self.endpoint_path()) {
            Err(err) if err.kind() != io::ErrorKind::NotFound => Err(err),
            Ok(()) | Err(_) => Ok(()),
        }
    }

    /// Takes the spawn lock, blocking until it is free.
    ///
    /// Proxies hold this while checking for and spawning a daemon, so that a stampede of
    /// simultaneously started clients results in exactly one daemon.
    ///
    /// # Errors
    ///
    /// Returns [`io::Error`] if the lock file cannot be opened or locked.
    pub fn lock(&self) -> io::Result<SpawnLock> {
        let file = fs::OpenOptions::new()
            .create(true)
            .truncate(false)
            .write(true)
            .open(self.path.join("lock"))?;
        file.lock()?;
        Ok(SpawnLock(file))
    }
}

/// A held spawn lock, released on drop.
#[derive(Debug)]
pub struct SpawnLock(fs::File);

impl Drop for SpawnLock {
    fn drop(&mut self) {
        let _ = self.0.unlock();
    }
}

/// Connection details of a running daemon, as stored in its `endpoint` file.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Endpoint {
    /// The transport the daemon listens on.
    #[serde(flatten)]
    pub transport: Transport,
    /// Shared secret a connection must present in the handshake.
    pub token: Token,
    /// Process id of the daemon, for diagnostics only.
    pub pid: u32,
    /// Human-readable build description of the daemon, for diagnostics only.
    pub version: String,
}

/// A transport a daemon can listen on.
///
/// Stored tagged in the endpoint file so that additional transports (unix sockets,
/// named pipes) can be added without changing the discovery protocol.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "transport", rename_all = "kebab-case")]
pub enum Transport {
    /// TCP on a loopback address, authenticated by [`Endpoint::token`].
    Tcp {
        /// The loopback address the daemon accepts connections on.
        addr: SocketAddr,
    },
}

/// Shared secret authenticating connections to a daemon.
///
/// The TCP listener is reachable by every local process, so the daemon only talks to
/// connections that present the token from the owner-readable endpoint file.
#[derive(Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(transparent)]
pub struct Token(String);

impl Token {
    /// Generates a fresh token from 256 bits of OS entropy.
    ///
    /// # Panics
    ///
    /// Panics if the OS entropy source fails.
    pub fn generate() -> Token {
        let mut bytes = [0u8; 32];
        getrandom::fill(&mut bytes).expect("failed to obtain OS entropy");
        Token(bytes.iter().map(|b| format!("{b:02x}")).collect())
    }
}

impl AsRef<str> for Token {
    fn as_ref(&self) -> &str {
        &self.0
    }
}

impl fmt::Debug for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Token(redacted)")
    }
}

fn write_private(path: &Path, contents: &[u8]) -> io::Result<()> {
    let mut options = fs::OpenOptions::new();
    options.write(true).create(true).truncate(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    io::Write::write_all(&mut options.open(path)?, contents)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_dir(name: &str) -> InstanceDir {
        let path = env::temp_dir()
            .join("ra-daemon-endpoint-tests")
            .join(format!("{name}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&path);
        InstanceDir::create(path).unwrap()
    }

    fn endpoint() -> Endpoint {
        Endpoint {
            transport: Transport::Tcp { addr: "127.0.0.1:12345".parse().unwrap() },
            token: Token::generate(),
            pid: std::process::id(),
            version: version().to_string(),
        }
    }

    #[test]
    fn endpoint_roundtrip() {
        let dir = test_dir("roundtrip");
        assert_eq!(dir.read_endpoint(), None);
        let endpoint = endpoint();
        dir.write_endpoint(&endpoint).unwrap();
        assert_eq!(dir.read_endpoint(), Some(endpoint.clone()));

        let replacement = Endpoint { pid: endpoint.pid + 1, ..endpoint };
        dir.write_endpoint(&replacement).unwrap();
        assert_eq!(dir.read_endpoint(), Some(replacement));

        dir.remove_endpoint().unwrap();
        assert_eq!(dir.read_endpoint(), None);
        dir.remove_endpoint().unwrap();
    }

    #[test]
    fn garbage_endpoint_reads_as_absent() {
        let dir = test_dir("garbage");
        fs::write(dir.endpoint_path(), b"not json").unwrap();
        assert_eq!(dir.read_endpoint(), None);
    }

    #[test]
    fn tokens_are_unique_and_redacted() {
        let a = Token::generate();
        let b = Token::generate();
        assert_ne!(a.as_ref(), b.as_ref());
        assert_eq!(a.as_ref().len(), 64);
        assert_eq!(format!("{a:?}"), "Token(redacted)");
    }

    #[test]
    fn instance_key_is_fs_safe() {
        let key = InstanceKey::from_build_info().unwrap();
        assert!(!key.as_ref().is_empty());
        assert!(
            key.as_ref().chars().all(|c| c.is_ascii_alphanumeric() || matches!(c, '.' | '-' | '_'))
        );
    }

    #[test]
    fn spawn_lock_excludes() {
        let dir = test_dir("lock");
        let held = dir.lock().unwrap();
        let contender = fs::OpenOptions::new().write(true).open(dir.path.join("lock")).unwrap();
        assert!(matches!(contender.try_lock(), Err(std::fs::TryLockError::WouldBlock)));
        drop(held);
        contender.try_lock().unwrap();
    }
}
