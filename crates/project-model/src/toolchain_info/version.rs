//! Get the version string of the toolchain.

use anyhow::Context;
use rustc_hash::FxHashMap;
use semver::Version;
use toolchain::Tool;

use crate::{toolchain_info::QueryConfig, utf8_stdout};

pub(crate) fn get(
    config: QueryConfig<'_>,
    extra_env: &FxHashMap<String, Option<String>>,
) -> Result<Option<Version>, anyhow::Error> {
    let (mut cmd, prefix) = match config {
        QueryConfig::Cargo(sysroot, cargo_toml, _) => {
            (sysroot.tool(Tool::Cargo, cargo_toml.parent(), extra_env), "cargo ")
        }
        QueryConfig::Rustc(sysroot, current_dir) => {
            (sysroot.tool(Tool::Rustc, current_dir, extra_env), "rustc ")
        }
    };
    cmd.arg("--version");
    let out = utf8_stdout(&mut cmd).with_context(|| format!("Failed to query rust toolchain version via `{cmd:?}`, is your toolchain setup correctly?"))?;

    let version =
        out.strip_prefix(prefix).and_then(|it| Version::parse(it.split_whitespace().next()?).ok());
    if version.is_none() {
        tracing::warn!("Failed to parse `{cmd:?}` output `{out}` as a semver version");
    }
    anyhow::Ok(version)
}

pub fn require_cargo_unstable_options<'a>(
    version: Option<&Version>,
    cmd: &'a mut std::process::Command,
) -> &'a mut std::process::Command {
    if version.is_none_or(|v| v.pre.as_str() == "nightly") {
        cmd.env("__CARGO_TEST_CHANNEL_OVERRIDE_DO_NOT_USE_THIS", "nightly");
    }
    cmd.args(["-Z", "unstable-options"])
}

#[cfg(test)]
mod tests {
    use paths::{AbsPathBuf, Utf8PathBuf};

    use crate::{ManifestPath, Sysroot};

    use super::*;

    #[test]
    fn cargo() {
        let manifest_path = concat!(env!("CARGO_MANIFEST_DIR"), "/Cargo.toml");
        let sysroot = Sysroot::empty();
        let manifest_path =
            ManifestPath::try_from(AbsPathBuf::assert(Utf8PathBuf::from(manifest_path))).unwrap();
        let cfg = QueryConfig::Cargo(&sysroot, &manifest_path, &None);
        assert!(get(cfg, &FxHashMap::default()).is_ok());
    }

    #[test]
    fn rustc() {
        let sysroot = Sysroot::empty();
        let cfg = QueryConfig::Rustc(&sysroot, env!("CARGO_MANIFEST_DIR").as_ref());
        assert!(get(cfg, &FxHashMap::default()).is_ok());
    }
}
