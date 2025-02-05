//! A standalone binary for `proc-macro-srv`.
//! Driver for proc macro server
#![cfg_attr(feature = "in-rust-tree", feature(rustc_private))]
#![allow(clippy::print_stderr)]

#[cfg(feature = "in-rust-tree")]
extern crate rustc_driver as _;

#[cfg(all(not(feature = "ng"), any(feature = "sysroot-abi", rust_analyzer)))]
mod main_loop;
#[cfg(all(not(feature = "ng"), any(feature = "sysroot-abi", rust_analyzer)))]
use main_loop::run;
#[cfg(all(feature = "ng", any(feature = "sysroot-abi", rust_analyzer)))]
mod main_loop_ng;
#[cfg(all(feature = "ng", any(feature = "sysroot-abi", rust_analyzer)))]
use main_loop_ng::run;

fn main() -> std::io::Result<()> {
    let v = std::env::var("RUST_ANALYZER_INTERNALS_DO_NOT_USE");
    if v.is_err() {
        eprintln!(
            "This is an IDE implementation detail, you can use this tool by exporting RUST_ANALYZER_INTERNALS_DO_NOT_USE."
        );
        eprintln!(
            "Note that this tool's API is highly unstable and may break without prior notice"
        );
        std::process::exit(122);
    }

    run(proc_macro_api::ng_protocol::msg::SpanMode::RustAnalyzer)
}

#[cfg(not(any(feature = "sysroot-abi", rust_analyzer)))]
fn run() -> std::io::Result<()> {
    Err(std::io::Error::new(
        std::io::ErrorKind::Unsupported,
        "proc-macro-srv-cli needs to be compiled with the `sysroot-abi` feature to function"
            .to_owned(),
    ))
}
