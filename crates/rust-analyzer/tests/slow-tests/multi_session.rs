//! Tests running several LSP sessions inside one process over memory transports,
//! sharing process-wide services the way sessions of one daemon do.

use std::sync::Arc;

use lsp_types::{HoverParams, HoverRequest, Position, TextDocumentPositionParams};
use rust_analyzer::SharedServices;
use test_utils::skip_slow_tests;

use crate::support::Project;

/// A workspace with a hand-rolled derive macro, so proc-macro servers get spawned.
const PROC_MACRO_FIXTURE: &str = r###"
//- /foo/Cargo.toml
[package]
name = "foo"
version = "0.0.0"
edition = "2021"
[dependencies]
bar = {path = "../bar"}

//- /foo/src/main.rs
use bar::Bar;

trait Bar {
  fn bar();
}
#[derive(Bar)]
struct Foo {}
fn main() {
  Foo::bar();
}

//- /bar/Cargo.toml
[package]
name = "bar"
version = "0.0.0"
edition = "2021"

[lib]
proc-macro = true

//- /bar/src/lib.rs
use proc_macro::{Delimiter, Group, Ident, Span, TokenStream, TokenTree};
macro_rules! t {
    ($n:literal) => {
        TokenTree::from(Ident::new($n, Span::call_site()))
    };
    ({}) => {
        TokenTree::from(Group::new(Delimiter::Brace, TokenStream::new()))
    };
    (()) => {
        TokenTree::from(Group::new(Delimiter::Parenthesis, TokenStream::new()))
    };
}
#[proc_macro_derive(Bar)]
pub fn foo(_input: TokenStream) -> TokenStream {
    // impl Bar for Foo { fn bar() {} }
    let mut res = TokenStream::new();
    let mut tokens = vec![t!("impl"), t!("Bar"), t!("for"), t!("Foo")];
    let mut fn_stream = TokenStream::new();
    fn_stream.extend(vec![t!("fn"), t!("bar"), t!(()), t!({})]);
    tokens.push(Group::new(Delimiter::Brace, fn_stream).into());
    res.extend(tokens);
    res
}
"###;

#[test]
fn sessions_share_proc_macro_servers() {
    if skip_slow_tests() {
        return;
    }

    let shared = Arc::new(SharedServices::default());
    let session = |shared: &Arc<SharedServices>| {
        Project::with_fixture(PROC_MACRO_FIXTURE)
            .with_config(serde_json::json!({
                "cargo": {
                    "buildScripts": {
                        "enable": true
                    },
                    "sysroot": "discover",
                },
                "procMacro": {
                    "enable": true,
                }
            }))
            .root("foo")
            .root("bar")
            .with_shared(shared)
            .server()
            .wait_until_workspace_is_loaded()
    };

    let first = session(&shared);
    assert_eq!(shared.pooled_proc_macro_servers(), 1);

    let second = session(&shared);
    assert_eq!(
        shared.pooled_proc_macro_servers(),
        1,
        "the second session must reuse the pooled proc-macro server"
    );

    // Both sessions resolve the derive through the shared server.
    for server in [&first, &second] {
        let res = server.send_request::<HoverRequest>(HoverParams {
            text_document_position_params: TextDocumentPositionParams::new(
                server.doc_id("foo/src/main.rs"),
                Position::new(8, 9),
            ),
            work_done_progress_params: Default::default(),
        });
        let contents = res["contents"]["value"].as_str().unwrap();
        assert!(contents.contains("fn bar()"), "derive did not resolve: {contents}");
    }

    drop(first);
    assert_eq!(
        shared.pooled_proc_macro_servers(),
        1,
        "the server must survive as long as one session uses it"
    );

    drop(second);
    assert_eq!(
        shared.pooled_proc_macro_servers(),
        0,
        "the server must exit with the last session using it"
    );
}
