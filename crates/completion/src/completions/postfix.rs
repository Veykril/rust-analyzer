//! Postfix completions, like `Ok(10).ifl<|>` => `if let Ok() = Ok(10) { <|> }`.

mod format_like;

use ide_db::ty_filter::TryEnum;
use itertools::Itertools;
use syntax::{
    ast::{self, AstNode, AstToken},
    TextRange, TextSize,
};
use text_edit::TextEdit;

use self::format_like::add_format_like_completions;
use crate::{
    config::SnippetCap,
    context::CompletionContext,
    item::{Builder, CompletionKind},
    CompletionItem, CompletionItemKind, Completions,
};

pub(crate) fn complete_postfix(acc: &mut Completions, ctx: &CompletionContext) {
    if !ctx.config.enable_postfix_completions {
        return;
    }

    let dot_receiver = match &ctx.dot_receiver {
        Some(it) => it,
        None => return,
    };

    let receiver_text =
        get_receiver_text(dot_receiver, ctx.dot_receiver_is_ambiguous_float_literal);

    let receiver_ty = match ctx.sema.type_of_expr(&dot_receiver) {
        Some(it) => it,
        None => return,
    };

    let cap = match ctx.config.snippet_cap {
        Some(it) => it,
        None => return,
    };
    let try_enum = TryEnum::from_ty(&ctx.sema, &receiver_ty);
    if let Some(try_enum) = &try_enum {
        match try_enum {
            TryEnum::Result => {
                postfix_snippet(
                    ctx,
                    cap,
                    &dot_receiver,
                    "ifl",
                    "if let Ok {}",
                    &format!("if let Ok($1) = {} {{\n    $0\n}}", receiver_text),
                )
                .add_to(acc);

                postfix_snippet(
                    ctx,
                    cap,
                    &dot_receiver,
                    "while",
                    "while let Ok {}",
                    &format!("while let Ok($1) = {} {{\n    $0\n}}", receiver_text),
                )
                .add_to(acc);
            }
            TryEnum::Option => {
                postfix_snippet(
                    ctx,
                    cap,
                    &dot_receiver,
                    "ifl",
                    "if let Some {}",
                    &format!("if let Some($1) = {} {{\n    $0\n}}", receiver_text),
                )
                .add_to(acc);

                postfix_snippet(
                    ctx,
                    cap,
                    &dot_receiver,
                    "while",
                    "while let Some {}",
                    &format!("while let Some($1) = {} {{\n    $0\n}}", receiver_text),
                )
                .add_to(acc);
            }
        }
    } else if receiver_ty.is_bool() || receiver_ty.is_unknown() {
        postfix_snippet(
            ctx,
            cap,
            &dot_receiver,
            "if",
            "if expr {}",
            &format!("if {} {{\n    $0\n}}", receiver_text),
        )
        .add_to(acc);
        postfix_snippet(
            ctx,
            cap,
            &dot_receiver,
            "while",
            "while expr {}",
            &format!("while {} {{\n    $0\n}}", receiver_text),
        )
        .add_to(acc);
        postfix_snippet(ctx, cap, &dot_receiver, "not", "!expr", &format!("!{}", receiver_text))
            .add_to(acc);
    }

    postfix_snippet(ctx, cap, &dot_receiver, "ref", "&expr", &format!("&{}", receiver_text))
        .add_to(acc);
    postfix_snippet(
        ctx,
        cap,
        &dot_receiver,
        "refm",
        "&mut expr",
        &format!("&mut {}", receiver_text),
    )
    .add_to(acc);

    // The rest of the postfix completions create an expression that moves an argument,
    // so it's better to consider references now to avoid breaking the compilation
    let dot_receiver = include_references(dot_receiver);
    let receiver_text =
        get_receiver_text(&dot_receiver, ctx.dot_receiver_is_ambiguous_float_literal);

    match try_enum {
        Some(try_enum) => match try_enum {
            TryEnum::Result => {
                postfix_snippet(
                    ctx,
                    cap,
                    &dot_receiver,
                    "match",
                    "match expr {}",
                    &format!("match {} {{\n    Ok(${{1:_}}) => {{$2}},\n    Err(${{3:_}}) => {{$0}},\n}}", receiver_text),
                )
                .add_to(acc);
            }
            TryEnum::Option => {
                postfix_snippet(
                    ctx,
                    cap,
                    &dot_receiver,
                    "match",
                    "match expr {}",
                    &format!(
                        "match {} {{\n    Some(${{1:_}}) => {{$2}},\n    None => {{$0}},\n}}",
                        receiver_text
                    ),
                )
                .add_to(acc);
            }
        },
        None => {
            postfix_snippet(
                ctx,
                cap,
                &dot_receiver,
                "match",
                "match expr {}",
                &format!("match {} {{\n    ${{1:_}} => {{$0}},\n}}", receiver_text),
            )
            .add_to(acc);
        }
    }

    postfix_snippet(
        ctx,
        cap,
        &dot_receiver,
        "box",
        "Box::new(expr)",
        &format!("Box::new({})", receiver_text),
    )
    .add_to(acc);

    postfix_snippet(ctx, cap, &dot_receiver, "ok", "Ok(expr)", &format!("Ok({})", receiver_text))
        .add_to(acc);

    postfix_snippet(
        ctx,
        cap,
        &dot_receiver,
        "some",
        "Some(expr)",
        &format!("Some({})", receiver_text),
    )
    .add_to(acc);

    postfix_snippet(
        ctx,
        cap,
        &dot_receiver,
        "dbg",
        "dbg!(expr)",
        &format!("dbg!({})", receiver_text),
    )
    .add_to(acc);

    postfix_snippet(
        ctx,
        cap,
        &dot_receiver,
        "dbgr",
        "dbg!(&expr)",
        &format!("dbg!(&{})", receiver_text),
    )
    .add_to(acc);

    postfix_snippet(
        ctx,
        cap,
        &dot_receiver,
        "call",
        "function(expr)",
        &format!("${{1}}({})", receiver_text),
    )
    .add_to(acc);

    if let ast::Expr::Literal(literal) = dot_receiver.clone() {
        if let Some(literal_text) = ast::String::cast(literal.token()) {
            add_format_like_completions(acc, ctx, &dot_receiver, cap, &literal_text);
        }
    }
    add_postfix_let_destruct(acc, ctx, cap, &dot_receiver, &receiver_ty, &receiver_text);
}

fn add_postfix_let_destruct(
    acc: &mut Completions,
    ctx: &CompletionContext,
    cap: SnippetCap,
    dot_receiver: &ast::Expr,
    receiver_ty: &hir::Type,
    receiver_text: &str,
) {
    if receiver_ty.is_tuple() && !receiver_ty.is_unit() {
        let fields = receiver_ty.tuple_fields(ctx.db);
        let field_names = fields
            .iter()
            .enumerate()
            .map(|(idx, ty)| match ty.as_adt() {
                Some(adt) => format!("${{{idx}:{name}}}", idx = idx, name = adt.name(ctx.db)),
                None => format!("${}", idx),
            })
            .collect::<Vec<_>>();
        postfix_snippet(
            ctx,
            cap,
            &dot_receiver,
            "letp",
            "let pattern = expr;",
            &format!("let ({}) = {};", field_names.iter().join(", "), receiver_text),
        )
        .add_to(acc);
        postfix_snippet(
            ctx,
            cap,
            &dot_receiver,
            "letpm",
            "let pattern = expr;",
            &format!("let (mut {}) = {};", field_names.iter().join(", mut "), receiver_text),
        )
        .add_to(acc);
    } else if let Some(strukt) = receiver_ty.as_adt().and_then(|adt| match adt {
        hir::Adt::Struct(strukt) if !strukt.is_unit(ctx.db) => Some(strukt),
        _ => None,
    }) {
        let name = strukt.name(ctx.db);
        let fields = strukt.fields(ctx.db);
        let field_names = fields
            .iter()
            .enumerate()
            .map(|(idx, field)| format!("${{{idx}:{name}}}", idx = idx, name = field.name(ctx.db)))
            .collect::<Vec<_>>();
        let (immutable, mutable) = if strukt.is_tuple(ctx.db) {
            (
                format!("let {}({}) = {};", &name, field_names.iter().join(", "), receiver_text),
                format!(
                    "let {}(mut {}) = {};",
                    &name,
                    field_names.iter().join(", mut "),
                    receiver_text
                ),
            )
        } else {
            (
                format!("let {} {{{}}} = {};", &name, field_names.iter().join(", "), receiver_text),
                format!(
                    "let {} {{mut {}}} = {};",
                    &name,
                    field_names.iter().join(", mut "),
                    receiver_text
                ),
            )
        };
        postfix_snippet(ctx, cap, &dot_receiver, "letp", "let pattern = expr;", &immutable)
            .add_to(acc);
        postfix_snippet(ctx, cap, &dot_receiver, "letpm", "let pattern = expr;", &mutable)
            .add_to(acc);
    }
}

fn get_receiver_text(receiver: &ast::Expr, receiver_is_ambiguous_float_literal: bool) -> String {
    if receiver_is_ambiguous_float_literal {
        let text = receiver.syntax().text();
        let without_dot = ..text.len() - TextSize::of('.');
        text.slice(without_dot).to_string()
    } else {
        receiver.to_string()
    }
}

fn include_references(initial_element: &ast::Expr) -> ast::Expr {
    let mut resulting_element = initial_element.clone();
    while let Some(parent_ref_element) =
        resulting_element.syntax().parent().and_then(ast::RefExpr::cast)
    {
        resulting_element = ast::Expr::from(parent_ref_element);
    }
    resulting_element
}

fn postfix_snippet(
    ctx: &CompletionContext,
    cap: SnippetCap,
    receiver: &ast::Expr,
    label: &str,
    detail: &str,
    snippet: &str,
) -> Builder {
    let edit = {
        let receiver_syntax = receiver.syntax();
        let receiver_range = ctx.sema.original_range(receiver_syntax).range;
        let delete_range = TextRange::new(receiver_range.start(), ctx.source_range().end());
        TextEdit::replace(delete_range, snippet.to_string())
    };
    CompletionItem::new(CompletionKind::Postfix, ctx.source_range(), label)
        .detail(detail)
        .kind(CompletionItemKind::Snippet)
        .snippet_edit(cap, edit)
}

#[cfg(test)]
mod tests {
    use expect_test::{expect, Expect};

    use crate::{
        test_utils::{check_edit, completion_list},
        CompletionKind,
    };

    fn check(ra_fixture: &str, expect: Expect) {
        let actual = completion_list(ra_fixture, CompletionKind::Postfix);
        expect.assert_eq(&actual)
    }

    #[test]
    fn postfix_completion_works_for_trivial_path_expression() {
        check(
            r#"
fn main() {
    let bar = true;
    bar.<|>
}
"#,
            expect![[r#"
                sn box   Box::new(expr)
                sn call  function(expr)
                sn dbg   dbg!(expr)
                sn dbgr  dbg!(&expr)
                sn if    if expr {}
                sn match match expr {}
                sn not   !expr
                sn ok    Ok(expr)
                sn ref   &expr
                sn refm  &mut expr
                sn some  Some(expr)
                sn while while expr {}
            "#]],
        );
    }

    #[test]
    fn postfix_type_filtering() {
        check(
            r#"
fn main() {
    let bar: u8 = 12;
    bar.<|>
}
"#,
            expect![[r#"
                sn box   Box::new(expr)
                sn call  function(expr)
                sn dbg   dbg!(expr)
                sn dbgr  dbg!(&expr)
                sn match match expr {}
                sn ok    Ok(expr)
                sn ref   &expr
                sn refm  &mut expr
                sn some  Some(expr)
            "#]],
        )
    }

    #[test]
    fn option_iflet() {
        check_edit(
            "ifl",
            r#"
enum Option<T> { Some(T), None }

fn main() {
    let bar = Option::Some(true);
    bar.<|>
}
"#,
            r#"
enum Option<T> { Some(T), None }

fn main() {
    let bar = Option::Some(true);
    if let Some($1) = bar {
    $0
}
}
"#,
        );
    }

    #[test]
    fn result_match() {
        check_edit(
            "match",
            r#"
enum Result<T, E> { Ok(T), Err(E) }

fn main() {
    let bar = Result::Ok(true);
    bar.<|>
}
"#,
            r#"
enum Result<T, E> { Ok(T), Err(E) }

fn main() {
    let bar = Result::Ok(true);
    match bar {
    Ok(${1:_}) => {$2},
    Err(${3:_}) => {$0},
}
}
"#,
        );
    }

    #[test]
    fn tuple_let_destruct() {
        check_edit(
            "letp",
            r#"
struct Foo;
struct Bar(i32);

fn main() {
    let foo = (123, 544, 0.5345, "foobar", Foo, Bar(3));
    foo.<|>
}
"#,
            r#"
struct Foo;
struct Bar(i32);

fn main() {
    let foo = (123, 544, 0.5345, "foobar", Foo, Bar(3));
    let ($0, $1, $2, $3, ${4:Foo}, ${5:Bar}) = foo;
}
"#,
        );
    }

    #[test]
    fn tuple_let_mut_destruct() {
        check_edit(
            "letpm",
            r#"
struct Foo;
struct Bar(i32);

fn main() {
    let foo = (123, 544, 0.5345, "foobar", Foo, Bar(3));
    foo.<|>
}
"#,
            r#"
struct Foo;
struct Bar(i32);

fn main() {
    let foo = (123, 544, 0.5345, "foobar", Foo, Bar(3));
    let (mut $0, mut $1, mut $2, mut $3, mut ${4:Foo}, mut ${5:Bar}) = foo;
}
"#,
        );
    }

    #[test]
    fn record_let_destruct() {
        check_edit(
            "letp",
            r#"
struct Foo { bar: i32, baz: f32, qux: Qux };
struct Qux(i32);

fn main() {
    let foo = Foo { bar: 3, baz: 5.1, qux: Qux(1)};
    foo.<|>
}
"#,
            r#"
struct Foo { bar: i32, baz: f32, qux: Qux };
struct Qux(i32);

fn main() {
    let foo = Foo { bar: 3, baz: 5.1, qux: Qux(1)};
    let Foo {${0:bar}, ${1:baz}, ${2:qux}} = foo;
}
"#,
        );
    }

    #[test]
    fn postfix_completion_works_for_ambiguous_float_literal() {
        check_edit("refm", r#"fn main() { 42.<|> }"#, r#"fn main() { &mut 42 }"#)
    }

    #[test]
    fn works_in_simple_macro() {
        check_edit(
            "dbg",
            r#"
macro_rules! m { ($e:expr) => { $e } }
fn main() {
    let bar: u8 = 12;
    m!(bar.d<|>)
}
"#,
            r#"
macro_rules! m { ($e:expr) => { $e } }
fn main() {
    let bar: u8 = 12;
    m!(dbg!(bar))
}
"#,
        );
    }

    #[test]
    fn postfix_completion_for_references() {
        check_edit("dbg", r#"fn main() { &&42.<|> }"#, r#"fn main() { dbg!(&&42) }"#);
        check_edit("refm", r#"fn main() { &&42.<|> }"#, r#"fn main() { &&&mut 42 }"#);
    }

    #[test]
    fn postfix_completion_for_format_like_strings() {
        check_edit(
            "fmt",
            r#"fn main() { "{some_var:?}".<|> }"#,
            r#"fn main() { format!("{:?}", some_var) }"#,
        );
        check_edit(
            "panic",
            r#"fn main() { "Panic with {a}".<|> }"#,
            r#"fn main() { panic!("Panic with {}", a) }"#,
        );
        check_edit(
            "println",
            r#"fn main() { "{ 2+2 } { SomeStruct { val: 1, other: 32 } :?}".<|> }"#,
            r#"fn main() { println!("{} {:?}", 2+2, SomeStruct { val: 1, other: 32 }) }"#,
        );
        check_edit(
            "loge",
            r#"fn main() { "{2+2}".<|> }"#,
            r#"fn main() { log::error!("{}", 2+2) }"#,
        );
        check_edit(
            "logt",
            r#"fn main() { "{2+2}".<|> }"#,
            r#"fn main() { log::trace!("{}", 2+2) }"#,
        );
        check_edit(
            "logd",
            r#"fn main() { "{2+2}".<|> }"#,
            r#"fn main() { log::debug!("{}", 2+2) }"#,
        );
        check_edit(
            "logi",
            r#"fn main() { "{2+2}".<|> }"#,
            r#"fn main() { log::info!("{}", 2+2) }"#,
        );
        check_edit(
            "logw",
            r#"fn main() { "{2+2}".<|> }"#,
            r#"fn main() { log::warn!("{}", 2+2) }"#,
        );
        check_edit(
            "loge",
            r#"fn main() { "{2+2}".<|> }"#,
            r#"fn main() { log::error!("{}", 2+2) }"#,
        );
    }
}
