//! Completes constants and paths in patterns.

use ide_db::helpers::insert_use::ImportScope;

use crate::{CompletionContext, Completions};

/// Completes constants and paths in patterns.
pub(crate) fn complete_pattern(acc: &mut Completions, ctx: &CompletionContext) {
    if !(ctx.is_pat_binding_or_const || ctx.is_irrefutable_pat_binding) {
        return;
    }
    if ctx.record_pat_syntax.is_some() {
        return;
    }

    let expected_type = ctx.expected_type.as_ref().map(|ty| ty.strip_references());

    if !ctx.is_irrefutable_pat_binding {
        if let Some(hir::Adt::Enum(e)) = expected_type.as_ref().and_then(hir::Type::as_adt) {
            super::complete_enum_variants(acc, ctx, e, |acc, ctx, variant, path| {
                acc.add_qualified_variant_pat(ctx, variant, path.clone());
                acc.add_qualified_enum_variant(ctx, variant, path);
            });
        }
    }
    if let Some(hir::Adt::Struct(strukt)) = expected_type.as_ref().and_then(hir::Type::as_adt) {
        let import_scope = ctx
            .original_token
            .parent()
            .and_then(|node| ImportScope::find_insert_use_container_with_macros(&node, &ctx.sema))
            .unwrap();
        let current_module = ctx.scope.module();
        let path = current_module.and_then(|module| {
            module.find_use_path_prefixed(
                ctx.db,
                hir::ModuleDef::from(strukt),
                ctx.config.insert_use.prefix_kind,
            )
        });
        if let Some(import) = path {
            match import.as_ident() {
                Some(name) => acc.add_struct_pat(ctx, strukt, Some(name.clone())),
                None => acc.add_struct_pat_with_import(ctx, strukt, import, import_scope),
            }
        }
    }

    let ty_is_unknown = expected_type.map_or(true, |ty| ty.is_unknown());
    // FIXME: ideally, we should look at the type we are matching against and
    // suggest variants + auto-imports
    ctx.scope.process_all_names(&mut |name, res| {
        let add_resolution = match &res {
            hir::ScopeDef::ModuleDef(def) => match def {
                hir::ModuleDef::Adt(hir::Adt::Struct(strukt)) if ty_is_unknown => {
                    acc.add_struct_pat(ctx, *strukt, Some(name.clone()));
                    true
                }
                hir::ModuleDef::Variant(variant) if !ctx.is_irrefutable_pat_binding => {
                    acc.add_variant_pat(ctx, *variant, Some(name.clone()));
                    true
                }
                hir::ModuleDef::Adt(hir::Adt::Enum(..))
                | hir::ModuleDef::Variant(..)
                | hir::ModuleDef::Const(..)
                | hir::ModuleDef::Module(..) => !ctx.is_irrefutable_pat_binding,
                _ => false,
            },
            hir::ScopeDef::MacroDef(_) => true,
            hir::ScopeDef::ImplSelfType(impl_) => match impl_.self_ty(ctx.db).as_adt() {
                Some(hir::Adt::Struct(strukt)) => {
                    acc.add_struct_pat(ctx, strukt, Some(name.clone()));
                    true
                }
                Some(hir::Adt::Enum(_)) => !ctx.is_irrefutable_pat_binding,
                _ => true,
            },
            _ => false,
        };
        if add_resolution {
            acc.add_resolution(ctx, name.to_string(), &res);
        }
    });
}

#[cfg(test)]
mod tests {
    use expect_test::{expect, Expect};

    use crate::{
        test_utils::{check_edit, completion_list},
        CompletionKind,
    };

    fn check(ra_fixture: &str, expect: Expect) {
        let actual = completion_list(ra_fixture, CompletionKind::Reference);
        expect.assert_eq(&actual)
    }

    fn check_snippet(ra_fixture: &str, expect: Expect) {
        let actual = completion_list(ra_fixture, CompletionKind::Snippet);
        expect.assert_eq(&actual)
    }

    #[test]
    fn completes_enum_variants_and_modules() {
        check(
            r#"
enum E { X }
use self::E::X;
const Z: E = E::X;
mod m {}

static FOO: E = E::X;
struct Bar { f: u32 }

fn foo() {
   match E::X { a$0 }
}
"#,
            expect![[r#"
                en E
                ct Z
                st Bar
                ev X
                md m
            "#]],
        );
    }

    #[test]
    fn completes_in_simple_macro_call() {
        check(
            r#"
macro_rules! m { ($e:expr) => { $e } }
enum E { X }

fn foo() {
   m!(match E::X { a$0 })
}
"#,
            expect![[r#"
                ev E::X  ()
                en E
                ma m!(…) macro_rules! m
            "#]],
        );
    }

    #[test]
    fn completes_in_irrefutable_let() {
        check(
            r#"
enum E { X }
use self::E::X;
const Z: E = E::X;
mod m {}

static FOO: E = E::X;
struct Bar { f: u32 }

fn foo() {
   let a$0
}
"#,
            expect![[r#"
                st Bar
            "#]],
        );
    }

    #[test]
    fn completes_in_param() {
        check(
            r#"
enum E { X }

static FOO: E = E::X;
struct Bar { f: u32 }

fn foo(a$0) {
}
"#,
            expect![[r#"
                st Bar
            "#]],
        );
    }

    #[test]
    fn completes_pat_in_let() {
        check_snippet(
            r#"
struct Bar { f: u32 }

fn foo() {
   let a$0
}
"#,
            expect![[r#"
                bn Bar Bar { f$1 }$0
            "#]],
        );
    }

    #[test]
    fn completes_param_pattern() {
        check_snippet(
            r#"
struct Foo { bar: String, baz: String }
struct Bar(String, String);
struct Baz;
fn outer(a$0) {}
"#,
            expect![[r#"
                bn Foo Foo { bar$1, baz$2 }: Foo$0
                bn Bar Bar($1, $2): Bar$0
            "#]],
        )
    }

    #[test]
    fn completes_let_pattern() {
        check_snippet(
            r#"
struct Foo { bar: String, baz: String }
struct Bar(String, String);
struct Baz;
fn outer() {
    let a$0
}
"#,
            expect![[r#"
                bn Foo Foo { bar$1, baz$2 }$0
                bn Bar Bar($1, $2)$0
            "#]],
        )
    }

    #[test]
    fn completes_refutable_pattern() {
        check_snippet(
            r#"
struct Foo { bar: i32, baz: i32 }
struct Bar(String, String);
struct Baz;
fn outer() {
    match () {
        a$0
    }
}
"#,
            expect![[r#"
                bn Foo Foo { bar$1, baz$2 }$0
                bn Bar Bar($1, $2)$0
            "#]],
        )
    }

    #[test]
    fn omits_private_fields_pat() {
        check_snippet(
            r#"
mod foo {
    pub struct Foo { pub bar: i32, baz: i32 }
    pub struct Bar(pub String, String);
    pub struct Invisible(String, String);
}
use foo::*;

fn outer() {
    match () {
        a$0
    }
}
"#,
            expect![[r#"
                bn Foo Foo { bar$1, .. }$0
                bn Bar Bar($1, ..)$0
            "#]],
        )
    }

    #[test]
    fn only_shows_ident_completion() {
        check_edit(
            "Foo",
            r#"
struct Foo(i32);
fn main() {
    match Foo(92) {
        a$0(92) => (),
    }
}
"#,
            r#"
struct Foo(i32);
fn main() {
    match Foo(92) {
        Foo(92) => (),
    }
}
"#,
        );
    }

    #[test]
    fn completes_self_pats() {
        check_snippet(
            r#"
struct Foo(i32);
impl Foo {
    fn foo() {
        match () {
            a$0
        }
    }
}
    "#,
            expect![[r#"
                bn Self Self($1)$0
                bn Foo  Foo($1)$0
            "#]],
        )
    }

    #[test]
    fn completes_qualified_variant() {
        check_snippet(
            r#"
enum Foo {
    Bar { baz: i32 }
}
impl Foo {
    fn foo() {
        match {Foo::Bar { baz: 0 }} {
            B$0
        }
    }
}
    "#,
            expect![[r#"
                bn Self::Bar Self::Bar { baz$1 }$0
                bn Foo::Bar  Foo::Bar { baz$1 }$0
            "#]],
        )
    }

    #[test]
    fn completes_enum_variant_matcharm() {
        check(
            r#"
enum Foo { Bar, Baz, Quux }

fn main() {
    let foo = Foo::Quux;
    match foo { Qu$0 }
}
"#,
            expect![[r#"
                ev Foo::Bar  ()
                ev Foo::Baz  ()
                ev Foo::Quux ()
                en Foo
            "#]],
        )
    }

    #[test]
    fn completes_enum_variant_matcharm_ref() {
        check(
            r#"
enum Foo { Bar, Baz, Quux }

fn main() {
    let foo = Foo::Quux;
    match &foo { Qu$0 }
}
"#,
            expect![[r#"
                ev Foo::Bar  ()
                ev Foo::Baz  ()
                ev Foo::Quux ()
                en Foo
            "#]],
        )
    }

    #[test]
    fn completes_enum_variant_iflet() {
        check(
            r#"
enum Foo { Bar, Baz, Quux }

fn main() {
    let foo = Foo::Quux;
    if let Qu$0 = foo { }
}
"#,
            expect![[r#"
                ev Foo::Bar  ()
                ev Foo::Baz  ()
                ev Foo::Quux ()
                en Foo
            "#]],
        )
    }

    #[test]
    fn completes_enum_variant_impl() {
        check(
            r#"
enum Foo { Bar, Baz, Quux }
impl Foo {
    fn foo() { match Foo::Bar { Q$0 } }
}
"#,
            expect![[r#"
                ev Self::Bar  ()
                ev Self::Baz  ()
                ev Self::Quux ()
                ev Foo::Bar   ()
                ev Foo::Baz   ()
                ev Foo::Quux  ()
                sp Self
                en Foo
            "#]],
        )
    }
}
