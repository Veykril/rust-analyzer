use hir::{HasVisibility, Semantics};
use ide_db::{defs::Definition, RootDatabase};
use syntax::ast::{self, make, AstNode};

use crate::{utils::mod_path_to_ast, AssistContext, AssistId, AssistKind, Assists};

// Assist: destructure_irrefutable
//
// Turn an ident pattern into an irrefutable destructuring pattern.
//
// ```
// struct Foo { foo: i32 }
// fn main() {
//     let x<|> = Foo { foo: 3 };
// }
// ```
// ->
// ```
// struct Foo { foo: i32 }
// fn main() {
//     let Foo { foo } = Foo { foo: 3 };
// }
// ```
pub(crate) fn destructure_irrefutable(acc: &mut Assists, ctx: &AssistContext) -> Option<()> {
    let ident_pat = ctx.find_node_at_offset::<ast::IdentPat>()?;
    if ident_pat.pat().is_some() {
        return None;
    }
    let local = ctx.sema.to_def(&ident_pat)?;
    let usages = Definition::Local(local).usages(&ctx.sema).all();
    for usage in usages { //FIXME
    }

    let current_module = ctx.sema.scope(ident_pat.syntax()).module()?;
    let ty = ctx.sema.type_of_pat(&ast::Pat::IdentPat(ident_pat.clone()))?;
    let pat = ty_to_irrefutable_pat(&ctx.sema, current_module, &ty)?;

    acc.add(
        AssistId("destructure_irrefutable", AssistKind::RefactorRewrite),
        format!("Destructure pattern `{}`", ident_pat),
        ident_pat.syntax().text_range(),
        |builder| builder.replace(ident_pat.syntax().text_range(), pat.to_string()),
    )
}

fn ty_to_irrefutable_pat(
    sema: &Semantics<RootDatabase>,
    current_module: hir::Module,
    ty: &hir::Type,
) -> Option<ast::Pat> {
    match ty.as_adt() {
        Some(hir::Adt::Struct(strukt)) if strukt.is_unit(sema.db) => None,
        Some(hir::Adt::Struct(strukt)) => {
            let path = current_module
                .find_use_path(sema.db, hir::ModuleDef::Adt(hir::Adt::Struct(strukt)))
                .as_ref()
                .map(mod_path_to_ast)?;
            let mut fields = strukt.fields(sema.db);
            let len = fields.len();
            fields
                .retain(|f| f.visibility(sema.db).is_visible_from(sema.db, current_module.into()));
            let has_rest = len != fields.len();
            if strukt.is_record(sema.db) {
                Some(ast::Pat::RecordPat(make::record_pat(
                    path,
                    fields.iter().map(|f| {
                        ast::Pat::IdentPat(make::ident_pat(make::name(
                            &f.name(sema.db).to_string(),
                        )))
                    }),
                    has_rest,
                )))
            } else {
                Some(ast::Pat::TupleStructPat(make::tuple_struct_pat(
                    path,
                    fields.iter().map(|f| {
                        ast::Pat::IdentPat(make::ident_pat(make::name(&format!(
                            "_{}",
                            f.name(sema.db)
                        ))))
                    }),
                    has_rest,
                )))
            }
        }
        // None if ty.is_tuple() => (),
        _ => None, //FIXME: tuples and fixed size arrays
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::tests::{check_assist, check_assist_not_applicable};

    #[test]
    fn destructure_record() {
        check_assist(
            destructure_irrefutable,
            r#"struct Foo { foo: i32 }
fn foo() {
    let foo<|> = Foo { foo: 3 };
}"#,
            r#"struct Foo { foo: i32 }
fn foo() {
    let Foo { foo } = Foo { foo: 3 };
}"#,
        );
    }

    #[test]
    fn destructure_tuple_struct() {
        check_assist(
            destructure_irrefutable,
            r#"struct Foo(i32);
fn foo() {
    let foo<|> = Foo(3);
}"#,
            r#"struct Foo(i32);
fn foo() {
    let Foo(_0) = Foo(3);
}"#,
        );
    }

    #[test]
    fn destructure_record_partial_priv() {
        check_assist(
            destructure_irrefutable,
            r#"mod priv { pub struct Foo { pub foo: i32, bar: f32 } }
fn main(param: priv::Foo) {
    let bar<|> = param;
}"#,
            r#"mod priv { pub struct Foo { pub foo: i32, bar: f32 } }
fn main(param: priv::Foo) {
    let priv::Foo { foo, .. } = param;
}"#,
        );
    }

    #[test]
    fn destructure_tuple_struct_partial_priv() {
        check_assist(
            destructure_irrefutable,
            r#"mod priv { pub struct Foo(pub i32, f32); }
fn main(param: priv::Foo) {
    let bar<|> = param;
}"#,
            r#"mod priv { pub struct Foo(pub i32, f32); }
fn main(param: priv::Foo) {
    let priv::Foo(_0, ..) = param;
}"#,
        );
    }

    #[test]
    fn destructure_record_in_param() {
        check_assist(
            destructure_irrefutable,
            r#"struct Foo { foo: i32 }
fn foo(foo<|>: Foo) {}"#,
            r#"struct Foo { foo: i32 }
fn foo(Foo { foo }: Foo) {}"#,
        );
    }

    #[test]
    fn destructure_record_in_match() {
        check_assist(
            destructure_irrefutable,
            r#"struct Foo { foo: i32 }
fn main(param: Foo) {
    match param {
        foo<|> => (),
    }
}"#,
            r#"struct Foo { foo: i32 }
fn main(param: Foo) {
    match param {
        Foo { foo } => (),
    }
}"#,
        )
    }

    #[test]
    fn destructure_nested_record_pat() {
        check_assist(
            destructure_irrefutable,
            r#"struct Foo { qux: i32 }
struct Bar { foo: Foo };
fn main(Bar { foo<|> }: Bar) {}"#,
            r#"struct Foo { qux: i32 }
struct Bar { foo: Foo };
fn main(Bar { foo: Foo { qux } }: Bar) {}"#,
        )
    }

    #[test]
    fn destructure_nested_box_pat() {
        check_assist(
            destructure_irrefutable,
            r#"struct Foo { qux: i32 }
fn main(box foo<|>: Box<Foo>) {}"#,
            r#"struct Foo { qux: i32 }
struct Bar { foo: Foo };
fn main(box Foo { qux }: Box<Foo>) {}"#,
        )
    }

    #[test]
    fn destructure_renamed_ident_pat_not_applicable() {
        check_assist_not_applicable(
            destructure_irrefutable,
            r#"struct Foo { qux: i32 }
fn main(foo<|> @ Foo { .. }: Foo) {}"#,
        )
    }

    #[test]
    fn destructure_nested_or_pat() {
        check_assist(
            destructure_irrefutable,
            r#"struct Foo { qux: i32 }
fn main(foo: Foo) {
    match foo {
        foo1 | foo2<|> => ()
    }
}"#,
            // this obviously doesn't compile due to different name bindings in the or pattern
            r#"struct Foo { qux: i32 }
fn main(foo: Foo) {
    match foo {
        foo1 | Foo { qux } => ()
    }
}"#,
        )
    }

    #[test]
    fn destructure_nested_paren_pat() {
        check_assist(
            destructure_irrefutable,
            r#"struct Foo { qux: i32 }
fn main((foo<|>): Foo) {}"#,
            r#"struct Foo { qux: i32 }
fn main((Foo { qux }): Foo) {}"#,
        )
    }

    #[test]
    fn destructure_nested_ref_pat() {
        check_assist_not_applicable(
            destructure_irrefutable,
            r#"struct Foo { qux: i32 }
fn main(ref foo<|>: Foo) {}"#,
        )
    }

    #[test]
    fn destructure_nested_slice_pat() {
        check_assist(
            destructure_irrefutable,
            r#"struct Foo { qux: i32 }
fn main([foo, bar<|>]: [Foo; 2]) {}"#,
            r#"struct Foo { qux: i32 }
fn main([foo, Foo { qux }]: [Foo; 2]) {}"#,
        )
    }

    #[test]
    fn destructure_nested_tuple_pat() {
        check_assist(
            destructure_irrefutable,
            r#"struct Foo { qux: i32 }
fn main((foo<|>, bar): (Foo, i32)) {}"#,
            r#"struct Foo { qux: i32 }
fn main((Foo { qux }, bar): (Foo, i32)) {}"#,
        )
    }

    #[test]
    fn destructure_nested_tuple_struct_pat() {
        check_assist(
            destructure_irrefutable,
            r#"struct Foo { qux: i32 }
struct Bar(Foo, i32);
fn main(Bar(foo<|>, bar): Bar) {}"#,
            r#"struct Foo { qux: i32 }
struct Bar(Foo, i32);
fn main(Bar(Foo { qux }, bar): Bar) {}"#,
        )
    }
}
