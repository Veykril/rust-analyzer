use hir::ModuleDef;
use ide_db::helpers::get_path_in_derive_attr;
use ide_db::helpers::{import_assets::NameToImport, mod_path_to_ast};
use ide_db::items_locator;
use itertools::Itertools;
use syntax::ast::HasModuleItem;
use syntax::{
    ast::{self, make, AstNode, HasName},
    SyntaxKind::{IDENT, WHITESPACE},
};
use syntax::{ted, AstToken, Direction, SyntaxElement, T};

use crate::{
    assist_context::{AssistBuilder, AssistContext, Assists},
    utils::{
        add_trait_assoc_items_to_impl, filter_assoc_items, gen_trait_fn_body,
        generate_trait_impl_text, render_snippet, Cursor, DefaultMethods,
    },
    AssistId, AssistKind,
};

// Assist: replace_derive_with_manual_impl
//
// Converts a `derive` impl into a manual one.
//
// ```
// # trait Debug { fn fmt(&self, f: &mut Formatter) -> Result<()>; }
// #[derive(Deb$0ug, Display)]
// struct S;
// ```
// ->
// ```
// # trait Debug { fn fmt(&self, f: &mut Formatter) -> Result<()>; }
// #[derive(Display)]
// struct S;
//
// impl Debug for S {
//     $0fn fmt(&self, f: &mut Formatter) -> Result<()> {
//         f.debug_struct("S").finish()
//     }
// }
// ```
pub(crate) fn replace_derive_with_manual_impl(
    acc: &mut Assists,
    ctx: &AssistContext,
) -> Option<()> {
    let attr = ctx.find_node_at_offset::<ast::Attr>()?;
    let tt = attr.token_tree()?;
    let trait_token = attr.syntax().token_at_offset(ctx.offset()).find_map(ast::Ident::cast)?;
    let path = get_path_in_derive_attr(&ctx.sema, &attr, &trait_token)?;
    if path.parent_path().is_some() {
        return None;
    }

    let idx = trait_token
        .syntax()
        .siblings_with_tokens(Direction::Prev)
        .take_while(|tok| tok.kind() != T!['('])
        .filter(|t| t.kind() == T![,])
        .count();

    let trait_ = ctx
        .sema
        .expand_derive_macro(&attr)?
        .get(idx)
        .cloned()
        .and_then(ast::MacroItems::cast)
        .and_then(|it| {
            it.items()
                .filter_map(|item| match item {
                    ast::Item::Impl(it) => Some(it),
                    _ => None,
                })
                .find_map(|impl_| impl_.trait_())
        })?;
    let trait_ = match trait_ {
        ast::Type::PathType(it) => it.path()?,
        _ => return None,
    };
    let trait_ = match ctx.sema.resolve_path(&trait_)? {
        hir::PathResolution::Def(ModuleDef::Trait(trait_)) => trait_,
        _ => return None,
    };

    let adt = attr.syntax().parent().and_then(ast::Adt::cast)?;

    let current_module = ctx.sema.scope(adt.syntax()).module()?;
    let current_crate = current_module.krate();

    let trait_path = current_module
        .find_use_path(ctx.sema.db, hir::ModuleDef::Trait(trait_))
        .as_ref()
        .map(mod_path_to_ast)?;

    let target = attr.syntax().text_range();
    let annotated_name = adt.name()?;
    let label = format!("Convert to manual `impl {} for {}`", trait_path, annotated_name);
    let trait_name = trait_path.segment().and_then(|seg| seg.name_ref())?;

    acc.add(
        AssistId("replace_derive_with_manual_impl", AssistKind::Refactor),
        label,
        target,
        |builder| {
            let insert_pos = adt.syntax().text_range().end();
            let impl_def_with_items =
                impl_def_from_trait(&ctx.sema, &adt, &annotated_name, Some(trait_), &trait_path);
            let tt = builder.make_syntax_mut(tt.syntax().clone());
            let mut i = 0;
            let tokens = tt
                .descendants_with_tokens()
                .filter_map(SyntaxElement::into_token)
                .map(|it| {
                    i += (it.kind() == T![,]) as usize;
                    (it, i)
                })
                .skip_while(|&(_, i)| i < idx)
                .take_while(|(it, _)| it.kind() != T![,] || it.kind() != T![')'])
                .map(|(it, _)| it.into());
            ted::remove_all_iter(tokens);

            let trait_path = format!("{}", trait_path);
            match (ctx.config.snippet_cap, impl_def_with_items) {
                (None, _) => {
                    builder.insert(insert_pos, generate_trait_impl_text(&adt, &trait_path, ""))
                }
                (Some(cap), None) => builder.insert_snippet(
                    cap,
                    insert_pos,
                    generate_trait_impl_text(&adt, &trait_path, "    $0"),
                ),
                (Some(cap), Some((impl_def, first_assoc_item))) => {
                    let mut cursor = Cursor::Before(first_assoc_item.syntax());
                    let placeholder;
                    if let ast::AssocItem::Fn(ref func) = first_assoc_item {
                        if let Some(m) = func.syntax().descendants().find_map(ast::MacroCall::cast)
                        {
                            if m.syntax().text() == "todo!()" {
                                placeholder = m;
                                cursor = Cursor::Replace(placeholder.syntax());
                            }
                        }
                    }

                    builder.insert_snippet(
                        cap,
                        insert_pos,
                        format!("\n\n{}", render_snippet(cap, impl_def.syntax(), cursor)),
                    )
                }
            };
        },
    )
}

fn impl_def_from_trait(
    sema: &hir::Semantics<ide_db::RootDatabase>,
    adt: &ast::Adt,
    annotated_name: &ast::Name,
    trait_: Option<hir::Trait>,
    trait_path: &ast::Path,
) -> Option<(ast::Impl, ast::AssocItem)> {
    let trait_ = trait_?;
    let target_scope = sema.scope(annotated_name.syntax());
    let trait_items = filter_assoc_items(sema.db, &trait_.items(sema.db), DefaultMethods::No);
    if trait_items.is_empty() {
        return None;
    }
    let impl_def =
        make::impl_trait(trait_path.clone(), make::ext::ident_path(&annotated_name.text()));
    let (impl_def, first_assoc_item) =
        add_trait_assoc_items_to_impl(sema, trait_items, trait_, impl_def, target_scope);

    // Generate a default `impl` function body for the derived trait.
    if let ast::AssocItem::Fn(ref func) = first_assoc_item {
        let _ = gen_trait_fn_body(func, trait_path, adt);
    };

    Some((impl_def, first_assoc_item))
}

fn update_attribute(
    builder: &mut AssistBuilder,
    input: &ast::TokenTree,
    trait_name: &ast::NameRef,
    attr: &ast::Attr,
) {
    let trait_name = trait_name.text();
    let new_attr_input = input
        .syntax()
        .descendants_with_tokens()
        .filter(|t| t.kind() == IDENT)
        .filter_map(|t| t.into_token().map(|t| t.text().to_string()))
        .filter(|t| t != &trait_name)
        .collect::<Vec<_>>();
    let has_more_derives = !new_attr_input.is_empty();

    if has_more_derives {
        let new_attr_input = format!("({})", new_attr_input.iter().format(", "));
        builder.replace(input.syntax().text_range(), new_attr_input);
    } else {
        let attr_range = attr.syntax().text_range();
        builder.delete(attr_range);

        if let Some(line_break_range) = attr
            .syntax()
            .next_sibling_or_token()
            .filter(|t| t.kind() == WHITESPACE)
            .map(|t| t.text_range())
        {
            builder.delete(line_break_range);
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::tests::{check_assist, check_assist_not_applicable};

    use super::*;

    #[test]
    fn add_custom_impl_debug_record_struct() {
        check_assist(
            replace_derive_with_manual_impl,
            r#"
//- minicore: fmt
#[derive(Debu$0g)]
struct Foo {
    bar: String,
}
"#,
            r#"
struct Foo {
    bar: String,
}

impl core::fmt::Debug for Foo {
    $0fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Foo").field("bar", &self.bar).finish()
    }
}
"#,
        )
    }
    #[test]
    fn add_custom_impl_debug_tuple_struct() {
        check_assist(
            replace_derive_with_manual_impl,
            r#"
//- minicore: fmt
#[derive(Debu$0g)]
struct Foo(String, usize);
"#,
            r#"struct Foo(String, usize);

impl core::fmt::Debug for Foo {
    $0fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("Foo").field(&self.0).field(&self.1).finish()
    }
}
"#,
        )
    }
    #[test]
    fn add_custom_impl_debug_empty_struct() {
        check_assist(
            replace_derive_with_manual_impl,
            r#"
//- minicore: fmt
#[derive(Debu$0g)]
struct Foo;
"#,
            r#"
struct Foo;

impl core::fmt::Debug for Foo {
    $0fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Foo").finish()
    }
}
"#,
        )
    }
    #[test]
    fn add_custom_impl_debug_enum() {
        check_assist(
            replace_derive_with_manual_impl,
            r#"
//- minicore: fmt
#[derive(Debu$0g)]
enum Foo {
    Bar,
    Baz,
}
"#,
            r#"
enum Foo {
    Bar,
    Baz,
}

impl core::fmt::Debug for Foo {
    $0fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Bar => write!(f, "Bar"),
            Self::Baz => write!(f, "Baz"),
        }
    }
}
"#,
        )
    }

    #[test]
    fn add_custom_impl_debug_tuple_enum() {
        check_assist(
            replace_derive_with_manual_impl,
            r#"
//- minicore: fmt
#[derive(Debu$0g)]
enum Foo {
    Bar(usize, usize),
    Baz,
}
"#,
            r#"
enum Foo {
    Bar(usize, usize),
    Baz,
}

impl core::fmt::Debug for Foo {
    $0fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Bar(arg0, arg1) => f.debug_tuple("Bar").field(arg0).field(arg1).finish(),
            Self::Baz => write!(f, "Baz"),
        }
    }
}
"#,
        )
    }
    #[test]
    fn add_custom_impl_debug_record_enum() {
        check_assist(
            replace_derive_with_manual_impl,
            r#"
//- minicore: fmt
#[derive(Debu$0g)]
enum Foo {
    Bar {
        baz: usize,
        qux: usize,
    },
    Baz,
}
"#,
            r#"
enum Foo {
    Bar {
        baz: usize,
        qux: usize,
    },
    Baz,
}

impl core::fmt::Debug for Foo {
    $0fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Bar { baz, qux } => f.debug_struct("Bar").field("baz", baz).field("qux", qux).finish(),
            Self::Baz => write!(f, "Baz"),
        }
    }
}
"#,
        )
    }
    #[test]
    fn add_custom_impl_default_record_struct() {
        check_assist(
            replace_derive_with_manual_impl,
            r#"
//- minicore: default
#[derive(Defau$0lt)]
struct Foo {
    foo: usize,
}
"#,
            r#"
struct Foo {
    foo: usize,
}

impl Default for Foo {
    $0fn default() -> Self {
        Self { foo: Default::default() }
    }
}
"#,
        )
    }
    #[test]
    fn add_custom_impl_default_tuple_struct() {
        check_assist(
            replace_derive_with_manual_impl,
            r#"
//- minicore: default
#[derive(Defau$0lt)]
struct Foo(usize);
"#,
            r#"
struct Foo(usize);

impl Default for Foo {
    $0fn default() -> Self {
        Self(Default::default())
    }
}
"#,
        )
    }
    #[test]
    fn add_custom_impl_default_empty_struct() {
        check_assist(
            replace_derive_with_manual_impl,
            r#"
//- minicore: default
#[derive(Defau$0lt)]
struct Foo;
"#,
            r#"
struct Foo;

impl Default for Foo {
    $0fn default() -> Self {
        Self {  }
    }
}
"#,
        )
    }

    #[test]
    fn add_custom_impl_hash_record_struct() {
        check_assist(
            replace_derive_with_manual_impl,
            r#"
//- minicore: hash
#[derive(Has$0h)]
struct Foo {
    bin: usize,
    bar: usize,
}
"#,
            r#"
struct Foo {
    bin: usize,
    bar: usize,
}

impl core::hash::Hash for Foo {
    $0fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.bin.hash(state);
        self.bar.hash(state);
    }
}
"#,
        )
    }

    #[test]
    fn add_custom_impl_hash_tuple_struct() {
        check_assist(
            replace_derive_with_manual_impl,
            r#"
//- minicore: hash
#[derive(Has$0h)]
struct Foo(usize, usize);
"#,
            r#"
struct Foo(usize, usize);

impl core::hash::Hash for Foo {
    $0fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
        self.1.hash(state);
    }
}
"#,
        )
    }

    #[test]
    fn add_custom_impl_hash_enum() {
        check_assist(
            replace_derive_with_manual_impl,
            r#"
//- minicore: hash
#[derive(Has$0h)]
enum Foo {
    Bar,
    Baz,
}
"#,
            r#"
enum Foo {
    Bar,
    Baz,
}

impl core::hash::Hash for Foo {
    $0fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        core::mem::discriminant(self).hash(state);
    }
}
"#,
        )
    }

    #[test]
    fn add_custom_impl_clone_record_struct() {
        check_assist(
            replace_derive_with_manual_impl,
            r#"
//- minicore: clone
#[derive(Clo$0ne)]
struct Foo {
    bin: usize,
    bar: usize,
}
"#,
            r#"
struct Foo {
    bin: usize,
    bar: usize,
}

impl Clone for Foo {
    $0fn clone(&self) -> Self {
        Self { bin: self.bin.clone(), bar: self.bar.clone() }
    }
}
"#,
        )
    }

    #[test]
    fn add_custom_impl_clone_tuple_struct() {
        check_assist(
            replace_derive_with_manual_impl,
            r#"
//- minicore: clone
#[derive(Clo$0ne)]
struct Foo(usize, usize);
"#,
            r#"
struct Foo(usize, usize);

impl Clone for Foo {
    $0fn clone(&self) -> Self {
        Self(self.0.clone(), self.1.clone())
    }
}
"#,
        )
    }

    #[test]
    fn add_custom_impl_clone_empty_struct() {
        check_assist(
            replace_derive_with_manual_impl,
            r#"
//- minicore: clone
#[derive(Clo$0ne)]
struct Foo;
"#,
            r#"
struct Foo;

impl Clone for Foo {
    $0fn clone(&self) -> Self {
        Self {  }
    }
}
"#,
        )
    }

    #[test]
    fn add_custom_impl_clone_enum() {
        check_assist(
            replace_derive_with_manual_impl,
            r#"
//- minicore: clone
#[derive(Clo$0ne)]
enum Foo {
    Bar,
    Baz,
}
"#,
            r#"
enum Foo {
    Bar,
    Baz,
}

impl Clone for Foo {
    $0fn clone(&self) -> Self {
        match self {
            Self::Bar => Self::Bar,
            Self::Baz => Self::Baz,
        }
    }
}
"#,
        )
    }

    #[test]
    fn add_custom_impl_clone_tuple_enum() {
        check_assist(
            replace_derive_with_manual_impl,
            r#"
//- minicore: clone
#[derive(Clo$0ne)]
enum Foo {
    Bar(String),
    Baz,
}
"#,
            r#"
enum Foo {
    Bar(String),
    Baz,
}

impl Clone for Foo {
    $0fn clone(&self) -> Self {
        match self {
            Self::Bar(arg0) => Self::Bar(arg0.clone()),
            Self::Baz => Self::Baz,
        }
    }
}
"#,
        )
    }

    #[test]
    fn add_custom_impl_clone_record_enum() {
        check_assist(
            replace_derive_with_manual_impl,
            r#"
//- minicore: clone
#[derive(Clo$0ne)]
enum Foo {
    Bar {
        bin: String,
    },
    Baz,
}
"#,
            r#"
enum Foo {
    Bar {
        bin: String,
    },
    Baz,
}

impl Clone for Foo {
    $0fn clone(&self) -> Self {
        match self {
            Self::Bar { bin } => Self::Bar { bin: bin.clone() },
            Self::Baz => Self::Baz,
        }
    }
}
"#,
        )
    }

    #[test]
    fn add_custom_impl_partial_ord_record_struct() {
        check_assist(
            replace_derive_with_manual_impl,
            r#"
//- minicore: ord
#[derive(Partial$0Ord)]
struct Foo {
    bin: usize,
}
"#,
            r#"
struct Foo {
    bin: usize,
}

impl PartialOrd for Foo {
    $0fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        self.bin.partial_cmp(&other.bin)
    }
}
"#,
        )
    }

    #[test]
    fn add_custom_impl_partial_ord_record_struct_multi_field() {
        check_assist(
            replace_derive_with_manual_impl,
            r#"
//- minicore: ord
#[derive(Partial$0Ord)]
struct Foo {
    bin: usize,
    bar: usize,
    baz: usize,
}
"#,
            r#"
struct Foo {
    bin: usize,
    bar: usize,
    baz: usize,
}

impl PartialOrd for Foo {
    $0fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        match self.bin.partial_cmp(&other.bin) {
            Some(core::cmp::Ordering::Equal) => {}
            ord => return ord,
        }
        match self.bar.partial_cmp(&other.bar) {
            Some(core::cmp::Ordering::Equal) => {}
            ord => return ord,
        }
        self.baz.partial_cmp(&other.baz)
    }
}
"#,
        )
    }

    #[test]
    fn add_custom_impl_partial_ord_tuple_struct() {
        check_assist(
            replace_derive_with_manual_impl,
            r#"
//- minicore: ord
#[derive(Partial$0Ord)]
struct Foo(usize, usize, usize);
"#,
            r#"
struct Foo(usize, usize, usize);

impl PartialOrd for Foo {
    $0fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        match self.0.partial_cmp(&other.0) {
            Some(core::cmp::Ordering::Equal) => {}
            ord => return ord,
        }
        match self.1.partial_cmp(&other.1) {
            Some(core::cmp::Ordering::Equal) => {}
            ord => return ord,
        }
        self.2.partial_cmp(&other.2)
    }
}
"#,
        )
    }

    #[test]
    fn add_custom_impl_partial_eq_record_struct() {
        check_assist(
            replace_derive_with_manual_impl,
            r#"
//- minicore: eq
#[derive(Partial$0Eq)]
struct Foo {
    bin: usize,
    bar: usize,
}
"#,
            r#"
struct Foo {
    bin: usize,
    bar: usize,
}

impl PartialEq for Foo {
    $0fn eq(&self, other: &Self) -> bool {
        self.bin == other.bin && self.bar == other.bar
    }
}
"#,
        )
    }

    #[test]
    fn add_custom_impl_partial_eq_tuple_struct() {
        check_assist(
            replace_derive_with_manual_impl,
            r#"
//- minicore: eq
#[derive(Partial$0Eq)]
struct Foo(usize, usize);
"#,
            r#"
struct Foo(usize, usize);

impl PartialEq for Foo {
    $0fn eq(&self, other: &Self) -> bool {
        self.0 == other.0 && self.1 == other.1
    }
}
"#,
        )
    }

    #[test]
    fn add_custom_impl_partial_eq_empty_struct() {
        check_assist(
            replace_derive_with_manual_impl,
            r#"
//- minicore: eq
#[derive(Partial$0Eq)]
struct Foo;
"#,
            r#"
struct Foo;

impl PartialEq for Foo {
    $0fn eq(&self, other: &Self) -> bool {
        true
    }
}
"#,
        )
    }

    #[test]
    fn add_custom_impl_partial_eq_enum() {
        check_assist(
            replace_derive_with_manual_impl,
            r#"
//- minicore: eq
#[derive(Partial$0Eq)]
enum Foo {
    Bar,
    Baz,
}
"#,
            r#"
enum Foo {
    Bar,
    Baz,
}

impl PartialEq for Foo {
    $0fn eq(&self, other: &Self) -> bool {
        core::mem::discriminant(self) == core::mem::discriminant(other)
    }
}
"#,
        )
    }

    #[test]
    fn add_custom_impl_partial_eq_tuple_enum() {
        check_assist(
            replace_derive_with_manual_impl,
            r#"
//- minicore: eq
#[derive(Partial$0Eq)]
enum Foo {
    Bar(String),
    Baz,
}
"#,
            r#"
enum Foo {
    Bar(String),
    Baz,
}

impl PartialEq for Foo {
    $0fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Bar(l0), Self::Bar(r0)) => l0 == r0,
            _ => core::mem::discriminant(self) == core::mem::discriminant(other),
        }
    }
}
"#,
        )
    }

    #[test]
    fn add_custom_impl_partial_eq_record_enum() {
        check_assist(
            replace_derive_with_manual_impl,
            r#"
//- minicore: eq
#[derive(Partial$0Eq)]
enum Foo {
    Bar {
        bin: String,
    },
    Baz {
        qux: String,
        fez: String,
    },
    Qux {},
    Bin,
}
"#,
            r#"
enum Foo {
    Bar {
        bin: String,
    },
    Baz {
        qux: String,
        fez: String,
    },
    Qux {},
    Bin,
}

impl PartialEq for Foo {
    $0fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Bar { bin: l_bin }, Self::Bar { bin: r_bin }) => l_bin == r_bin,
            (Self::Baz { qux: l_qux, fez: l_fez }, Self::Baz { qux: r_qux, fez: r_fez }) => l_qux == r_qux && l_fez == r_fez,
            _ => core::mem::discriminant(self) == core::mem::discriminant(other),
        }
    }
}
"#,
        )
    }
    #[test]
    fn add_custom_impl_all() {
        check_assist(
            replace_derive_with_manual_impl,
            r#"
mod foo {
    pub trait Bar {
        type Qux;
        const Baz: usize = 42;
        const Fez: usize;
        fn foo();
        fn bar() {}
    }
}

#[derive($0Bar)]
struct Foo {
    bar: String,
}
"#,
            r#"
mod foo {
    pub trait Bar {
        type Qux;
        const Baz: usize = 42;
        const Fez: usize;
        fn foo();
        fn bar() {}
    }
}

struct Foo {
    bar: String,
}

impl foo::Bar for Foo {
    $0type Qux;

    const Baz: usize = 42;

    const Fez: usize;

    fn foo() {
        todo!()
    }
}
"#,
        )
    }
    #[test]
    fn add_custom_impl_for_unique_input() {
        check_assist(
            replace_derive_with_manual_impl,
            r#"
#[derive(Debu$0g)]
struct Foo {
    bar: String,
}
            "#,
            r#"
struct Foo {
    bar: String,
}

impl Debug for Foo {
    $0
}
            "#,
        )
    }

    #[test]
    fn add_custom_impl_for_with_visibility_modifier() {
        check_assist(
            replace_derive_with_manual_impl,
            r#"
#[derive(Debug$0)]
pub struct Foo {
    bar: String,
}
            "#,
            r#"
pub struct Foo {
    bar: String,
}

impl Debug for Foo {
    $0
}
            "#,
        )
    }

    #[test]
    fn add_custom_impl_when_multiple_inputs() {
        check_assist(
            replace_derive_with_manual_impl,
            r#"
#[derive(Display, Debug$0, Serialize)]
struct Foo {}
            "#,
            r#"
#[derive(Display, Serialize)]
struct Foo {}

impl Debug for Foo {
    $0
}
            "#,
        )
    }

    #[test]
    fn test_ignore_derive_macro_without_input() {
        check_assist_not_applicable(
            replace_derive_with_manual_impl,
            r#"
#[derive($0)]
struct Foo {}
            "#,
        )
    }

    #[test]
    fn test_ignore_if_cursor_on_param() {
        check_assist_not_applicable(
            replace_derive_with_manual_impl,
            r#"
#[derive$0(Debug)]
struct Foo {}
            "#,
        );

        check_assist_not_applicable(
            replace_derive_with_manual_impl,
            r#"
#[derive(Debug)$0]
struct Foo {}
            "#,
        )
    }

    #[test]
    fn test_ignore_if_not_derive() {
        check_assist_not_applicable(
            replace_derive_with_manual_impl,
            r#"
#[allow(non_camel_$0case_types)]
struct Foo {}
            "#,
        )
    }

    #[test]
    fn works_at_start_of_file() {
        cov_mark::check!(outside_of_attr_args);
        check_assist_not_applicable(
            replace_derive_with_manual_impl,
            r#"
$0#[derive(Debug)]
struct S;
            "#,
        );
    }
}
