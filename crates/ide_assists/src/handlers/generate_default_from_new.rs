use std::array;

use crate::{
    assist_context::{AssistContext, Assists},
    AssistId,
};
use ide_db::helpers::FamousDefs;
use syntax::{
    ast::{self, make, Impl, NameOwner},
    AstNode,
};

// Assist: generate_default_from_new
//
// Generates default implementation from new method.
//
// ```
// struct Example { _inner: () }
//
// impl Example {
//     pub fn n$0ew() -> Self {
//         Self { _inner: () }
//     }
// }
// ```
// ->
// ```
// struct Example { _inner: () }
//
// impl Example {
//     pub fn new() -> Self {
//         Self { _inner: () }
//     }
// }
//
// impl Default for Example {
//     fn default() -> Self {
//         Self::new()
//     }
// }
// ```
pub(crate) fn generate_default_from_new(acc: &mut Assists, ctx: &AssistContext) -> Option<()> {
    let fn_node = ctx.find_node_at_offset::<ast::Fn>()?;
    let fn_name = fn_node.name()?;

    if fn_name.text() != "new" {
        cov_mark::hit!(other_function_than_new);
        return None;
    }

    if fn_node.param_list()?.params().next().is_some() {
        cov_mark::hit!(new_function_with_parameters);
        return None;
    }

    let impl_ = fn_node.syntax().ancestors().into_iter().find_map(ast::Impl::cast)?;
    if is_default_implemented(ctx, &impl_) {
        cov_mark::hit!(default_block_is_already_present);
        cov_mark::hit!(struct_in_module_with_default);
        return None;
    }

    let insert_location = impl_.syntax().text_range();

    acc.add(
        AssistId("generate_default_from_new", crate::AssistKind::Generate),
        "Generate a Default impl from a new fn",
        insert_location,
        move |builder| {
            let impl_ = impl_.clone_for_update();
            let default_trait = make::ty_path(make::ext::ident_path("Default"));
            impl_.insert_trait(default_trait.clone_for_update());
            impl_.clear_assoc_item_list();
            let new_call = make::expr_call(
                make::expr_path(make::path_from_segments(
                    array::IntoIter::new([
                        make::path_segment(make::name_ref("Self")),
                        make::path_segment(make::name_ref("new")),
                    ]),
                    false,
                )),
                make::arg_list(None),
            )
            .clone_for_update();
            let body = make::block_expr(None, None).clone_for_update();
            body.append_expr(new_call);
            let fn_ = make::fn_(
                None,
                make::name("default"),
                None,
                make::param_list(None, None),
                body,
                Some(make::ext::ty_alias_self()),
            );
            impl_
                .get_or_create_assoc_item_list()
                .add_item(ast::AssocItem::Fn(fn_.clone_for_update()));
            builder.insert(insert_location.end(), impl_.to_string());
        },
    )
}

fn is_default_implemented(ctx: &AssistContext, impl_: &Impl) -> bool {
    let db = ctx.sema.db;
    let impl_ = ctx.sema.to_def(impl_);
    let impl_def = match impl_ {
        Some(value) => value,
        None => return false,
    };

    let ty = impl_def.self_ty(db);
    let krate = impl_def.module(db).krate();
    let default = FamousDefs(&ctx.sema, Some(krate)).core_default_Default();
    let default_trait = match default {
        Some(value) => value,
        None => return false,
    };

    ty.impls_trait(db, default_trait, &[])
}

#[cfg(test)]
mod tests {
    use ide_db::helpers::FamousDefs;

    use crate::tests::{check_assist, check_assist_not_applicable};

    use super::*;

    #[test]
    fn generate_default() {
        check_pass(
            r#"
struct Example { _inner: () }

impl Example {
    pub fn ne$0w() -> Self {
        Self { _inner: () }
    }
}

fn main() {}
"#,
            r#"
struct Example { _inner: () }

impl Example {
    pub fn new() -> Self {
        Self { _inner: () }
    }
}

impl Default for Example {
    fn default() -> Self {
        Self::new()
    }
}

fn main() {}
"#,
        );
    }

    #[test]
    fn generate_default2() {
        check_pass(
            r#"
struct Test { value: u32 }

impl Test {
    pub fn ne$0w() -> Self {
        Self { value: 0 }
    }
}
"#,
            r#"
struct Test { value: u32 }

impl Test {
    pub fn new() -> Self {
        Self { value: 0 }
    }
}

impl Default for Test {
    fn default() -> Self {
        Self::new()
    }
}
"#,
        );
    }

    #[test]
    fn new_function_with_generic() {
        check_pass(
            r#"
pub struct Foo<T> {
    _bar: *mut T,
}

impl<T> Foo<T> {
    pub fn ne$0w() -> Self {
        unimplemented!()
    }
}
"#,
            r#"
pub struct Foo<T> {
    _bar: *mut T,
}

impl<T> Foo<T> {
    pub fn new() -> Self {
        unimplemented!()
    }
}

impl<T> Default for Foo<T> {
    fn default() -> Self {
        Self::new()
    }
}
"#,
        );
    }

    #[test]
    fn new_function_with_generics() {
        check_pass(
            r#"
pub struct Foo<T, B> {
    _tars: *mut T,
    _bar: *mut B,
}

impl<T, B> Foo<T, B> {
    pub fn ne$0w() -> Self {
        unimplemented!()
    }
}
"#,
            r#"
pub struct Foo<T, B> {
    _tars: *mut T,
    _bar: *mut B,
}

impl<T, B> Foo<T, B> {
    pub fn new() -> Self {
        unimplemented!()
    }
}

impl<T, B> Default for Foo<T, B> {
    fn default() -> Self {
        Self::new()
    }
}
"#,
        );
    }

    #[test]
    fn new_function_with_generic_and_bound() {
        check_pass(
            r#"
pub struct Foo<T> {
    t: T,
}

impl<T: From<i32>> Foo<T> {
    pub fn ne$0w() -> Self {
        Foo { t: 0.into() }
    }
}
"#,
            r#"
pub struct Foo<T> {
    t: T,
}

impl<T: From<i32>> Foo<T> {
    pub fn new() -> Self {
        Foo { t: 0.into() }
    }
}

impl<T: From<i32>> Default for Foo<T> {
    fn default() -> Self {
        Self::new()
    }
}
"#,
        );
    }

    #[test]
    fn new_function_with_generics_and_bounds() {
        check_pass(
            r#"
pub struct Foo<T, B> {
    _tars: T,
    _bar: B,
}

impl<T: From<i32>, B: From<i64>> Foo<T, B> {
    pub fn ne$0w() -> Self {
        unimplemented!()
    }
}
"#,
            r#"
pub struct Foo<T, B> {
    _tars: T,
    _bar: B,
}

impl<T: From<i32>, B: From<i64>> Foo<T, B> {
    pub fn new() -> Self {
        unimplemented!()
    }
}

impl<T: From<i32>, B: From<i64>> Default for Foo<T, B> {
    fn default() -> Self {
        Self::new()
    }
}
"#,
        );
    }

    #[test]
    fn new_function_with_generic_and_where() {
        check_pass(
            r#"
pub struct Foo<T> {
    t: T,
}

impl<T: From<i32>> Foo<T>
where
    Option<T>: Debug
{
    pub fn ne$0w() -> Self {
        Foo { t: 0.into() }
    }
}
"#,
            r#"
pub struct Foo<T> {
    t: T,
}

impl<T: From<i32>> Foo<T>
where
    Option<T>: Debug
{
    pub fn new() -> Self {
        Foo { t: 0.into() }
    }
}

impl<T: From<i32>> Default for Foo<T>
where
    Option<T>: Debug
{
    fn default() -> Self {
        Self::new()
    }
}
"#,
        );
    }

    #[test]
    fn new_function_with_generics_and_wheres() {
        check_pass(
            r#"
pub struct Foo<T, B> {
    _tars: T,
    _bar: B,
}

impl<T: From<i32>, B: From<i64>> Foo<T, B>
where
    Option<T>: Debug, Option<B>: Debug,
{
    pub fn ne$0w() -> Self {
        unimplemented!()
    }
}
"#,
            r#"
pub struct Foo<T, B> {
    _tars: T,
    _bar: B,
}

impl<T: From<i32>, B: From<i64>> Foo<T, B>
where
    Option<T>: Debug, Option<B>: Debug,
{
    pub fn new() -> Self {
        unimplemented!()
    }
}

impl<T: From<i32>, B: From<i64>> Default for Foo<T, B>
where
    Option<T>: Debug, Option<B>: Debug,
{
    fn default() -> Self {
        Self::new()
    }
}
"#,
        );
    }

    #[test]
    fn new_function_with_parameters() {
        cov_mark::check!(new_function_with_parameters);
        check_not_applicable(
            r#"
struct Example { _inner: () }

impl Example {
    pub fn $0new(value: ()) -> Self {
        Self { _inner: value }
    }
}
"#,
        );
    }

    #[test]
    fn other_function_than_new() {
        cov_mark::check!(other_function_than_new);
        check_not_applicable(
            r#"
struct Example { _inner: () }

impl Example {
    pub fn a$0dd() -> Self {
        Self { _inner: () }
    }
}

"#,
        );
    }

    #[test]
    fn default_block_is_already_present() {
        cov_mark::check!(default_block_is_already_present);
        check_not_applicable(
            r#"
struct Example { _inner: () }

impl Example {
    pub fn n$0ew() -> Self {
        Self { _inner: () }
    }
}

impl Default for Example {
    fn default() -> Self {
        Self::new()
    }
}
"#,
        );
    }

    #[test]
    fn standalone_new_function() {
        check_not_applicable(
            r#"
fn n$0ew() -> u32 {
    0
}
"#,
        );
    }

    #[test]
    fn multiple_struct_blocks() {
        check_pass(
            r#"
struct Example { _inner: () }
struct Test { value: u32 }

impl Example {
    pub fn new$0() -> Self {
        Self { _inner: () }
    }
}
"#,
            r#"
struct Example { _inner: () }
struct Test { value: u32 }

impl Example {
    pub fn new() -> Self {
        Self { _inner: () }
    }
}

impl Default for Example {
    fn default() -> Self {
        Self::new()
    }
}
"#,
        );
    }

    #[test]
    fn when_struct_is_after_impl() {
        check_pass(
            r#"
impl Example {
    pub fn $0new() -> Self {
        Self { _inner: () }
    }
}

struct Example { _inner: () }
"#,
            r#"
impl Example {
    pub fn new() -> Self {
        Self { _inner: () }
    }
}

impl Default for Example {
    fn default() -> Self {
        Self::new()
    }
}

struct Example { _inner: () }
"#,
        );
    }

    #[test]
    fn struct_in_module() {
        check_pass(
            r#"
mod test {
    struct Example { _inner: () }

    impl Example {
        pub fn n$0ew() -> Self {
            Self { _inner: () }
        }
    }
}
"#,
            r#"
mod test {
    struct Example { _inner: () }

    impl Example {
        pub fn new() -> Self {
            Self { _inner: () }
        }
    }

impl Default for Example {
    fn default() -> Self {
        Self::new()
    }
}
}
"#,
        );
    }

    #[test]
    fn struct_in_module_with_default() {
        cov_mark::check!(struct_in_module_with_default);
        check_not_applicable(
            r#"
mod test {
    struct Example { _inner: () }

    impl Example {
        pub fn n$0ew() -> Self {
            Self { _inner: () }
        }
    }

    impl Default for Example {
        fn default() -> Self {
            Self::new()
        }
    }
}
"#,
        );
    }

    fn check_pass(before: &str, after: &str) {
        let before = &format!("//- /main.rs crate:main deps:core{}{}", before, FamousDefs::FIXTURE);
        check_assist(generate_default_from_new, before, after);
    }

    fn check_not_applicable(before: &str) {
        let before = &format!("//- /main.rs crate:main deps:core{}{}", before, FamousDefs::FIXTURE);
        check_assist_not_applicable(generate_default_from_new, before);
    }
}
