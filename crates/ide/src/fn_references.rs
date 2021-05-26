//! This module implements a methods and free functions search in the specified file.
//! We have to skip tests, so cannot reuse file_structure module.

use hir::Semantics;
use ide_assists::utils::test_related_attribute;
use ide_db::RootDatabase;
use syntax::{ast, ast::NameOwner, AstNode, SyntaxNode, TextSize};

use crate::{FileId, FileRange};

pub(crate) fn find_all_methods(db: &RootDatabase, file_id: FileId) -> Vec<(TextSize, FileRange)> {
    let sema = Semantics::new(db);
    let source_file = sema.parse(file_id);
    source_file.syntax().descendants().filter_map(|it| method_range(it, file_id)).collect()
}

fn method_range(item: SyntaxNode, file_id: FileId) -> Option<(TextSize, FileRange)> {
    ast::Fn::cast(item).and_then(|fn_def| {
        if test_related_attribute(&fn_def).is_some() {
            None
        } else {
            Some((
                fn_def.name()?.syntax().text_range().start(),
                FileRange { file_id, range: fn_def.syntax().text_range() },
            ))
        }
    })
}

#[cfg(test)]
mod tests {
    use crate::fixture;
    use crate::{FileRange, TextSize};
    use std::ops::RangeInclusive;

    #[test]
    fn test_find_all_methods() {
        let (analysis, pos) = fixture::position(
            r#"
fn private_fn() {$0}

pub fn pub_fn() {}

pub fn generic_fn<T>(arg: T) {}"#,
        );

        let refs = analysis.find_all_methods(pos.file_id).unwrap();
        check_result(&refs, &[(3, 0..=18), (27, 20..=38), (47, 40..=71)]);
    }

    #[test]
    fn test_find_trait_methods() {
        let (analysis, pos) = fixture::position(
            r#"
trait Foo {
    fn bar() {$0}
    fn baz() {}
}"#,
        );

        let refs = analysis.find_all_methods(pos.file_id).unwrap();
        check_result(&refs, &[(19, 16..=27), (35, 32..=43)]);
    }

    #[test]
    fn test_skip_tests() {
        let (analysis, pos) = fixture::position(
            r#"
//- /lib.rs
#[test]
fn foo() {$0}

pub fn pub_fn() {}

mod tests {
    #[test]
    fn bar() {}
}"#,
        );

        let refs = analysis.find_all_methods(pos.file_id).unwrap();
        check_result(&refs, &[(28, 21..=39)]);
    }

    fn check_result(refs: &[(TextSize, FileRange)], expected: &[(u32, RangeInclusive<u32>)]) {
        assert_eq!(refs.len(), expected.len());

        for (&(eoffset, ref erange), &(offset, frange)) in expected.iter().zip(refs) {
            assert_eq!(TextSize::from(eoffset), offset);
            assert_eq!(TextSize::from(*erange.start()), frange.range.start());
            assert_eq!(TextSize::from(*erange.end()), frange.range.end());
        }
    }
}
