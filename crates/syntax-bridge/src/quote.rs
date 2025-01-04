//! A simplified version of quote-crate like quasi quote macro
#![allow(clippy::crate_in_macro_def)]

use intern::{sym, Symbol};
use span::Span;
use syntax::ToSmolStr;
use tt::{iter::TtElement, IdentIsRaw, TopSubtreeBuilder};

pub fn dollar_crate(span: Span) -> tt::Token<Span> {
    tt::Token { kind: tt::TokenKind::Dollar, span }
}

// A helper macro quote macro
// FIXME:
// 1. Not all puncts are handled
// 2. #()* pattern repetition not supported now
//    * But we can do it manually, see `test_quote_derive_copy_hack`
#[doc(hidden)]
#[macro_export]
macro_rules! quote_impl__ {
    ($span:ident $builder:ident) => {};

    ( @SUBTREE($span:ident $builder:ident) $delim:ident $($tt:tt)* ) => {
        {
            $builder.open($crate::tt::Delimiter::$delim, $span);
            $crate::quote::__quote!($span $builder  $($tt)*);
            $builder.close($span);
        }
    };

    ( @PUNCT($span:ident $builder:ident) $first:expr ) => {
        $builder.push(
            $crate::tt::Token { kind: $first, span: $span },
            $crate::tt::Spacing::Alone
        );
    };

    // hash variable
    ($span:ident $builder:ident # $first:ident $($tail:tt)* ) => {
        $crate::quote::ToTokenTree::to_tokens($first, $span, $builder);
        $crate::quote::__quote!($span $builder $($tail)*);
    };

    ($span:ident $builder:ident ## $first:ident $($tail:tt)* ) => {{
        ::std::iter::IntoIterator::into_iter($first).for_each(|it| $crate::quote::ToTokenTree::to_tokens(it, $span, $builder));
        $crate::quote::__quote!($span $builder $($tail)*);
    }};

    // Brace
    ($span:ident $builder:ident { $($tt:tt)* } ) => { $crate::quote::__quote!(@SUBTREE($span $builder) Brace $($tt)*) };
    // Bracket
    ($span:ident $builder:ident [ $($tt:tt)* ] ) => { $crate::quote::__quote!(@SUBTREE($span $builder) Bracket $($tt)*) };
    // Parenthesis
    ($span:ident $builder:ident ( $($tt:tt)* ) ) => { $crate::quote::__quote!(@SUBTREE($span $builder) Parenthesis $($tt)*) };

    // Literal
    ($span:ident $builder:ident $tt:literal ) => { $crate::quote::ToTokenTree::to_tokens($tt, $span, $builder) };
    // Ident
    ($span:ident $builder:ident $tt:ident ) => {
        $builder.push(
            $crate::tt::Token { kind: $crate::tt::TokenKind::Ident(intern::Symbol::intern(stringify!($crate::tt)), tt::IdentIsRaw::No), span: $span },
            $crate::tt::Spacing::Alone
        );
    };
    ($span:ident $builder:ident $tt:lifetime ) => {
        $builder.push(
            $crate::tt::Token { kind: $crate::tt::TokenKind::Lifetime(intern::Symbol::intern(&stringify!($crate::tt)[1..])), span: $span },
            $crate::tt::Spacing::Alone
        );
    };

    // Puncts
    // FIXME: Not all puncts are handled
    ($span:ident $builder:ident -> ) => {$crate::quote::__quote!(@PUNCT($span $builder) $crate::tt::TokenKind::RArrow)};
    ($span:ident $builder:ident => ) => {$crate::quote::__quote!(@PUNCT($span $builder) $crate::tt::TokenKind::FatArrow)};
    ($span:ident $builder:ident = ) => {$crate::quote::__quote!(@PUNCT($span $builder) $crate::tt::TokenKind::Eq)};
    ($span:ident $builder:ident & ) => {$crate::quote::__quote!(@PUNCT($span $builder) $crate::tt::TokenKind::BinOp($crate::tt::BinOpToken::And))};
    ($span:ident $builder:ident , ) => {$crate::quote::__quote!(@PUNCT($span $builder) $crate::tt::TokenKind::Comma)};
    ($span:ident $builder:ident : ) => {$crate::quote::__quote!(@PUNCT($span $builder) $crate::tt::TokenKind::Colon)};
    ($span:ident $builder:ident ; ) => {$crate::quote::__quote!(@PUNCT($span $builder) $crate::tt::TokenKind::Semi)};
    ($span:ident $builder:ident :: ) => {$crate::quote::__quote!(@PUNCT($span $builder) $crate::tt::TokenKind::PathSep)};
    ($span:ident $builder:ident && ) => {$crate::quote::__quote!(@PUNCT($span $builder) $crate::tt::TokenKind::AndAnd)};
    ($span:ident $builder:ident . ) => {$crate::quote::__quote!(@PUNCT($span $builder) $crate::tt::TokenKind::Dot)};
    ($span:ident $builder:ident < ) => {$crate::quote::__quote!(@PUNCT($span $builder) $crate::tt::TokenKind::Lt)};
    ($span:ident $builder:ident > ) => {$crate::quote::__quote!(@PUNCT($span $builder) $crate::tt::TokenKind::Gt)};
    ($span:ident $builder:ident ! ) => {$crate::quote::__quote!(@PUNCT($span $builder) $crate::tt::TokenKind::Not)};
    ($span:ident $builder:ident # ) => {$crate::quote::__quote!(@PUNCT($span $builder) $crate::tt::TokenKind::Pound)};
    ($span:ident $builder:ident $ ) => {$crate::quote::__quote!(@PUNCT($span $builder) $crate::tt::TokenKind::Dollar)};
    ($span:ident $builder:ident * ) => {$crate::quote::__quote!(@PUNCT($span $builder) $crate::tt::TokenKind::BinOp($crate::tt::BinOpToken::Star))};

    ($span:ident $builder:ident $first:tt $($tail:tt)+ ) => {{
        $crate::quote::__quote!($span $builder $first);
        $crate::quote::__quote!($span $builder $($tail)*);
    }};
}
pub use quote_impl__ as __quote;

/// FIXME:
/// It probably should implement in proc-macro
#[macro_export]
macro_rules! quote {
    ($span:ident=> $($tt:tt)* ) => {
        {
            let mut builder = $crate::tt::TopSubtreeBuilder::new($crate::tt::DelimSpan {
                open: $span,
                close: $span,
            }, $crate::tt::Delimiter::Invisible);
            #[allow(unused)]
            let builder_ref = &mut builder;
            $crate::quote::__quote!($span builder_ref $($tt)*);
            builder.build_skip_top_subtree()
        }
    }
}
pub use quote;

pub trait ToTokenTree<S> {
    fn to_tokens(self, span: S, builder: &mut TopSubtreeBuilder<S>);
}

/// Wraps `TokenTreesView` with a delimiter (a subtree, but without allocating).
pub struct WithDelimiter<'a, S> {
    pub delimiter: tt::Delimiter,
    pub span: tt::DelimSpan<S>,
    pub token_trees: tt::TokenTreesView<'a, S>,
}

impl<S: Copy> ToTokenTree<S> for WithDelimiter<'_, S> {
    fn to_tokens(self, span: S, builder: &mut TopSubtreeBuilder<S>) {
        builder.open(self.delimiter, self.span.open);
        self.token_trees.to_tokens(span, builder);
        builder.close(self.span.close);
    }
}

impl<S: Copy> ToTokenTree<S> for tt::TokenTreesView<'_, S> {
    fn to_tokens(self, _: S, builder: &mut TopSubtreeBuilder<S>) {
        builder.extend_with_tt(self);
    }
}

impl<S: Copy> ToTokenTree<S> for tt::SubtreeView<'_, S> {
    fn to_tokens(self, _: S, builder: &mut TopSubtreeBuilder<S>) {
        builder.extend_with_tt(self.as_token_trees());
    }
}

impl<S: Copy> ToTokenTree<S> for tt::TopSubtree<S> {
    fn to_tokens(self, _: S, builder: &mut TopSubtreeBuilder<S>) {
        builder.extend_tt_dangerous(self.0);
    }
}

impl<S: Copy> ToTokenTree<S> for TtElement<'_, S> {
    fn to_tokens(self, _: S, builder: &mut TopSubtreeBuilder<S>) {
        match self {
            TtElement::Token(token, spacing) => builder.push(token.clone(), spacing),
            TtElement::Delimited(span, spacing, delim, subtree, subtree_iter) => {
                builder.extend_tt_dangerous(
                    std::iter::once(tt::TokenTree::Delimited(*span, spacing, delim, subtree))
                        .chain(subtree_iter.remaining().flat_tokens().iter().cloned()),
                );
            }
        }
    }
}

impl<T: ToTokenTree<S> + Clone, S: Copy> ToTokenTree<S> for &T {
    fn to_tokens(self, span: S, builder: &mut TopSubtreeBuilder<S>) {
        self.clone().to_tokens(span, builder);
    }
}

impl<S: Copy> ToTokenTree<S> for tt::Token<S> {
    fn to_tokens(self, _: S, builder: &mut TopSubtreeBuilder<S>) {
        builder.push(self, tt::Spacing::Alone);
    }
}

macro_rules! impl_to_to_tokentrees {
    ($($span:ident: $ty:ty => $this:ident $im:block;)*) => {
        $(
            impl<S: Copy> ToTokenTree<S> for $ty {
                fn to_tokens($this, $span: S, builder: &mut TopSubtreeBuilder<S>) {
                    let token: tt::Token<S> = $im.into();
                    builder.push(token, tt::Spacing::Alone);
                }
            }
        )*
    }
}

impl_to_to_tokentrees! {
    span: u32 => self { tt::Token{ kind: tt::TokenKind::Literal(Box::new(tt::Literal{symbol: Symbol::integer(self as _), kind: tt::LitKind::Integer, suffix: None })), span } };
    span: usize => self { tt::Token{ kind: tt::TokenKind::Literal(Box::new(tt::Literal{symbol: Symbol::integer(self as _), kind: tt::LitKind::Integer, suffix: None })), span } };
    span: i32 => self { tt::Token{ kind: tt::TokenKind::Literal(Box::new(tt::Literal{symbol: Symbol::integer(self as _), kind: tt::LitKind::Integer, suffix: None })), span } };
    span: f32 => self { tt::Token{ kind: tt::TokenKind::Literal(Box::new(tt::Literal{symbol: Symbol::intern(&self.to_smolstr()), kind: tt::LitKind::Float, suffix: None })), span } };
    span: &str => self { tt::Token{ kind: tt::TokenKind::Literal(Box::new(tt::Literal{symbol: Symbol::intern(&self.escape_default().to_smolstr()), kind: tt::LitKind::Str, suffix: None })), span}};
    span: char => self { tt::Token{ kind: tt::TokenKind::Literal(Box::new(tt::Literal{symbol: Symbol::intern(&self.escape_default().to_smolstr()), kind: tt::LitKind::Char, suffix: None })), span}};
    span: String => self { tt::Token{ kind: tt::TokenKind::Literal(Box::new(tt::Literal{symbol: Symbol::intern(&self.escape_default().to_smolstr()), kind: tt::LitKind::Str, suffix: None })), span}};
    span: bool => self { tt::Token{ kind: tt::TokenKind::Ident(if self { sym::true_.clone() } else { sym::false_.clone() }, tt::IdentIsRaw::No), span } };
    span: tt::Literal => self { tt::Token{ kind: tt::TokenKind::Literal(Box::new(self)), span } };
    span: Symbol => self {
        let (is_raw, s) = IdentIsRaw::split_from_symbol(self.as_str());
        tt::Token{ kind: tt::TokenKind::Ident(Symbol::intern(s), is_raw), span }
    };
}

#[cfg(test)]
mod tests {
    use core::fmt;

    use expect_test::expect;
    use intern::Symbol;

    use super::quote;

    #[derive(Copy, Clone, Debug)]
    struct DummySpan;
    impl fmt::Display for DummySpan {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "span")
        }
    }

    #[test]
    fn test_quote_delimiters() {
        assert_eq!(quote!(DummySpan =>{}).to_string(), "{}");
        assert_eq!(quote!(DummySpan =>()).to_string(), "()");
        assert_eq!(quote!(DummySpan =>[]).to_string(), "[]");
    }

    #[test]
    fn test_quote_idents() {
        assert_eq!(quote!(DummySpan =>32).to_string(), "32");
        assert_eq!(quote!(DummySpan =>struct).to_string(), "struct");
    }

    #[test]
    fn test_quote_hash_simple_literal() {
        let a = 20;
        assert_eq!(quote!(DummySpan =>#a).to_string(), "20");
        let s: String = "hello".into();
        assert_eq!(quote!(DummySpan =>#s).to_string(), "\"hello\"");
    }

    #[test]
    fn test_quote_hash_token_tree() {
        let a = Symbol::intern("hello");

        let quoted = quote!(DummySpan =>#a);
        assert_eq!(quoted.to_string(), "hello");
        let t = format!("{quoted:#?}");
        expect![[r#"
            SUBTREE $$ 937550:0@0..0#0 937550:0@0..0#0
              IDENT   hello 937550:0@0..0#0"#]]
        .assert_eq(&t);
    }

    #[test]
    fn test_quote_simple_derive_copy() {
        let name = Symbol::intern("Foo");

        let quoted = quote! {DummySpan =>
            impl Clone for #name {
                fn clone(&self) -> Self {
                    Self {}
                }
            }
        };

        assert_eq!(quoted.to_string(), "impl Clone for Foo {fn clone (& self) -> Self {Self {}}}");
    }

    #[test]
    fn test_quote_derive_copy_hack() {
        // Assume the given struct is:
        // struct Foo {
        //  name: String,
        //  id: u32,
        // }
        let struct_name = Symbol::intern("Foo");
        let fields = [Symbol::intern("name"), Symbol::intern("id")];
        let fields = fields.iter().map(|it| quote!(DummySpan =>#it: self.#it.clone(), ));

        let mut builder = tt::TopSubtreeBuilder::new(
            tt::DelimSpan { open: DummySpan, close: DummySpan },
            tt::Delimiter::Brace,
        );
        fields.for_each(|field| builder.extend_with_tt(field.view().as_token_trees()));
        let list = builder.build();

        let quoted = quote! {DummySpan =>
            impl Clone for #struct_name {
                fn clone(&self) -> Self {
                    Self #list
                }
            }
        };

        assert_eq!(quoted.to_string(), "impl Clone for Foo {fn clone (& self) -> Self {Self {name : self . name . clone () , id : self . id . clone () ,}}}");
    }
}
