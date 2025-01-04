//! Conversions between [`SyntaxNode`] and [`tt::TokenTree`].

use std::fmt;

use intern::{sym, Symbol};
use rustc_hash::{FxHashMap, FxHashSet};
use span::{Edition, SpanAnchor, SpanData, SpanMap};
use stdx::{format_to, itertools::Either};
use syntax::{
    format_smolstr, Parse, PreorderWithTokens, SmolStr, SyntaxElement,
    SyntaxKind::{self, *},
    SyntaxNode, SyntaxToken, SyntaxTreeBuilder, TextRange, TextSize, WalkEvent,
};
use tt::{
    buffer::Cursor, token_to_literal, BinOpToken, DelimSpan, Delimiter, IdentIsRaw, Spacing, Token,
    TokenKind,
};

#[doc(hidden)]
pub use tt;

pub mod prettify_macro_expansion;
pub mod quote;
mod to_parser_input;
pub use to_parser_input::to_parser_input;
// FIXME: we probably should re-think  `token_tree_to_syntax_node` interfaces
pub use ::parser::TopEntryPoint;

#[cfg(test)]
mod tests;

pub trait SpanMapper<S> {
    fn span_for(&self, range: TextRange) -> S;
}

impl<S> SpanMapper<SpanData<S>> for SpanMap<S>
where
    SpanData<S>: Copy,
{
    fn span_for(&self, range: TextRange) -> SpanData<S> {
        self.span_at(range.start())
    }
}

impl<S: Copy, SM: SpanMapper<S>> SpanMapper<S> for &SM {
    fn span_for(&self, range: TextRange) -> S {
        SM::span_for(self, range)
    }
}

/// Dummy things for testing where spans don't matter.
pub mod dummy_test_span_utils {

    use span::{Span, SyntaxContextId};

    use super::*;

    pub const DUMMY: Span = Span {
        range: TextRange::empty(TextSize::new(0)),
        anchor: span::SpanAnchor {
            file_id: span::EditionedFileId::new(
                span::FileId::from_raw(0xe4e4e),
                span::Edition::CURRENT,
            ),
            ast_id: span::ROOT_ERASED_FILE_AST_ID,
        },
        ctx: SyntaxContextId::ROOT,
    };

    pub struct DummyTestSpanMap;

    impl SpanMapper<Span> for DummyTestSpanMap {
        fn span_for(&self, range: syntax::TextRange) -> Span {
            Span {
                range,
                anchor: span::SpanAnchor {
                    file_id: span::EditionedFileId::new(
                        span::FileId::from_raw(0xe4e4e),
                        span::Edition::CURRENT,
                    ),
                    ast_id: span::ROOT_ERASED_FILE_AST_ID,
                },
                ctx: SyntaxContextId::ROOT,
            }
        }
    }
}

/// Doc comment desugaring differs between mbe and proc-macros.
#[derive(Copy, Clone, PartialEq, Eq)]
pub enum DocCommentDesugarMode {
    /// Desugars doc comments as quoted raw strings
    Mbe,
    /// Desugars doc comments as quoted strings
    ProcMacro,
}

/// Converts a syntax tree to a [`tt::Subtree`] using the provided span map to populate the
/// subtree's spans.
pub fn syntax_node_to_token_tree<Ctx, SpanMap>(
    node: &SyntaxNode,
    map: SpanMap,
    span: SpanData<Ctx>,
    mode: DocCommentDesugarMode,
) -> tt::TopSubtree<SpanData<Ctx>>
where
    SpanData<Ctx>: Copy + fmt::Debug,
    SpanMap: SpanMapper<SpanData<Ctx>>,
{
    let mut c = NodeConverter::new(node, map, Default::default(), Default::default(), span, mode);
    convert_tokens(&mut c)
}

/// Converts a syntax tree to a [`tt::Subtree`] using the provided span map to populate the
/// subtree's spans. Additionally using the append and remove parameters, the additional tokens can
/// be injected or hidden from the output.
pub fn syntax_node_to_token_tree_modified<Ctx, SpanMap>(
    node: &SyntaxNode,
    map: SpanMap,
    append: FxHashMap<SyntaxElement, Vec<tt::Token<SpanData<Ctx>>>>,
    remove: FxHashSet<SyntaxElement>,
    call_site: SpanData<Ctx>,
    mode: DocCommentDesugarMode,
) -> tt::TopSubtree<SpanData<Ctx>>
where
    SpanMap: SpanMapper<SpanData<Ctx>>,
    SpanData<Ctx>: Copy + fmt::Debug,
{
    let mut c = NodeConverter::new(node, map, append, remove, call_site, mode);
    convert_tokens(&mut c)
}

// The following items are what `rustc` macro can be parsed into :
// link: https://github.com/rust-lang/rust/blob/9ebf47851a357faa4cd97f4b1dc7835f6376e639/src/libsyntax/ext/expand.rs#L141
// * Expr(P<ast::Expr>)                     -> token_tree_to_expr
// * Pat(P<ast::Pat>)                       -> token_tree_to_pat
// * Ty(P<ast::Ty>)                         -> token_tree_to_ty
// * Stmts(SmallVec<[ast::Stmt; 1]>)        -> token_tree_to_stmts
// * Items(SmallVec<[P<ast::Item>; 1]>)     -> token_tree_to_items
//
// * TraitItems(SmallVec<[ast::TraitItem; 1]>)
// * AssocItems(SmallVec<[ast::AssocItem; 1]>)
// * ForeignItems(SmallVec<[ast::ForeignItem; 1]>

/// Converts a [`tt::Subtree`] back to a [`SyntaxNode`].
/// The produced `SpanMap` contains a mapping from the syntax nodes offsets to the subtree's spans.
pub fn token_tree_to_syntax_node<Ctx>(
    tt: &tt::TopSubtree<SpanData<Ctx>>,
    entry_point: parser::TopEntryPoint,
    edition: parser::Edition,
) -> (Parse<SyntaxNode>, SpanMap<Ctx>)
where
    SpanData<Ctx>: Copy + fmt::Debug,
    Ctx: PartialEq,
{
    let buffer = tt.view().strip_invisible();
    let parser_input = to_parser_input(edition, buffer);
    let parser_output = entry_point.parse(&parser_input, edition);
    let mut tree_sink = TtTreeSink::new(buffer.cursor());
    for event in parser_output.iter() {
        match event {
            parser::Step::Token { kind, n_input_tokens: n_raw_tokens } => {
                tree_sink.token(kind, n_raw_tokens)
            }
            parser::Step::FloatSplit { ends_in_dot: has_pseudo_dot } => {
                // tree_sink.float_split(has_pseudo_dot)
            }
            parser::Step::Enter { kind } => tree_sink.start_node(kind),
            parser::Step::Exit => tree_sink.finish_node(),
            parser::Step::Error { msg } => tree_sink.error(msg.to_owned()),
        }
    }
    tree_sink.finish()
}

/// Convert a string to a `TokenTree`. The spans of the subtree will be anchored to the provided
/// anchor with the given context.
pub fn parse_to_token_tree<Ctx>(
    edition: Edition,
    anchor: SpanAnchor,
    ctx: Ctx,
    text: &str,
) -> Option<tt::TopSubtree<SpanData<Ctx>>>
where
    SpanData<Ctx>: Copy + fmt::Debug,
    Ctx: Copy,
{
    let lexed = parser::LexedStr::new(edition, text);
    if lexed.errors().next().is_some() {
        return None;
    }
    let mut conv =
        RawConverter { lexed, anchor, pos: 0, ctx, mode: DocCommentDesugarMode::ProcMacro };
    Some(convert_tokens(&mut conv))
}

/// Convert a string to a `TokenTree`. The passed span will be used for all spans of the produced subtree.
pub fn parse_to_token_tree_static_span<S>(
    edition: Edition,
    span: S,
    text: &str,
) -> Option<tt::TopSubtree<S>>
where
    S: Copy + fmt::Debug,
{
    let lexed = parser::LexedStr::new(edition, text);
    if lexed.errors().next().is_some() {
        return None;
    }
    let mut conv =
        StaticRawConverter { lexed, pos: 0, span, mode: DocCommentDesugarMode::ProcMacro };
    Some(convert_tokens(&mut conv))
}

fn convert_tokens<S, C>(conv: &mut C) -> tt::TopSubtree<S>
where
    C: TokenConverter<S>,
    S: Copy + fmt::Debug,
{
    let mut builder =
        tt::TopSubtreeBuilder::new(DelimSpan::from_single(conv.call_site()), Delimiter::Invisible);

    while let Some(r) = conv.bump() {
        dbg!(&r);
        let (token, abs_range, text) = match r {
            Either::Left(it) => it,
            Either::Right(t) => {
                builder.push(t, Spacing::Alone);
                continue;
            }
        };
        let expected = builder.expected_delimiter();
        let kind = match token {
            L_PAREN => {
                builder.open(Delimiter::Parenthesis, conv.span_for(abs_range));
                continue;
            }
            L_CURLY => {
                builder.open(Delimiter::Brace, conv.span_for(abs_range));
                continue;
            }
            L_BRACK => {
                builder.open(Delimiter::Bracket, conv.span_for(abs_range));
                continue;
            }

            R_CURLY if matches!(expected, Some(Delimiter::Brace)) => {
                builder.close(conv.span_for(abs_range));
                continue;
            }
            R_PAREN if matches!(expected, Some(Delimiter::Parenthesis)) => {
                builder.close(conv.span_for(abs_range));
                continue;
            }
            R_BRACK if matches!(expected, Some(Delimiter::Bracket)) => {
                builder.close(conv.span_for(abs_range));
                continue;
            }

            L_ANGLE => TokenKind::Lt,
            R_ANGLE => TokenKind::Gt,

            DOLLAR => TokenKind::Dollar,
            SEMICOLON => TokenKind::Semi,
            COMMA => TokenKind::Comma,
            AT => TokenKind::At,
            POUND => TokenKind::Pound,
            TILDE => TokenKind::Tilde,
            QUESTION => TokenKind::Question,
            PLUS => TokenKind::BinOp(BinOpToken::Plus),
            MINUS => TokenKind::BinOp(BinOpToken::Minus),
            PIPE => TokenKind::BinOp(BinOpToken::Or),
            AMP => TokenKind::BinOp(BinOpToken::And),
            CARET => TokenKind::BinOp(BinOpToken::Caret),
            SLASH => TokenKind::BinOp(BinOpToken::Slash),
            STAR => TokenKind::BinOp(BinOpToken::Star),
            PERCENT => TokenKind::BinOp(BinOpToken::Percent),
            SHL => TokenKind::BinOp(BinOpToken::Shl),
            SHR => TokenKind::BinOp(BinOpToken::Shr),
            PLUSEQ => TokenKind::BinOpEq(BinOpToken::Plus),
            MINUSEQ => TokenKind::BinOpEq(BinOpToken::Minus),
            PIPEEQ => TokenKind::BinOpEq(BinOpToken::Or),
            AMPEQ => TokenKind::BinOpEq(BinOpToken::And),
            CARETEQ => TokenKind::BinOpEq(BinOpToken::Caret),
            SLASHEQ => TokenKind::BinOpEq(BinOpToken::Slash),
            STAREQ => TokenKind::BinOpEq(BinOpToken::Star),
            PERCENTEQ => TokenKind::BinOpEq(BinOpToken::Percent),
            SHLEQ => TokenKind::BinOpEq(BinOpToken::Shl),
            SHREQ => TokenKind::BinOpEq(BinOpToken::Shr),
            UNDERSCORE => TokenKind::Ident(sym::underscore.clone(), tt::IdentIsRaw::No),
            DOT => TokenKind::Dot,
            DOT2 => TokenKind::DotDot,
            DOT3 => TokenKind::DotDotDot,
            DOT2EQ => TokenKind::DotDotEq,
            COLON => TokenKind::Colon,
            COLON2 => TokenKind::PathSep,
            EQ => TokenKind::Eq,
            EQ2 => TokenKind::EqEq,
            FAT_ARROW => TokenKind::FatArrow,
            BANG => TokenKind::Not,
            NEQ => TokenKind::Ne,
            THIN_ARROW => TokenKind::RArrow,
            LTEQ => TokenKind::Le,
            GTEQ => TokenKind::Ge,
            AMP2 => TokenKind::AndAnd,
            PIPE2 => TokenKind::OrOr,
            // FIXME: split up (raw) c string literals to an ident and a string literal when edition < 2021.
            k if k.is_literal() => TokenKind::Literal(Box::new(token_to_literal(text))),
            // FIXME: Doc desugaring
            COMMENT => continue,
            LIFETIME_IDENT => TokenKind::Lifetime(Symbol::intern(text)),
            ident if ident.is_any_identifier() => {
                let (raw, sym) = IdentIsRaw::split_from_symbol(text);
                TokenKind::Ident(Symbol::intern(sym), raw)
            }
            WHITESPACE => continue,
            kind => unreachable!("{kind:?}"),
        };
        let spacing = match conv.peek() {
            Some(kind) if is_single_token_op(kind) => tt::Spacing::Joint,
            _ => tt::Spacing::Alone,
        };
        builder.push(tt::Token::new(kind, conv.span_for(abs_range)), spacing);
    }

    // If we get here, we've consumed all input tokens.
    // We might have more than one subtree in the stack, if the delimiters are improperly balanced.
    // Merge them so we're left with one.
    builder.flatten_unclosed_subtrees();

    builder.build_skip_top_subtree()
}

fn is_single_token_op(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        EQ | L_ANGLE
            | R_ANGLE
            | BANG
            | AMP
            | PIPE
            | TILDE
            | AT
            | DOT
            | COMMA
            | SEMICOLON
            | COLON
            | POUND
            | DOLLAR
            | QUESTION
            | PLUS
            | MINUS
            | STAR
            | SLASH
            | PERCENT
            | CARET
            // LIFETIME_IDENT will be split into a sequence of `'` (a single quote) and an
            // identifier.
            | LIFETIME_IDENT
    )
}

/// Returns the textual content of a doc comment block as a quoted string
/// That is, strips leading `///` (or `/**`, etc)
/// and strips the ending `*/`
/// And then quote the string, which is needed to convert to `tt::Literal`
///
/// Note that proc-macros desugar with string literals where as macro_rules macros desugar with raw string literals.
pub fn desugar_doc_comment_text(text: &str, mode: DocCommentDesugarMode) -> (Symbol, tt::LitKind) {
    match mode {
        DocCommentDesugarMode::Mbe => {
            let mut num_of_hashes = 0;
            let mut count = 0;
            for ch in text.chars() {
                count = match ch {
                    '"' => 1,
                    '#' if count > 0 => count + 1,
                    _ => 0,
                };
                num_of_hashes = num_of_hashes.max(count);
            }

            // Quote raw string with delimiters
            (Symbol::intern(text), tt::LitKind::StrRaw(num_of_hashes))
        }
        // Quote string with delimiters
        DocCommentDesugarMode::ProcMacro => {
            (Symbol::intern(&format_smolstr!("{}", text.escape_debug())), tt::LitKind::Str)
        }
    }
}

// fn convert_doc_comment<S: Copy>(
//     token: &syntax::SyntaxToken,
//     span: S,
//     mode: DocCommentDesugarMode,
//     builder: &mut tt::TopSubtreeBuilder<S>,
// ) {
//     let Some(comment) = ast::Comment::cast(token.clone()) else { return };
//     let Some(doc) = comment.kind().doc else { return };

//     let mk_ident = |s: &str| {
//         tt::Token::from(tt::Ident { sym: Symbol::intern(s), span, is_raw: tt::IdentIsRaw::No })
//     };

//     let mk_punct =
//         |c: char| tt::Token::from(tt::Punct { char: c, spacing: tt::Spacing::Alone, span });

//     let mk_doc_literal = |comment: &ast::Comment| {
//         let prefix_len = comment.prefix().len();
//         let mut text = &comment.text()[prefix_len..];

//         // Remove ending "*/"
//         if comment.kind().shape == ast::CommentShape::Block {
//             text = &text[0..text.len() - 2];
//         }
//         let (text, kind) = desugar_doc_comment_text(text, mode);
//         let lit = tt::Literal { symbol: text, span, kind, suffix: None };

//         tt::Token::from(lit)
//     };

//     // Make `doc="\" Comments\""
//     let meta_tkns = [mk_ident("doc"), mk_punct('='), mk_doc_literal(&comment)];

//     // Make `#![]`
//     builder.push(mk_punct('#'));
//     if let ast::CommentPlacement::Inner = doc {
//         builder.push(mk_punct('!'));
//     }
//     builder.open(Delimiter::Bracket, span);
//     builder.extend(meta_tkns);
//     builder.close(span);
// }

/// A raw token (straight from lexer) converter
struct RawConverter<'a, Ctx> {
    lexed: parser::LexedStr<'a>,
    pos: usize,
    anchor: SpanAnchor,
    ctx: Ctx,
    mode: DocCommentDesugarMode,
}
/// A raw token (straight from lexer) converter that gives every token the same span.
struct StaticRawConverter<'a, S> {
    lexed: parser::LexedStr<'a>,
    pos: usize,
    span: S,
    mode: DocCommentDesugarMode,
}

trait SrcToken<Ctx, S> {
    fn kind(&self, ctx: &Ctx) -> SyntaxKind;

    fn to_char(&self, ctx: &Ctx) -> Option<char>;

    fn to_text(&self, ctx: &Ctx) -> SmolStr;

    fn as_leaf(&self) -> Option<&tt::Token<S>> {
        None
    }
}

trait TokenConverter<S>: Sized {
    // fn convert_doc_comment(
    //     &self,
    //     token: &Self::Token,
    //     span: S,
    //     builder: &mut tt::TopSubtreeBuilder<S>,
    // );

    fn bump(&mut self) -> Option<Either<(SyntaxKind, TextRange, &str), Token<S>>>;

    fn peek(&self) -> Option<SyntaxKind>;

    fn span_for(&self, range: TextRange) -> S;

    fn call_site(&self) -> S;
}

impl<Ctx: Copy> TokenConverter<SpanData<Ctx>> for RawConverter<'_, Ctx>
where
    SpanData<Ctx>: Copy,
{
    // fn convert_doc_comment(
    //     &self,
    //     &token: &usize,
    //     span: SpanData<Ctx>,
    //     builder: &mut tt::TopSubtreeBuilder<SpanData<Ctx>>,
    // ) {
    //     let text = self.lexed.text(token);
    //     convert_doc_comment(&doc_comment(text), span, self.mode, builder);
    // }

    fn bump(&mut self) -> Option<Either<(SyntaxKind, TextRange, &str), Token<SpanData<Ctx>>>> {
        if self.pos == self.lexed.len() {
            return None;
        }
        let token = self.pos;
        self.pos += 1;
        let range = self.lexed.text_range(token);
        let range = TextRange::new(range.start.try_into().ok()?, range.end.try_into().ok()?);

        Some(Either::Left((self.lexed.kind(token), range, self.lexed.text(token))))
    }

    fn peek(&self) -> Option<SyntaxKind> {
        if self.pos == self.lexed.len() {
            return None;
        }
        Some(self.lexed.kind(self.pos))
    }

    fn span_for(&self, range: TextRange) -> SpanData<Ctx> {
        SpanData { range, anchor: self.anchor, ctx: self.ctx }
    }

    fn call_site(&self) -> SpanData<Ctx> {
        SpanData { range: TextRange::empty(0.into()), anchor: self.anchor, ctx: self.ctx }
    }
}

impl<S> TokenConverter<S> for StaticRawConverter<'_, S>
where
    S: Copy,
{
    // fn convert_doc_comment(&self, &token: &usize, span: S, builder: &mut tt::TopSubtreeBuilder<S>) {
    //     let text = self.lexed.text(token);
    //     convert_doc_comment(&doc_comment(text), span, self.mode, builder);
    // }

    fn bump(&mut self) -> Option<Either<(SyntaxKind, TextRange, &str), Token<S>>> {
        if self.pos == self.lexed.len() {
            return None;
        }
        let token = self.pos;
        self.pos += 1;
        let range = self.lexed.text_range(token);
        let range = TextRange::new(range.start.try_into().ok()?, range.end.try_into().ok()?);

        Some(Either::Left((self.lexed.kind(self.pos), range, self.lexed.text(self.pos))))
    }

    fn peek(&self) -> Option<SyntaxKind> {
        if self.pos == self.lexed.len() {
            return None;
        }
        Some(self.lexed.kind(self.pos))
    }

    fn span_for(&self, _: TextRange) -> S {
        self.span
    }

    fn call_site(&self) -> S {
        self.span
    }
}

struct NodeConverter<SpanMap, S> {
    current: Option<SyntaxToken>,
    current_leaves: Vec<tt::Token<S>>,
    preorder: PreorderWithTokens,
    range: TextRange,
    /// Used to make the emitted text ranges in the spans relative to the span anchor.
    map: SpanMap,
    append: FxHashMap<SyntaxElement, Vec<tt::Token<S>>>,
    remove: FxHashSet<SyntaxElement>,
    call_site: S,
    mode: DocCommentDesugarMode,
}

impl<SpanMap, S> NodeConverter<SpanMap, S> {
    fn new(
        node: &SyntaxNode,
        map: SpanMap,
        append: FxHashMap<SyntaxElement, Vec<tt::Token<S>>>,
        remove: FxHashSet<SyntaxElement>,
        call_site: S,
        mode: DocCommentDesugarMode,
    ) -> Self {
        let mut this = NodeConverter {
            current: None,
            preorder: node.preorder_with_tokens(),
            range: node.text_range(),
            map,
            append,
            remove,
            call_site,
            current_leaves: vec![],
            mode,
        };
        let first = this.next_token();
        this.current = first;
        this
    }

    fn next_token(&mut self) -> Option<SyntaxToken> {
        while let Some(ev) = self.preorder.next() {
            match ev {
                WalkEvent::Enter(token) => {
                    if self.remove.contains(&token) {
                        match token {
                            syntax::NodeOrToken::Token(_) => {
                                continue;
                            }
                            node => {
                                self.preorder.skip_subtree();
                                if let Some(mut v) = self.append.remove(&node) {
                                    v.reverse();
                                    self.current_leaves.extend(v);
                                    return None;
                                }
                            }
                        }
                    } else if let syntax::NodeOrToken::Token(token) = token {
                        return Some(token);
                    }
                }
                WalkEvent::Leave(ele) => {
                    if let Some(mut v) = self.append.remove(&ele) {
                        v.reverse();
                        self.current_leaves.extend(v);
                        return None;
                    }
                }
            }
        }
        None
    }
}

impl<S, SpanMap> TokenConverter<S> for NodeConverter<SpanMap, S>
where
    S: Copy,
    SpanMap: SpanMapper<S>,
{
    // fn convert_doc_comment(
    //     &self,
    //     token: &Self::Token,
    //     span: S,
    //     builder: &mut tt::TopSubtreeBuilder<S>,
    // ) {
    //     convert_doc_comment(token.token(), span, self.mode, builder);
    // }

    fn bump(&mut self) -> Option<Either<(SyntaxKind, TextRange, &str), Token<S>>> {
        if let Some(leaf) = self.current_leaves.pop() {
            if self.current_leaves.is_empty() {
                self.current = self.next_token();
            }
            return Some(Either::Right(leaf));
        }

        let curr = self.current.clone()?;
        if !self.range.contains_range(curr.text_range()) {
            return None;
        }

        self.current = self.next_token();

        let range = curr.text_range();
        Some(Either::Left((
            curr.kind(),
            range,
            // FIXME: lifetimes begone
            unsafe { std::mem::transmute::<&str, &str>(curr.text()) },
        )))
    }

    // FIXME: current_leaves
    fn peek(&self) -> Option<SyntaxKind> {
        let curr = self.current.clone()?;
        if !self.range.contains_range(curr.text_range()) {
            return None;
        }

        let token = if curr.kind().is_punct() {
            SyntaxKind::from_char(curr.text().chars().next().unwrap()).unwrap()
        } else {
            curr.kind()
        };
        Some(token)
    }

    fn span_for(&self, range: TextRange) -> S {
        self.map.span_for(range)
    }
    fn call_site(&self) -> S {
        self.call_site
    }
}

struct TtTreeSink<'a, Ctx>
where
    SpanData<Ctx>: Copy,
{
    buf: String,
    cursor: Cursor<'a, SpanData<Ctx>>,
    text_pos: TextSize,
    inner: SyntaxTreeBuilder,
    token_map: SpanMap<Ctx>,
}

impl<'a, Ctx> TtTreeSink<'a, Ctx>
where
    SpanData<Ctx>: Copy,
{
    fn new(cursor: Cursor<'a, SpanData<Ctx>>) -> Self {
        TtTreeSink {
            buf: String::new(),
            cursor,
            text_pos: 0.into(),
            inner: SyntaxTreeBuilder::default(),
            token_map: SpanMap::empty(),
        }
    }

    fn finish(mut self) -> (Parse<SyntaxNode>, SpanMap<Ctx>) {
        self.token_map.finish();
        (self.inner.finish(), self.token_map)
    }
}

fn delim_to_str(d: Delimiter, closing: bool) -> Option<&'static str> {
    let texts = match d {
        Delimiter::Parenthesis => "()",
        Delimiter::Brace => "{}",
        Delimiter::Bracket => "[]",
        Delimiter::Invisible => return None,
    };

    let idx = closing as usize;
    Some(&texts[idx..texts.len() - (1 - idx)])
}

impl<Ctx> TtTreeSink<'_, Ctx>
where
    SpanData<Ctx>: Copy + fmt::Debug,
    Ctx: PartialEq,
{
    // /// Parses a float literal as if it was a one to two name ref nodes with a dot inbetween.
    // /// This occurs when a float literal is used as a field access.
    // fn float_split(&mut self, has_pseudo_dot: bool) {
    //     let (text, span) = match self.cursor.token_tree() {
    //         Some(tt::TokenTree::Token(tt::Token::Literal(tt::Literal {
    //             symbol: text,
    //             span,
    //             kind: tt::LitKind::Float,
    //             suffix: _,
    //         }))) => (text.as_str(), *span),
    //         tt => unreachable!("{tt:?}"),
    //     };
    //     // FIXME: Span splitting
    //     match text.split_once('.') {
    //         Some((left, right)) => {
    //             assert!(!left.is_empty());

    //             self.inner.start_node(SyntaxKind::NAME_REF);
    //             self.inner.token(SyntaxKind::INT_NUMBER, left);
    //             self.inner.finish_node();
    //             self.token_map.push(self.text_pos + TextSize::of(left), span);

    //             // here we move the exit up, the original exit has been deleted in process
    //             self.inner.finish_node();

    //             self.inner.token(SyntaxKind::DOT, ".");
    //             self.token_map.push(self.text_pos + TextSize::of(left) + TextSize::of("."), span);

    //             if has_pseudo_dot {
    //                 assert!(right.is_empty(), "{left}.{right}");
    //             } else {
    //                 assert!(!right.is_empty(), "{left}.{right}");
    //                 self.inner.start_node(SyntaxKind::NAME_REF);
    //                 self.inner.token(SyntaxKind::INT_NUMBER, right);
    //                 self.token_map.push(self.text_pos + TextSize::of(text), span);
    //                 self.inner.finish_node();

    //                 // the parser creates an unbalanced start node, we are required to close it here
    //                 self.inner.finish_node();
    //             }
    //             self.text_pos += TextSize::of(text);
    //         }
    //         None => unreachable!(),
    //     }
    //     self.cursor.bump();
    // }

    fn token(&mut self, kind: SyntaxKind, mut n_tokens: u8) {
        dbg!(n_tokens);
        if kind == LIFETIME_IDENT {
            // n_tokens = 2;
        }

        let mut last_two = self.cursor.peek_two_tokens();
        let mut combined_span = None;
        let mut last_spacing = Spacing::Joint;
        'tokens: for _ in 0..n_tokens {
            let Some((t, spacing)) = self.cursor.peek_token() else { break };
            dbg!(t);
            last_spacing = spacing;
            let text = match &t.kind {
                TokenKind::Eq => "=",
                TokenKind::Lt => "<",
                TokenKind::Le => "<=",
                TokenKind::EqEq => "==",
                TokenKind::Ne => "!=",
                TokenKind::Ge => ">=",
                TokenKind::Gt => ">",
                TokenKind::AndAnd => "&&",
                TokenKind::OrOr => "||",
                TokenKind::Not => "!",
                TokenKind::Tilde => "~",
                TokenKind::BinOp(b) => match b {
                    tt::BinOpToken::Plus => "+",
                    tt::BinOpToken::Minus => "-",
                    tt::BinOpToken::Star => "*",
                    tt::BinOpToken::Slash => "/",
                    tt::BinOpToken::Percent => "%",
                    tt::BinOpToken::Caret => "^",
                    tt::BinOpToken::And => "&",
                    tt::BinOpToken::Or => "|",
                    tt::BinOpToken::Shl => "<<",
                    tt::BinOpToken::Shr => ">>",
                },
                TokenKind::BinOpEq(b) => match b {
                    tt::BinOpToken::Plus => "+=",
                    tt::BinOpToken::Minus => "-=",
                    tt::BinOpToken::Star => "*=",
                    tt::BinOpToken::Slash => "/=",
                    tt::BinOpToken::Percent => "%=",
                    tt::BinOpToken::Caret => "^=",
                    tt::BinOpToken::And => "&=",
                    tt::BinOpToken::Or => "|=",
                    tt::BinOpToken::Shl => "<<=",
                    tt::BinOpToken::Shr => ">>=",
                },
                TokenKind::At => "@",
                TokenKind::Dot => ".",
                TokenKind::DotDot => "..",
                TokenKind::DotDotDot => "...",
                TokenKind::DotDotEq => "..=",
                TokenKind::Comma => ",",
                TokenKind::Semi => ";",
                TokenKind::Colon => ":",
                TokenKind::PathSep => "::",
                TokenKind::RArrow => "->",
                TokenKind::LArrow => "<-",
                TokenKind::FatArrow => "=>",
                TokenKind::Pound => "#",
                TokenKind::Dollar => "$",
                TokenKind::Question => "?",
                TokenKind::SingleQuote => "'",
                &TokenKind::OpenDelim(d) => match delim_to_str(d, false) {
                    Some(it) => it,
                    None => continue,
                },
                &TokenKind::CloseDelim(d) => match delim_to_str(d, true) {
                    Some(it) => it,
                    None => continue,
                },
                TokenKind::Literal(lit) => {
                    let buf_l = self.buf.len();
                    format_to!(self.buf, "{lit}");
                    debug_assert_ne!(self.buf.len() - buf_l, 0);
                    self.text_pos += TextSize::new((self.buf.len() - buf_l) as u32);
                    ""
                }
                TokenKind::Ident(ref ident, raw) => {
                    if raw.yes() {
                        self.buf.push_str("r#");
                        self.text_pos += TextSize::of("r#");
                    }
                    ident.as_str()
                }
                TokenKind::Lifetime(_) => todo!(),
                TokenKind::DocComment(_, _, _) => todo!(),
                TokenKind::Eof => todo!(),
            };
            self.buf += text;
            self.text_pos += TextSize::of(text);
            self.cursor.bump();
            combined_span = match combined_span {
                None => Some(t.span),
                Some(prev_span) => Some(Self::merge_spans(prev_span, t.span)),
            }
        }

        self.token_map.push(self.text_pos, combined_span.expect("expected at least one token"));
        self.inner.token(kind, self.buf.as_str());
        self.buf.clear();
        // FIXME: Emitting whitespace for this is really just a hack, we should get rid of it.
        // Add whitespace between adjoint puncts
        // if let Some([tt::Token::Punct(curr), tt::Token::Punct(next)]) = last_two {
        //     // Note: We always assume the semi-colon would be the last token in
        //     // other parts of RA such that we don't add whitespace here.
        //     //
        //     // When `next` is a `Punct` of `'`, that's a part of a lifetime identifier so we don't
        //     // need to add whitespace either.
        //     if curr.spacing == tt::Spacing::Alone && curr.char != ';' && next.char != '\'' {
        //         self.inner.token(WHITESPACE, " ");
        //         self.text_pos += TextSize::of(' ');
        //         self.token_map.push(self.text_pos, curr.span);
        //     }
        // }
    }

    fn start_node(&mut self, kind: SyntaxKind) {
        self.inner.start_node(kind);
    }

    fn finish_node(&mut self) {
        self.inner.finish_node();
    }

    fn error(&mut self, error: String) {
        self.inner.error(error, self.text_pos)
    }

    fn merge_spans(a: SpanData<Ctx>, b: SpanData<Ctx>) -> SpanData<Ctx> {
        // We don't do what rustc does exactly, rustc does something clever when the spans have different syntax contexts
        // but this runs afoul of our separation between `span` and `hir-expand`.
        SpanData {
            range: if a.ctx == b.ctx && a.anchor == b.anchor {
                TextRange::new(
                    std::cmp::min(a.range.start(), b.range.start()),
                    std::cmp::max(a.range.end(), b.range.end()),
                )
            } else {
                // Combining ranges make no sense when they come from different syntax contexts.
                a.range
            },
            anchor: a.anchor,
            ctx: a.ctx,
        }
    }
}
