#![cfg(FALSE)]
//! This module implements declarative macros: old `macro_rules` and the newer
//! `macro`. Declarative macros are also known as "macro by example", and that's
//! why we call this module `mbe`. For external documentation, prefer the
//! official terminology: "declarative macros".

pub(crate) mod diagnostics;
pub(crate) mod macro_rules;

mod macro_check;
mod macro_parser;
mod metavar_expr;
mod quoted;
mod transcribe;

use span::Span;
use tt::Spacing;

use self::metavar_expr::MetaVarExpr;

type Ident = tt::Ident<Span>;
type Token = tt::Ident<Span>;
type TokenKind = parser::SyntaxKind;

/// Describes how a sequence of token trees is delimited.
/// Cannot use `proc_macro::Delimiter` directly because this
/// structure should implement some additional traits.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Delimiter {
    /// `( ... )`
    Parenthesis,
    /// `{ ... }`
    Brace,
    /// `[ ... ]`
    Bracket,
    /// `∅ ... ∅`
    /// An invisible delimiter, that may, for example, appear around tokens coming from a
    /// "macro variable" `$var`. It is important to preserve operator priorities in cases like
    /// `$var * 3` where `$var` is `1 + 2`.
    /// Invisible delimiters might not survive roundtrip of a token stream through a string.
    Invisible,
}

/// Contains the sub-token-trees of a "delimited" token tree such as `(a b c)`.
/// The delimiters are not represented explicitly in the `tts` vector.
#[derive(PartialEq, Debug)]
struct Delimited {
    delim: Delimiter,
    /// FIXME: #67062 has details about why this is sub-optimal.
    tts: Vec<TokenTree>,
}

#[derive(PartialEq, Debug)]
struct SequenceRepetition {
    /// The sequence of token trees
    tts: Vec<TokenTree>,
    /// The optional separator
    separator: Option<Token>,
    /// Whether the sequence can be repeated zero (*), or one or more times (+)
    kleene: KleeneToken,
    /// The number of `Match`s that appear in the sequence (and subsequences)
    num_captures: usize,
}

#[derive(Clone, PartialEq, Debug, Copy)]
struct KleeneToken {
    span: Span,
    op: KleeneOp,
}

impl KleeneToken {
    fn new(op: KleeneOp, span: Span) -> KleeneToken {
        KleeneToken { span, op }
    }
}

/// A Kleene-style [repetition operator](https://en.wikipedia.org/wiki/Kleene_star)
/// for token sequences.
#[derive(Clone, PartialEq, Debug, Copy)]
pub(crate) enum KleeneOp {
    /// Kleene star (`*`) for zero or more repetitions
    ZeroOrMore,
    /// Kleene plus (`+`) for one or more repetitions
    OneOrMore,
    /// Kleene optional (`?`) for zero or one repetitions
    ZeroOrOne,
}

/// Similar to `tokenstream::TokenTree`, except that `Sequence`, `MetaVar`, `MetaVarDecl`, and
/// `MetaVarExpr` are "first-class" token trees. Useful for parsing macros.
#[derive(Debug, PartialEq)]
enum TokenTree {
    Token(Token),
    /// A delimited sequence, e.g. `($e:expr)` (RHS) or `{ $e }` (LHS).
    Delimited(DelimSpan, DelimSpacing, Delimited),
    /// A kleene-style repetition sequence, e.g. `$($e:expr)*` (RHS) or `$($e),*` (LHS).
    Sequence(DelimSpan, SequenceRepetition),
    /// e.g., `$var`.
    MetaVar(Span, Ident),
    /// e.g., `$var:expr`. Only appears on the LHS.
    MetaVarDecl(Span, Ident /* name to bind */, Option<NonterminalKind>),
    /// A meta-variable expression inside `${...}`.
    MetaVarExpr(DelimSpan, MetaVarExpr),
}

impl TokenTree {
    /// Returns `true` if the given token tree is delimited.
    fn is_delimited(&self) -> bool {
        matches!(*self, TokenTree::Delimited(..))
    }

    /// Returns `true` if the given token tree is a token of the given kind.
    fn is_token(&self, expected_kind: &TokenKind) -> bool {
        match self {
            TokenTree::Token(t) => t.kind() == expected_kind,
            _ => false,
        }
    }

    /// Retrieves the `TokenTree`'s span.
    fn span(&self) -> Span {
        match *self {
            TokenTree::Token(t) => t.span(),
            TokenTree::MetaVar(span, _) | TokenTree::MetaVarDecl(span, _, _) => span,
            TokenTree::Delimited(span, ..)
            | TokenTree::MetaVarExpr(span, _)
            | TokenTree::Sequence(span, _) => span.entire(),
        }
    }

    fn token(kind: TokenKind, span: Span) -> TokenTree {
        TokenTree::Token(Token::new(kind, span))
    }
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum NonterminalKind {
    Item,
    Block,
    Stmt,
    Pat(NtPatKind),
    Expr(NtExprKind),
    Ty,
    Ident,
    Lifetime,
    Literal,
    Meta,
    Path,
    Vis,
    TT,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum NtPatKind {
    // Matches or-patterns. Was written using `pat` in edition 2021 or later.
    PatWithOr,
    // Doesn't match or-patterns.
    // - `inferred`: was written using `pat` in edition 2015 or 2018.
    // - `!inferred`: was written using `pat_param`.
    PatParam { inferred: bool },
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum NtExprKind {
    // Matches expressions using the post-edition 2024. Was written using
    // `expr` in edition 2024 or later.
    Expr,
    // Matches expressions using the pre-edition 2024 rules.
    // - `inferred`: was written using `expr` in edition 2021 or earlier.
    // - `!inferred`: was written using `expr_2021`.
    Expr2021 { inferred: bool },
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub struct DelimSpan {
    pub open: Span,
    pub close: Span,
}

impl DelimSpan {
    pub fn from_single(sp: Span) -> Self {
        DelimSpan { open: sp, close: sp }
    }

    pub fn from_pair(open: Span, close: Span) -> Self {
        DelimSpan { open, close }
    }

    pub fn entire(self) -> Span {
        self.open.with_hi(self.close.hi())
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct DelimSpacing {
    pub open: Spacing,
    pub close: Spacing,
}

impl DelimSpacing {
    pub fn new(open: Spacing, close: Spacing) -> DelimSpacing {
        DelimSpacing { open, close }
    }
}
