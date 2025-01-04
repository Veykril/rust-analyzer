//! Parser recognizes special macro syntax, `$var` and `$(repeat)*`, in token
//! trees.

use std::sync::Arc;

use arrayvec::ArrayVec;
use intern::{sym, Symbol};
use span::{Edition, Span, SyntaxContextId};
use tt::{
    iter::{TtElement, TtIter},
    BinOpToken, IdentIsRaw, Literal, TokenKind,
};

type Token = tt::Token<Span>;

use crate::ParseError;

/// Consider
///
/// ```
/// macro_rules! an_macro {
///     ($x:expr + $y:expr) => ($y * $x)
/// }
/// ```
///
/// Stuff to the left of `=>` is a [`MetaTemplate`] pattern (which is matched
/// with input).
///
/// Stuff to the right is a [`MetaTemplate`] template which is used to produce
/// output.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MetaTemplate(pub(crate) Box<[Op]>);

impl MetaTemplate {
    pub(crate) fn parse_pattern(
        edition: impl Copy + Fn(SyntaxContextId) -> Edition,
        pattern: TtIter<'_, Span>,
    ) -> Result<Self, ParseError> {
        MetaTemplate::parse(edition, pattern, Mode::Pattern)
    }

    pub(crate) fn parse_template(
        edition: impl Copy + Fn(SyntaxContextId) -> Edition,
        template: TtIter<'_, Span>,
    ) -> Result<Self, ParseError> {
        MetaTemplate::parse(edition, template, Mode::Template)
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = &Op> {
        self.0.iter()
    }

    fn parse(
        edition: impl Copy + Fn(SyntaxContextId) -> Edition,
        mut src: TtIter<'_, Span>,
        mode: Mode,
    ) -> Result<Self, ParseError> {
        let mut res = Vec::new();
        while let Some(first) = src.peek() {
            let op = next_op(edition, first, &mut src, mode)?;
            res.push(op);
        }

        Ok(MetaTemplate(res.into_boxed_slice()))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Op {
    Var {
        name: Symbol,
        kind: Option<MetaVarKind>,
        id: Span,
    },
    Ignore {
        name: Symbol,
        id: Span,
    },
    Index {
        depth: usize,
    },
    Len {
        depth: usize,
    },
    Count {
        name: Symbol,
        // FIXME: `usize`` once we drop support for 1.76
        depth: Option<usize>,
    },
    Concat {
        elements: Box<[ConcatMetaVarExprElem]>,
        span: Span,
    },
    Repeat {
        tokens: MetaTemplate,
        kind: RepeatKind,
        separator: Option<Token>,
    },
    Subtree {
        tokens: MetaTemplate,
        delim_span: tt::DelimSpan<Span>,
        delimiter: tt::Delimiter,
    },
    Token(Token),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ConcatMetaVarExprElem {
    /// There is NO preceding dollar sign, which means that this identifier should be interpreted
    /// as a literal.
    Ident(Symbol),
    /// There is a preceding dollar sign, which means that this identifier should be expanded
    /// and interpreted as a variable.
    Var(Symbol),
    /// For example, a number or a string.
    Literal(Literal),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum RepeatKind {
    ZeroOrMore,
    OneOrMore,
    ZeroOrOne,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum ExprKind {
    // Matches expressions using the post-edition 2024. Was written using
    // `expr` in edition 2024 or later.
    Expr,
    // Matches expressions using the pre-edition 2024 rules.
    // Either written using `expr` in edition 2021 or earlier or.was written using `expr_2021`.
    Expr2021,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum MetaVarKind {
    Path,
    Ty,
    Pat,
    PatParam,
    Stmt,
    Block,
    Meta,
    Item,
    Vis,
    Expr(ExprKind),
    Ident,
    Tt,
    Lifetime,
    Literal,
}

#[derive(Clone, Copy)]
enum Mode {
    Pattern,
    Template,
}

fn next_op(
    edition: impl Copy + Fn(SyntaxContextId) -> Edition,
    first_peeked: TtElement<'_, Span>,
    src: &mut TtIter<'_, Span>,
    mode: Mode,
) -> Result<Op, ParseError> {
    let res = match first_peeked {
        TtElement::Token(t @ tt::Token { kind: TokenKind::Dollar, .. }, ..) => {
            src.next().expect("first token already peeked");
            // Note that the '$' itself is a valid token inside macro_rules.
            let second = match src.next() {
                None => return Ok(Op::Token(t.clone())),
                Some(it) => it,
            };
            match second {
                TtElement::Delimited(_, _, delimiter, _, mut subtree_iter) => match delimiter {
                    tt::Delimiter::Parenthesis => {
                        let (separator, kind) = parse_repeat(src)?;
                        let tokens = MetaTemplate::parse(edition, subtree_iter, mode)?;
                        Op::Repeat { tokens, separator, kind }
                    }
                    tt::Delimiter::Brace => match mode {
                        Mode::Template => parse_metavar_expr(&mut subtree_iter).map_err(|()| {
                            ParseError::unexpected("invalid metavariable expression")
                        })?,
                        Mode::Pattern => {
                            return Err(ParseError::unexpected(
                                "`${}` metavariable expressions are not allowed in matchers",
                            ))
                        }
                    },
                    _ => {
                        return Err(ParseError::expected(
                            "expected `$()` repetition or `${}` expression",
                        ))
                    }
                },
                TtElement::Token(t, _) => match &t.kind {
                    TokenKind::Ident(ident, IdentIsRaw::No) if *ident == sym::crate_ => {
                        // We simply produce identifier `$crate` here. And it will be resolved when lowering ast to Path.
                        // Op::Ident(tt::Ident {
                        //     sym: sym::dollar_crate.clone(),
                        //     span: t.span,
                        //     is_raw: tt::IdentIsRaw::No,
                        // })
                        todo!()
                    }
                    TokenKind::Ident(ident, _raw) => {
                        let kind = eat_fragment_kind(edition, src, mode)?;
                        let name = ident.clone();
                        let id = t.span;
                        Op::Var { name, kind, id }
                    }
                    TokenKind::Literal(lit) if is_boolean_literal(lit) => {
                        let kind = eat_fragment_kind(edition, src, mode)?;
                        let name = lit.symbol.clone();
                        let id = t.span;
                        Op::Var { name, kind, id }
                    }
                    TokenKind::Dollar => match mode {
                        Mode::Pattern => {
                            return Err(ParseError::unexpected(
                                "`$$` is not allowed on the pattern side",
                            ))
                        }
                        Mode::Template => Op::Token(t.clone()),
                    },
                    _ => return Err(ParseError::expected("expected ident")),
                },
            }
        }

        TtElement::Token(token, _) => {
            src.next().expect("first token already peeked");
            Op::Token(token.clone())
        }

        TtElement::Delimited(delim_span, _, delimiter, _, subtree_iter) => {
            src.next().expect("first token already peeked");
            let tokens = MetaTemplate::parse(edition, subtree_iter, mode)?;
            Op::Subtree { tokens, delim_span: *delim_span, delimiter }
        }
    };
    Ok(res)
}

fn eat_fragment_kind(
    edition: impl Copy + Fn(SyntaxContextId) -> Edition,
    src: &mut TtIter<'_, Span>,
    mode: Mode,
) -> Result<Option<MetaVarKind>, ParseError> {
    if let Mode::Pattern = mode {
        src.expect_colon().map_err(|()| ParseError::unexpected("missing fragment specifier"))?;
        let (ident, raw, span) = src
            .expect_ident()
            .map_err(|()| ParseError::unexpected("missing fragment specifier"))?;
        let kind = match ident.as_str() {
            _ if raw.yes() => return Ok(None),
            "path" => MetaVarKind::Path,
            "ty" => MetaVarKind::Ty,
            "pat" => {
                if edition(span.ctx).at_least_2021() {
                    MetaVarKind::Pat
                } else {
                    MetaVarKind::PatParam
                }
            }
            "pat_param" => MetaVarKind::PatParam,
            "stmt" => MetaVarKind::Stmt,
            "block" => MetaVarKind::Block,
            "meta" => MetaVarKind::Meta,
            "item" => MetaVarKind::Item,
            "vis" => MetaVarKind::Vis,
            "expr" => {
                if edition(span.ctx).at_least_2024() {
                    MetaVarKind::Expr(ExprKind::Expr)
                } else {
                    MetaVarKind::Expr(ExprKind::Expr2021)
                }
            }
            "expr_2021" => MetaVarKind::Expr(ExprKind::Expr2021),
            "ident" => MetaVarKind::Ident,
            "tt" => MetaVarKind::Tt,
            "lifetime" => MetaVarKind::Lifetime,
            "literal" => MetaVarKind::Literal,
            _ => return Ok(None),
        };
        return Ok(Some(kind));
    };
    Ok(None)
}

fn is_boolean_literal(lit: &Literal) -> bool {
    matches!(lit.symbol.as_str(), "true" | "false")
}

fn parse_repeat(iter: &mut TtIter<'_, Span>) -> Result<(Option<Token>, RepeatKind), ParseError> {
    match parse_kleene_op(iter) {
        Ok(Ok((op, span))) => return Ok((None, op)),

        // #1 is a separator followed by #2, a KleeneOp
        Ok(Err(token)) => match parse_kleene_op(iter) {
            // #2 is the `?` Kleene op, which does not take a separator (error)
            Ok(Ok((RepeatKind::ZeroOrOne, span))) => Err(ParseError::InvalidRepeat),

            // #2 is a KleeneOp :D
            Ok(Ok((op, span))) => return Ok((Some(token), op)),

            // #2 is a random token or not a token at all :(
            Ok(Err(Token { .. })) | Err(_) => Err(ParseError::InvalidRepeat),
        },

        // #1 is not a token
        Err(span) => Err(ParseError::InvalidRepeat),
    }
}

fn parse_kleene_op(
    iter: &mut TtIter<'_, Span>,
) -> Result<Result<(RepeatKind, Span), Token>, ParseError> {
    match iter.next() {
        Some(TtElement::Token(token, _)) => match kleene_op(token) {
            Some(op) => Ok(Ok((op, token.span))),
            None => Ok(Err(token.clone())),
        },
        _ => Err(ParseError::InvalidRepeat),
    }
}

fn kleene_op(token: &Token) -> Option<RepeatKind> {
    match token.kind {
        TokenKind::BinOp(BinOpToken::Star) => Some(RepeatKind::ZeroOrMore),
        TokenKind::BinOp(BinOpToken::Plus) => Some(RepeatKind::OneOrMore),
        TokenKind::Question => Some(RepeatKind::ZeroOrOne),
        _ => None,
    }
}

fn parse_metavar_expr(src: &mut TtIter<'_, Span>) -> Result<Op, ()> {
    let (func, raw, span) = src.expect_ident()?;
    let func = func.clone();
    let (delimiter, mut args_iter) = src.expect_subtree()?;

    if delimiter != tt::Delimiter::Parenthesis {
        return Err(());
    }

    let op = match func {
        s if sym::ignore == s => {
            args_iter.expect_dollar()?;
            let (ident, raw, span) = args_iter.expect_ident()?;
            Op::Ignore { name: ident.clone(), id: span }
        }
        s if sym::index == s => Op::Index { depth: parse_depth(&mut args_iter)? },
        s if sym::len == s => Op::Len { depth: parse_depth(&mut args_iter)? },
        s if sym::count == s => {
            args_iter.expect_dollar()?;
            let ident = args_iter.expect_ident()?.0.clone();
            let depth = if try_eat_comma(&mut args_iter) {
                Some(parse_depth(&mut args_iter)?)
            } else {
                None
            };
            Op::Count { name: ident, depth }
        }
        s if sym::concat == s => {
            let mut elements = Vec::new();
            while let Some(next) = args_iter.peek() {
                let element =
                    if let TtElement::Token(tt::Token { kind: TokenKind::Literal(lit), .. }, ..) =
                        next
                    {
                        args_iter.next().expect("already peeked");
                        ConcatMetaVarExprElem::Literal((**lit).clone())
                    } else {
                        let is_var = try_eat_dollar(&mut args_iter);
                        let (ident, _, _) = args_iter.expect_ident()?;

                        if is_var {
                            ConcatMetaVarExprElem::Var(ident.clone())
                        } else {
                            ConcatMetaVarExprElem::Ident(ident.clone())
                        }
                    };
                elements.push(element);
                if !args_iter.is_empty() {
                    args_iter.expect_comma()?;
                }
            }
            if elements.len() < 2 {
                return Err(());
            }
            Op::Concat { elements: elements.into_boxed_slice(), span }
        }
        _ => return Err(()),
    };

    if args_iter.next().is_some() {
        return Err(());
    }

    Ok(op)
}

fn parse_depth(src: &mut TtIter<'_, Span>) -> Result<usize, ()> {
    if src.is_empty() {
        Ok(0)
    } else if let Literal { symbol: text, suffix: None, .. } = src.expect_literal()?.0 {
        // Suffixes are not allowed.
        text.as_str().parse().map_err(|_| ())
    } else {
        Err(())
    }
}

fn try_eat_comma(src: &mut TtIter<'_, Span>) -> bool {
    if let Some(TtElement::Token(tt::Token { kind: TokenKind::Comma, .. }, ..)) = src.peek() {
        let _ = src.next();
        return true;
    }
    false
}

fn try_eat_dollar(src: &mut TtIter<'_, Span>) -> bool {
    if let Some(TtElement::Token(tt::Token { kind: TokenKind::Dollar, .. }, ..)) = src.peek() {
        let _ = src.next();
        return true;
    }
    false
}
