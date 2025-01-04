//! Convert macro-by-example tokens which are specific to macro expansion into a
//! format that works for our parser.

use std::fmt;

use span::Edition;
use syntax::{SyntaxKind, SyntaxKind::*, T};
use tt::TopSubtreeBuilder;

use crate::quote;

pub fn to_parser_input<S: Copy + fmt::Debug>(
    edition: Edition,
    buffer: tt::TokenTreesView<'_, S>,
) -> parser::Input {
    let mut res = parser::Input::default();

    let mut cursor = buffer.cursor();

    'cursor: while !cursor.eof() {
        let Some(tt) = cursor.token_tree() else {
            let d = cursor.end();
            if let Some(kind) = match d {
                tt::Delimiter::Parenthesis => Some(T![')']),
                tt::Delimiter::Brace => Some(T!['}']),
                tt::Delimiter::Bracket => Some(T![']']),
                tt::Delimiter::Invisible => None,
            } {
                res.push(kind);
            };
            continue;
        };
        let (token, mut spacing) = match tt {
            tt::TokenTree::Token(token, spacing) => (token, *spacing),
            tt::TokenTree::Delimited(_, _, delimiter, _) => {
                if let Some(kind) = match delimiter {
                    tt::Delimiter::Parenthesis => Some(T!['(']),
                    tt::Delimiter::Brace => Some(T!['{']),
                    tt::Delimiter::Bracket => Some(T!['[']),
                    tt::Delimiter::Invisible => None,
                } {
                    res.push(kind);
                }
                cursor.bump();
                continue 'cursor;
            }
        };
        'multi: {
            let kinds: &[_] = match &token.kind {
                tt::TokenKind::Le => &[L_ANGLE, EQ],
                tt::TokenKind::EqEq => &[EQ, EQ],
                tt::TokenKind::Ne => &[BANG, EQ],
                tt::TokenKind::Ge => &[R_ANGLE, EQ],
                tt::TokenKind::AndAnd => &[AMP, AMP],
                tt::TokenKind::OrOr => &[PIPE, PIPE],
                tt::TokenKind::BinOpEq(binop) => match binop {
                    tt::BinOpToken::Plus => &[PLUS, EQ],
                    tt::BinOpToken::Minus => &[MINUS, EQ],
                    tt::BinOpToken::Star => &[STAR, EQ],
                    tt::BinOpToken::Slash => &[SLASH, EQ],
                    tt::BinOpToken::Percent => &[PERCENT, EQ],
                    tt::BinOpToken::Caret => &[CARET, EQ],
                    tt::BinOpToken::And => &[AMP, EQ],
                    tt::BinOpToken::Or => &[PIPE, EQ],
                    tt::BinOpToken::Shl => &[L_ANGLE, L_ANGLE, EQ],
                    tt::BinOpToken::Shr => &[R_ANGLE, R_ANGLE, EQ],
                },
                tt::TokenKind::DotDot => &[DOT, DOT],
                tt::TokenKind::DotDotDot => &[DOT, DOT, DOT],
                tt::TokenKind::DotDotEq => &[DOT, DOT, EQ],
                tt::TokenKind::PathSep => &[COLON, COLON],
                tt::TokenKind::RArrow => &[MINUS, R_ANGLE],
                tt::TokenKind::LArrow => &[L_ANGLE, MINUS],
                tt::TokenKind::FatArrow => &[EQ, R_ANGLE],
                tt::TokenKind::BinOp(binop) => match binop {
                    tt::BinOpToken::Shl => &[L_ANGLE, L_ANGLE],
                    tt::BinOpToken::Shr => &[R_ANGLE, R_ANGLE],
                    _ => break 'multi,
                },
                _ => break 'multi,
            };
            // FIXME: Jointness of first token is wrong?
            for &kind in kinds {
                res.push(kind);
                res.was_joint();
            }
            cursor.bump();
            continue 'cursor;
        }

        let kind = match &token.kind {
            tt::TokenKind::BinOp(binop) => match binop {
                tt::BinOpToken::Plus => PLUS,
                tt::BinOpToken::Minus => MINUS,
                tt::BinOpToken::Star => STAR,
                tt::BinOpToken::Slash => SLASH,
                tt::BinOpToken::Percent => PERCENT,
                tt::BinOpToken::Caret => CARET,
                tt::BinOpToken::And => AMP,
                tt::BinOpToken::Or => PIPE,
                tt::BinOpToken::Shl | tt::BinOpToken::Shr => unreachable!(),
            },

            tt::TokenKind::Eq => EQ,
            tt::TokenKind::Lt => L_ANGLE,
            tt::TokenKind::Gt => R_ANGLE,
            tt::TokenKind::Not => BANG,
            tt::TokenKind::Tilde => TILDE,
            tt::TokenKind::At => AT,
            tt::TokenKind::Dot => DOT,
            tt::TokenKind::Comma => COMMA,
            tt::TokenKind::Semi => SEMICOLON,
            tt::TokenKind::Colon => COLON,
            tt::TokenKind::Pound => POUND,
            tt::TokenKind::Dollar => DOLLAR,
            tt::TokenKind::Question => QUESTION,
            // proc-macros generate lifetimes like this
            tt::TokenKind::SingleQuote => {
                cursor.bump();
                match cursor.token_tree() {
                    Some(&tt::TokenTree::Token(
                        tt::Token { kind: tt::TokenKind::Ident(..), .. },
                        spacing_,
                    )) => {
                        spacing = spacing_;
                        LIFETIME_IDENT
                    }
                    _ => panic!("Next token must be ident"),
                }
            }
            // should be unreachable?
            tt::TokenKind::OpenDelim(delim) => match delim {
                tt::Delimiter::Parenthesis => L_PAREN,
                tt::Delimiter::Brace => L_CURLY,
                tt::Delimiter::Bracket => L_BRACK,
                tt::Delimiter::Invisible => {
                    cursor.bump();
                    continue;
                }
            },
            // should be unreachable?
            tt::TokenKind::CloseDelim(delim) => match delim {
                tt::Delimiter::Parenthesis => R_PAREN,
                tt::Delimiter::Brace => R_CURLY,
                tt::Delimiter::Bracket => R_BRACK,
                tt::Delimiter::Invisible => {
                    cursor.bump();
                    continue;
                }
            },
            tt::TokenKind::Literal(lit) => match lit.kind {
                tt::LitKind::Byte => BYTE,
                tt::LitKind::Char => CHAR,
                tt::LitKind::Integer => INT_NUMBER,
                tt::LitKind::Float => {
                    if lit.suffix.is_none() && !lit.symbol.as_str().ends_with('.') {
                        // Tag the token as joint if it is float with a fractional part
                        // we use this jointness to inform the parser about what token split
                        // event to emit when we encounter a float literal in a field access
                        spacing = tt::Spacing::Joint
                    }
                    FLOAT_NUMBER
                }
                tt::LitKind::Str => STRING,
                tt::LitKind::StrRaw(_) => STRING,
                tt::LitKind::ByteStr => BYTE_STRING,
                tt::LitKind::ByteStrRaw(_) => BYTE_STRING,
                tt::LitKind::CStr => C_STRING,
                tt::LitKind::CStrRaw(_) => C_STRING,
                tt::LitKind::Err(_) => ERROR,
            },
            tt::TokenKind::Ident(sym, raw) => match sym.as_str() {
                _ if raw.yes() => IDENT,
                "_" => T![_],
                // is this right?
                // i if i.starts_with('\'') => LIFETIME_IDENT,
                text => match SyntaxKind::from_keyword(text, edition) {
                    Some(kind) => kind,
                    None => match SyntaxKind::from_contextual_keyword(text, edition) {
                        Some(contextual_keyword) => {
                            res.push_ident(contextual_keyword);
                            if spacing == tt::Spacing::Joint {
                                res.was_joint();
                            }
                            cursor.bump();
                            continue;
                        }
                        None => IDENT,
                    },
                },
            },
            tt::TokenKind::Lifetime(_) => LIFETIME,
            tt::TokenKind::DocComment(_, _, _) => todo!(),
            tt::TokenKind::Eof => break,
            _ => unreachable!(),
        };
        res.push(kind);
        if spacing == tt::Spacing::Joint {
            res.was_joint();
        }
        cursor.bump();
    }

    res
}

#[cfg(test)]
mod tests {
    use expect_test::expect;

    use super::*;

    const DUMMY: () = ();

    #[test]
    fn smoke() {
        let tt = quote! {DUMMY =>
            /// A
            const DUMMY: &'static Span = &Span {
                range: TextRange::empty(TextSize::new(0)),
                anchor: SpanAnchor {
                    file_id: span::EditionedFileId::new(
                        span::FileId::from_raw(0xe4e4e),
                        span::Edition::CURRENT,
                    ),
                    ast_id: ROOT_ERASED_FILE_AST_ID,
                },
                ctx: SyntaxContextId::ROOT,
            };
        };

        let input = to_parser_input(Edition::CURRENT, tt.token_trees());
        expect![[r#"
            Input[POUND, L_BRACK, IDENT, EQ, STRING, R_BRACK, IDENT, IDENT, COLON, AMP, LIFETIME, IDENT, EQ, AMP, IDENT, L_CURLY, IDENT, COLON, IDENT, COLON(Joint), COLON(Joint), IDENT, L_PAREN, IDENT, COLON(Joint), COLON(Joint), IDENT, L_PAREN, INT_NUMBER, R_PAREN, R_PAREN, COMMA, IDENT, COLON, IDENT, L_CURLY, IDENT, COLON, IDENT, COLON(Joint), COLON(Joint), IDENT, COLON(Joint), COLON(Joint), IDENT, L_PAREN, IDENT, COLON(Joint), COLON(Joint), IDENT, COLON(Joint), COLON(Joint), IDENT, L_PAREN, INT_NUMBER, R_PAREN, COMMA, IDENT, COLON(Joint), COLON(Joint), IDENT, COLON(Joint), COLON(Joint), IDENT, COMMA, R_PAREN, COMMA, IDENT, COLON, IDENT, COMMA, R_CURLY, COMMA, IDENT, COLON, IDENT, COLON(Joint), COLON(Joint), IDENT, COMMA, R_CURLY, SEMICOLON, ]
        "#]]
        .assert_debug_eq(&input);
    }

    #[test]
    fn lit() {
        let tt = quote! {DUMMY =>
            0
            ""
            0.0
            'a'
        };

        let input = to_parser_input(Edition::CURRENT, tt.token_trees());
        expect![[r#"
            Input[INT_NUMBER, STRING, FLOAT_NUMBER(Joint), CHAR, ]
        "#]]
        .assert_debug_eq(&input);
    }
}
