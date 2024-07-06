//! Convert macro-by-example tokens which are specific to macro expansion into a
//! format that works for our parser.

use std::fmt;

use syntax::{SyntaxKind, SyntaxKind::*, T};

use crate::flat_tt::{self, iter::TtIter, Subtree, TokenTree};

pub(crate) fn to_parser_input<S: Copy + fmt::Debug>(tree: &Subtree<S>) -> parser::Input {
    let mut res = parser::Input::default();
    to_parser_input_subtree(&mut res, tree);
    res
}

pub(crate) fn to_parser_input_tt_iter<S: Copy + fmt::Debug>(tree: &TtIter<'_, S>) -> parser::Input {
    let mut res = parser::Input::default();
    to_parser_input_tt(&mut res, tree);
    res
}

fn to_parser_input_tt<S: Copy + fmt::Debug>(
    res: &mut parser::Input,
    mut iter_token_trees: impl Iterator<Item = TokenTree<'_, S>>,
) {
    while let Some(tt) = iter_token_trees.next() {
        match tt {
            flat_tt::TokenTree::Leaf(tt::Leaf::Punct(punct)) if punct.char == '\'' => {
                let next = iter_token_trees.next();
                match next {
                    Some(flat_tt::TokenTree::Leaf(tt::Leaf::Ident(_ident))) => {
                        res.push(LIFETIME_IDENT);
                        continue;
                    }
                    _ => panic!("Next token must be ident : {:#?}", next),
                }
            }
            flat_tt::TokenTree::Leaf(leaf) => {
                match leaf {
                    tt::Leaf::Literal(lit) => {
                        let is_negated = lit.text.starts_with('-');
                        let inner_text = &lit.text[if is_negated { 1 } else { 0 }..];

                        let kind = parser::LexedStr::single_token(inner_text)
                            .map(|(kind, _error)| kind)
                            .filter(|kind| {
                                kind.is_literal()
                                    && (!is_negated || matches!(kind, FLOAT_NUMBER | INT_NUMBER))
                            })
                            .unwrap_or_else(|| panic!("Fail to convert given literal {:#?}", &lit));

                        res.push(kind);

                        if kind == FLOAT_NUMBER && !inner_text.ends_with('.') {
                            // Tag the token as joint if it is float with a fractional part
                            // we use this jointness to inform the parser about what token split
                            // event to emit when we encounter a float literal in a field access
                            res.was_joint();
                        }
                    }
                    tt::Leaf::Ident(ident) => match ident.text.as_ref() {
                        "_" => res.push(T![_]),
                        i if i.starts_with('\'') => res.push(LIFETIME_IDENT),
                        _ => match SyntaxKind::from_keyword(&ident.text) {
                            Some(kind) => res.push(kind),
                            None => {
                                let contextual_keyword =
                                    SyntaxKind::from_contextual_keyword(&ident.text)
                                        .unwrap_or(SyntaxKind::IDENT);
                                res.push_ident(contextual_keyword);
                            }
                        },
                    },
                    tt::Leaf::Punct(punct) => {
                        let kind = SyntaxKind::from_char(punct.char)
                            .unwrap_or_else(|| panic!("{punct:#?} is not a valid punct"));
                        res.push(kind);
                        if punct.spacing == tt::Spacing::Joint {
                            res.was_joint();
                        }
                    }
                }
            }
            flat_tt::TokenTree::Subtree(t) => to_parser_input_subtree(res, t),
        }
    }
}
fn to_parser_input_subtree<S: Copy + fmt::Debug>(res: &mut parser::Input, tree: &Subtree<S>) {
    let delimiter_kind = tree.delimiter().kind;
    if let Some(kind) = match delimiter_kind {
        tt::DelimiterKind::Parenthesis => Some(T!['(']),
        tt::DelimiterKind::Brace => Some(T!['{']),
        tt::DelimiterKind::Bracket => Some(T!['[']),
        tt::DelimiterKind::Invisible => None,
    } {
        res.push(kind);
    }

    to_parser_input_tt(res, tree.iter_token_trees());

    if let Some(kind) = match delimiter_kind {
        tt::DelimiterKind::Parenthesis => Some(T!['(']),
        tt::DelimiterKind::Brace => Some(T!['{']),
        tt::DelimiterKind::Bracket => Some(T!['[']),
        tt::DelimiterKind::Invisible => None,
    } {
        res.push(kind);
    }
}
