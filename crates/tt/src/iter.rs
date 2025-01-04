//! A "Parser" structure for token trees. We use this when parsing a declarative
//! macro definition into a list of patterns and templates.

use std::fmt;

use arrayvec::ArrayVec;
use intern::{sym, Symbol};

use crate::{
    BinOpToken, DelimSpacing, DelimSpan, Delimiter, IdentIsRaw, Literal, Spacing, Subtree, Token,
    TokenKind, TokenTree, TokenTreesView,
};

#[derive(Clone)]
pub struct TtIter<'a, S> {
    inner: std::slice::Iter<'a, TokenTree<S>>,
}

impl<S: Copy + fmt::Debug> fmt::Debug for TtIter<'_, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TtIter").field("remaining", &self.remaining()).finish()
    }
}

#[derive(Clone, Copy)]
pub struct TtIterSavepoint<'a, S>(&'a [TokenTree<S>]);

impl<'a, S: Copy> TtIterSavepoint<'a, S> {
    pub fn remaining(self) -> TokenTreesView<'a, S> {
        TokenTreesView::new(self.0)
    }
}

impl<'a, S: Copy> TtIter<'a, S> {
    pub(crate) fn new(tt: &'a [TokenTree<S>]) -> TtIter<'a, S> {
        TtIter { inner: tt.iter() }
    }

    pub fn expect_token(&mut self) -> Result<&Token<S>, ()> {
        match self.next() {
            Some(TtElement::Token(t, ..)) => Ok(t),
            _ => Err(()),
        }
    }

    pub fn expect_any_token(&mut self, tokens: &[crate::TokenKind]) -> Result<(), ()> {
        match self.next() {
            Some(TtElement::Token(Token { kind, .. }, ..)) if tokens.contains(kind) => Ok(()),
            _ => Err(()),
        }
    }

    pub fn expect_subtree(&mut self) -> Result<(Delimiter, TtIter<'a, S>), ()> {
        match self.next() {
            Some(TtElement::Delimited(.., delimiter, _, iter)) => Ok((delimiter, iter)),
            _ => Err(()),
        }
    }

    // pub fn expect_token(&mut self) -> Result<&'a Token<S>, ()> {
    //     match self.next() {
    //         Some(TtElement::Token(it)) => Ok(it),
    //         _ => Err(()),
    //     }
    // }

    pub fn expect_dollar(&mut self) -> Result<(), ()> {
        match self.next() {
            Some(TtElement::Token(Token { kind: TokenKind::Dollar, .. }, _)) => Ok(()),
            _ => Err(()),
        }
    }

    pub fn expect_comma(&mut self) -> Result<(), ()> {
        match self.next() {
            Some(TtElement::Token(Token { kind: TokenKind::Comma, .. }, _)) => Ok(()),
            _ => Err(()),
        }
    }

    pub fn expect_ident(&mut self) -> Result<(&Symbol, IdentIsRaw, S), ()> {
        match self.next() {
            Some(TtElement::Token(Token { kind: TokenKind::Ident(ident, raw), span }, _)) => {
                Ok((ident, *raw, *span))
            }
            _ => Err(()),
        }
    }

    pub fn expect_literal(&mut self) -> Result<(&Literal, S), ()> {
        match self.next() {
            Some(TtElement::Token(Token { kind: TokenKind::Literal(lit), span }, _)) => {
                Ok((lit, *span))
            }
            _ => Err(()),
        }
    }

    // pub fn expect_ident_or_underscore(&mut self) -> Result<&'a Ident<S>, ()> {
    //     match self.expect_token()? {
    //         Token::Ident(it) => Ok(it),
    //         _ => Err(()),
    //     }
    // }

    // pub fn expect_literal(&mut self) -> Result<&'a Token<S>, ()> {
    //     let it = self.expect_token()?;
    //     match it {
    //         Token::Literal(_) => Ok(it),
    //         Token::Ident(ident) if ident.sym == sym::true_ || ident.sym == sym::false_ => Ok(it),
    //         _ => Err(()),
    //     }
    // }

    // pub fn expect_single_punct(&mut self) -> Result<&'a Punct<S>, ()> {
    //     match self.expect_token()? {
    //         Token::Punct(it) => Ok(it),
    //         _ => Err(()),
    //     }
    // }

    /// Returns consecutive `Punct`s that can be glued together.
    ///
    /// This method currently may return a single quotation, which is part of lifetime ident and
    /// conceptually not a punct in the context of mbe. Callers should handle this.
    pub fn expect_glued_punct(&mut self) -> Result<ArrayVec<&Token<S>, 3>, ()> {
        let TtElement::Token(first, spacing) = self.next().ok_or(())? else {
            return Err(());
        };

        let mut res = ArrayVec::new();
        if spacing == Spacing::Alone {
            res.push(first);
            return Ok(res);
        }

        let (second, third) = match (self.peek_n(0), self.peek_n(1)) {
            (Some(TokenTree::Token(p2, spacing2)), Some(TokenTree::Token(p3, spacing3)))
                if *spacing2 == Spacing::Joint =>
            {
                (p2, Some(p3))
            }
            (Some(TokenTree::Token(p2, spacing2)), _) => (p2, None),
            _ => {
                res.push(first);
                return Ok(res);
            }
        };

        match (&first.kind, &second.kind, third.as_ref().map(|it| &it.kind)) {
            (TokenKind::Dot, TokenKind::Dot, Some(TokenKind::Dot | TokenKind::Eq))
            | (TokenKind::Lt, TokenKind::Lt, Some(TokenKind::Eq))
            | (TokenKind::Gt, TokenKind::Gt, Some(TokenKind::Eq)) => {
                let _ = self.next().unwrap();
                let _ = self.next().unwrap();
                res.push(first);
                res.push(second);
                res.push(third.unwrap());
            }
            (
                TokenKind::BinOp(BinOpToken::Minus)
                | TokenKind::Not
                | TokenKind::BinOp(BinOpToken::Star)
                | TokenKind::BinOp(BinOpToken::Slash)
                | TokenKind::BinOp(BinOpToken::And)
                | TokenKind::BinOp(BinOpToken::Percent)
                | TokenKind::BinOp(BinOpToken::Caret)
                | TokenKind::Lt
                | TokenKind::BinOp(BinOpToken::Plus)
                | TokenKind::Eq
                | TokenKind::Gt
                | TokenKind::BinOp(BinOpToken::Or),
                TokenKind::Eq,
                _,
            )
            | (
                TokenKind::BinOp(BinOpToken::Minus) | TokenKind::Eq | TokenKind::Gt,
                TokenKind::Gt,
                _,
            )
            | (_, _, Some(TokenKind::Semi))
            | (TokenKind::Lt, TokenKind::BinOp(BinOpToken::Minus), _)
            | (TokenKind::Colon, TokenKind::Colon, _)
            | (TokenKind::Dot, TokenKind::Dot, _)
            | (TokenKind::BinOp(BinOpToken::And), TokenKind::BinOp(BinOpToken::And), _)
            | (TokenKind::Lt, TokenKind::Lt, _)
            | (TokenKind::BinOp(BinOpToken::Or), TokenKind::BinOp(BinOpToken::Or), _) => {
                let _ = self.next().unwrap();
                res.push(first);
                res.push(second);
            }
            _ => res.push(first),
        }
        Ok(res)
    }

    /// This method won't check for subtrees, so the nth token tree may not be the nth sibling of the current tree.
    fn peek_n(&self, n: usize) -> Option<&'a TokenTree<S>> {
        self.inner.as_slice().get(n)
    }

    pub fn peek(&self) -> Option<TtElement<'a, S>> {
        match self.inner.as_slice().first()? {
            TokenTree::Token(token, spacing) => Some(TtElement::Token(token, *spacing)),
            &TokenTree::Delimited(ref span, spacing, delim, subtree) => {
                let nested_iter =
                    TtIter { inner: self.inner.as_slice()[1..][..subtree.usize_len()].iter() };
                Some(TtElement::Delimited(span, spacing, delim, subtree, nested_iter))
            }
        }
    }

    /// Equivalent to `peek().is_none()`, but a bit faster.
    pub fn is_empty(&self) -> bool {
        self.inner.len() == 0
    }

    pub fn next_span(&self) -> Option<S> {
        Some(self.inner.as_slice().first()?.first_span())
    }

    pub fn remaining(&self) -> TokenTreesView<'a, S> {
        TokenTreesView::new(self.inner.as_slice())
    }

    /// **Warning**: This advances `skip` **flat** token trees, subtrees account for children+1!
    pub fn flat_advance(&mut self, skip: usize) {
        self.inner = self.inner.as_slice()[skip..].iter();
    }

    pub fn savepoint(&self) -> TtIterSavepoint<'a, S> {
        TtIterSavepoint(self.inner.as_slice())
    }

    pub fn from_savepoint(&self, savepoint: TtIterSavepoint<'a, S>) -> TokenTreesView<'a, S> {
        let len = (self.inner.as_slice().as_ptr() as usize - savepoint.0.as_ptr() as usize)
            / size_of::<TokenTree<S>>();
        TokenTreesView::new(&savepoint.0[..len])
    }

    pub fn next_as_view(&mut self) -> Option<TokenTreesView<'a, S>> {
        let savepoint = self.savepoint();
        self.next()?;
        Some(self.from_savepoint(savepoint))
    }
}

pub enum TtElement<'a, S> {
    Token(&'a Token<S>, Spacing),
    Delimited(&'a DelimSpan<S>, DelimSpacing, Delimiter, Subtree, TtIter<'a, S>),
}

impl<S: Copy> TtElement<'_, S> {
    #[inline]
    pub fn first_span(&self) -> S {
        match self {
            TtElement::Token(it, _) => it.span,
            TtElement::Delimited(it, ..) => it.open,
        }
    }
}

impl<'a, S> Iterator for TtIter<'a, S> {
    type Item = TtElement<'a, S>;
    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.next()? {
            TokenTree::Token(token, spacing) => Some(TtElement::Token(token, *spacing)),
            &TokenTree::Delimited(ref span, spacing, delim, subtree) => {
                let nested_iter =
                    TtIter { inner: self.inner.as_slice()[..subtree.usize_len()].iter() };
                self.inner = self.inner.as_slice()[subtree.usize_len()..].iter();
                Some(TtElement::Delimited(span, spacing, delim, subtree, nested_iter))
            }
        }
    }
}
