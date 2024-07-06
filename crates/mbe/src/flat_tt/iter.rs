//! A "Parser" structure for token trees. We use this when parsing a declarative
//! macro definition into a list of patterns and templates.

use std::mem;

use arrayvec::ArrayVec;

use crate::flat_tt::{ChildRange, Subtree, SubtreeView, TokenTree, TokenTreeImpl};
use tt::{Ident, Leaf, Punct, Spacing};

#[derive(Debug, Clone)]
pub struct TtIter<'a, S> {
    inner: &'a Subtree,
    idx: usize,
    max: usize,
}

impl<'a, S: Copy> TtIter<'a, S> {
    pub fn new(subtree: &'a Subtree<S>) -> TtIter<'a, S> {
        // max = token tree count + idx 1 offset
        // idx 1 to skip delims
        TtIter { inner: subtree, idx: 1, max: subtree.len() + 1 }
    }

    pub fn expect_char(&mut self, char: char) -> Result<&'a tt::Leaf<S>, ()> {
        match self.next() {
            Some(TokenTree::Leaf(l @ &Leaf::Punct(Punct { char: c, .. }))) if c == char => Ok(l),
            _ => Err(()),
        }
    }

    pub fn expect_any_char(&mut self, chars: &[char]) -> Result<(), ()> {
        match self.next() {
            Some(TokenTree::Leaf(Leaf::Punct(Punct { char: c, .. }))) if chars.contains(c) => {
                Ok(())
            }
            _ => Err(()),
        }
    }

    pub fn expect_subtree(&mut self) -> Result<&'a Subtree<S>, ()> {
        match self.next() {
            Some(TokenTree::Subtree(it)) => Ok(it),
            _ => Err(()),
        }
    }

    pub fn expect_leaf(&mut self) -> Result<&'a Leaf<S>, ()> {
        match self.next() {
            Some(TokenTree::Leaf(it)) => Ok(it),
            _ => Err(()),
        }
    }

    pub fn expect_dollar(&mut self) -> Result<(), ()> {
        match self.expect_leaf()? {
            Leaf::Punct(Punct { char: '$', .. }) => Ok(()),
            _ => Err(()),
        }
    }

    pub fn expect_ident(&mut self) -> Result<&'a Ident<S>, ()> {
        match self.expect_leaf()? {
            Leaf::Ident(it) if it.text != "_" => Ok(it),
            _ => Err(()),
        }
    }

    pub fn expect_ident_or_underscore(&mut self) -> Result<&'a Ident<S>, ()> {
        match self.expect_leaf()? {
            Leaf::Ident(it) => Ok(it),
            _ => Err(()),
        }
    }

    pub fn expect_literal(&mut self) -> Result<&'a Leaf<S>, ()> {
        let it = self.expect_leaf()?;
        match it {
            Leaf::Literal(_) => Ok(it),
            Leaf::Ident(ident) if ident.text == "true" || ident.text == "false" => Ok(it),
            _ => Err(()),
        }
    }

    pub fn expect_single_punct(&mut self) -> Result<&'a Punct<S>, ()> {
        match self.expect_leaf()? {
            Leaf::Punct(it) => Ok(it),
            _ => Err(()),
        }
    }

    /// Returns consecutive `Punct`s that can be glued together.
    ///
    /// This method currently may return a single quotation, which is part of lifetime ident and
    /// conceptually not a punct in the context of mbe. Callers should handle this.
    pub fn expect_glued_punct(&mut self) -> Result<ArrayVec<Punct<S>, 3>, ()> {
        let TokenTree::Leaf(&Leaf::Punct(first)) = self.next().ok_or(())?.clone() else {
            return Err(());
        };

        let mut res = ArrayVec::new();
        if first.spacing == Spacing::Alone {
            res.push(first);
            return Ok(res);
        }

        let (second, third) = match (self.peek_n(0), self.peek_n(1)) {
            (Some(TokenTree::Leaf(Leaf::Punct(p2))), Some(TokenTree::Leaf(Leaf::Punct(p3))))
                if p2.spacing == Spacing::Joint =>
            {
                (p2, Some(p3))
            }
            (Some(TokenTree::Leaf(Leaf::Punct(p2))), _) => (p2, None),
            _ => {
                res.push(first);
                return Ok(res);
            }
        };

        match (first.char, second.char, third.map(|it| it.char)) {
            ('.', '.', Some('.' | '=')) | ('<', '<', Some('=')) | ('>', '>', Some('=')) => {
                let _ = self.next().unwrap();
                let _ = self.next().unwrap();
                res.push(first);
                res.push(*second);
                res.push(*third.unwrap());
            }
            ('-' | '!' | '*' | '/' | '&' | '%' | '^' | '+' | '<' | '=' | '>' | '|', '=', _)
            | ('-' | '=' | '>', '>', _)
            | ('<', '-', _)
            | (':', ':', _)
            | ('.', '.', _)
            | ('&', '&', _)
            | ('<', '<', _)
            | ('|', '|', _) => {
                let _ = self.next().unwrap();
                res.push(first);
                res.push(*second);
            }
            _ => res.push(first),
        }
        Ok(res)
    }

    pub fn peek_n(&self, n: usize) -> Option<TokenTree<'a, S>> {
        self.inner.0.get(self.idx + n).map(|it| match it {
            TokenTreeImpl::Leaf(leaf) => TokenTree::Leaf(leaf),
            TokenTreeImpl::Subtree(idx) => {
                TokenTree::Subtree(&Subtree::from_slice_internal(&self.inner[*idx..]))
            }
            _ => unreachable!(),
        })
    }

    pub fn subtree_view(&self) -> SubtreeView<'a, S> {
        SubtreeView(&self.inner, ChildRange { start: self.idx, end: self.inner.len() })
    }

    pub(crate) fn current(&self) -> usize {
        self.idx
    }
}

impl<'a, S> Iterator for TtIter<'a, S> {
    type Item = TokenTree<'a, S>;
    fn next(&mut self) -> Option<Self::Item> {
        if self.idx >= self.max {
            return None;
        }
        let idx = mem::replace(&mut self.idx, self.idx + 1);
        self.inner.0.get(idx).map(|it| match it {
            TokenTreeImpl::Leaf(leaf) => TokenTree::Leaf(leaf),
            TokenTreeImpl::Subtree(idx) => {
                TokenTree::Subtree(&Subtree::from_slice_internal(&self.inner[*idx..]))
            }
            _ => unreachable!(),
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.inner.0.len() - self.idx, Some(self.inner.0.len() - self.idx))
    }
}

impl<S> std::iter::ExactSizeIterator for TtIter<'_, S> {}
