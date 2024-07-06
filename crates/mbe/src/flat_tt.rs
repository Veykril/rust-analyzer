//! `tt` crate defines a `TokenTree` data structure: this is the interface (both
//! input and output) of macros. It closely mirrors `proc_macro` crate's
//! `TokenTree`.

// We want all children of a node to come after the node itself
// A child offset of a node is relative to the start of the current node
// The first child of a node follows the node itself immediately, recursively
// That is children are laid out pre-order

// a nice property of this is that if you take any subtree and all of its children, they all form a
// contiguous range with no garbage inbetween.

use std::{fmt, ops};

use tt::DelimiterKind;

pub mod iter;

pub fn flatten<S: Copy + PartialEq + std::fmt::Debug>(tt: &tt::Subtree<S>) -> Tree<S> {
    let mut buf = vec![];
    flatten_r(&mut buf, tt);
    debug_assert_eq!(buf.last(), Some(&TokenTreeImpl::End), "unfinished tree");
    Tree { buf }
}

fn flatten_r<S: Copy>(buf: &mut Vec<TokenTreeImpl<S>>, tt: &tt::Subtree<S>) {
    let start = buf.len();
    buf.push(TokenTreeImpl::Delimiter(tt.delimiter));
    // + 2 for the delimiter and the end token
    buf.resize(start + tt.token_trees.len() + 2, TokenTreeImpl::End);
    for (idx, tt) in tt.token_trees.iter().enumerate() {
        // + 1 for the delimiter offset
        match tt {
            tt::TokenTree::Leaf(leaf) => buf[start + 1 + idx] = TokenTreeImpl::Leaf(leaf.clone()),
            tt::TokenTree::Subtree(subtree) => {
                assert!(buf.len() - start > 2);
                buf[start + 1 + idx] = TokenTreeImpl::Subtree(buf.len() - start);
                flatten_r(buf, subtree);
            }
        }
    }
}

/// A TokenTree is followed by its children
/// [Delimiter, TokenTree, TokenTree, TokenTree, Delimiter, /*first child subtree */Delimiter, ... , Delimiter...]
// or for starters
/// [Delimiter, TokenTree, TokenTree, TokenTree, End, /*first child subtree */Delimiter, ... , End...]
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Tree<S> {
    buf: Vec<TokenTreeImpl<S>>,
}
impl<S> Tree<S> {
    pub(crate) fn empty(call_site: tt::Delimiter<S>) -> Tree<S> {
        todo!()
    }
    pub(crate) fn empty(call_site: tt::Delimiter<S>) -> Tree<S> {
        todo!()
    }

    pub(crate) fn subtree_or_wrap(it: TokenTreeOwned<S>, delim_span: tt::DelimSpan<S>) -> Tree<S> {
        match it {
            TokenTreeOwned::Leaf(it) => todo!(),
            TokenTreeOwned::Subtree(it) => Tree { buf: todo!() },
        }
    }

    pub(crate) fn from_tts(
        call_site: tt::Delimiter<S>,
        tts: impl IntoIterator<Item = TokenTreeOwned<S>>,
    ) -> Tree<S> {
        todo!()
    }
}

impl<S: fmt::Debug> fmt::Debug for Tree<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        print_debug_subtree(f, self, 0)
    }
}

impl<S> ops::Deref for Tree<S> {
    type Target = Subtree<S>;

    fn deref(&self) -> &Self::Target {
        Subtree::from_slice_internal(&self.buf)
    }
}

#[derive(PartialEq, Eq, Hash)]
pub struct SubtreeView<'tree, S>(&'tree Subtree, ChildRange);

impl<'tree, S> SubtreeView<'tree, S> {
    pub fn slice_end(&self, idx: usize) -> Self {
        assert!(idx <= self.1.end);
        SubtreeView(self.0, ChildRange { start: self.1.start, end: idx })
    }
}

#[derive(PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Subtree<S>([TokenTreeImpl<S>]);

impl<S: fmt::Debug> fmt::Debug for Subtree<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        print_debug_subtree(f, self, 0)
    }
}

impl<S> Subtree<S> {
    fn from_slice_internal(buf: &[TokenTreeImpl<S>]) -> &Self {
        unsafe { &*(buf as *const _ as *const Subtree<S>) }
    }
    fn from_box_internal(buf: Box<[TokenTreeImpl<S>]>) -> Box<Self> {
        unsafe { Box::from_raw(Box::into_raw(buf) as *mut Subtree<S>) }
    }
    pub fn new_boxed_leafs(
        delim: tt::Delimiter<S>,
        content: impl IntoIterator<Item = tt::Leaf<S>>,
    ) -> Box<Self> {
        let mut buf = vec![TokenTreeImpl::Delimiter(delim)];
        buf.extend(content.into_iter().map(TokenTreeImpl::Leaf).collect());
        buf.push(TokenTreeImpl::End);
        Self::from_box_internal(buf.into())
    }
    pub fn new_internal(
        delim: tt::Delimiter<S>,
        content: impl IntoIterator<Item = TokenTreeImpl<S>>,
    ) -> Box<Self> {
        let mut buf = vec![TokenTreeImpl::Delimiter(delim)];
        buf.extend(content.into_iter().collect());
        buf.push(TokenTreeImpl::End);
        Self::from_box_internal(buf.into())
    }
    pub fn delimiter(&self) -> &tt::Delimiter<S> {
        match &self.0 {
            [TokenTreeImpl::Delimiter(d), ..] => d,
            _ => unreachable!(),
        }
    }
    pub fn set_delimiter(&mut self, delim: tt::Delimiter<S>) {
        match &mut self.0 {
            [TokenTreeImpl::Delimiter(d), ..] => *d = delim,
            _ => unreachable!(),
        }
    }
    fn token_trees(&self) -> &[TokenTreeImpl<S>] {
        let end = self.0.iter().position(|it| matches!(it, TokenTreeImpl::End)).unwrap();
        &self.0[1..end]
    }
    pub(crate) fn len(&self) -> usize {
        self.token_trees().len()
    }
    pub fn iter_token_trees(&self) -> impl '_ + Iterator<Item = TokenTree<'_, S>> {
        self.token_trees().iter().map(|it| match it {
            TokenTreeImpl::Leaf(leaf) => TokenTree::Leaf(leaf),
            &TokenTreeImpl::Subtree(idx) => {
                TokenTree::Subtree(&Subtree::from_slice_internal(&self.0[idx..]))
            }
            _ => unreachable!(),
        })
    }

    pub(crate) fn empty(delim: tt::Delimiter<S>) -> Box<Subtree<S>> {
        todo!()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TokenTreeOwned<S> {
    Leaf(tt::Leaf<S>),
    Subtree(Box<Subtree<S>>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TokenTree<'tree, S> {
    Leaf(&'tree tt::Leaf<S>),
    Subtree(&'tree Subtree<S>),
}

impl<S: Clone> ToOwned for TokenTree<'_, S> {
    type Owned = TokenTreeOwned<S>;

    fn to_owned(&self) -> Self::Owned {
        match *self {
            TokenTree::Leaf(leaf) => TokenTreeOwned::Leaf(leaf.clone()),
            TokenTree::Subtree(subtree) => TokenTreeOwned::Subtree(subtree.to_owned()),
        }
    }
}
impl<S> ToOwned for Subtree<S> {
    type Owned = Box<Subtree<S>>;

    fn to_owned(&self) -> Self::Owned {
        let buf = self.0.to_vec();
        Self::from_box_internal(buf.into())
    }
}

/// A range that restricts the children of a subtree to a smaller view
pub(crate) struct ChildRange {
    pub(crate) start: usize,
    pub(crate) end: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum TokenTreeImpl<S> {
    Delimiter(tt::Delimiter<S>),
    Leaf(tt::Leaf<S>),
    // Forward pointer relative to the containing subtree
    Subtree(usize),
    // do we need this? Delimiter already signals a node start, so it can double as the end as well
    End,
}

fn print_debug_subtree<S: fmt::Debug>(
    f: &mut fmt::Formatter<'_>,
    subtree: &Subtree<S>,
    level: usize,
) -> fmt::Result {
    let align = "  ".repeat(level);

    let tt::Delimiter { kind, open, close } = &subtree.delimiter();
    let delim = match kind {
        DelimiterKind::Invisible => "$$",
        DelimiterKind::Parenthesis => "()",
        DelimiterKind::Brace => "{}",
        DelimiterKind::Bracket => "[]",
    };

    write!(f, "{align}SUBTREE {delim} ",)?;
    fmt::Debug::fmt(&open, f)?;
    write!(f, " ")?;
    fmt::Debug::fmt(&close, f)?;
    if !subtree.token_trees().is_empty() {
        writeln!(f)?;
        for (idx, child) in subtree.iter_token_trees().enumerate() {
            print_debug_token(f, child, level + 1)?;
            if idx != subtree.token_trees().len() - 1 {
                writeln!(f)?;
            }
        }
    }

    Ok(())
}

fn print_debug_token<S: fmt::Debug>(
    f: &mut fmt::Formatter<'_>,
    tkn: TokenTree<'_, S>,
    level: usize,
) -> fmt::Result {
    let align = "  ".repeat(level);

    match tkn {
        TokenTree::Leaf(leaf) => match leaf {
            tt::Leaf::Literal(lit) => {
                write!(f, "{}LITERAL {}", align, lit.text)?;
                fmt::Debug::fmt(&lit.span, f)?;
            }
            tt::Leaf::Punct(punct) => {
                write!(
                    f,
                    "{}PUNCH   {} [{}] ",
                    align,
                    punct.char,
                    if punct.spacing == tt::Spacing::Alone { "alone" } else { "joint" },
                )?;
                fmt::Debug::fmt(&punct.span, f)?;
            }
            tt::Leaf::Ident(ident) => {
                write!(f, "{}IDENT   {} ", align, ident.text)?;
                fmt::Debug::fmt(&ident.span, f)?;
            }
        },
        TokenTree::Subtree(subtree) => {
            print_debug_subtree(f, subtree, level)?;
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use expect_test::expect;

    use crate::syntax_bridge::{self, dummy_test_span_utils};

    use super::*;

    #[test]
    fn test_name() {
        let tt = syntax_bridge::parse_to_token_tree_static_span(
            dummy_test_span_utils::DUMMY,
            "{a {} b c {d (e) }}",
        )
        .unwrap();
        let tt_s = format!("{:?}", tt);
        let tt_flat = flatten(&tt);
        let tt_flat_s = format!("{:?}", tt_flat);
        assert_eq!(tt_s, tt_flat_s);
    }
}
