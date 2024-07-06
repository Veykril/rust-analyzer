//! `tt` crate defines a `TokenTree` data structure: this is the interface (both
//! input and output) of macros. It closely mirrors `proc_macro` crate's
//! `TokenTree`.

// We want all children of a node to come after the node itself
// A child offset of a node is relative to the start of the current node
// The first child of a node follows the node itself immediately, recursively
// That is children are laid out pre-order

// a nice property of this is that if you take any subtree and all of its children, they all form a
// contiguous range with no garbage inbetween.

use std::{fmt, mem::transmute, ops};

use triomphe::Arc;

use crate::{DelimSpan, Delimiter, DelimiterKind, Leaf, Spacing, SubtreeBuilder};

pub fn flatten<S: Copy + PartialEq + std::fmt::Debug>(tt: &crate::Subtree<S>) -> Arc<Subtree<S>> {
    let mut buf = vec![];
    flatten_r(&mut buf, tt);
    assert!(!buf.is_empty());
    unsafe { transmute::<Arc<[_]>, _>(buf.into()) }
}

pub fn flatten_b<S: Copy + PartialEq + std::fmt::Debug>(tt: &crate::Subtree<S>) -> Box<Subtree<S>> {
    let mut buf = vec![];
    flatten_r(&mut buf, tt);
    assert!(!buf.is_empty());
    unsafe { transmute::<Box<[_]>, _>(buf.into()) }
}

fn flatten_r<S: Copy>(buf: &mut Vec<TokenTreeImpl<S>>, tt: &crate::Subtree<S>) {
    let start = buf.len();
    buf.push(TokenTreeImpl::Delimiter(tt.delimiter));
    // + 1 for the delimiter
    buf.resize(start + tt.token_trees.len() + 1, TokenTreeImpl::Subtree(0));
    for (idx, tt) in tt.token_trees.iter().enumerate() {
        // + 1 for the delimiter offset
        match tt {
            crate::TokenTree::Leaf(leaf) => {
                buf[start + 1 + idx] = TokenTreeImpl::Leaf(leaf.clone())
            }
            crate::TokenTree::Subtree(subtree) => {
                buf[start + 1 + idx] = TokenTreeImpl::Subtree(buf.len() - start);
                flatten_r(buf, subtree);
            }
        }
    }
}

pub fn unflatten<S: Clone>(arg: &Subtree<S>) -> crate::Subtree<S> {
    let mut builder = SubtreeBuilder { delimiter: arg.delimiter().clone(), token_trees: vec![] };
    for it in arg.iter_token_trees() {
        match it {
            TokenTree::Leaf(l) => builder.token_trees.push(crate::TokenTree::Leaf(l.clone())),
            TokenTree::Subtree(s) => {
                builder.token_trees.push(crate::TokenTree::Subtree(unflatten(s)))
            }
        }
    }
    builder.build()
}

impl<S: Clone> Clone for Box<Subtree<S>> {
    fn clone(&self) -> Self {
        Subtree::from_box_internal(
            unsafe { &*(self as *const Box<_> as *const Box<[TokenTreeImpl<S>]>) }
                .to_vec()
                .into_boxed_slice(),
        )
    }
}

impl<S: Copy> From<&Subtree<S>> for Arc<Subtree<S>> {
    fn from(value: &Subtree<S>) -> Self {
        unsafe { transmute(Arc::from_iter(value.0.iter().cloned())) }
    }
}
impl<S: Copy> From<&Subtree<S>> for Box<Subtree<S>> {
    fn from(value: &Subtree<S>) -> Self {
        Subtree::from_box_internal(Box::from(&value.0))
    }
}
impl<S: Copy> From<Box<Subtree<S>>> for Arc<Subtree<S>> {
    fn from(value: Box<Subtree<S>>) -> Self {
        unsafe {
            transmute(Arc::<[_]>::from(transmute::<_, Box<[TokenTreeImpl<S>]>>(value).into_vec()))
        }
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
    fn from_arc_internal(buf: Arc<[TokenTreeImpl<S>]>) -> Arc<Self> {
        unsafe { transmute(buf) }
    }
    pub fn empty(delim: Delimiter<S>) -> Arc<Self> {
        Self::new_internal_triomphe_arc(delim, [])
    }
    pub fn empty_triomphe_arc(delim: Delimiter<S>) -> Arc<Self> {
        Self::new_internal_triomphe_arc(delim, [])
    }
    pub fn new_boxed_leafs(
        delim: Delimiter<S>,
        content: impl IntoIterator<Item = Leaf<S>>,
    ) -> Box<Self> {
        let mut buf = vec![TokenTreeImpl::Delimiter(delim)];
        buf.extend(content.into_iter().map(TokenTreeImpl::Leaf));
        Self::from_box_internal(buf.into())
    }
    pub fn new_internal(
        delim: Delimiter<S>,
        content: impl IntoIterator<Item = TokenTreeImpl<S>>,
    ) -> Box<Self> {
        let mut buf = vec![TokenTreeImpl::Delimiter(delim)];
        buf.extend(content.into_iter());
        Self::from_box_internal(buf.into())
    }
    pub fn new_internal_triomphe_arc(
        delim: Delimiter<S>,
        content: impl IntoIterator<Item = TokenTreeImpl<S>>,
    ) -> Arc<Self> {
        let mut buf = vec![TokenTreeImpl::Delimiter(delim)];
        buf.extend(content.into_iter());
        Self::from_arc_internal(buf.into())
    }
    pub fn delimiter(&self) -> &Delimiter<S> {
        match &self.0 {
            [TokenTreeImpl::Delimiter(d), ..] => d,
            _ => unreachable!(),
        }
    }
    pub fn set_delimiter(&mut self, delim: Delimiter<S>) {
        match &mut self.0 {
            [TokenTreeImpl::Delimiter(d), ..] => *d = delim,
            _ => unreachable!(),
        }
    }
    pub fn set_delimiter_kind(&mut self, delim: DelimiterKind) {
        match &mut self.0 {
            [TokenTreeImpl::Delimiter(d), ..] => d.kind = delim,
            _ => unreachable!(),
        }
    }
    fn token_trees(&self) -> &[TokenTreeImpl<S>] {
        let end = self
            .0
            .iter()
            .skip(1)
            .position(|it| matches!(it, TokenTreeImpl::Delimiter(_)))
            .unwrap_or(self.0.len() - 1);
        &self.0[1..][..end]
    }
    pub(crate) fn len(&self) -> usize {
        self.token_trees().len()
    }
    pub fn iter_token_trees(&self) -> impl '_ + Iterator<Item = TokenTree<'_, S>> {
        self.token_trees().iter().map(|it| match it {
            TokenTreeImpl::Leaf(leaf) => TokenTree::Leaf(leaf),
            &TokenTreeImpl::Subtree(idx) => {
                TokenTree::Subtree(Subtree::from_slice_internal(&self.0[idx..]))
            }
            _ => unreachable!(),
        })
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TokenTree<'tree, S> {
    Leaf(&'tree Leaf<S>),
    Subtree(&'tree Subtree<S>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum TokenTreeImpl<S> {
    Delimiter(Delimiter<S>),
    Leaf(Leaf<S>),
    // Forward pointer relative to the containing subtree
    Subtree(usize),
}

fn print_debug_subtree<S: fmt::Debug>(
    f: &mut fmt::Formatter<'_>,
    subtree: &Subtree<S>,
    level: usize,
) -> fmt::Result {
    let align = "  ".repeat(level);

    let Delimiter { kind, open, close } = &subtree.delimiter();
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
            Leaf::Literal(lit) => {
                write!(f, "{}LITERAL {}", align, lit.text)?;
                fmt::Debug::fmt(&lit.span, f)?;
            }
            Leaf::Punct(punct) => {
                write!(
                    f,
                    "{}PUNCH   {} [{}] ",
                    align,
                    punct.char,
                    if punct.spacing == Spacing::Alone { "alone" } else { "joint" },
                )?;
                fmt::Debug::fmt(&punct.span, f)?;
            }
            Leaf::Ident(ident) => {
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

// #[cfg(test)]
// mod tests {
//     use expect_test::expect;

//     use crate::syntax_bridge::{self, dummy_test_span_utils};

//     use super::*;

//     #[test]
//     fn test_name() {
//         let tt = syntax_bridge::parse_to_token_tree_static_span(
//             dummy_test_span_utils::DUMMY,
//             "{a {} b c {d (e) }}",
//         )
//         .unwrap();
//         let tt_s = format!("{:?}", tt);
//         let tt_flat = flatten(&tt);
//         let tt_flat_s = format!("{:?}", tt_flat);
//         assert_eq!(tt_s, tt_flat_s);
//     }
// }

impl<S> fmt::Display for Subtree<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (l, r) = match self.delimiter().kind {
            DelimiterKind::Parenthesis => ("(", ")"),
            DelimiterKind::Brace => ("{", "}"),
            DelimiterKind::Bracket => ("[", "]"),
            DelimiterKind::Invisible => ("", ""),
        };
        f.write_str(l)?;
        let mut needs_space = false;
        for tt in self.iter_token_trees() {
            if needs_space {
                f.write_str(" ")?;
            }
            needs_space = true;
            match tt {
                TokenTree::Leaf(Leaf::Punct(p)) => {
                    needs_space = p.spacing == Spacing::Alone;
                    fmt::Display::fmt(p, f)?;
                }
                tt => fmt::Display::fmt(&tt, f)?,
            }
        }
        f.write_str(r)?;
        Ok(())
    }
}

impl<S> fmt::Display for TokenTree<'_, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenTree::Leaf(it) => fmt::Display::fmt(it, f),
            TokenTree::Subtree(it) => fmt::Display::fmt(it, f),
        }
    }
}
