//! Defines database & queries for macro expansion.

use base_db::{Crate, RootQueryDb};
use either::Either;
use mbe::MatchedArmIndex;
use rustc_hash::FxHashSet;
use span::{AstIdMap, Edition, Span, SyntaxContext};
use syntax::{AstNode, Parse, SyntaxElement, SyntaxError, SyntaxNode, SyntaxToken, T, ast};
use syntax_bridge::{DocCommentDesugarMode, syntax_node_to_token_tree};
use triomphe::Arc;

use crate::{
    AstId, BuiltinAttrExpander, BuiltinDeriveExpander, BuiltinFnLikeExpander, EagerCallInfo,
    EagerExpander, EditionedFileId, ExpandError, ExpandResult, ExpandTo, HirFileId, InFile,
    MacroCallId, MacroCallKind, MacroExpander,
    attrs::{AttrId, AttrInput, RawAttrs, collect_attrs},
    builtin::pseudo_derive_attr_expansion,
    cfg_process,
    declarative::DeclarativeMacroExpander,
    fixup::{self, SyntaxFixupUndoInfo},
    hygiene::{span_with_call_site_ctxt, span_with_def_site_ctxt, span_with_mixed_site_ctxt},
    proc_macro::{CrateProcMacros, CustomProcMacroExpander, ProcMacros},
    span_map::{ExpansionSpanMap, RealSpanMap, SpanMap, SpanMapRef},
    tt,
};
/// This is just to ensure the types of smart_macro_arg and macro_arg are the same
type MacroArgResult = (Arc<tt::TopSubtree>, SyntaxFixupUndoInfo, Span);
/// Total limit on the number of tokens produced by any macro invocation.
///
/// If an invocation produces more tokens than this limit, it will not be stored in the database and
/// an error will be emitted.
///
/// Actual max for `analysis-stats .` at some point: 30672.
const TOKEN_LIMIT: usize = 2_097_152;

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum TokenExpander {
    /// Old-style `macro_rules` or the new macros 2.0
    DeclarativeMacro(Arc<DeclarativeMacroExpander>),
    /// Stuff like `line!` and `file!`.
    BuiltIn(BuiltinFnLikeExpander),
    /// Built-in eagerly expanded fn-like macros (`include!`, `concat!`, etc.)
    BuiltInEager(EagerExpander),
    /// `global_allocator` and such.
    BuiltInAttr(BuiltinAttrExpander),
    /// `derive(Copy)` and such.
    BuiltInDerive(BuiltinDeriveExpander),
    /// The thing we love the most here in rust-analyzer -- procedural macros.
    ProcMacro(CustomProcMacroExpander),
}

pub trait DepInjectDatabase {
    fn macro_call_call_crate(&self, macro_call: MacroCallId) -> Crate;
    fn macro_call_def_crate(&self, macro_call: MacroCallId) -> Crate;
    fn macro_call_def_file_id(&self, macro_call: MacroCallId) -> AstId<ast::Item>;
    fn macro_call_kind(&self, macro_call: MacroCallId) -> MacroCallKind;
    fn macro_call_expander(&self, macro_call: MacroCallId) -> MacroExpander;
    fn proc_macro_call_expander(
        &self,
        macro_call: MacroCallId,
    ) -> Option<(CustomProcMacroExpander, AstId<ast::Fn>)>;
    fn macro_call_ctx(&self, macro_call: MacroCallId) -> SyntaxContext;
    fn macro_call_local_inner(&self, macro_call: MacroCallId) -> bool;
    fn to_node(&self, macro_call: MacroCallId) -> InFile<SyntaxNode>;
}

#[query_group::query_group]
pub trait ExpandDatabase: RootQueryDb + DepInjectDatabase {
    /// The proc macros. Do not use this! Use `proc_macros_for_crate()` instead.
    #[salsa::input]
    fn proc_macros(&self) -> Arc<ProcMacros>;

    /// Incrementality query to prevent queries from directly depending on `ExpandDatabase::proc_macros`.
    #[salsa::invoke(crate::proc_macro::proc_macros_for_crate)]
    fn proc_macros_for_crate(&self, krate: Crate) -> Option<Arc<CrateProcMacros>>;

    #[salsa::invoke(ast_id_map)]
    #[salsa::lru(1024)]
    fn ast_id_map(&self, file_id: HirFileId) -> Arc<AstIdMap>;

    #[salsa::transparent]
    fn parse_or_expand(&self, file_id: HirFileId) -> SyntaxNode;

    /// Implementation for the macro case.
    #[salsa::lru(512)]
    fn parse_macro_expansion(
        &self,
        macro_file: MacroCallId,
    ) -> ExpandResult<(Parse<SyntaxNode>, Arc<ExpansionSpanMap>)>;

    #[salsa::transparent]
    #[salsa::invoke(SpanMap::new)]
    fn span_map(&self, file_id: HirFileId) -> SpanMap;

    #[salsa::transparent]
    #[salsa::invoke(crate::span_map::expansion_span_map)]
    fn expansion_span_map(&self, file_id: MacroCallId) -> Arc<ExpansionSpanMap>;
    #[salsa::invoke(crate::span_map::real_span_map)]
    fn real_span_map(&self, file_id: EditionedFileId) -> Arc<RealSpanMap>;

    /// Lowers syntactic macro call to a token tree representation. That's a firewall
    /// query, only typing in the macro call itself changes the returned
    /// subtree.
    #[deprecated = "calling this is incorrect, call `macro_arg_considering_derives` instead"]
    #[salsa::invoke(macro_arg)]
    fn macro_arg(&self, id: MacroCallId) -> MacroArgResult;

    #[salsa::transparent]
    fn macro_arg_considering_derives(
        &self,
        id: MacroCallId,
        kind: &MacroCallKind,
    ) -> MacroArgResult;

    // /// Fetches the expander for this macro.
    // #[salsa::transparent]
    // #[salsa::invoke(TokenExpander::macro_expander)]
    // fn macro_expander(&self, id: MacroDefId) -> TokenExpander;

    /// Fetches (and compiles) the expander of this decl macro.
    #[salsa::invoke(DeclarativeMacroExpander::expander)]
    fn decl_macro_expander(
        &self,
        def_crate: Crate,
        id: AstId<ast::Macro>,
    ) -> Arc<DeclarativeMacroExpander>;

    /// Special case of the previous query for procedural macros. We can't LRU
    /// proc macros, since they are not deterministic in general, and
    /// non-determinism breaks salsa in a very, very, very bad way.
    /// @edwin0cheng heroically debugged this once! See #4315 for details
    #[salsa::invoke(expand_proc_macro)]
    fn expand_proc_macro(&self, call: MacroCallId) -> ExpandResult<Arc<tt::TopSubtree>>;
    /// Retrieves the span to be used for a proc-macro expansions spans.
    /// This is a firewall query as it requires parsing the file, which we don't want proc-macros to
    /// directly depend on as that would cause to frequent invalidations, mainly because of the
    /// parse queries being LRU cached. If they weren't the invalidations would only happen if the
    /// user wrote in the file that defines the proc-macro.
    #[salsa::invoke_interned(proc_macro_span)]
    fn proc_macro_span(&self, fun: AstId<ast::Fn>) -> Span;

    /// Firewall query that returns the errors from the `parse_macro_expansion` query.
    #[salsa::invoke(parse_macro_expansion_error)]
    fn parse_macro_expansion_error(
        &self,
        macro_call: MacroCallId,
    ) -> Option<Arc<ExpandResult<Arc<[SyntaxError]>>>>;

    #[salsa::transparent]
    fn syntax_context(&self, file: HirFileId, edition: Edition) -> SyntaxContext;
}

#[salsa_macros::interned(no_lifetime, id = span::SyntaxContext)]
pub struct SyntaxContextWrapper {
    pub data: SyntaxContext,
}

fn syntax_context(db: &dyn ExpandDatabase, file: HirFileId, edition: Edition) -> SyntaxContext {
    match file {
        HirFileId::FileId(_) => SyntaxContext::root(edition),
        HirFileId::MacroFile(m) => {
            let kind = db.macro_call_kind(m);
            db.macro_arg_considering_derives(m, &kind).2.ctx
        }
    }
}

/// This expands the given macro call, but with different arguments. This is
/// used for completion, where we want to see what 'would happen' if we insert a
/// token. The `token_to_map` mapped down into the expansion, with the mapped
/// token(s) returned with their priority.
pub fn expand_speculative(
    db: &dyn ExpandDatabase,
    actual_macro_call: MacroCallId,
    speculative_args: &SyntaxNode,
    token_to_map: SyntaxToken,
) -> Option<(SyntaxNode, Vec<(SyntaxToken, u8)>)> {
    let kind = db.macro_call_kind(actual_macro_call);
    let def_kind = db.macro_call_expander(actual_macro_call);
    let def = db.macro_call_expander(actual_macro_call);
    let def_crate = db.macro_call_def_crate(actual_macro_call);
    let call_crate = db.macro_call_call_crate(actual_macro_call);
    let (_, _, span) = db.macro_arg_considering_derives(actual_macro_call, &kind);

    let span_map = RealSpanMap::absolute(span.anchor.file_id);
    let span_map = SpanMapRef::RealSpanMap(&span_map);

    // Build the subtree and token mapping for the speculative args
    let (mut tt, undo_info) = match kind {
        MacroCallKind::FnLike { .. } => (
            syntax_bridge::syntax_node_to_token_tree(
                speculative_args,
                span_map,
                span,
                if def.is_proc_macro() {
                    DocCommentDesugarMode::ProcMacro
                } else {
                    DocCommentDesugarMode::Mbe
                },
            ),
            SyntaxFixupUndoInfo::NONE,
        ),
        MacroCallKind::Attr { .. } if def.is_attribute_derive() => (
            syntax_bridge::syntax_node_to_token_tree(
                speculative_args,
                span_map,
                span,
                DocCommentDesugarMode::ProcMacro,
            ),
            SyntaxFixupUndoInfo::NONE,
        ),
        MacroCallKind::Derive { derive_attr_index: index, .. }
        | MacroCallKind::Attr { invoc_attr_index: index, .. } => {
            let censor = if let MacroCallKind::Derive { .. } = kind {
                censor_derive_input(index, &ast::Adt::cast(speculative_args.clone())?)
            } else {
                attr_source(index, &ast::Item::cast(speculative_args.clone())?)
                    .into_iter()
                    .map(|it| it.syntax().clone().into())
                    .collect()
            };

            let censor_cfg = cfg_process::process_cfg_attrs(
                db,
                speculative_args,
                &def,
                db.macro_call_call_crate(actual_macro_call),
            )
            .unwrap_or_default();
            let mut fixups = fixup::fixup_syntax(
                span_map,
                speculative_args,
                span,
                DocCommentDesugarMode::ProcMacro,
            );
            fixups.append.retain(|it, _| match it {
                syntax::NodeOrToken::Token(_) => true,
                it => !censor.contains(it) && !censor_cfg.contains(it),
            });
            fixups.remove.extend(censor);
            fixups.remove.extend(censor_cfg);

            (
                syntax_bridge::syntax_node_to_token_tree_modified(
                    speculative_args,
                    span_map,
                    fixups.append,
                    fixups.remove,
                    span,
                    DocCommentDesugarMode::ProcMacro,
                ),
                fixups.undo_info,
            )
        }
    };

    let attr_arg = match kind {
        MacroCallKind::Attr { invoc_attr_index, .. } => {
            if def.is_attribute_derive() {
                // for pseudo-derive expansion we actually pass the attribute itself only
                ast::Attr::cast(speculative_args.clone()).and_then(|attr| attr.token_tree()).map(
                    |token_tree| {
                        let mut tree = syntax_node_to_token_tree(
                            token_tree.syntax(),
                            span_map,
                            span,
                            DocCommentDesugarMode::ProcMacro,
                        );
                        *tree.top_subtree_delimiter_mut() = tt::Delimiter::invisible_spanned(span);
                        tree
                    },
                )
            } else {
                // Attributes may have an input token tree, build the subtree and map for this as well
                // then try finding a token id for our token if it is inside this input subtree.
                let item = ast::Item::cast(speculative_args.clone())?;
                let attrs = RawAttrs::new_expanded(db, &item, span_map, call_crate.cfg_options(db));
                attrs.iter().find(|attr| attr.id == invoc_attr_index).and_then(|attr| {
                    match attr.input.as_deref()? {
                        AttrInput::TokenTree(tt) => {
                            let mut attr_arg = tt.clone();
                            attr_arg.top_subtree_delimiter_mut().kind =
                                tt::DelimiterKind::Invisible;
                            Some(attr_arg)
                        }
                        AttrInput::Literal(_) => None,
                    }
                })
            }
        }
        _ => None,
    };

    // Do the actual expansion, we need to directly expand the proc macro due to the attribute args
    // Otherwise the expand query will fetch the non speculative attribute args and pass those instead.
    let mut speculative_expansion = match def_kind {
        MacroExpander::ProcMacro(expander, _) => {
            let span =
                db.proc_macro_span(db.proc_macro_call_expander(actual_macro_call).unwrap().1);
            *tt.top_subtree_delimiter_mut() = tt::Delimiter::invisible_spanned(span);
            expander.expand(
                db,
                def_crate,
                call_crate,
                &tt,
                attr_arg.as_ref(),
                span_with_def_site_ctxt(db, span, actual_macro_call, def_crate.data(db).edition),
                span_with_call_site_ctxt(db, span, actual_macro_call, call_crate.data(db).edition),
                span_with_mixed_site_ctxt(db, span, actual_macro_call, def_crate.data(db).edition),
            )
        }
        MacroExpander::BuiltInAttr(it) if it.is_derive() => {
            pseudo_derive_attr_expansion(&tt, attr_arg.as_ref()?, span)
        }
        MacroExpander::Declarative(it) => {
            it.expand_unhygienic(tt, span, def_crate.data(db).edition)
        }
        MacroExpander::BuiltIn(it) => {
            it.expand(db, actual_macro_call, &tt, span).map_err(Into::into)
        }
        MacroExpander::BuiltInDerive(it) => {
            it.expand(db, actual_macro_call, &tt, span).map_err(Into::into)
        }
        MacroExpander::BuiltInEager(it) => {
            it.expand(db, actual_macro_call, &tt, span).map_err(Into::into)
        }
        MacroExpander::BuiltInAttr(it) => it.expand(db, actual_macro_call, &tt, span),
    };

    let expand_to = kind.expand_to();

    fixup::reverse_fixups(&mut speculative_expansion.value, &undo_info);
    let (node, rev_tmap) = token_tree_to_syntax_node(
        db,
        &speculative_expansion.value,
        expand_to,
        def_crate.data(db).edition,
    );

    let syntax_node = node.syntax_node();
    let token = rev_tmap
        .ranges_with_span(span_map.span_for_range(token_to_map.text_range()))
        .filter_map(|(range, ctx)| syntax_node.covering_element(range).into_token().zip(Some(ctx)))
        .map(|(t, ctx)| {
            // prefer tokens of the same kind and text, as well as non opaque marked ones
            // Note the inversion of the score here, as we want to prefer the first token in case
            // of all tokens having the same score
            let ranking = ctx.is_opaque(db) as u8
                + 2 * (t.kind() != token_to_map.kind()) as u8
                + 4 * ((t.text() != token_to_map.text()) as u8);
            (t, ranking)
        })
        .collect();
    Some((node.syntax_node(), token))
}

fn ast_id_map(db: &dyn ExpandDatabase, file_id: HirFileId) -> triomphe::Arc<AstIdMap> {
    triomphe::Arc::new(AstIdMap::from_source(&db.parse_or_expand(file_id)))
}

/// Main public API -- parses a hir file, not caring whether it's a real
/// file or a macro expansion.
fn parse_or_expand(db: &dyn ExpandDatabase, file_id: HirFileId) -> SyntaxNode {
    match file_id {
        HirFileId::FileId(file_id) => db.parse(file_id).syntax_node(),
        HirFileId::MacroFile(macro_file) => {
            db.parse_macro_expansion(macro_file).value.0.syntax_node()
        }
    }
}

// FIXME: We should verify that the parsed node is one of the many macro node variants we expect
// instead of having it be untyped
fn parse_macro_expansion(
    db: &dyn ExpandDatabase,
    macro_file: MacroCallId,
) -> ExpandResult<(Parse<SyntaxNode>, Arc<ExpansionSpanMap>)> {
    let _p = tracing::info_span!("parse_macro_expansion").entered();
    let def_crate = db.macro_call_def_crate(macro_file);
    let def_edition = def_crate.data(db).edition;
    let call_kind = db.macro_call_kind(macro_file);
    let expand_to = call_kind.expand_to();
    let def_kind = db.macro_call_expander(macro_file);
    let mbe::ValueResult { value: (tt, matched_arm), err } =
        macro_expand(db, macro_file, &def_kind, &call_kind);

    let (parse, mut rev_token_map) = token_tree_to_syntax_node(
        db,
        match &tt {
            CowArc::Arc(it) => it,
            CowArc::Owned(it) => it,
        },
        expand_to,
        def_edition,
    );
    rev_token_map.matched_arm = matched_arm;

    ExpandResult { value: (parse, Arc::new(rev_token_map)), err }
}

fn parse_macro_expansion_error(
    db: &dyn ExpandDatabase,
    macro_call_id: MacroCallId,
) -> Option<Arc<ExpandResult<Arc<[SyntaxError]>>>> {
    let e: ExpandResult<Arc<[SyntaxError]>> =
        db.parse_macro_expansion(macro_call_id).map(|it| Arc::from(it.0.errors()));
    if e.value.is_empty() && e.err.is_none() { None } else { Some(Arc::new(e)) }
}

pub(crate) fn parse_with_map(
    db: &dyn ExpandDatabase,
    file_id: HirFileId,
) -> (Parse<SyntaxNode>, SpanMap) {
    match file_id {
        HirFileId::FileId(file_id) => {
            (db.parse(file_id).to_syntax(), SpanMap::RealSpanMap(db.real_span_map(file_id)))
        }
        HirFileId::MacroFile(macro_file) => {
            let (parse, map) = db.parse_macro_expansion(macro_file).value;
            (parse, SpanMap::ExpansionSpanMap(map))
        }
    }
}

/// This resolves the [MacroCallId] to check if it is a derive macro if so get the [macro_arg] for the derive.
/// Other wise return the [macro_arg] for the macro_call_id.
///
/// This is not connected to the database so it does not cached the result. However, the inner [macro_arg] query is
#[allow(deprecated)] // we are macro_arg_considering_derives
fn macro_arg_considering_derives(
    db: &dyn ExpandDatabase,
    id: MacroCallId,
    kind: &MacroCallKind,
) -> MacroArgResult {
    match kind {
        // Get the macro arg for the derive macro
        MacroCallKind::Derive { derive_macro_id, .. } => db.macro_arg(*derive_macro_id),
        // Normal macro arg
        _ => db.macro_arg(id),
    }
}

fn macro_arg(db: &dyn ExpandDatabase, id: MacroCallId) -> MacroArgResult {
    let def_kind = db.macro_call_expander(id);
    let call_kind = db.macro_call_kind(id);

    if let (MacroExpander::BuiltInEager(..), MacroCallKind::FnLike { eager: Some(eager), .. }) =
        (&def_kind, &call_kind)
    {
        return (eager.arg.clone(), SyntaxFixupUndoInfo::NONE, eager.span);
    }

    let (parse, map) = parse_with_map(db, call_kind.file_id());
    let root = parse.syntax_node();

    let (censor, item_node, span) = match call_kind {
        MacroCallKind::FnLike { ast_id, .. } => {
            let node = &ast_id.to_ptr(db).to_node(&root);
            let path_range = node
                .path()
                .map_or_else(|| node.syntax().text_range(), |path| path.syntax().text_range());
            let span = map.span_for_range(path_range);

            let dummy_tt = |kind| {
                (
                    Arc::new(tt::TopSubtree::from_token_trees(
                        tt::Delimiter { open: span, close: span, kind },
                        tt::TokenTreesView::new(&[]),
                    )),
                    SyntaxFixupUndoInfo::default(),
                    span,
                )
            };

            let Some(tt) = node.token_tree() else {
                return dummy_tt(tt::DelimiterKind::Invisible);
            };
            let first = tt.left_delimiter_token().map(|it| it.kind()).unwrap_or(T!['(']);
            let last = tt.right_delimiter_token().map(|it| it.kind()).unwrap_or(T![.]);

            let mismatched_delimiters = !matches!(
                (first, last),
                (T!['('], T![')']) | (T!['['], T![']']) | (T!['{'], T!['}'])
            );
            if mismatched_delimiters {
                // Don't expand malformed (unbalanced) macro invocations. This is
                // less than ideal, but trying to expand unbalanced  macro calls
                // sometimes produces pathological, deeply nested code which breaks
                // all kinds of things.
                //
                // So instead, we'll return an empty subtree here
                cov_mark::hit!(issue9358_bad_macro_stack_overflow);

                let kind = match first {
                    _ if def_kind.is_proc_macro() => tt::DelimiterKind::Invisible,
                    T!['('] => tt::DelimiterKind::Parenthesis,
                    T!['['] => tt::DelimiterKind::Bracket,
                    T!['{'] => tt::DelimiterKind::Brace,
                    _ => tt::DelimiterKind::Invisible,
                };
                return dummy_tt(kind);
            }

            let mut tt = syntax_bridge::syntax_node_to_token_tree(
                tt.syntax(),
                map.as_ref(),
                span,
                if def_kind.is_proc_macro() {
                    DocCommentDesugarMode::ProcMacro
                } else {
                    DocCommentDesugarMode::Mbe
                },
            );
            if def_kind.is_proc_macro() {
                // proc macros expect their inputs without parentheses, MBEs expect it with them included
                tt.top_subtree_delimiter_mut().kind = tt::DelimiterKind::Invisible;
            }
            return (Arc::new(tt), SyntaxFixupUndoInfo::NONE, span);
        }
        // MacroCallKind::Derive should not be here. As we are getting the argument for the derive macro
        MacroCallKind::Derive { .. } => {
            unreachable!("`ExpandDatabase::macro_arg` called with `MacroCallKind::Derive`")
        }
        MacroCallKind::Attr { ast_id, invoc_attr_index, .. } => {
            let node = ast_id.to_ptr(db).to_node(&root);
            let attr_source = attr_source(invoc_attr_index, &node);

            let span = map.span_for_range(
                attr_source
                    .as_ref()
                    .and_then(|it| it.path())
                    .map_or_else(|| node.syntax().text_range(), |it| it.syntax().text_range()),
            );
            // If derive attribute we need to censor the derive input
            if matches!(def_kind, MacroExpander::BuiltInAttr(expander) if expander.is_derive())
                && ast::Adt::can_cast(node.syntax().kind())
            {
                let adt = ast::Adt::cast(node.syntax().clone()).unwrap();
                let censor_derive_input = censor_derive_input(invoc_attr_index, &adt);
                (censor_derive_input, node, span)
            } else {
                (attr_source.into_iter().map(|it| it.syntax().clone().into()).collect(), node, span)
            }
        }
    };

    let (mut tt, undo_info) = {
        let syntax = item_node.syntax();
        let censor_cfg =
            cfg_process::process_cfg_attrs(db, syntax, &def_kind, db.macro_call_call_crate(id))
                .unwrap_or_default();
        let mut fixups =
            fixup::fixup_syntax(map.as_ref(), syntax, span, DocCommentDesugarMode::ProcMacro);
        fixups.append.retain(|it, _| match it {
            syntax::NodeOrToken::Token(_) => true,
            it => !censor.contains(it) && !censor_cfg.contains(it),
        });
        fixups.remove.extend(censor);
        fixups.remove.extend(censor_cfg);

        (
            syntax_bridge::syntax_node_to_token_tree_modified(
                syntax,
                map,
                fixups.append,
                fixups.remove,
                span,
                DocCommentDesugarMode::ProcMacro,
            ),
            fixups.undo_info,
        )
    };

    if def_kind.is_proc_macro() {
        // proc macros expect their inputs without parentheses, MBEs expect it with them included
        tt.top_subtree_delimiter_mut().kind = tt::DelimiterKind::Invisible;
    }

    (Arc::new(tt), undo_info, span)
}

// FIXME: Censoring info should be calculated by the caller! Namely by name resolution
/// Derives expect all `#[derive(..)]` invocations up to (and including) the currently invoked one to be stripped
fn censor_derive_input(derive_attr_index: AttrId, node: &ast::Adt) -> FxHashSet<SyntaxElement> {
    // FIXME: handle `cfg_attr`
    cov_mark::hit!(derive_censoring);
    collect_attrs(node)
        .take(derive_attr_index.ast_index() + 1)
        .filter_map(|(_, attr)| Either::left(attr))
        // FIXME, this resolution should not be done syntactically
        // derive is a proper macro now, no longer builtin
        // But we do not have resolution at this stage, this means
        // we need to know about all macro calls for the given ast item here
        // so we require some kind of mapping...
        .filter(|attr| attr.simple_name().as_deref() == Some("derive"))
        .map(|it| it.syntax().clone().into())
        .collect()
}

/// Attributes expect the invoking attribute to be stripped
fn attr_source(invoc_attr_index: AttrId, node: &ast::Item) -> Option<ast::Attr> {
    // FIXME: handle `cfg_attr`
    cov_mark::hit!(attribute_macro_attr_censoring);
    collect_attrs(node).nth(invoc_attr_index.ast_index()).and_then(|(_, attr)| Either::left(attr))
}

// impl TokenExpander {
//     fn macro_expander(db: &dyn ExpandDatabase, id: MacroDefId) -> TokenExpander {
//         match id.kind {
//             MacroDefKind::Declarative(ast_id) => {
//                 TokenExpander::DeclarativeMacro(db.decl_macro_expander(id.krate, ast_id))
//             }
//             MacroDefKind::BuiltIn(_, expander) => TokenExpander::BuiltIn(expander),
//             MacroDefKind::BuiltInAttr(_, expander) => TokenExpander::BuiltInAttr(expander),
//             MacroDefKind::BuiltInDerive(_, expander) => TokenExpander::BuiltInDerive(expander),
//             MacroDefKind::BuiltInEager(_, expander) => TokenExpander::BuiltInEager(expander),
//             MacroDefKind::ProcMacro(_, expander, _) => TokenExpander::ProcMacro(expander),
//         }
//     }
// }

enum CowArc<T> {
    Arc(Arc<T>),
    Owned(T),
}

fn macro_expand(
    db: &dyn ExpandDatabase,
    macro_call_id: MacroCallId,
    def_kind: &MacroExpander,
    kind: &MacroCallKind,
) -> ExpandResult<(CowArc<tt::TopSubtree>, MatchedArmIndex)> {
    let _p = tracing::info_span!("macro_expand").entered();

    let (ExpandResult { value: (tt, matched_arm), err }, span) = match def_kind {
        MacroExpander::ProcMacro(..) => {
            return db.expand_proc_macro(macro_call_id).map(CowArc::Arc).zip_val(None);
        }
        _ => {
            let (macro_arg, undo_info, span) =
                db.macro_arg_considering_derives(macro_call_id, kind);

            let arg = &*macro_arg;
            let res = match def_kind {
                MacroExpander::Declarative(id) => id.expand(db, arg.clone(), macro_call_id, span),
                MacroExpander::BuiltIn(it) => {
                    it.expand(db, macro_call_id, arg, span).map_err(Into::into).zip_val(None)
                }
                MacroExpander::BuiltInDerive(it) => {
                    it.expand(db, macro_call_id, arg, span).map_err(Into::into).zip_val(None)
                }
                MacroExpander::BuiltInEager(it) => {
                    // This might look a bit odd, but we do not expand the inputs to eager macros here.
                    // Eager macros inputs are expanded, well, eagerly when we collect the macro calls.
                    // That kind of expansion uses the ast id map of an eager macros input though which goes through
                    // the HirFileId machinery. As eager macro inputs are assigned a macro file id that query
                    // will end up going through here again, whereas we want to just want to inspect the raw input.
                    // As such we just return the input subtree here.
                    let eager = match &kind {
                        MacroCallKind::FnLike { eager: None, .. } => {
                            return ExpandResult::ok(CowArc::Arc(macro_arg.clone())).zip_val(None);
                        }
                        MacroCallKind::FnLike { eager: Some(eager), .. } => Some(&**eager),
                        _ => None,
                    };

                    let mut res = it.expand(db, macro_call_id, arg, span).map_err(Into::into);

                    if let Some(EagerCallInfo { error, .. }) = eager {
                        // FIXME: We should report both errors!
                        res.err = error.clone().or(res.err);
                    }
                    res.zip_val(None)
                }
                MacroExpander::BuiltInAttr(it) => {
                    let mut res = it.expand(db, macro_call_id, arg, span);
                    fixup::reverse_fixups(&mut res.value, &undo_info);
                    res.zip_val(None)
                }
                MacroExpander::ProcMacro(_, _) => unreachable!(),
            };
            (ExpandResult { value: res.value, err: res.err }, span)
        }
    };

    // Skip checking token tree limit for include! macro call
    if !def_kind.is_include() {
        // Set a hard limit for the expanded tt
        if let Err(value) = check_tt_count(&tt) {
            return value
                .map(|()| CowArc::Owned(tt::TopSubtree::empty(tt::DelimSpan::from_single(span))))
                .zip_val(matched_arm);
        }
    }

    ExpandResult { value: (CowArc::Owned(tt), matched_arm), err }
}

fn proc_macro_span(db: &dyn ExpandDatabase, ast: AstId<ast::Fn>) -> Span {
    let root = db.parse_or_expand(ast.file_id);
    let ast_id_map = &db.ast_id_map(ast.file_id);
    let span_map = &db.span_map(ast.file_id);

    let node = ast_id_map.get(ast.value).to_node(&root);
    let range = ast::HasName::name(&node)
        .map_or_else(|| node.syntax().text_range(), |name| name.syntax().text_range());
    span_map.span_for_range(range)
}

fn expand_proc_macro(
    db: &dyn ExpandDatabase,
    id: MacroCallId,
) -> ExpandResult<Arc<tt::TopSubtree>> {
    let kind = db.macro_call_kind(id);
    let (expander, ast_id) = db.proc_macro_call_expander(id).unwrap();
    let def_crate = db.macro_call_def_crate(id);
    let call_crate = db.macro_call_call_crate(id);
    let (macro_arg, undo_info, span) = db.macro_arg_considering_derives(id, &kind);

    let attr_arg = match &kind {
        MacroCallKind::Attr { attr_args: Some(attr_args), .. } => Some(&**attr_args),
        _ => None,
    };

    let ExpandResult { value: mut tt, err } = {
        let span = db.proc_macro_span(ast_id);
        expander.expand(
            db,
            def_crate,
            call_crate,
            &macro_arg,
            attr_arg,
            span_with_def_site_ctxt(db, span, id, def_crate.data(db).edition),
            span_with_call_site_ctxt(db, span, id, def_crate.data(db).edition),
            span_with_mixed_site_ctxt(db, span, id, def_crate.data(db).edition),
        )
    };

    // Set a hard limit for the expanded tt
    if let Err(value) = check_tt_count(&tt) {
        return value.map(|()| Arc::new(tt::TopSubtree::empty(tt::DelimSpan::from_single(span))));
    }

    fixup::reverse_fixups(&mut tt, &undo_info);

    ExpandResult { value: Arc::new(tt), err }
}

pub(crate) fn token_tree_to_syntax_node(
    db: &dyn ExpandDatabase,
    tt: &tt::TopSubtree,
    expand_to: ExpandTo,
    edition: parser::Edition,
) -> (Parse<SyntaxNode>, ExpansionSpanMap) {
    let entry_point = match expand_to {
        ExpandTo::Statements => syntax_bridge::TopEntryPoint::MacroStmts,
        ExpandTo::Items => syntax_bridge::TopEntryPoint::MacroItems,
        ExpandTo::Pattern => syntax_bridge::TopEntryPoint::Pattern,
        ExpandTo::Type => syntax_bridge::TopEntryPoint::Type,
        ExpandTo::Expr => syntax_bridge::TopEntryPoint::Expr,
    };
    syntax_bridge::token_tree_to_syntax_node(tt, entry_point, &mut |ctx| ctx.edition(db), edition)
}

fn check_tt_count(tt: &tt::TopSubtree) -> Result<(), ExpandResult<()>> {
    let tt = tt.top_subtree();
    let count = tt.count();
    if count <= TOKEN_LIMIT {
        Ok(())
    } else {
        Err(ExpandResult {
            value: (),
            err: Some(ExpandError::other(
                tt.delimiter.open,
                format!(
                    "macro invocation exceeds token limit: produced {count} tokens, limit is {TOKEN_LIMIT}",
                ),
            )),
        })
    }
}
