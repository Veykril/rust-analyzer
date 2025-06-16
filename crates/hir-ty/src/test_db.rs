//! Database used for testing `hir`.

use std::{fmt, panic, sync::Mutex};

use base_db::{
    Crate, CrateGraphBuilder, CratesMap, FileSourceRootInput, FileText, RootQueryDb,
    SourceDatabase, SourceRoot, SourceRootId, SourceRootInput,
};

use either::Either;
use hir_def::{Lookup, MacroId, ModuleId, db::DefDatabase, nameres::crate_def_map};
use hir_expand::{DepInjectDatabase, EditionedFileId, InFile, MacroCallKind, attrs::collect_attrs};
use rustc_hash::FxHashMap;
use salsa::{AsDynDatabase, Durability};
use span::FileId;
use syntax::{AstNode, SyntaxNode, TextRange, ast};
use test_utils::extract_annotations;
use triomphe::Arc;

#[salsa_macros::db]
#[derive(Clone)]
pub(crate) struct TestDB {
    storage: salsa::Storage<Self>,
    files: Arc<base_db::Files>,
    crates_map: Arc<CratesMap>,
    events: Arc<Mutex<Option<Vec<salsa::Event>>>>,
}

impl Default for TestDB {
    fn default() -> Self {
        let events = <Arc<Mutex<Option<Vec<salsa::Event>>>>>::default();
        let mut this = Self {
            storage: salsa::Storage::new(Some(Box::new({
                let events = events.clone();
                move |event| {
                    let mut events = events.lock().unwrap();
                    if let Some(events) = &mut *events {
                        events.push(event);
                    }
                }
            }))),
            events,
            files: Default::default(),
            crates_map: Default::default(),
        };
        this.set_expand_proc_attr_macros_with_durability(true, Durability::HIGH);
        // This needs to be here otherwise `CrateGraphBuilder` panics.
        this.set_all_crates(Arc::new(Box::new([])));
        CrateGraphBuilder::default().set_in_db(&mut this);
        this
    }
}

impl fmt::Debug for TestDB {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TestDB").finish()
    }
}

impl DepInjectDatabase for TestDB {
    fn macro_call_call_crate(&self, macro_call: span::MacroCallId) -> Crate {
        macro_call.lookup(self).container.krate()
    }

    fn macro_call_def_crate(&self, macro_call: span::MacroCallId) -> Crate {
        macro_call.lookup(self).def.krate(self)
    }

    fn macro_call_def_file_id(
        &self,
        macro_call: span::MacroCallId,
    ) -> hir_expand::AstId<ast::Item> {
        match macro_call.lookup(self).def {
            MacroId::Macro2Id(macro2_id) => macro2_id.lookup(self).id.upcast(),
            MacroId::MacroRulesId(macro_rules_id) => macro_rules_id.lookup(self).id.upcast(),
            MacroId::ProcMacroId(proc_macro_id) => proc_macro_id.lookup(self).id.upcast(),
        }
    }

    fn macro_call_kind(&self, macro_call: span::MacroCallId) -> hir_expand::MacroCallKind {
        macro_call.lookup(self).kind
    }

    fn macro_call_expander(&self, macro_call: span::MacroCallId) -> hir_expand::MacroExpander {
        macro_call.lookup(self).def.expander(self)
    }

    fn macro_call_ctx(&self, macro_call: span::MacroCallId) -> span::SyntaxContext {
        macro_call.lookup(self).ctxt
    }

    fn macro_call_local_inner(&self, macro_call: span::MacroCallId) -> bool {
        macro_call.lookup(self).def.local_inner(self)
    }

    fn proc_macro_call_expander(
        &self,
        macro_call: span::MacroCallId,
    ) -> Option<(hir_expand::proc_macro::CustomProcMacroExpander, hir_expand::AstId<ast::Fn>)> {
        match macro_call.lookup(self).def {
            MacroId::ProcMacroId(it) => Some({
                let lookup = it.lookup(self);
                (lookup.expander, lookup.id)
            }),
            MacroId::Macro2Id(_) | MacroId::MacroRulesId(_) => None,
        }
    }
    fn to_node(&self, macro_call: span::MacroCallId) -> InFile<SyntaxNode> {
        let lookup = macro_call.lookup(self);
        match lookup.kind {
            MacroCallKind::FnLike { ast_id, .. } => {
                ast_id.with_value(ast_id.to_node(self).syntax().clone())
            }
            MacroCallKind::Derive { ast_id, derive_attr_index, .. } => {
                // FIXME: handle `cfg_attr`
                ast_id.with_value(ast_id.to_node(self)).map(|it| {
                    collect_attrs(&it)
                        .nth(derive_attr_index.ast_index())
                        .and_then(|it| match it.1 {
                            Either::Left(attr) => Some(attr.syntax().clone()),
                            Either::Right(_) => None,
                        })
                        .unwrap_or_else(|| it.syntax().clone())
                })
            }
            MacroCallKind::Attr { ast_id, invoc_attr_index, .. } => {
                if lookup.def.expander(self).is_attribute_derive() {
                    // FIXME: handle `cfg_attr`
                    ast_id.with_value(ast_id.to_node(self)).map(|it| {
                        collect_attrs(&it)
                            .nth(invoc_attr_index.ast_index())
                            .and_then(|it| match it.1 {
                                Either::Left(attr) => Some(attr.syntax().clone()),
                                Either::Right(_) => None,
                            })
                            .unwrap_or_else(|| it.syntax().clone())
                    })
                } else {
                    ast_id.with_value(ast_id.to_node(self).syntax().clone())
                }
            }
        }
    }
}

#[salsa_macros::db]
impl SourceDatabase for TestDB {
    fn file_text(&self, file_id: base_db::FileId) -> FileText {
        self.files.file_text(file_id)
    }

    fn set_file_text(&mut self, file_id: base_db::FileId, text: &str) {
        let files = Arc::clone(&self.files);
        files.set_file_text(self, file_id, text);
    }

    fn set_file_text_with_durability(
        &mut self,
        file_id: base_db::FileId,
        text: &str,
        durability: Durability,
    ) {
        let files = Arc::clone(&self.files);
        files.set_file_text_with_durability(self, file_id, text, durability);
    }

    /// Source root of the file.
    fn source_root(&self, source_root_id: SourceRootId) -> SourceRootInput {
        self.files.source_root(source_root_id)
    }

    fn set_source_root_with_durability(
        &mut self,
        source_root_id: SourceRootId,
        source_root: Arc<SourceRoot>,
        durability: Durability,
    ) {
        let files = Arc::clone(&self.files);
        files.set_source_root_with_durability(self, source_root_id, source_root, durability);
    }

    fn file_source_root(&self, id: base_db::FileId) -> FileSourceRootInput {
        self.files.file_source_root(id)
    }

    fn set_file_source_root_with_durability(
        &mut self,
        id: base_db::FileId,
        source_root_id: SourceRootId,
        durability: Durability,
    ) {
        let files = Arc::clone(&self.files);
        files.set_file_source_root_with_durability(self, id, source_root_id, durability);
    }

    fn crates_map(&self) -> Arc<CratesMap> {
        self.crates_map.clone()
    }
}

#[salsa_macros::db]
impl salsa::Database for TestDB {}

impl panic::RefUnwindSafe for TestDB {}

impl TestDB {
    pub(crate) fn module_for_file_opt(&self, file_id: impl Into<FileId>) -> Option<ModuleId> {
        let file_id = file_id.into();
        for &krate in self.relevant_crates(file_id).iter() {
            let crate_def_map = crate_def_map(self, krate);
            for (local_id, data) in crate_def_map.modules() {
                if data.origin.file_id().map(|file_id| file_id.file_id(self)) == Some(file_id) {
                    return Some(crate_def_map.module_id(local_id));
                }
            }
        }
        None
    }

    pub(crate) fn module_for_file(&self, file_id: impl Into<FileId>) -> ModuleId {
        self.module_for_file_opt(file_id.into()).unwrap()
    }

    pub(crate) fn extract_annotations(
        &self,
    ) -> FxHashMap<EditionedFileId, Vec<(TextRange, String)>> {
        let mut files = Vec::new();
        for &krate in self.all_crates().iter() {
            let crate_def_map = crate_def_map(self, krate);
            for (module_id, _) in crate_def_map.modules() {
                let file_id = crate_def_map[module_id].origin.file_id();
                files.extend(file_id)
            }
        }
        files
            .into_iter()
            .filter_map(|file_id| {
                let text = self.file_text(file_id.file_id(self));
                let annotations = extract_annotations(&text.text(self));
                if annotations.is_empty() {
                    return None;
                }
                Some((file_id, annotations))
            })
            .collect()
    }
}

impl TestDB {
    pub(crate) fn log(&self, f: impl FnOnce()) -> Vec<salsa::Event> {
        *self.events.lock().unwrap() = Some(Vec::new());
        f();
        self.events.lock().unwrap().take().unwrap()
    }

    pub(crate) fn log_executed(&self, f: impl FnOnce()) -> Vec<String> {
        let events = self.log(f);
        events
            .into_iter()
            .filter_map(|e| match e.kind {
                // This is pretty horrible, but `Debug` is the only way to inspect
                // QueryDescriptor at the moment.
                salsa::EventKind::WillExecute { database_key } => {
                    let ingredient = self
                        .as_dyn_database()
                        .ingredient_debug_name(database_key.ingredient_index());
                    Some(ingredient.to_string())
                }
                _ => None,
            })
            .collect()
    }
}
