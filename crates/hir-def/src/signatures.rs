use bitflags::bitflags;
use hir_expand::{Lookup, name::Name};
use intern::{Symbol, sym};
use la_arena::{Arena, Idx};
use rustc_abi::ReprOptions;
use syntax::ast::HasGenericParams;
use triomphe::Arc;

use crate::{
    ConstId, EnumId, EnumVariantId, FunctionId, HasModule, ImplId, StaticId, StructId,
    TraitAliasId, TraitId, TypeAliasId, UnionId, VariantId,
    db::DefDatabase,
    expr_store::{
        ExpressionStore, ExpressionStoreSourceMap,
        lower::{lower_generic_params, lower_type_alias},
    },
    hir::{ExprId, PatId, generics::GenericParams},
    item_tree::{FieldsShape, ModItem, RawVisibility},
    lang_item::LangItem,
    src::HasSource,
    type_ref::{PathId, TypeBound, TypeRef, TypeRefId},
};

#[derive(Debug, PartialEq, Eq)]
pub struct StructSignature {
    pub generic_params: Arc<GenericParams>,
    pub store: Arc<ExpressionStore>,
    pub flags: StructFlags,
    pub shape: FieldsShape,
    pub repr: Option<ReprOptions>,
}

bitflags! {
    #[derive(Debug, Copy, Clone, PartialEq, Eq)]
    pub struct StructFlags: u8 {
        const NO_FLAGS         = 0;
        /// Indicates whether the struct is `PhantomData`.
        const IS_PHANTOM_DATA  = 1 << 2;
        /// Indicates whether the struct has a `#[fundamental]` attribute.
        const IS_FUNDAMENTAL   = 1 << 3;
        /// Indicates whether the struct has a `#[rustc_has_incoherent_inherent_impls]` attribute.
        const IS_RUSTC_HAS_INCOHERENT_INHERENT_IMPLS      = 1 << 4;
        /// Indicates whether this struct is `Box`.
        const IS_BOX           = 1 << 5;
        /// Indicates whether this struct is `ManuallyDrop`.
        const IS_MANUALLY_DROP = 1 << 6;
        /// Indicates whether this struct is `UnsafeCell`.
        const IS_UNSAFE_CELL   = 1 << 7;
    }
}

impl StructSignature {
    pub fn query(db: &dyn DefDatabase, id: StructId) -> Arc<Self> {
        let loc = id.lookup(db);
        let item_tree = loc.id.item_tree(db);
        let attrs = item_tree.attrs(db, loc.container.krate, ModItem::from(loc.id.value).into());

        let mut flags = StructFlags::NO_FLAGS;
        if attrs.by_key(&sym::rustc_has_incoherent_inherent_impls).exists() {
            flags |= StructFlags::IS_RUSTC_HAS_INCOHERENT_INHERENT_IMPLS;
        }
        if attrs.by_key(&sym::fundamental).exists() {
            flags |= StructFlags::IS_FUNDAMENTAL;
        }
        if let Some(lang) = attrs.lang_item() {
            match lang {
                LangItem::PhantomData => flags |= StructFlags::IS_PHANTOM_DATA,
                LangItem::OwnedBox => flags |= StructFlags::IS_BOX,
                LangItem::ManuallyDrop => flags |= StructFlags::IS_MANUALLY_DROP,
                LangItem::UnsafeCell => flags |= StructFlags::IS_UNSAFE_CELL,
                _ => (),
            }
        }
        let repr = attrs.repr();

        let hir_expand::files::InFileWrapper { file_id, value } = loc.source(db);
        let (store, generic_params) = lower_generic_params(
            db,
            loc.container,
            file_id,
            value.generic_param_list(),
            value.where_clause(),
        );

        Arc::new(StructSignature {
            generic_params,
            store,
            flags,
            shape: item_tree[loc.id.value].shape,
            repr,
        })
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct UnionSignature {
    pub generic_params: Arc<GenericParams>,
    pub store: Arc<ExpressionStore>,
    pub flags: StructFlags,
    pub repr: Option<ReprOptions>,
}

impl UnionSignature {
    pub fn query(db: &dyn DefDatabase, id: UnionId) -> Arc<Self> {
        let loc = id.lookup(db);
        let krate = loc.container.krate;
        let item_tree = loc.id.item_tree(db);
        let attrs = item_tree.attrs(db, krate, ModItem::from(loc.id.value).into());
        let mut flags = StructFlags::NO_FLAGS;
        if attrs.by_key(&sym::rustc_has_incoherent_inherent_impls).exists() {
            flags |= StructFlags::IS_RUSTC_HAS_INCOHERENT_INHERENT_IMPLS;
        }
        if attrs.by_key(&sym::fundamental).exists() {
            flags |= StructFlags::IS_FUNDAMENTAL;
        }

        let repr = attrs.repr();

        let hir_expand::files::InFileWrapper { file_id, value } = loc.source(db);
        let (store, generic_params) = lower_generic_params(
            db,
            loc.container,
            file_id,
            value.generic_param_list(),
            value.where_clause(),
        );

        Arc::new(UnionSignature { generic_params, store, flags, repr })
    }
}

bitflags! {
    #[derive(Debug, Copy, Clone, PartialEq, Eq)]
    pub struct EnumFlags: u8 {
        const NO_FLAGS         = 0;
        const IS_RUSTC_HAS_INCOHERENT_INHERENT_IMPLS  = 1 << 4;
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct EnumSignature {
    pub generic_params: Arc<GenericParams>,
    pub store: Arc<ExpressionStore>,
    pub flags: EnumFlags,
    pub repr: Option<ReprOptions>,
}

impl EnumSignature {
    pub fn query(db: &dyn DefDatabase, id: EnumId) -> Arc<Self> {
        let loc = id.lookup(db);
        let item_tree = loc.id.item_tree(db);
        let attrs = item_tree.attrs(db, loc.container.krate, ModItem::from(loc.id.value).into());
        let mut flags = EnumFlags::NO_FLAGS;
        if attrs.by_key(&sym::rustc_has_incoherent_inherent_impls).exists() {
            flags |= EnumFlags::IS_RUSTC_HAS_INCOHERENT_INHERENT_IMPLS;
        }

        let repr = attrs.repr();

        let hir_expand::files::InFileWrapper { file_id, value } = loc.source(db);
        let (store, generic_params) = lower_generic_params(
            db,
            loc.container,
            file_id,
            value.generic_param_list(),
            value.where_clause(),
        );

        Arc::new(EnumSignature { generic_params, store, flags, repr })
    }
}
bitflags::bitflags! {
    #[derive(Debug, Clone, Copy, Eq, PartialEq, Default)]
    pub struct ConstFlags: u8 {
        const NO_FLAGS         = 0;
        const HAS_BODY = 1 << 0;
        const RUSTC_ALLOW_INCOHERENT_IMPL = 1 << 1;
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct ConstSignature {
    // generic_params: Arc<GenericParams>,
    pub store: Arc<ExpressionStore>,
    pub type_ref: TypeRefId,
    pub flags: ConstFlags,
}

impl ConstSignature {
    pub fn query(db: &dyn DefDatabase, id: ConstId) -> (Arc<Self>, Arc<ExpressionStoreSourceMap>) {
        let loc = id.lookup(db);
        let item_tree = loc.id.item_tree(db);

        let module = loc.container.module(db);
        let attrs = item_tree.attrs(db, module.krate, ModItem::from(loc.id.value).into());
        let mut flags = ConstFlags::NO_FLAGS;
        if attrs.by_key(&sym::rustc_allow_incoherent_impl).exists() {
            flags |= ConstFlags::RUSTC_ALLOW_INCOHERENT_IMPL;
        }
        // FIXME: Body flag
        let src = loc.source(db);

        let (store, source_map, type_ref) = crate::expr_store::lower::lower_type_ref(
            db,
            module,
            src.map(|it| it.ty()).transpose().expect("FIXME"),
        );

        (Arc::new(ConstSignature { store: Arc::new(store), type_ref, flags }), Arc::new(source_map))
    }
}

bitflags::bitflags! {
    #[derive(Debug, Clone, Copy, Eq, PartialEq, Default)]
    pub struct StaticFlags: u8 {
        const HAS_BODY = 1 << 0;
        const RUSTC_ALLOW_INCOHERENT_IMPL = 1 << 1;
        const MUTABLE = 1 << 2;
        const HAS_UNSAFE = 1 << 3;
        const HAS_SAFE = 1 << 4;
        const IS_EXTERN = 1 << 5;
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct StaticSignature {
    // generic_params: Arc<GenericParams>,
    pub store: Arc<ExpressionStore>,
    pub type_ref: TypeRefId,
    pub flags: StaticFlags,
}
impl StaticSignature {
    pub fn query(db: &dyn DefDatabase, id: StaticId) -> (Arc<Self>, Arc<ExpressionStoreSourceMap>) {
        let loc = id.lookup(db);
        let item_tree = loc.id.item_tree(db);

        let module = loc.container.module(db);
        let attrs = item_tree.attrs(db, module.krate, ModItem::from(loc.id.value).into());
        let mut flags = StaticFlags::empty();
        if attrs.by_key(&sym::rustc_allow_incoherent_impl).exists() {
            flags |= StaticFlags::RUSTC_ALLOW_INCOHERENT_IMPL;
        }
        // FIXME: flags
        let src = loc.source(db);

        let (store, source_map, type_ref) = crate::expr_store::lower::lower_type_ref(
            db,
            module,
            src.map(|it| it.ty()).transpose().expect("FIXME"),
        );

        (
            Arc::new(StaticSignature { store: Arc::new(store), type_ref, flags }),
            Arc::new(source_map),
        )
    }
}

bitflags::bitflags! {
    #[derive(Debug, Clone, Copy, Eq, PartialEq, Default)]
    pub struct ImplFlags: u8 {
        const IS_NEGATIVE = 1 << 0;
        const IS_UNSAFE = 1 << 1;
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct ImplSignature {
    pub generic_params: Arc<GenericParams>,
    pub store: Arc<ExpressionStore>,
    pub self_ty: TypeRefId,
    pub target_trait: Option<PathId>,
    pub flags: ImplFlags,
}

impl ImplSignature {
    pub fn query(db: &dyn DefDatabase, id: ImplId) -> Arc<Self> {
        let loc = id.lookup(db);

        let flags = ImplFlags::empty();
        // FIXME: flags
        let src = loc.source(db);
        let (store, source_map, self_ty, target_trait, generic_params) =
            crate::expr_store::lower::lower_impl(db, loc.container, src);

        Arc::new(ImplSignature {
            store: Arc::new(store),
            generic_params,
            self_ty,
            target_trait,
            flags,
        })
    }
}

bitflags::bitflags! {
    #[derive(Debug, Clone, Copy, Eq, PartialEq, Default)]
    pub struct TraitFlags: u8 {
        const IS_AUTO = 1 << 0;
        const IS_UNSAFE = 1 << 1;
        const IS_FUNDAMENTAL = 1 << 2;
        const RUSTC_HAS_INCOHERENT_INHERENT_IMPLS = 1 << 3;
        const SKIP_ARRAY_DURING_METHOD_DISPATCH = 1 << 4;
        const SKIP_BOXED_SLICE_DURING_METHOD_DISPATCH = 1 << 5;
        const RUSTC_PAREN_SUGAR = 1 << 6;
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct TraitSignature {
    pub generic_params: Arc<GenericParams>,
    pub store: Arc<ExpressionStore>,
    pub target: TypeRefId,
    pub trait_: Option<TypeRefId>,
    pub flags: TraitFlags,
}

impl TraitSignature {
    pub fn query(db: &dyn DefDatabase, id: TraitId) -> Arc<Self> {
        let loc = id.lookup(db);
        let item_tree = loc.id.item_tree(db);

        let flags = TraitFlags::empty();
        // FIXME: flags
        let src = loc.source(db);
        let (store, target, trait_, generic_params) = lower_trait();

        Arc::new(TraitSignature { store: Arc::new(store), generic_params, flags, target, trait_ })
    }
}

fn lower_trait() -> (ExpressionStore, Idx<TypeRef>, Option<Idx<TypeRef>>, Arc<GenericParams>) {
    todo!()
}
#[derive(Debug, PartialEq, Eq)]
pub struct TraitAliasSignature {
    pub generic_params: Arc<GenericParams>,
    pub store: Arc<ExpressionStore>,
}

impl TraitAliasSignature {
    pub fn query(db: &dyn DefDatabase, id: TraitAliasId) -> Arc<Self> {
        let loc = id.lookup(db);
        let item_tree = loc.id.item_tree(db);

        // FIXME: flags
        let hir_expand::files::InFileWrapper { file_id, value } = loc.source(db);
        let (store, generic_params) = lower_generic_params(
            db,
            loc.container,
            file_id,
            value.generic_param_list(),
            value.where_clause(),
        );

        Arc::new(TraitAliasSignature { generic_params, store })
    }
}

bitflags! {
    #[derive(Debug, Clone, Copy, Eq, PartialEq, Default)]
    pub(crate) struct FnFlags: u16 {
        const HAS_SELF_PARAM = 1 << 0;
        const HAS_BODY = 1 << 1;
        const HAS_DEFAULT_KW = 1 << 2;
        const HAS_CONST_KW = 1 << 3;
        const HAS_ASYNC_KW = 1 << 4;
        const HAS_UNSAFE_KW = 1 << 5;
        const IS_VARARGS = 1 << 6;
        const HAS_SAFE_KW = 1 << 7;
        /// The `#[target_feature]` attribute is necessary to check safety (with RFC 2396),
        /// but keeping it for all functions will consume a lot of memory when there are
        /// only very few functions with it. So we only encode its existence here, and lookup
        /// it if needed.
        const HAS_TARGET_FEATURE = 1 << 8;
        const DEPRECATED_SAFE_2024 = 1 << 9;
        const RUSTC_ALLOW_INCOHERENT_IMPLS = 1 << 9;
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct FunctionSignature {
    pub generic_params: Arc<GenericParams>,
    pub store: Arc<ExpressionStore>,
    pub params: Box<[TypeRefId]>,
    pub ret_type: Option<TypeRefId>,
    pub abi: Option<Symbol>,
    pub flags: FnFlags,
    // FIXME: we should put this behind a fn flags + query to avoid bloating the struct
    pub legacy_const_generics_indices: Option<Box<Box<[u32]>>>,
}

impl FunctionSignature {
    pub fn query(db: &dyn DefDatabase, id: FunctionId) -> Arc<Self> {
        let loc = id.lookup(db);
        let krate = loc.container.module(db).krate;
        let item_tree = loc.id.item_tree(db);
        let func = &item_tree[loc.id.value];

        // let cfg_options = krate.cfg_options(db);
        // let attr_owner = |idx| {
        //     item_tree::AttrOwner::Param(loc.id.value, Idx::from_raw(RawIdx::from(idx as u32)))
        // };

        // FIXME: Flags
        let mut flags = FnFlags::empty();
        // if flags.contains(FnFlags::HAS_SELF_PARAM) {
        //     // If there's a self param in the syntax, but it is cfg'd out, remove the flag.
        //     let is_cfgd_out =
        //         !item_tree.attrs(db, krate, attr_owner(0usize)).is_cfg_enabled(cfg_options);
        //     if is_cfgd_out {
        //         cov_mark::hit!(cfgd_out_self_param);
        //         flags.remove(FnFlags::HAS_SELF_PARAM);
        //     }
        // }
        // if flags.contains(FnFlags::IS_VARARGS) {
        //     if let Some((_, param)) = func.params.iter().enumerate().rev().find(|&(idx, _)| {
        //         item_tree.attrs(db, krate, attr_owner(idx)).is_cfg_enabled(cfg_options)
        //     }) {
        //         if param.type_ref.is_some() {
        //             flags.remove(FnFlags::IS_VARARGS);
        //         }
        //     } else {
        //         flags.remove(FnFlags::IS_VARARGS);
        //     }
        // }

        let attrs = item_tree.attrs(db, krate, ModItem::from(loc.id.value).into());
        let rustc_allow_incoherent_impl = attrs.by_key(&sym::rustc_allow_incoherent_impl).exists();
        if flags.contains(FnFlags::HAS_UNSAFE_KW)
            && attrs.by_key(&sym::rustc_deprecated_safe_2024).exists()
        {
            flags.remove(FnFlags::HAS_UNSAFE_KW);
            flags.insert(FnFlags::DEPRECATED_SAFE_2024);
        }

        if attrs.by_key(&sym::target_feature).exists() {
            flags.insert(FnFlags::HAS_TARGET_FEATURE);
        }
        let legacy_const_generics_indices = attrs.rustc_legacy_const_generics();

        // FIXME: flags
        let (store, params, ret_type, generic_params) = lower_fn_sig();
        Arc::new(FunctionSignature {
            generic_params,
            store,
            params,
            ret_type,
            abi: todo!(),
            flags,
            legacy_const_generics_indices,
        })
    }

    pub fn has_body(&self) -> bool {
        self.flags.contains(FnFlags::HAS_BODY)
    }

    /// True if the first param is `self`. This is relevant to decide whether this
    /// can be called as a method.
    pub fn has_self_param(&self) -> bool {
        self.flags.contains(FnFlags::HAS_SELF_PARAM)
    }

    pub fn is_default(&self) -> bool {
        self.flags.contains(FnFlags::HAS_DEFAULT_KW)
    }

    pub fn is_const(&self) -> bool {
        self.flags.contains(FnFlags::HAS_CONST_KW)
    }

    pub fn is_async(&self) -> bool {
        self.flags.contains(FnFlags::HAS_ASYNC_KW)
    }

    pub fn is_unsafe(&self) -> bool {
        self.flags.contains(FnFlags::HAS_UNSAFE_KW)
    }

    pub fn is_deprecated_safe_2024(&self) -> bool {
        self.flags.contains(FnFlags::DEPRECATED_SAFE_2024)
    }

    pub fn is_safe(&self) -> bool {
        self.flags.contains(FnFlags::HAS_SAFE_KW)
    }

    pub fn is_varargs(&self) -> bool {
        self.flags.contains(FnFlags::IS_VARARGS)
    }

    pub fn has_target_feature(&self) -> bool {
        self.flags.contains(FnFlags::HAS_TARGET_FEATURE)
    }
}

fn lower_fn_sig() -> (ExpressionStore, Box<[Idx<TypeRef>]>, Option<Idx<TypeRef>>, Arc<GenericParams>)
{
    todo!()
}

bitflags! {
    #[derive(Debug, Clone, Copy, Eq, PartialEq, Default)]
    pub(crate) struct TypeAliasFlags: u16 {
        const IS_EXTERN = 1 << 7;
        const RUSTC_ALLOW_INCOHERENT_IMPLS = 1 << 8;
        const RUSTC_HAS_INCOHERENT_INHERENT_IMPLS = 1 << 9;
    }
}
#[derive(Debug, PartialEq, Eq)]
pub struct TypeAliasSignature {
    pub generic_params: Arc<GenericParams>,
    pub store: Arc<ExpressionStore>,
    pub bounds: Box<[TypeBound]>,
    pub flags: TypeAliasFlags,
}

impl TypeAliasSignature {
    pub fn query(db: &dyn DefDatabase, id: TypeAliasId) -> Arc<Self> {
        let loc = id.lookup(db);
        let item_tree = loc.id.item_tree(db);

        let flags = TypeAliasFlags::empty();
        // FIXME: flags
        let (store, generic_params, bounds) = lower_type_alias();

        Arc::new(TypeAliasSignature { store, generic_params, flags, bounds })
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct FunctionBody {
    pub store: Arc<ExpressionStore>,
    pub parameters: Box<[PatId]>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct SimpleBody {
    pub store: Arc<ExpressionStore>,
}
pub type StaticBody = SimpleBody;
pub type ConstBody = SimpleBody;
pub type EnumVariantBody = SimpleBody;

#[derive(Debug, PartialEq, Eq)]
pub struct VariantFieldsBody {
    pub store: Arc<ExpressionStore>,
    pub fields: Box<[Option<ExprId>]>,
}

/// A single field of an enum variant or struct
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FieldData {
    pub name: Name,
    pub type_ref: TypeRefId,
    pub visibility: RawVisibility,
}

pub type LocalFieldId = Idx<FieldData>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VariantFields {
    fields: Arena<FieldData>,
}
impl VariantFields {
    pub fn variant_fields_query(db: &dyn DefDatabase, id: VariantId) -> Arc<Self> {
        todo!()
    }

    pub fn len(&self) -> usize {
        todo!()
    }

    pub fn fields(&self) -> &Arena<FieldData> {
        todo!()
    }

    pub fn field(&self, name: &Name) -> Option<LocalFieldId> {
        self.fields().iter().find_map(|(id, data)| if &data.name == name { Some(id) } else { None })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnumVariants {
    pub variants: Box<[(Name, EnumVariantId)]>,
}
impl EnumVariants {
    #[inline]
    pub(crate) fn enum_variants_query(db: &dyn DefDatabase, id: EnumId) -> Arc<EnumVariants> {
        todo!()
    }

    pub fn variant(&self, name: &Name) -> Option<EnumVariantId> {
        self.variants.iter().find_map(|(n, v)| if n == name { Some(*v) } else { None })
    }
}
