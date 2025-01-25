//! Many kinds of items or constructs can have generic parameters: functions,
//! structs, impls, traits, etc. This module provides a common HIR for these
//! generic parameters. See also the `Generics` type and the `generics_of` query
//! in rustc.

use std::{ops, sync::LazyLock};

use either::Either;
use hir_expand::{
    ExpandResult,
    name::{AsName, Name},
};
use intern::sym;
use la_arena::{Arena, RawIdx};
use stdx::{
    impl_from,
    thin_vec::{EmptyOptimizedThinVec, ThinVec},
};
use syntax::ast::{self, HasGenericParams, HasName, HasTypeBounds};
use triomphe::Arc;

use crate::{
    AdtId, ConstParamId, GenericDefId, HasModule, ItemTreeLoc, LifetimeParamId,
    LocalLifetimeParamId, LocalTypeOrConstParamId, Lookup, TypeOrConstParamId, TypeParamId,
    db::DefDatabase,
    hir::generics::{
        ConstParamData, GenericParams, LifetimeParamData, TypeOrConstParamData, TypeParamData,
        TypeParamProvenance, WherePredicate, WherePredicateTypeTarget,
    },
    item_tree::{AttrOwner, FileItemTreeId, ItemTree},
    nameres::{DefMap, LocalDefMap, MacroSubNs},
    type_ref::{
        ArrayType, ConstRef, FnType, LifetimeRef, PathId, RefType, TypeBound, TypeRef, TypeRefId,
        TypesMap, TypesSourceMap,
    },
};

#[derive(Clone, Default)]
pub(crate) struct GenericParamsCollector {
    type_or_consts: Arena<TypeOrConstParamData>,
    lifetimes: Arena<LifetimeParamData>,
    where_predicates: Vec<WherePredicate>,
}

impl GenericParamsCollector {
    pub(crate) fn fill_self_param(&mut self) {
        self.type_or_consts.alloc(
            TypeParamData {
                name: Some(Name::new_symbol_root(sym::Self_.clone())),
                default: None,
                provenance: TypeParamProvenance::TraitSelf,
            }
            .into(),
        );
    }

    pub(crate) fn fill(
        &mut self,
        lower_ctx: &mut LowerCtx<'_>,
        node: &dyn HasGenericParams,
        add_param_attrs: impl FnMut(
            Either<LocalTypeOrConstParamId, LocalLifetimeParamId>,
            ast::GenericParam,
        ),
    ) {
        if let Some(params) = node.generic_param_list() {
            self.fill_params(lower_ctx, params, add_param_attrs)
        }
        if let Some(where_clause) = node.where_clause() {
            self.fill_where_predicates(lower_ctx, where_clause);
        }
    }

    pub(crate) fn fill_implicit_self_bound(
        &mut self,
        lower_ctx: &mut LowerCtx<'_>,
        type_bounds: Option<ast::TypeBoundList>,
    ) {
        Self::fill_bounds(
            self,
            lower_ctx,
            type_bounds,
            Either::Left(lower_ctx.alloc_type_ref_desugared(TypeRef::Path(
                Name::new_symbol_root(sym::Self_.clone()).into(),
            ))),
        );
    }

    fn fill_bounds(
        &mut self,
        lower_ctx: &mut LowerCtx<'_>,
        type_bounds: Option<ast::TypeBoundList>,
        target: Either<TypeRefId, LifetimeRef>,
    ) {
        for bound in type_bounds.iter().flat_map(|type_bound_list| type_bound_list.bounds()) {
            self.add_where_predicate_from_bound(lower_ctx, bound, None, target.clone());
        }
    }

    fn fill_params(
        &mut self,
        lower_ctx: &mut LowerCtx<'_>,
        params: ast::GenericParamList,
        mut add_param_attrs: impl FnMut(
            Either<LocalTypeOrConstParamId, LocalLifetimeParamId>,
            ast::GenericParam,
        ),
    ) {
        for type_or_const_param in params.type_or_const_params() {
            match type_or_const_param {
                ast::TypeOrConstParam::Type(type_param) => {
                    let name = type_param.name().map_or_else(Name::missing, |it| it.as_name());
                    // FIXME: Use `Path::from_src`
                    let default =
                        type_param.default_type().map(|it| TypeRef::from_ast(lower_ctx, it));
                    let param = TypeParamData {
                        name: Some(name.clone()),
                        default,
                        provenance: TypeParamProvenance::TypeParamList,
                    };
                    let idx = self.type_or_consts.alloc(param.into());
                    let type_ref = lower_ctx.alloc_type_ref_desugared(TypeRef::Path(name.into()));
                    self.fill_bounds(
                        lower_ctx,
                        type_param.type_bound_list(),
                        Either::Left(type_ref),
                    );
                    add_param_attrs(Either::Left(idx), ast::GenericParam::TypeParam(type_param));
                }
                ast::TypeOrConstParam::Const(const_param) => {
                    let name = const_param.name().map_or_else(Name::missing, |it| it.as_name());
                    let ty = TypeRef::from_ast_opt(lower_ctx, const_param.ty());
                    let param = ConstParamData {
                        name,
                        ty,
                        default: ConstRef::from_const_param(lower_ctx, &const_param),
                    };
                    let idx = self.type_or_consts.alloc(param.into());
                    add_param_attrs(Either::Left(idx), ast::GenericParam::ConstParam(const_param));
                }
            }
        }
        for lifetime_param in params.lifetime_params() {
            let name =
                lifetime_param.lifetime().map_or_else(Name::missing, |lt| Name::new_lifetime(&lt));
            let param = LifetimeParamData { name: name.clone() };
            let idx = self.lifetimes.alloc(param);
            let lifetime_ref = LifetimeRef::new_name(name);
            self.fill_bounds(
                lower_ctx,
                lifetime_param.type_bound_list(),
                Either::Right(lifetime_ref),
            );
            add_param_attrs(Either::Right(idx), ast::GenericParam::LifetimeParam(lifetime_param));
        }
    }

    fn fill_where_predicates(
        &mut self,
        lower_ctx: &mut LowerCtx<'_>,
        where_clause: ast::WhereClause,
    ) {
        for pred in where_clause.predicates() {
            let target = if let Some(type_ref) = pred.ty() {
                Either::Left(TypeRef::from_ast(lower_ctx, type_ref))
            } else if let Some(lifetime) = pred.lifetime() {
                Either::Right(LifetimeRef::new(&lifetime))
            } else {
                continue;
            };

            let lifetimes: Option<Box<_>> = pred.generic_param_list().map(|param_list| {
                // Higher-Ranked Trait Bounds
                param_list
                    .lifetime_params()
                    .map(|lifetime_param| {
                        lifetime_param
                            .lifetime()
                            .map_or_else(Name::missing, |lt| Name::new_lifetime(&lt))
                    })
                    .collect()
            });
            for bound in pred.type_bound_list().iter().flat_map(|l| l.bounds()) {
                self.add_where_predicate_from_bound(
                    lower_ctx,
                    bound,
                    lifetimes.as_deref(),
                    target.clone(),
                );
            }
        }
    }

    fn add_where_predicate_from_bound(
        &mut self,
        lower_ctx: &mut LowerCtx<'_>,
        bound: ast::TypeBound,
        hrtb_lifetimes: Option<&[Name]>,
        target: Either<TypeRefId, LifetimeRef>,
    ) {
        let bound = TypeBound::from_ast(lower_ctx, bound);
        self.fill_impl_trait_bounds(lower_ctx.take_impl_traits_bounds());
        let predicate = match (target, bound) {
            (Either::Left(type_ref), bound) => match hrtb_lifetimes {
                Some(hrtb_lifetimes) => WherePredicate::ForLifetime {
                    lifetimes: hrtb_lifetimes.to_vec().into_boxed_slice(),
                    target: WherePredicateTypeTarget::TypeRef(type_ref),
                    bound,
                },
                None => WherePredicate::TypeBound {
                    target: WherePredicateTypeTarget::TypeRef(type_ref),
                    bound,
                },
            },
            (Either::Right(lifetime), TypeBound::Lifetime(bound)) => {
                WherePredicate::Lifetime { target: lifetime, bound }
            }
            _ => return,
        };
        self.where_predicates.push(predicate);
    }

    fn fill_impl_trait_bounds(&mut self, impl_bounds: Vec<ThinVec<TypeBound>>) {
        for bounds in impl_bounds {
            let param = TypeParamData {
                name: None,
                default: None,
                provenance: TypeParamProvenance::ArgumentImplTrait,
            };
            let param_id = self.type_or_consts.alloc(param.into());
            for bound in &bounds {
                self.where_predicates.push(WherePredicate::TypeBound {
                    target: WherePredicateTypeTarget::TypeOrConstParam(param_id),
                    bound: bound.clone(),
                });
            }
        }
    }

    fn fill_implicit_impl_trait_args(
        &mut self,
        db: &dyn DefDatabase,
        generics_types_map: &mut TypesMap,
        generics_types_source_map: &mut TypesSourceMap,
        // FIXME: Change this back to `LazyCell` if https://github.com/rust-lang/libs-team/issues/429 is accepted.
        exp: &mut Option<(Arc<DefMap>, Arc<LocalDefMap>, Expander)>,
        exp_fill: &mut dyn FnMut() -> (Arc<DefMap>, Arc<LocalDefMap>, Expander),
        type_ref: TypeRefId,
        types_map: &TypesMap,
        types_source_map: &TypesSourceMap,
    ) {
        TypeRef::walk(type_ref, types_map, &mut |type_ref| {
            if let TypeRef::ImplTrait(bounds) = type_ref {
                let param = TypeParamData {
                    name: None,
                    default: None,
                    provenance: TypeParamProvenance::ArgumentImplTrait,
                };
                let param_id = self.type_or_consts.alloc(param.into());
                for bound in bounds {
                    let bound = copy_type_bound(
                        bound,
                        types_map,
                        types_source_map,
                        generics_types_map,
                        generics_types_source_map,
                    );
                    self.where_predicates.push(WherePredicate::TypeBound {
                        target: WherePredicateTypeTarget::TypeOrConstParam(param_id),
                        bound,
                    });
                }
            }
        });
    }

    pub(crate) fn finish(
        self,
        mut generics_types_map: TypesMap,
        generics_types_source_map: &mut TypesSourceMap,
    ) -> Arc<GenericParams> {
        let Self { mut lifetimes, mut type_or_consts, mut where_predicates } = self;

        if lifetimes.is_empty() && type_or_consts.is_empty() && where_predicates.is_empty() {
            static EMPTY: LazyLock<Arc<GenericParams>> = LazyLock::new(|| {
                Arc::new(GenericParams {
                    lifetimes: Arena::new(),
                    type_or_consts: Arena::new(),
                    where_predicates: Box::default(),
                    types_map: TypesMap::default(),
                })
            });
            return Arc::clone(&EMPTY);
        }

        lifetimes.shrink_to_fit();
        type_or_consts.shrink_to_fit();
        where_predicates.shrink_to_fit();
        generics_types_map.shrink_to_fit();
        generics_types_source_map.shrink_to_fit();
        Arc::new(GenericParams {
            type_or_consts,
            lifetimes,
            where_predicates: where_predicates.into_boxed_slice(),
            types_map: generics_types_map,
        })
    }
}

/// Copies a `TypeRef` from a `TypesMap` (accompanied with `TypesSourceMap`) into another `TypesMap`
/// (and `TypesSourceMap`).
fn copy_type_ref(
    type_ref: TypeRefId,
    from: &TypesMap,
    from_source_map: &TypesSourceMap,
    to: &mut TypesMap,
    to_source_map: &mut TypesSourceMap,
) -> TypeRefId {
    let result = match &from[type_ref] {
        TypeRef::Fn(fn_) => {
            let params = fn_.params().iter().map(|(name, param_type)| {
                (name.clone(), copy_type_ref(*param_type, from, from_source_map, to, to_source_map))
            });
            TypeRef::Fn(FnType::new(fn_.is_varargs(), fn_.is_unsafe(), fn_.abi().clone(), params))
        }
        TypeRef::Tuple(types) => TypeRef::Tuple(EmptyOptimizedThinVec::from_iter(
            types.iter().map(|&t| copy_type_ref(t, from, from_source_map, to, to_source_map)),
        )),
        &TypeRef::RawPtr(type_ref, mutbl) => TypeRef::RawPtr(
            copy_type_ref(type_ref, from, from_source_map, to, to_source_map),
            mutbl,
        ),
        TypeRef::Reference(ref_) => TypeRef::Reference(Box::new(RefType {
            ty: copy_type_ref(ref_.ty, from, from_source_map, to, to_source_map),
            lifetime: ref_.lifetime.clone(),
            mutability: ref_.mutability,
        })),
        TypeRef::Array(array) => TypeRef::Array(Box::new(ArrayType {
            ty: copy_type_ref(array.ty, from, from_source_map, to, to_source_map),
            len: array.len.clone(),
        })),
        &TypeRef::Slice(type_ref) => {
            TypeRef::Slice(copy_type_ref(type_ref, from, from_source_map, to, to_source_map))
        }
        TypeRef::ImplTrait(bounds) => TypeRef::ImplTrait(ThinVec::from_iter(copy_type_bounds(
            bounds,
            from,
            from_source_map,
            to,
            to_source_map,
        ))),
        TypeRef::DynTrait(bounds) => TypeRef::DynTrait(ThinVec::from_iter(copy_type_bounds(
            bounds,
            from,
            from_source_map,
            to,
            to_source_map,
        ))),
        TypeRef::Path(path) => {
            TypeRef::Path(copy_path(path, from, from_source_map, to, to_source_map))
        }
        TypeRef::Never => TypeRef::Never,
        TypeRef::Placeholder => TypeRef::Placeholder,
        TypeRef::Error => TypeRef::Error,
    };
    let id = to.types.alloc(result);
    if let Some(&ptr) = from_source_map.types_map_back.get(id) {
        to_source_map.types_map_back.insert(id, ptr);
    }
    id
}

fn copy_path(
    path: &Path,
    from: &TypesMap,
    from_source_map: &TypesSourceMap,
    to: &mut TypesMap,
    to_source_map: &mut TypesSourceMap,
) -> Path {
    match path {
        Path::BarePath(mod_path) => Path::BarePath(mod_path.clone()),
        Path::Normal(path) => {
            let type_anchor = path
                .type_anchor()
                .map(|type_ref| copy_type_ref(type_ref, from, from_source_map, to, to_source_map));
            let mod_path = path.mod_path().clone();
            let generic_args = path.generic_args().iter().map(|generic_args| {
                copy_generic_args(generic_args, from, from_source_map, to, to_source_map)
            });
            Path::Normal(NormalPath::new(type_anchor, mod_path, generic_args))
        }
        Path::LangItem(lang_item, name) => Path::LangItem(*lang_item, name.clone()),
    }
}

fn copy_generic_args(
    generic_args: &Option<GenericArgs>,
    from: &TypesMap,
    from_source_map: &TypesSourceMap,
    to: &mut TypesMap,
    to_source_map: &mut TypesSourceMap,
) -> Option<GenericArgs> {
    generic_args.as_ref().map(|generic_args| {
        let args = generic_args
            .args
            .iter()
            .map(|arg| match arg {
                &GenericArg::Type(ty) => {
                    GenericArg::Type(copy_type_ref(ty, from, from_source_map, to, to_source_map))
                }
                GenericArg::Lifetime(lifetime) => GenericArg::Lifetime(lifetime.clone()),
                GenericArg::Const(konst) => GenericArg::Const(konst.clone()),
            })
            .collect();
        let bindings = generic_args
            .bindings
            .iter()
            .map(|binding| {
                let name = binding.name.clone();
                let args =
                    copy_generic_args(&binding.args, from, from_source_map, to, to_source_map);
                let type_ref = binding.type_ref.map(|type_ref| {
                    copy_type_ref(type_ref, from, from_source_map, to, to_source_map)
                });
                let bounds =
                    copy_type_bounds(&binding.bounds, from, from_source_map, to, to_source_map)
                        .collect();
                AssociatedTypeBinding { name, args, type_ref, bounds }
            })
            .collect();
        GenericArgs {
            args,
            has_self_type: generic_args.has_self_type,
            bindings,
            parenthesized: generic_args.parenthesized,
        }
    })
}

fn copy_type_bounds<'a>(
    bounds: &'a [TypeBound],
    from: &'a TypesMap,
    from_source_map: &'a TypesSourceMap,
    to: &'a mut TypesMap,
    to_source_map: &'a mut TypesSourceMap,
) -> impl stdx::thin_vec::TrustedLen<Item = TypeBound> + 'a {
    bounds.iter().map(|bound| copy_type_bound(bound, from, from_source_map, to, to_source_map))
}

fn copy_type_bound(
    bound: &TypeBound,
    from: &TypesMap,
    from_source_map: &TypesSourceMap,
    to: &mut TypesMap,
    to_source_map: &mut TypesSourceMap,
) -> TypeBound {
    let mut copy_path_id = |path: PathId| {
        let new_path = copy_path(&from[path], from, from_source_map, to, to_source_map);
        let new_path_id = to.types.alloc(TypeRef::Path(new_path));
        if let Some(&ptr) = from_source_map.types_map_back.get(path.type_ref()) {
            to_source_map.types_map_back.insert(new_path_id, ptr);
        }
        PathId::from_type_ref_unchecked(new_path_id)
    };

    match bound {
        &TypeBound::Path(path, modifier) => TypeBound::Path(copy_path_id(path), modifier),
        TypeBound::ForLifetime(lifetimes, path) => {
            TypeBound::ForLifetime(lifetimes.clone(), copy_path_id(*path))
        }
        TypeBound::Lifetime(lifetime) => TypeBound::Lifetime(lifetime.clone()),
        TypeBound::Use(use_args) => TypeBound::Use(use_args.clone()),
        TypeBound::Error => TypeBound::Error,
    }
}
