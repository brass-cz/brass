//! Sufficient absence proof for a method's shared inference effects. Unknown
//! footprints are retained; this does not simulate solving or trust trace data.

use brass_hir::{MethodInfo, Program, Type, TypeInfo, TypeKind};
use fxhash::FxHashSet as HashSet;

/// Why an unused method must still prepare its owner's shared component.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SharedObligation {
    /// An open field, slot or transitive layout can be constrained by any method.
    OpenLayout,
    /// A record method contributes an open parameter or return scheme.
    OpenSignature,
    /// Calls, globals, captures or mutation lack a static absence proof.
    UnclassifiedEffects,
}

/// Prove absence of shared writes for a closed method, or retain it with a
/// reason. Keyed templates are handled by their specialization authority.
pub(super) fn signature_obligation(
    program: &Program,
    owner: &TypeInfo,
    method: &MethodInfo,
) -> Option<SharedObligation> {
    method.decl.body.as_ref()?;
    if !closed(program, &owner.type_ref(), &mut HashSet::default()) {
        return Some(SharedObligation::OpenLayout);
    }
    if !owner.is_sum()
        && (method
            .signature
            .params
            .iter()
            .filter(|p| p.name != "self")
            .any(|p| {
                p.resolved_ty
                    .as_ref()
                    .is_none_or(|t| !closed(program, t, &mut HashSet::default()))
            })
            || method
                .signature
                .ret_ty
                .as_ref()
                .is_none_or(|t| !closed(program, t, &mut HashSet::default())))
    {
        return Some(SharedObligation::OpenSignature);
    }
    None
}

/// Prove a method using the catalog's transitive shared-footprint certificate.
/// Records require a clean shared declaration walk. Closed sums have no record
/// co owner and use the external-effect projection; borrowed layouts, globals,
/// captures and unresolved callbacks still retain them.
pub fn shared_obligation(
    index: &super::ItemIndex<'_>,
    owner: &TypeInfo,
    method: &MethodInfo,
) -> Option<SharedObligation> {
    method.decl.body.as_ref()?;
    index.observe_method(&method.signature.name);
    let started = super::cost::start();
    let effects = index.effect_time.get();
    let result = signature_obligation(index.program, owner, method).or_else(|| {
        let Some(keys) = index
            .methods
            .get(&(owner.id, method.signature.name.as_str()))
        else {
            return Some(SharedObligation::UnclassifiedEffects);
        };
        keys.iter()
            .any(|key| !super::effects::summary(index, *key, owner.is_sum()).is_clean())
            .then_some(SharedObligation::UnclassifiedEffects)
    });
    if let Some(started) = started {
        index.certificate_time.set(
            index.certificate_time.get()
                + started
                    .elapsed()
                    .saturating_sub(index.effect_time.get() - effects),
        );
    }
    result
}

/// Whether an abstract receiver frame has a fully declared field layout.
pub(super) fn closed_layout(program: &Program, ty: &Type) -> bool {
    closed(program, ty, &mut HashSet::default())
}

/// Inspect declaration fields as well as substitutions. Recursive closed SCCs
/// terminate, but every member's fields are inspected before certification.
fn closed(program: &Program, ty: &Type, visiting: &mut HashSet<Type>) -> bool {
    match ty {
        Type::Unknown(_) | Type::SelfType => false,
        Type::Array(t, _)
        | Type::Slice(t)
        | Type::Nullable(t)
        | Type::ConstOf(t)
        | Type::Ref(t)
        | Type::Mut(t) => closed(program, t, visiting),
        Type::Tuple(ts) => ts.iter().all(|t| closed(program, t, visiting)),
        Type::Fun(ps, ret) => ps
            .iter()
            .chain(std::iter::once(ret.as_ref()))
            .all(|t| closed(program, t, visiting)),
        Type::Record(n) | Type::Sum(n) => {
            let Some(info) = program.type_by_id(n.id) else {
                return false;
            };
            // HIR substitutions contain instantiated real field types. They
            // take precedence over the open variables in the base declaration.
            if !visiting.insert(ty.clone()) {
                return true;
            }
            let groups = match &info.kind {
                TypeKind::Record { fields, .. } => vec![(None, fields)],
                TypeKind::Sum { variants } => variants
                    .iter()
                    .map(|v| (Some(&v.name), &v.fields))
                    .collect(),
            };
            let result = groups.iter().all(|(variant, fields)| {
                fields.iter().all(|f| {
                    let key = variant.map_or_else(|| f.name.clone(), |v| format!("{v}.{}", f.name));
                    n.substitution
                        .get(&key)
                        .cloned()
                        .or_else(|| super::layout::field(program, info, f))
                        .is_some_and(|decl| closed(program, &decl, visiting))
                })
            });
            visiting.remove(ty);
            result
        }
        _ => true,
    }
}

/// Whether an annotation can expose a declaration-owned field variable. A
/// substitution carrying a private unknown is safe: it is an instance cell,
/// unlike an unpinned nominal field. Recursive layouts preserve that distinction.
pub(super) fn borrows_layout(index: &super::ItemIndex<'_>, ty: &Type) -> bool {
    let program = index.program;
    let shared = index.shared_variables.get_or_init(|| {
        program
            .types
            .values()
            .flat_map(|owner| {
                let groups = match &owner.kind {
                    TypeKind::Record { fields, .. } => vec![fields],
                    TypeKind::Sum { variants } => variants.iter().map(|v| &v.fields).collect(),
                };
                groups
                    .into_iter()
                    .flatten()
                    .filter_map(|f| f.resolved_ty.as_ref())
                    .flat_map(brass_hir::type_vars)
            })
            .filter(|id| *id != brass_hir::INFER_VAR)
            .collect()
    });
    fn visit(
        program: &Program,
        ty: &Type,
        shared: &HashSet<u32>,
        seen: &mut HashSet<Type>,
    ) -> bool {
        match ty {
            Type::Unknown(id) => shared.contains(id),
            Type::SelfType => false,
            Type::Array(t, _)
            | Type::Slice(t)
            | Type::Nullable(t)
            | Type::ConstOf(t)
            | Type::Ref(t)
            | Type::Mut(t) => visit(program, t, shared, seen),
            Type::Tuple(ts) => ts.iter().any(|t| visit(program, t, shared, seen)),
            Type::Fun(ps, ret) => ps
                .iter()
                .chain(std::iter::once(ret.as_ref()))
                .any(|t| visit(program, t, shared, seen)),
            Type::Record(n) if n.id == brass_hir::types::STRUCTURAL_RECORD_ID => n
                .substitution
                .iter()
                .any(|(_, field)| visit(program, field, shared, seen)),
            Type::Record(n) | Type::Sum(n) if seen.insert(ty.clone()) => {
                let Some(info) = program.type_by_id(n.id) else {
                    return true;
                };
                let groups = match &info.kind {
                    TypeKind::Record { fields, .. } => vec![(None, fields)],
                    TypeKind::Sum { variants } => variants
                        .iter()
                        .map(|v| (Some(&v.name), &v.fields))
                        .collect(),
                };
                let result = groups.iter().any(|(variant, fields)| {
                    fields.iter().any(|f| {
                        let key =
                            variant.map_or_else(|| f.name.clone(), |v| format!("{v}.{}", f.name));
                        n.substitution
                            .get(&key)
                            .cloned()
                            .or_else(|| super::layout::field(program, info, f))
                            .is_none_or(|field| visit(program, &field, shared, seen))
                    })
                });
                seen.remove(ty);
                result
            }
            _ => false,
        }
    }
    visit(program, ty, shared, &mut HashSet::default())
}
