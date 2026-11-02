//! Declaration-level rendering policy shared by checking and execution.

use crate::{Program, Type, TypeKind};

/// Human text prefers `display`; structural text always uses effective `debug`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RenderForm {
    /// Top-level print, interpolation and string conversion.
    Display,
    /// Explicit debug and every child of a builtin structural renderer.
    Debug,
}

/// User method preferred by interpolation and print over structural rendering.
pub const DISPLAY_METHOD: &str = "display";

/// The nominal method selected for this form, before instance specialization.
/// Nullable and passing-mode wrappers expose their inner type's policy; callers
/// preserve the null branch. Primitive formatting stays builtin, including raw
/// display strings and quoted debug strings.
pub fn render_method(program: &Program, ty: &Type, form: RenderForm) -> Option<&'static str> {
    let ty = crate::peel_modes(ty);
    if let Type::Nullable(inner) = ty {
        return render_method(program, inner, form);
    }
    let (Type::Record(n) | Type::Sum(n)) = ty else {
        return None;
    };
    let info = program.type_by_id(n.id)?;
    let declared = |name| match &info.kind {
        TypeKind::Record { methods, .. } => methods.contains_key(name),
        TypeKind::Sum { variants } => variants.iter().any(|v| v.methods.contains_key(name)),
    };
    if form == RenderForm::Display && declared(DISPLAY_METHOD) {
        Some(DISPLAY_METHOD)
    } else if declared("debug") {
        Some("debug")
    } else {
        None
    }
}

/// Whether rendering can run user code at any structural depth. Custom methods
/// own their children's rendering; builtin nominal layouts inspect every field,
/// using concrete substitutions before declaration types. Recursive layouts are
/// visited once per concrete type so generic fields retain their instance policy.
pub fn rendering_runs_code(program: &Program, ty: &Type, form: RenderForm) -> bool {
    fn visit(program: &Program, ty: &Type, form: RenderForm, seen: &mut Vec<Type>) -> bool {
        if render_method(program, ty, form).is_some() {
            return true;
        }
        match crate::peel_modes(ty) {
            Type::Nullable(t) => visit(program, t, form, seen),
            Type::Slice(t) | Type::Array(t, _) => visit(program, t, RenderForm::Debug, seen),
            Type::Tuple(ts) => ts
                .iter()
                .any(|t| visit(program, t, RenderForm::Debug, seen)),
            Type::Record(n) | Type::Sum(n) if !seen.contains(ty) => {
                seen.push(ty.clone());
                let Some(info) = program.type_by_id(n.id) else {
                    return n
                        .substitution
                        .iter()
                        .any(|(_, t)| visit(program, t, RenderForm::Debug, seen));
                };
                let mut field_runs = |key: &str, field: &crate::FieldInfo| {
                    n.substitution
                        .get(key)
                        .or(field.resolved_ty.as_ref())
                        .is_some_and(|t| visit(program, t, RenderForm::Debug, seen))
                };
                match &info.kind {
                    TypeKind::Record { fields, .. } => {
                        fields.iter().any(|f| field_runs(&f.name, f))
                    }
                    TypeKind::Sum { variants } => variants.iter().any(|v| {
                        v.fields
                            .iter()
                            .any(|f| field_runs(&format!("{}.{}", v.name, f.name), f))
                    }),
                }
            }
            _ => false,
        }
    }
    visit(program, ty, form, &mut Vec::new())
}
