//! Rendering a runtime [`Value`] to a string, matching the typed back end's
//! `to_string` byte-for-byte (the LLVM renderer lives in
//! `prepoly_jit_llvm::codegen`).
//!
//! The rules the typed path fixes and this mirrors:
//!  - a float keeps a trailing `.0` when it is an integral finite value below 1e15;
//!  - an unsigned integer renders in its unsigned decimal range, a signed one in
//!    its signed range;
//!  - an array renders as `[e0, e1, ...]`;
//!  - a nullable renders its value, or `null`;
//!  - a record renders as `T {\n    field: <value>,\n}` and a sum variant as
//!    `T.Variant {\n    field: <value>,\n}` (a field-less variant as bare
//!    `T.Variant`), each field rendered recursively and indented one level so
//!    nested aggregates step in. The field order is the declaration order recovered
//!    from the HIR type, not the value's hash-map order.

use prepoly_hir::types::{RESULT_ERR_ERROR, RESULT_OK_VALUE};
use prepoly_hir::{IntKind, NominalType, Program, Type, TypeKind};

use crate::value::{Value, VariantObj};

/// Render `v`, whose concrete type is `ty`, as the typed back end would.
pub fn format_value(program: &Program, v: &Value, ty: &Type) -> String {
    match ty {
        Type::Str => v.as_str().to_string(),
        Type::Bool => bool_str(v.as_bool()),
        Type::Int(k) => int_str(v.as_int(), *k),
        Type::Float(_) => float_str(v.as_float()),
        // A nullable renders its value when present, else "null".
        Type::Nullable(inner) => {
            if v.is_null() {
                "null".to_string()
            } else {
                format_value(program, v, inner)
            }
        }
        Type::Slice(elem) | Type::Array(elem, _) => {
            let Value::Array(items) = v else {
                return "[]".to_string();
            };
            let rendered: Vec<String> = items
                .borrow()
                .iter()
                .map(|e| format_value(program, e, elem))
                .collect();
            format!("[{}]", rendered.join(", "))
        }
        // A tuple holds its (heterogeneous) elements in the array value; each is
        // rendered with its own element type.
        Type::Tuple(elems) => {
            let Value::Array(items) = v else {
                return "[]".to_string();
            };
            let items = items.borrow();
            let rendered: Vec<String> = elems
                .iter()
                .enumerate()
                .map(|(i, ety)| {
                    let e = items.get(i).cloned().unwrap_or(Value::Void);
                    format_value(program, &e, ety)
                })
                .collect();
            format!("[{}]", rendered.join(", "))
        }
        Type::Record(n) => match v {
            Value::Record(fields) => {
                let layout = record_field_layout(program, n);
                render_named_fields(program, record_header(n), &layout, &fields.borrow())
            }
            _ => n.name.clone(),
        },
        Type::Sum(n) => match v {
            Value::Variant(var) => render_sum(program, n, var),
            _ => n.name.clone(),
        },
        other => other.display(),
    }
}

/// `true`/`false`.
fn bool_str(b: bool) -> String {
    if b { "true" } else { "false" }.to_string()
}

/// Signed or unsigned decimal, per the integer kind.
fn int_str(v: i64, k: IntKind) -> String {
    if int_signed(k) {
        v.to_string()
    } else {
        // The value is normalized (zero-extended) for widths below 64; for uint64
        // the raw bit pattern is the unsigned value.
        (v as u64).to_string()
    }
}

/// A float with the typed path's trailing-`.0` rule.
pub fn float_str(v: f64) -> String {
    if v.is_finite() && v == v.trunc() && v.abs() < 1e15 {
        format!("{v:.1}")
    } else {
        format!("{v}")
    }
}

fn int_signed(k: IntKind) -> bool {
    matches!(k, IntKind::I8 | IntKind::I16 | IntKind::I32 | IntKind::I64)
}

/// Build `<header> {\n    f: <v>,\n}` for the named fields (or `<header> {}` when
/// the type has none). Each field value is rendered recursively and indented one
/// level (four spaces after each newline) so a nested aggregate steps in.
/// The label a record renders under: its nominal name, or `anonymous` for a
/// structural record (an anonymous structure / `T.from` result).
fn record_header(n: &NominalType) -> &str {
    if n.name == prepoly_hir::STRUCTURAL_RECORD_NAME {
        "anonymous"
    } else {
        &n.name
    }
}

fn render_named_fields(
    program: &Program,
    header: &str,
    fields: &[(String, Type)],
    values: &std::collections::HashMap<String, Value>,
) -> String {
    if fields.is_empty() {
        return format!("{header} {{}}");
    }
    let mut out = format!("{header} {{\n");
    for (fname, fty) in fields {
        let fv = values.get(fname).cloned().unwrap_or(Value::Void);
        let rendered = format_value(program, &fv, fty).replace('\n', "\n    ");
        out.push_str(&format!("    {fname}: {rendered},\n"));
    }
    out.push('}');
    out
}

/// Render a sum value as `T.Variant { ... }` (bare `T.Variant` when field-less).
fn render_sum(program: &Program, n: &NominalType, var: &VariantObj) -> String {
    let header = format!("{}.{}", n.name, var.variant);
    let fields = variant_field_layout(program, n, &var.variant);
    if fields.is_empty() {
        header
    } else {
        render_named_fields(program, &header, &fields, &var.fields.borrow())
    }
}

/// The `(field name, concrete type)` of each record field in declaration order.
/// A constructed record carries each field's concrete type in its substitution;
/// a bare reference falls back to the declared type. An unrecognized nominal (a
/// structural boundary record) renders its substitution in sorted-name order.
fn record_field_layout(program: &Program, n: &NominalType) -> Vec<(String, Type)> {
    if let Some(info) = program.type_by_id(n.id)
        && let TypeKind::Record { fields, .. } = &info.kind
    {
        return fields
            .iter()
            .filter_map(|f| {
                let ty = n
                    .substitution
                    .get(&f.name)
                    .cloned()
                    .or_else(|| f.resolved_ty.clone())?;
                Some((f.name.clone(), ty))
            })
            .collect();
    }
    n.substitution
        .iter()
        .map(|(k, t)| (k.to_string(), t.clone()))
        .collect()
}

/// The `(field name, concrete type)` of the named variant's fields in declaration
/// order. `Result` is handled directly (its payloads live in the nominal
/// substitution under `Ok.value` / `Err.error`).
fn variant_field_layout(program: &Program, n: &NominalType, variant: &str) -> Vec<(String, Type)> {
    if n.is_result_type() {
        let key = if variant == "Ok" {
            RESULT_OK_VALUE
        } else {
            RESULT_ERR_ERROR
        };
        let fname = if variant == "Ok" { "value" } else { "error" };
        return match n.substitution.get(key) {
            Some(t) => vec![(fname.to_string(), t.clone())],
            None => Vec::new(),
        };
    }
    let Some(info) = program.type_by_id(n.id) else {
        return Vec::new();
    };
    let TypeKind::Sum { variants } = &info.kind else {
        return Vec::new();
    };
    let Some(v) = variants.iter().find(|v| v.name == variant) else {
        return Vec::new();
    };
    v.fields
        .iter()
        .filter_map(|f| {
            // A field's concrete type may be carried in the substitution (keyed
            // `Variant.field`) when it was inferred at construction; otherwise the
            // declared type is concrete enough to render.
            let ty = n
                .substitution
                .get(&format!("{variant}.{}", f.name))
                .cloned()
                .or_else(|| f.resolved_ty.clone())?;
            Some((f.name.clone(), ty))
        })
        .collect()
}
