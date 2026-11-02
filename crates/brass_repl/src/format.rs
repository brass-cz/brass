//! Rendering a runtime [`Value`] to a string, matching the typed back end's
//! `to_string` byte-for-byte (the LLVM renderer lives in
//! `brass_jit_llvm::codegen`).
//!
//! The rules the typed path fixes and this mirrors:
//!  - float32 uses its own shortest round-trip form, with `.0` for integral values;
//!    float64 keeps `.0` for integral finite values below 1e15;
//!  - an unsigned integer renders in its unsigned decimal range, a signed one in
//!    its signed range;
//!  - an array or tuple renders as `[e0, e1, ...]`, its elements in effective debug form;
//!  - a nullable renders its value, or `null`;
//!  - a record renders as `T {\n    field: <value>,\n}` and a sum variant as
//!    `T.Variant {\n    field: <value>,\n}` (a field-less variant as bare
//!    `T.Variant`), each field rendered recursively and indented one level so
//!    nested aggregates step in; a string field renders quoted and escaped,
//!    and a function-valued field as `<opaque>`. Which fields render, in what
//!    order, at what types is not decided here: both back ends resolve that
//!    through `brass_engine::render_record_fields` / `render_variant_fields`,
//!    so the field decision cannot drift between them.

use brass_engine::render::{RenderForm, resolve_renderer};
use brass_hir::{IntKind, NominalType, Program, Type};

use crate::value::{MAX_VALUE_DEPTH, Value, VariantObj};

/// Render without executing user code, for builtin numeric conversions.
/// A custom renderer requires [`format_with_renderer`] and returns an error
/// here. Values deeper than [`MAX_VALUE_DEPTH`] also return an error, bounding
/// structural recursion through cyclic values.
pub fn format_value(program: &Program, v: &Value, ty: &Type) -> Result<String, String> {
    format_with_renderer(program, v, ty, RenderForm::Display, &mut |symbol, _| {
        Err(format!("renderer `{symbol}` needs an interpreter"))
    })
}

/// Render with an interpreter callback for the shared resolver's user methods.
/// No aggregate borrow survives a callback: rendering can execute ordinary code.
pub fn format_with_renderer(
    program: &Program,
    v: &Value,
    ty: &Type,
    form: RenderForm,
    call: &mut impl FnMut(&str, &Value) -> Result<String, String>,
) -> Result<String, String> {
    format_value_at(program, v, ty, form, 0, call)
}

fn format_value_at(
    program: &Program,
    v: &Value,
    ty: &Type,
    form: RenderForm,
    depth: usize,
    call: &mut impl FnMut(&str, &Value) -> Result<String, String>,
) -> Result<String, String> {
    if depth > MAX_VALUE_DEPTH {
        return Err("value depth exceeded while rendering (cyclic value?)".into());
    }
    if let Type::Nullable(inner) = ty {
        return if v.is_null() {
            Ok("null".into())
        } else {
            format_value_at(program, v, inner, form, depth + 1, call)
        };
    }
    if let Some(symbol) = resolve_renderer(program, ty, form) {
        return call(&symbol, v);
    }
    Ok(match ty {
        Type::Str if form == RenderForm::Debug => brass_utils::debug_quote(v.as_str()),
        Type::Str => v.as_str().to_string(),
        Type::Bool => bool_str(v.as_bool()),
        Type::Int(k) => int_str(v.as_int(), *k),
        Type::Float(brass_hir::FloatKind::F32) => brass_utils::float32_str(v.as_float() as f32),
        Type::Float(brass_hir::FloatKind::F64) => float_str(v.as_float()),
        Type::Slice(elem) | Type::Array(elem, _) => {
            let Value::Array(items) = v else {
                return Ok("[]".to_string());
            };
            let len = items.borrow().len();
            let rendered: Vec<String> = (0..len)
                .map(|i| {
                    let value = items.borrow().get(i).cloned().unwrap_or(Value::Void);
                    format_value_at(program, &value, elem, RenderForm::Debug, depth + 1, call)
                })
                .collect::<Result<_, _>>()?;
            format!("[{}]", rendered.join(", "))
        }
        // A tuple holds its (heterogeneous) elements in the array value; each is
        // rendered with its own element type.
        Type::Tuple(elems) => {
            let Value::Array(items) = v else {
                return Ok("[]".to_string());
            };
            let rendered: Vec<String> = elems
                .iter()
                .enumerate()
                .map(|(i, ety)| {
                    let e = items.borrow().get(i).cloned().unwrap_or(Value::Void);
                    format_value_at(program, &e, ety, RenderForm::Debug, depth + 1, call)
                })
                .collect::<Result<_, _>>()?;
            format!("[{}]", rendered.join(", "))
        }
        Type::Record(n) => match v {
            Value::Record(fields) => {
                // An unavailable layout renders as the bare `T {}`, like the JIT.
                let layout = brass_engine::render_record_fields(program, n).unwrap_or_default();
                render_named_fields(program, record_header(n), &layout, fields, depth, call)?
            }
            _ => n.name.clone(),
        },
        Type::Sum(n) => match v {
            Value::Variant(var) => render_sum(program, n, var, depth, call)?,
            _ => n.name.clone(),
        },
        // A value with no rendering of its own -- a function-valued field of
        // a rendered record -- shows as the same placeholder the JIT emits.
        _ => "<opaque>".to_string(),
    })
}

/// `true`/`false`.
fn bool_str(b: bool) -> String {
    if b { "true" } else { "false" }.to_string()
}

/// Signed or unsigned decimal, per the integer kind.
fn int_str(v: i64, k: IntKind) -> String {
    if k.is_signed() {
        v.to_string()
    } else {
        // The value is normalized (zero-extended) for widths below 64; for uint64
        // the raw bit pattern is the unsigned value.
        (v as u64).to_string()
    }
}

/// A float64 with the typed path's trailing-`.0` rule.
pub use brass_utils::float_str;

/// The label a record renders under: its nominal name, or `anonymous` for a
/// structural record (an anonymous structure / `T.from` result).
fn record_header(n: &NominalType) -> &str {
    if n.id == brass_hir::STRUCTURAL_RECORD_ID {
        "anonymous"
    } else {
        &n.name
    }
}

/// Build `<header> {\n    f: <v>,\n}` for the named fields (or `<header> {}` when
/// the type has none). Each field value is rendered recursively and indented one
/// level (four spaces after each newline) so a nested aggregate steps in.
fn render_named_fields(
    program: &Program,
    header: &str,
    fields: &[(String, Type)],
    values: &std::cell::RefCell<fxhash::FxHashMap<String, Value>>,
    depth: usize,
    call: &mut impl FnMut(&str, &Value) -> Result<String, String>,
) -> Result<String, String> {
    if fields.is_empty() {
        return Ok(format!("{header} {{}}"));
    }
    let mut out = format!("{header} {{\n");
    for (fname, fty) in fields {
        let fv = values.borrow().get(fname).cloned().unwrap_or(Value::Void);
        let rendered = format_value_at(program, &fv, fty, RenderForm::Debug, depth + 1, call)?
            .replace('\n', "\n    ");
        out.push_str(&format!("    {fname}: {rendered},\n"));
    }
    out.push('}');
    Ok(out)
}

/// Render a sum value as `T.Variant { ... }` (bare `T.Variant` when field-less).
/// A variant the shared resolver cannot resolve renders as the bare type name,
/// which is where the JIT's unknown-tag default lands for the same value.
fn render_sum(
    program: &Program,
    n: &NominalType,
    var: &VariantObj,
    depth: usize,
    call: &mut impl FnMut(&str, &Value) -> Result<String, String>,
) -> Result<String, String> {
    let Some((_tag, fields)) = brass_engine::render_variant_fields(program, n, &var.variant) else {
        return Ok(n.name.clone());
    };
    let header = format!("{}.{}", n.name, var.variant);
    if fields.is_empty() {
        Ok(header)
    } else {
        render_named_fields(program, &header, &fields, &var.fields, depth, call)
    }
}
