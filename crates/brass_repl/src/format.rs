//! Rendering a runtime [`Value`] to a string, matching the typed back end's
//! `to_string` byte-for-byte (the LLVM renderer lives in
//! `brass_jit_llvm::codegen`).
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
//!    nested aggregates step in. Which fields render, in what order, at what
//!    types is not decided here: both back ends resolve that through
//!    `brass_engine::render_record_fields` / `render_variant_fields`, so the
//!    field decision cannot drift between them.

use brass_hir::{IntKind, NominalType, Program, Type};

use crate::value::{MAX_VALUE_DEPTH, Value, VariantObj};

/// Render `v`, whose concrete type is `ty`, as the typed back end would. Errs
/// when the value nests deeper than [`MAX_VALUE_DEPTH`] -- with self-referential
/// record types a value can hold a reference cycle, which would otherwise recurse
/// forever.
pub fn format_value(program: &Program, v: &Value, ty: &Type) -> Result<String, String> {
    format_value_at(program, v, ty, 0)
}

fn format_value_at(
    program: &Program,
    v: &Value,
    ty: &Type,
    depth: usize,
) -> Result<String, String> {
    if depth > MAX_VALUE_DEPTH {
        return Err("value depth exceeded while rendering (cyclic value?)".into());
    }
    Ok(match ty {
        Type::Str => v.as_str().to_string(),
        Type::Bool => bool_str(v.as_bool()),
        Type::Int(k) => int_str(v.as_int(), *k),
        Type::Float(_) => float_str(v.as_float()),
        // A nullable renders its value when present, else "null".
        Type::Nullable(inner) => {
            if v.is_null() {
                "null".to_string()
            } else {
                format_value_at(program, v, inner, depth + 1)?
            }
        }
        Type::Slice(elem) | Type::Array(elem, _) => {
            let Value::Array(items) = v else {
                return Ok("[]".to_string());
            };
            let rendered: Vec<String> = items
                .borrow()
                .iter()
                .map(|e| format_value_at(program, e, elem, depth + 1))
                .collect::<Result<_, _>>()?;
            format!("[{}]", rendered.join(", "))
        }
        // A tuple holds its (heterogeneous) elements in the array value; each is
        // rendered with its own element type.
        Type::Tuple(elems) => {
            let Value::Array(items) = v else {
                return Ok("[]".to_string());
            };
            let items = items.borrow();
            let rendered: Vec<String> = elems
                .iter()
                .enumerate()
                .map(|(i, ety)| {
                    let e = items.get(i).cloned().unwrap_or(Value::Void);
                    format_value_at(program, &e, ety, depth + 1)
                })
                .collect::<Result<_, _>>()?;
            format!("[{}]", rendered.join(", "))
        }
        Type::Record(n) => match v {
            Value::Record(fields) => {
                // An unavailable layout renders as the bare `T {}`, like the JIT.
                let layout = brass_engine::render_record_fields(program, n).unwrap_or_default();
                render_named_fields(program, record_header(n), &layout, &fields.borrow(), depth)?
            }
            _ => n.name.clone(),
        },
        Type::Sum(n) => match v {
            Value::Variant(var) => render_sum(program, n, var, depth)?,
            _ => n.name.clone(),
        },
        other => other.display(),
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

/// A float with the typed path's trailing-`.0` rule.
pub use brass_utils::float_str;

/// Build `<header> {\n    f: <v>,\n}` for the named fields (or `<header> {}` when
/// the type has none). Each field value is rendered recursively and indented one
/// level (four spaces after each newline) so a nested aggregate steps in.
/// The label a record renders under: its nominal name, or `anonymous` for a
/// structural record (an anonymous structure / `T.from` result).
fn record_header(n: &NominalType) -> &str {
    if n.name == brass_hir::STRUCTURAL_RECORD_NAME {
        "anonymous"
    } else {
        &n.name
    }
}

fn render_named_fields(
    program: &Program,
    header: &str,
    fields: &[(String, Type)],
    values: &fxhash::FxHashMap<String, Value>,
    depth: usize,
) -> Result<String, String> {
    if fields.is_empty() {
        return Ok(format!("{header} {{}}"));
    }
    let mut out = format!("{header} {{\n");
    for (fname, fty) in fields {
        let fv = values.get(fname).cloned().unwrap_or(Value::Void);
        let rendered = format_value_at(program, &fv, fty, depth + 1)?.replace('\n', "\n    ");
        // A string-typed field value renders QUOTED (a present nullable string
        // too; `null` stays bare), so the struct output distinguishes the
        // string "1" from the number 1 -- mirroring the JIT renderer.
        let quoted = match fty {
            Type::Str => true,
            Type::Nullable(inner) if matches!(**inner, Type::Str) => !fv.is_null(),
            _ => false,
        };
        if quoted {
            out.push_str(&format!("    {fname}: \"{rendered}\",\n"));
        } else {
            out.push_str(&format!("    {fname}: {rendered},\n"));
        }
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
) -> Result<String, String> {
    let Some((_tag, fields)) = brass_engine::render_variant_fields(program, n, &var.variant) else {
        return Ok(n.name.clone());
    };
    let header = format!("{}.{}", n.name, var.variant);
    if fields.is_empty() {
        Ok(header)
    } else {
        render_named_fields(program, &header, &fields, &var.fields.borrow(), depth)
    }
}
