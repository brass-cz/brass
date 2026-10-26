//! Resolution of the reflective conversion `infer.from(x)`: which concrete
//! conversion (if any) the call reaches for a given (source, target) pair.
//!
//! The decision is deliberately NARROWER than the set of `T.from` forms the
//! language exposes directly: the reflective path follows the from/parse
//! partition (from = value conversion, parse = interpretation from text,
//! interpolation = formatting to text), so a JSON string can never silently
//! become a number and a JSON number can never silently become a string.
//! `Absent` means no conversion exists for the pair; the specializer turns it
//! into a runtime decode error raised at the decoder call.

use brass_hir::{FloatKind, IntKind, Program, Type, TypeKind};
use brass_parser::ast::TypeExpr;

/// Every numeric type: the sources a numeric key converts from.
const NUMERIC_TYPES: [Type; 10] = [
    Type::Int(IntKind::I8),
    Type::Int(IntKind::I16),
    Type::Int(IntKind::I32),
    Type::Int(IntKind::I64),
    Type::Int(IntKind::U8),
    Type::Int(IntKind::U16),
    Type::Int(IntKind::U32),
    Type::Int(IntKind::U64),
    Type::Float(FloatKind::F32),
    Type::Float(FloatKind::F64),
];

/// How `infer.from(x)` resolves for source type `from` and key (target) `to`.
#[derive(Clone, Debug, PartialEq)]
pub enum InferFrom {
    /// The source already is the target; the call is the argument itself.
    Identity,
    /// Resolves to the static call `<qualifier>.from(x)`. `fallible` when
    /// that call returns a Result (`intN.from` is range-checked; a user
    /// `from` declared `-> T!`) rather than the target value itself.
    Static { qualifier: String, fallible: bool },
    /// No conversion exists for this pair.
    Absent(String),
}

/// Resolve `infer.from(x)` for a source value of type `from` at key `to`.
pub fn infer_from(program: &Program, from: &Type, to: &Type) -> InferFrom {
    let from = brass_hir::peel_modes(from);
    match to {
        Type::Nullable(inner) => infer_from(program, from, inner),
        _ if from == to => InferFrom::Identity,
        Type::Int(k) => match from {
            Type::Int(_) | Type::Float(_) => InferFrom::Static {
                qualifier: k.name().to_string(),
                fallible: true,
            },
            _ => absent(from, to),
        },
        Type::Float(k) => match from {
            Type::Int(_) | Type::Float(_) => InferFrom::Static {
                qualifier: k.name().to_string(),
                fallible: false,
            },
            _ => absent(from, to),
        },
        // Text and booleans accept only their own type (handled by the Identity
        // case above); number->string is interpolation, not `from`.
        Type::Str | Type::Bool => absent(from, to),
        // A nominal target resolves through a user-defined static `from` method
        // when one exists (see `nominal_from`).
        Type::Record(_) | Type::Sum(_) => {
            nominal_from(program, to).unwrap_or_else(|| absent(from, to))
        }
        _ => absent(from, to),
    }
}

/// How `infer.from(x)` resolves at key `to` for a source whose type is only
/// known per instance: the dispatch a decoder compiles when its template
/// cannot name the source type (a local, a field, a literal, a call).
///
/// `arms` holds, in test order, every source type with a resolution other
/// than `otherwise`, each with the resolution [`infer_from`] gives it: the
/// key's own type (the identity) and, at a numeric key, every other numeric
/// type. `otherwise` is the resolution of every remaining source -- the
/// nominal key's own static `from` when it declares one, else `Absent` (a
/// runtime decode error). A source therefore resolves through the dispatch
/// exactly as it would through [`infer_from`] with its type in hand.
pub struct InferFromDispatch {
    pub arms: Vec<(Type, InferFrom)>,
    pub otherwise: InferFrom,
}

/// Build the per-instance dispatch of `infer.from(x)` at key `to`.
pub fn infer_from_dispatch(program: &Program, to: &Type) -> InferFromDispatch {
    let target = match to {
        Type::Nullable(inner) => inner,
        other => other,
    };
    let numeric_sources = matches!(target, Type::Int(_) | Type::Float(_))
        .then_some(NUMERIC_TYPES)
        .into_iter()
        .flatten()
        .filter(|source| source != target);
    let arms = std::iter::once(target.clone())
        .chain(numeric_sources)
        .filter_map(|source| match infer_from(program, &source, to) {
            InferFrom::Absent(_) => None,
            resolution => Some((source, resolution)),
        })
        .collect();
    let otherwise = nominal_from(program, target)
        .unwrap_or_else(|| InferFrom::Absent(format!("no conversion to `{}`", target.display())));
    InferFromDispatch { arms, otherwise }
}

/// A nominal target's user-defined static `from`, when it declares one. The
/// builtin structural record-from is deliberately NOT reachable reflectively
/// (it yields null on a miss rather than a decode error).
fn nominal_from(program: &Program, to: &Type) -> Option<InferFrom> {
    let (Type::Record(n) | Type::Sum(n)) = to else {
        return None;
    };
    let from_method = program.type_by_id(n.id).and_then(|info| match &info.kind {
        TypeKind::Record { methods, .. } => methods.get("from"),
        TypeKind::Sum { variants } => variants.iter().find_map(|v| v.methods.get("from")),
    })?;
    Some(InferFrom::Static {
        qualifier: to.type_name(),
        fallible: matches!(from_method.decl.ret, Some(TypeExpr::Fallible(..))),
    })
}

fn absent(from: &Type, to: &Type) -> InferFrom {
    InferFrom::Absent(format!(
        "no conversion from `{}` to `{}`",
        from.display(),
        to.display()
    ))
}
