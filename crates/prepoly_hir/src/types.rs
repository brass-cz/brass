//! The Prepoly type representation (DESIGN.md 5.1, 6.2) and its mapping to the
//! runtime value tags. `Unknown` models the parts inference leaves open, which
//! the JIT handles via runtime tag dispatch (deferred monomorphization).

use std::collections::BTreeMap;
use std::fmt;

use prepoly_parser::ast::TypeExpr;

pub const RESULT_TYPE_ID: i32 = 0;
pub const RESULT_TYPE_NAME: &str = "Result";
pub const RESULT_OK_VALUE: &str = "Ok.value";
pub const RESULT_ERR_ERROR: &str = "Err.error";

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum IntKind {
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
}

impl IntKind {
    pub fn name(self) -> &'static str {
        match self {
            IntKind::I8 => "int8",
            IntKind::I16 => "int16",
            IntKind::I32 => "int32",
            IntKind::I64 => "int64",
            IntKind::U8 => "uint8",
            IntKind::U16 => "uint16",
            IntKind::U32 => "uint32",
            IntKind::U64 => "uint64",
        }
    }
    pub fn from_name(s: &str) -> Option<IntKind> {
        Some(match s {
            "int8" => IntKind::I8,
            "int16" => IntKind::I16,
            "int32" => IntKind::I32,
            "int64" => IntKind::I64,
            "uint8" => IntKind::U8,
            "uint16" => IntKind::U16,
            "uint32" => IntKind::U32,
            "uint64" => IntKind::U64,
            _ => return None,
        })
    }
    /// Runtime tag value (matches prepoly_runtime::rt).
    pub fn tag(self) -> i64 {
        match self {
            IntKind::I8 => 8,
            IntKind::I16 => 9,
            IntKind::I32 => 10,
            IntKind::I64 => 11,
            IntKind::U8 => 12,
            IntKind::U16 => 13,
            IntKind::U32 => 14,
            IntKind::U64 => 15,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FloatKind {
    F32,
    F64,
}

impl FloatKind {
    pub fn name(self) -> &'static str {
        match self {
            FloatKind::F32 => "float32",
            FloatKind::F64 => "float64",
        }
    }
    pub fn tag(self) -> i64 {
        match self {
            FloatKind::F32 => 16,
            FloatKind::F64 => 17,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Type {
    Bool,
    Int(IntKind),
    Float(FloatKind),
    Str,
    Void,
    Never,
    Record(NominalType),
    Sum(NominalType),
    Array(Box<Type>, usize),
    Slice(Box<Type>),
    Fun(Vec<Type>, Box<Type>),
    Nullable(Box<Type>),
    ConstOf(Box<Type>),
    Unknown(u32),
    SelfType,
}

/// A nominal type substitution keyed by lowered member paths.
///
/// For the built-in `Result`, `Ok.value` and `Err.error` carry the statically
/// known payload types described by DESIGN.md 6.2.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Substitution {
    entries: BTreeMap<String, Type>,
}

impl Substitution {
    pub fn empty() -> Self {
        Self::default()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn insert(&mut self, key: impl Into<String>, ty: Type) {
        self.entries.insert(key.into(), ty);
    }

    pub fn get(&self, key: &str) -> Option<&Type> {
        self.entries.get(key)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&str, &Type)> {
        self.entries.iter().map(|(key, ty)| (key.as_str(), ty))
    }
}

/// A lowered nominal type reference. `id` is the runtime type id assigned by
/// HIR lowering; `name` is retained for diagnostics and current lookup tables.
#[derive(Clone, Debug, PartialEq)]
pub struct NominalType {
    pub id: i32,
    pub name: String,
    pub substitution: Substitution,
}

impl NominalType {
    pub fn new(id: i32, name: impl Into<String>) -> Self {
        Self {
            id,
            name: name.into(),
            substitution: Substitution::empty(),
        }
    }

    pub fn with_substitution(id: i32, name: impl Into<String>, substitution: Substitution) -> Self {
        Self {
            id,
            name: name.into(),
            substitution,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn is_name(&self, name: &str) -> bool {
        self.name == name
    }

    pub fn same_nominal(&self, other: &Self) -> bool {
        self.id == other.id
            && (self.id >= 0 || self.name == other.name)
            && self.substitution == other.substitution
    }

    pub fn is_result_type(&self) -> bool {
        self.is_name(RESULT_TYPE_NAME)
    }

    pub fn result_payloads(&self) -> Option<(&Type, &Type)> {
        if !self.is_result_type() {
            return None;
        }
        Some((
            self.substitution.get(RESULT_OK_VALUE)?,
            self.substitution.get(RESULT_ERR_ERROR)?,
        ))
    }
}

impl fmt::Display for NominalType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some((ok, err)) = self.result_payloads() {
            return write!(f, "Result<{}, {}>", ok.display(), err.display());
        }
        if self.substitution.is_empty() {
            return f.write_str(&self.name);
        }
        let entries = self
            .substitution
            .iter()
            .map(|(key, ty)| format!("{key}={}", ty.display()))
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "{}<{entries}>", self.name)
    }
}

/// The HIR kind of a user-defined nominal type name.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NominalKind {
    Record,
    Sum,
}

/// HIR metadata required to resolve a nominal type annotation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NominalInfo {
    pub id: i32,
    pub kind: NominalKind,
}

impl NominalInfo {
    pub fn record(id: i32) -> Self {
        Self {
            id,
            kind: NominalKind::Record,
        }
    }

    pub fn sum(id: i32) -> Self {
        Self {
            id,
            kind: NominalKind::Sum,
        }
    }
}

impl Type {
    pub fn result(ok: Type, err: Type) -> Self {
        let mut substitution = Substitution::empty();
        substitution.insert(RESULT_OK_VALUE, ok);
        substitution.insert(RESULT_ERR_ERROR, err);
        Type::Sum(NominalType::with_substitution(
            RESULT_TYPE_ID,
            RESULT_TYPE_NAME,
            substitution,
        ))
    }

    pub fn null() -> Self {
        Type::Nullable(Box::new(Type::Never))
    }

    pub fn is_unknown(&self) -> bool {
        matches!(self, Type::Unknown(_))
    }

    pub fn is_null(&self) -> bool {
        matches!(self, Type::Nullable(inner) if matches!(inner.as_ref(), Type::Never))
    }

    pub fn is_result_type(&self) -> bool {
        matches!(self, Type::Sum(name) if name.is_result_type())
    }

    /// The compile-time truthiness of a condition value of this (resolved) type,
    /// when it is fixed by the type alone. A `bool` or a non-trivial nullable
    /// depends on the runtime value, so it is `None`. A bare `null` (`never?`,
    /// inhabited only by null) is always false; any other non-nullable value is
    /// always true. Used to fold a statically-known `if`: the type checker
    /// tolerates the unreachable arm and the back end skips emitting it.
    pub fn static_truthiness(&self) -> Option<bool> {
        match self {
            Type::Bool | Type::Unknown(_) | Type::Never => None,
            Type::Nullable(inner) => matches!(**inner, Type::Never).then_some(false),
            _ => Some(true),
        }
    }

    pub fn result_payloads(&self) -> Option<(&Type, &Type)> {
        match self {
            Type::Sum(name) => name.result_payloads(),
            _ => None,
        }
    }

    pub fn display(&self) -> String {
        match self {
            Type::Bool => "bool".into(),
            Type::Int(k) => k.name().into(),
            Type::Float(k) => k.name().into(),
            Type::Str => "string".into(),
            Type::Void => "void".into(),
            Type::Never => "never".into(),
            Type::Record(n) | Type::Sum(n) => n.to_string(),
            Type::Array(t, n) => format!("{}[{}]", t.display(), n),
            Type::Slice(t) => format!("{}[]", t.display()),
            Type::Fun(ps, r) => format!(
                "({}) -> {}",
                ps.iter()
                    .map(|p| p.display())
                    .collect::<Vec<_>>()
                    .join(", "),
                r.display()
            ),
            Type::Nullable(t) => format!("{}?", t.display()),
            Type::ConstOf(t) => format!("const {}", t.display()),
            Type::Unknown(_) => "?".into(),
            Type::SelfType => "Self".into(),
        }
    }
}

/// Resolve a syntactic type expression to a `Type`.
///
/// The `nominal_info` callback returns the HIR id and kind for a user-defined
/// type name, allowing record and sum annotations to resolve to distinct
/// nominal references.
pub fn resolve(
    expr: &TypeExpr,
    mut nominal_info: impl FnMut(&str) -> Option<NominalInfo>,
) -> Result<Type, String> {
    resolve_inner(expr, &mut nominal_info)
}

fn resolve_inner(
    expr: &TypeExpr,
    nominal_info: &mut dyn FnMut(&str) -> Option<NominalInfo>,
) -> Result<Type, String> {
    match expr {
        TypeExpr::Named(name, _) => resolve_named(name, nominal_info),
        TypeExpr::Array(inner, Some(n), _) => Ok(Type::Array(
            Box::new(resolve_inner(inner, nominal_info)?),
            *n,
        )),
        TypeExpr::Array(inner, None, _) => {
            Ok(Type::Slice(Box::new(resolve_inner(inner, nominal_info)?)))
        }
        TypeExpr::Fun(params, ret, _) => Ok(Type::Fun(
            params
                .iter()
                .map(|p| resolve_inner(p, nominal_info))
                .collect::<Result<_, _>>()?,
            Box::new(resolve_inner(ret, nominal_info)?),
        )),
        TypeExpr::Nullable(inner, _) => Ok(Type::Nullable(Box::new(resolve_inner(
            inner,
            nominal_info,
        )?))),
    }
}

fn resolve_named(
    name: &str,
    nominal_info: &mut dyn FnMut(&str) -> Option<NominalInfo>,
) -> Result<Type, String> {
    if let Some(k) = IntKind::from_name(name) {
        return Ok(Type::Int(k));
    }
    Ok(match name {
        "bool" => Type::Bool,
        "float32" => Type::Float(FloatKind::F32),
        "float64" => Type::Float(FloatKind::F64),
        "string" => Type::Str,
        "void" => Type::Void,
        "Self" => Type::SelfType,
        _ => match nominal_info(name) {
            Some(info) => match info.kind {
                NominalKind::Record => Type::Record(NominalType::new(info.id, name)),
                NominalKind::Sum => Type::Sum(NominalType::new(info.id, name)),
            },
            None => return Err(format!("unknown type `{name}`")),
        },
    })
}

#[cfg(test)]
mod tests {
    use prepoly_lexer::Span;
    use prepoly_parser::ast::TypeExpr;

    use super::{IntKind, NominalInfo, NominalType, Substitution, Type, resolve};

    #[test]
    fn resolves_sum_nominal_kind() {
        let ty = resolve(&TypeExpr::Named("Shape".into(), Span::new(0, 5)), |name| {
            (name == "Shape").then_some(NominalInfo::sum(42))
        });
        assert_eq!(ty, Ok(Type::Sum(NominalType::new(42, "Shape"))));
    }

    #[test]
    fn resolves_record_nominal_kind() {
        let ty = resolve(&TypeExpr::Named("Point".into(), Span::new(0, 5)), |name| {
            (name == "Point").then_some(NominalInfo::record(7))
        });
        assert_eq!(ty, Ok(Type::Record(NominalType::new(7, "Point"))));
    }

    #[test]
    fn nominal_substitution_participates_in_identity_and_display() {
        let mut subst = Substitution::empty();
        subst.insert("Ok.value", Type::Int(IntKind::I32));
        subst.insert("Err.error", Type::Str);

        let result = NominalType::with_substitution(0, "Result", subst.clone());
        assert_eq!(result.to_string(), "Result<int32, string>");
        assert!(result.same_nominal(&NominalType::with_substitution(0, "Result", subst)));
        assert!(!result.same_nominal(&NominalType::new(0, "Result")));

        let wrapper = NominalType::with_substitution(1, "Wrapper", {
            let mut subst = Substitution::empty();
            subst.insert("item", Type::Str);
            subst
        });
        assert_eq!(wrapper.to_string(), "Wrapper<item=string>");
    }

    #[test]
    fn result_constructor_uses_substituted_sum_type() {
        let ty = Type::result(Type::Int(IntKind::I32), Type::Str);

        let Type::Sum(result) = &ty else {
            panic!("Result must lower to a nominal sum type");
        };
        assert!(result.is_result_type());
        assert_eq!(ty.display(), "Result<int32, string>");
        assert_eq!(
            ty.result_payloads(),
            Some((&Type::Int(IntKind::I32), &Type::Str))
        );
    }

    #[test]
    fn null_type_is_nullable_never() {
        let ty = Type::null();

        assert!(ty.is_null());
        assert_eq!(ty.display(), "never?");
    }
}
