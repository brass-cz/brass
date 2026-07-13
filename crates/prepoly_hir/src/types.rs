//! The Prepoly type representation and its mapping to the
//! runtime value tags. `Unknown` models the parts inference leaves open, which
//! the JIT handles via runtime tag dispatch (deferred monomorphization).

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use prepoly_parser::ast::TypeExpr;

pub const RESULT_TYPE_ID: i32 = 0;
pub const RESULT_TYPE_NAME: &str = "Result";
pub const RESULT_OK_VALUE: &str = "Ok.value";
pub const RESULT_ERR_ERROR: &str = "Err.error";

/// Type id and name of a *structural* record: one with no declaration, whose
/// layout and identity come from its field substitution rather than a nominal
/// definition. Used for anonymous structures (`{ f: v }` / `anonymous { f: T }`)
/// and records built at the deserialize boundary; both share this
/// id/name so structurally-identical values are the same type. Negative so it
/// never collides with a declared type's id.
pub const STRUCTURAL_RECORD_ID: i32 = i32::MIN;
pub const STRUCTURAL_RECORD_NAME: &str = "<structural>";

/// Build a structural `Type::Record` from named field types (an anonymous
/// structure). Field order is irrelevant -- the substitution is keyed by name and
/// laid out in sorted name order by the back ends.
pub fn structural_record(fields: Vec<(String, Type)>) -> Type {
    let mut subst = Substitution::empty();
    for (name, ty) in fields {
        subst.insert(name, ty);
    }
    Type::Record(NominalType::with_substitution(
        STRUCTURAL_RECORD_ID,
        STRUCTURAL_RECORD_NAME,
        subst,
    ))
}

/// Placeholder `Unknown` id that [`resolve`] emits for the `infer` type word and
/// for the error payload a `T!` annotation leaves open. It is not a real
/// inference variable: each occurrence must be replaced with a distinct fresh
/// variable by [`freshen_infer`], so two `infer` positions are independent rather
/// than one shared unknown. `u32::MAX` is reserved for this and never minted as a
/// genuine `Unknown` id.
pub const INFER_VAR: u32 = u32::MAX;

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
    /// The bit width of this integer type.
    pub fn bits(self) -> u32 {
        match self {
            IntKind::I8 | IntKind::U8 => 8,
            IntKind::I16 | IntKind::U16 => 16,
            IntKind::I32 | IntKind::U32 => 32,
            IntKind::I64 | IntKind::U64 => 64,
        }
    }

    /// Whether this integer type is signed.
    pub fn is_signed(self) -> bool {
        matches!(
            self,
            IntKind::I8 | IntKind::I16 | IntKind::I32 | IntKind::I64
        )
    }

    /// The integer type of a given signedness and bit width.
    pub fn of(signed: bool, bits: u32) -> IntKind {
        match (signed, bits) {
            (true, 8) => IntKind::I8,
            (true, 16) => IntKind::I16,
            (true, 64) => IntKind::I64,
            (false, 8) => IntKind::U8,
            (false, 16) => IntKind::U16,
            (false, 32) => IntKind::U32,
            (false, 64) => IntKind::U64,
            (true, _) => IntKind::I32,
            (false, _) => IntKind::U32,
        }
    }

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
    /// The bit width of this float type.
    pub fn bits(self) -> u32 {
        match self {
            FloatKind::F32 => 32,
            FloatKind::F64 => 64,
        }
    }

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
    /// A fixed-length, heterogeneous tuple `[T0, T1, ...]` (written `[int32,
    /// string]`). A bracket literal with elements of differing types is a tuple;
    /// one whose elements share a type is an `Array`/`Slice`.
    Tuple(Vec<Type>),
    Fun(Vec<Type>, Box<Type>),
    Nullable(Box<Type>),
    ConstOf(Box<Type>),
    /// A mutable `T` (written `mut(T)`): a place of this type may be mutated. The
    /// wrapper is transparent to unification (`mut(T)` unifies with `T`); it is
    /// the signal a mutation site / mutating-parameter position checks for. Plain
    /// `T` is immutable. Erased to `T` before the back ends.
    Mut(Box<Type>),
    /// A reference (written `ref(T)`, or `ref(mut(T))` for a mutable reference --
    /// the inner is then a `Mut`). A reference parameter borrows its argument; a
    /// non-reference heap parameter is deep-copied. Transparent to unification (it
    /// unifies with its referent type), so the reference is created implicitly from
    /// the parameter annotation. Erased to its referent before the back ends.
    Ref(Box<Type>),
    Unknown(u32),
    SelfType,
}

/// The caller-visible convention attached to a function parameter type.
///
/// Passing wrappers are transparent when a value is matched against a direct
/// call parameter, because the call itself creates the borrow or copy. They are
/// not transparent inside a function value's signature: replacing a copied
/// parameter with a mutable reference would change which caller-owned value the
/// function can modify.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PassingMode {
    Value,
    MutableCopy,
    SharedReference,
    MutableReference,
}

/// A nominal type substitution keyed by lowered member paths.
///
/// For the built-in `Result`, `Ok.value` and `Err.error` carry the statically
/// known payload types.
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

impl NominalType {
    /// Render this reference with inference variables printed by `unknown`;
    /// see [`Type::display_with`] for the contract shared with the language
    /// server's hover renderer.
    pub fn display_with(&self, unknown: &mut dyn FnMut(u32) -> String) -> String {
        self.render(unknown, true)
    }

    /// Like [`Self::display_with`], but keeping the `_`-prefixed members. See
    /// [`Type::display_full`].
    pub fn display_full_with(&self, unknown: &mut dyn FnMut(u32) -> String) -> String {
        self.render(unknown, false)
    }

    /// `hide_private` drops `_`-prefixed substitution members from the
    /// rendering.
    fn render(&self, unknown: &mut dyn FnMut(u32) -> String, hide_private: bool) -> String {
        if let Some((ok, err)) = self.result_payloads() {
            return format!(
                "Result<{}, {}>",
                ok.render(unknown, hide_private),
                err.render(unknown, hide_private)
            );
        }
        // A structural/anonymous record has no declared name; render it as the
        // `anonymous { field: Type, ... }` form the programmer writes, so a
        // diagnostic reads naturally instead of exposing the `<structural>`
        // placeholder. Fields are keyed in sorted name order by the substitution.
        if self.name == STRUCTURAL_RECORD_NAME {
            let fields = self
                .substitution
                .iter()
                .map(|(key, ty)| format!("{key}: {}", ty.render(unknown, hide_private)))
                .collect::<Vec<_>>()
                .join(", ");
            return format!("anonymous {{ {fields} }}");
        }
        // `_`-prefixed members are implementation details (the language's `_`
        // privacy convention), so they are omitted from the rendered
        // substitution; a type whose visible surface is only its `_` internals
        // reads as its bare name.
        let entries = self
            .substitution
            .iter()
            .filter(|(key, _)| !hide_private || !key.starts_with('_'))
            .map(|(key, ty)| format!("{key}={}", ty.render(unknown, hide_private)))
            .collect::<Vec<_>>()
            .join(", ");
        if entries.is_empty() {
            return self.name.clone();
        }
        format!("{}<{entries}>", self.name)
    }
}

impl fmt::Display for NominalType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.display_with(&mut |_| "?".into()))
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

    /// The dispatch class for a primitive/array receiver, used to route a
    /// `recv.m()` call to a stdlib method implemented with `fun T.m(...)`.
    /// Scalars map to their type word; every array (fixed or slice) maps to
    /// `"array"`. Returns `None` for nominal records/sums (dispatched by their
    /// unique symbol) and for types that cannot carry methods.
    pub fn primitive_class(&self) -> Option<&'static str> {
        match self {
            Type::Bool => Some("bool"),
            Type::Str => Some("string"),
            Type::Int(k) => Some(k.name()),
            Type::Float(k) => Some(k.name()),
            Type::Array(..) | Type::Slice(_) => Some("array"),
            _ => None,
        }
    }

    /// The dispatch class for a `fun T.m(...)` receiver type word: a primitive
    /// scalar (`"string"`, `"int32"`, ...) or `"array"` for an array receiver
    /// (`T[]`). Returns `None` for a name that is not a primitive type word, so
    /// the caller treats it as a nominal user type. The `array` flag is set by
    /// the parser when the receiver was written `T[]`.
    pub fn primitive_class_of_name(name: &str, array: bool) -> Option<&'static str> {
        if array {
            return Some("array");
        }
        if let Some(k) = IntKind::from_name(name) {
            return Some(k.name());
        }
        match name {
            "bool" => Some("bool"),
            "float32" => Some("float32"),
            "float64" => Some("float64"),
            "string" => Some("string"),
            _ => None,
        }
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
        self.display_with(&mut |_| "?".into())
    }

    /// Render this type with inference variables printed by `unknown`. This is
    /// the single source of type syntax for user-facing output: compiler
    /// diagnostics print every variable as `?` (via [`Self::display`]), while
    /// the language server numbers them `unknown_N` for hover. Everything else
    /// renders identically for both, so diagnostics and hover agree.
    pub fn display_with(&self, unknown: &mut dyn FnMut(u32) -> String) -> String {
        self.render(unknown, true)
    }

    /// Render including the `_`-prefixed members [`Self::display`] hides.
    ///
    /// Hiding them is right for every surface a programmer reads a type on
    /// (hover, a signature), but it can make two *different* instantiations of
    /// the same nominal print identically -- a type whose only open members are
    /// private renders as its bare name. A diagnostic that must tell two types
    /// apart falls back to this; see [`mismatch_display`].
    pub fn display_full(&self) -> String {
        self.render(&mut |_| "?".into(), false)
    }

    fn render(&self, unknown: &mut dyn FnMut(u32) -> String, hide_private: bool) -> String {
        let mut sub = |t: &Type| t.render(unknown, hide_private);
        match self {
            Type::Bool => "bool".into(),
            Type::Int(k) => k.name().into(),
            Type::Float(k) => k.name().into(),
            Type::Str => "string".into(),
            Type::Void => "void".into(),
            Type::Never => "never".into(),
            Type::Record(n) | Type::Sum(n) => n.render(unknown, hide_private),
            Type::Array(t, n) => format!("{}[{}]", sub(t), n),
            Type::Slice(t) => format!("{}[]", sub(t)),
            Type::Tuple(ts) => format!("[{}]", ts.iter().map(sub).collect::<Vec<_>>().join(", ")),
            Type::Fun(ps, r) => format!(
                "({}) -> {}",
                ps.iter()
                    .map(|p| p.render(unknown, hide_private))
                    .collect::<Vec<_>>()
                    .join(", "),
                r.render(unknown, hide_private)
            ),
            Type::Nullable(t) => format!("{}?", sub(t)),
            Type::ConstOf(t) => format!("const {}", sub(t)),
            Type::Mut(t) => format!("mut({})", sub(t)),
            Type::Ref(t) => format!("ref({})", sub(t)),
            Type::Unknown(id) => unknown(*id),
            Type::SelfType => "Self".into(),
        }
    }

    /// The bare source name of this type, as `typeof(x)` reports it: a
    /// nominal type's own name (no substitution), a primitive's keyword, and
    /// the structural forms of arrays/tuples/nullables. Distinct from
    /// [`Self::display`] only for records/sums, where the substitution is
    /// dropped so `typeof` is stable across instantiations.
    pub fn type_name(&self) -> String {
        match self {
            Type::Record(n) | Type::Sum(n) => n.name.clone(),
            Type::ConstOf(t) | Type::Mut(t) | Type::Ref(t) => t.type_name(),
            _ => self.display(),
        }
    }
}

/// The two strings a "cannot use `X` where `Y` is required" diagnostic should
/// print for `got` and `want`.
///
/// Normally the pretty rendering, which hides a nominal's `_`-prefixed
/// implementation members. When two *different* types render to the same
/// string that message says nothing, so both fall back to the unfiltered form
/// -- the only place a programmer sees a type's private members, and only when
/// they are what distinguishes it.
pub fn mismatch_display(got: &Type, want: &Type) -> (String, String) {
    let (g, w) = (got.display(), want.display());
    if g == w && got != want {
        return (got.display_full(), want.display_full());
    }
    (g, w)
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
    resolve_inner(expr, &mut nominal_info, &mut |_| None)
}

/// [`resolve`] with a `type Alias = ..` lookup consulted before the nominal
/// table, so an annotation naming a concrete-instance alias (a refinement
/// like `_JsonObject`) resolves to the alias's full substituted type instead
/// of failing as an unknown name. The caller owns the qualification rule
/// (module-local vs imported alias names).
pub fn resolve_with_aliases(
    expr: &TypeExpr,
    mut nominal_info: impl FnMut(&str) -> Option<NominalInfo>,
    mut alias: impl FnMut(&str) -> Option<Type>,
) -> Result<Type, String> {
    resolve_inner(expr, &mut nominal_info, &mut alias)
}

fn resolve_inner(
    expr: &TypeExpr,
    nominal_info: &mut dyn FnMut(&str) -> Option<NominalInfo>,
    alias: &mut dyn FnMut(&str) -> Option<Type>,
) -> Result<Type, String> {
    match expr {
        TypeExpr::Named(name, _) => {
            if let Some(t) = alias(name) {
                return Ok(t);
            }
            resolve_named(name, nominal_info)
        }
        TypeExpr::Array(inner, Some(n), _) => Ok(Type::Array(
            Box::new(resolve_inner(inner, nominal_info, alias)?),
            *n,
        )),
        TypeExpr::Array(inner, None, _) => Ok(Type::Slice(Box::new(resolve_inner(
            inner,
            nominal_info,
            alias,
        )?))),
        TypeExpr::Fun(params, ret, _) => Ok(Type::Fun(
            params
                .iter()
                .map(|p| resolve_inner(p, nominal_info, alias))
                .collect::<Result<_, _>>()?,
            Box::new(resolve_inner(ret, nominal_info, alias)?),
        )),
        TypeExpr::Nullable(inner, _) => Ok(Type::Nullable(Box::new(resolve_inner(
            inner,
            nominal_info,
            alias,
        )?))),
        // `T!` is the built-in fallible Result: success payload `T`, error payload
        // left open (an `infer` placeholder the caller freshens, so it is inferred
        // from the body's `error(...)` sites like an unannotated fallible return).
        TypeExpr::Fallible(inner, _) => Ok(Type::result(
            resolve_inner(inner, nominal_info, alias)?,
            Type::Unknown(INFER_VAR),
        )),
        TypeExpr::Tuple(elems, _) => Ok(Type::Tuple(
            elems
                .iter()
                .map(|e| resolve_inner(e, nominal_info, alias))
                .collect::<Result<_, _>>()?,
        )),
        // An anonymous structure resolves to a structural record whose field types
        // are resolved in place.
        TypeExpr::Anonymous(fields, _) => {
            let mut resolved = Vec::with_capacity(fields.len());
            for (name, fty) in fields {
                resolved.push((name.clone(), resolve_inner(fty, nominal_info, alias)?));
            }
            Ok(structural_record(resolved))
        }
        TypeExpr::Mut(inner, _) => Ok(Type::Mut(Box::new(resolve_inner(
            inner,
            nominal_info,
            alias,
        )?))),
        TypeExpr::Ref(inner, _) => Ok(Type::Ref(Box::new(resolve_inner(
            inner,
            nominal_info,
            alias,
        )?))),
        // `typeof(e)` cannot be resolved without inferring `e`'s type, which this
        // pure pass does not do. It resolves to the same open placeholder as an
        // `infer` word; the type checker replaces it with `e`'s inferred type
        // when resolving an annotation (see the checker's `resolve_annotation`).
        TypeExpr::TypeOf(_, _) => Ok(Type::Unknown(INFER_VAR)),
        // `type` slots, `Self.field` references, and `Base { .. }` refinements
        // depend on the enclosing type's fields (a slot's inference variable) and,
        // for a refinement, the base type's declared fields. The pure resolver has
        // neither, so they are resolved by `resolve_type_decls` (which owns the
        // slot-variable environment and the type table) and never reach here in a
        // well-formed program.
        TypeExpr::TypeSlot(_) => {
            Err("`type` may only appear as a field's whole declared type".into())
        }
        TypeExpr::SelfField(field, _) => Err(format!(
            "`Self.{field}` may only appear inside a type declaration"
        )),
        TypeExpr::Refine(base, _, _) => {
            let base = match base.as_ref() {
                TypeExpr::Named(n, _) => n.clone(),
                _ => "<type>".into(),
            };
            Err(format!(
                "a `{base} {{ .. }}` refinement is resolved only in a type declaration"
            ))
        }
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
        // The built-in `infer` lowers to an unknown so ordinary inference fills it
        // in (e.g. `infer[]` is an array whose element type is inferred). The
        // placeholder id is freshened per occurrence by `freshen_infer`.
        "infer" => Type::Unknown(INFER_VAR),
        _ => match nominal_info(name) {
            Some(info) => match info.kind {
                NominalKind::Record => Type::Record(NominalType::new(info.id, name)),
                NominalKind::Sum => Type::Sum(NominalType::new(info.id, name)),
            },
            None => return Err(format!("unknown type `{name}`")),
        },
    })
}

/// The storage symbol for a stdlib method implemented on a primitive/array
/// receiver (`fun T.m`): the method name qualified by its dispatch `class`, so it
/// never clashes with a free function or another class's method of the same
/// name. Shared by HIR lowering and the back ends so they agree on the symbol a
/// `recv.m()` call resolves to.
pub fn prim_method_symbol(class: &str, method: &str) -> String {
    format!("{method}@prim.{class}")
}

/// The default kind of an unconstrained integer literal: int32 when the value
/// fits, otherwise int64. A literal like `9223372036854775807` can only be an
/// int64; defaulting it to int32 (the canonical kind) would silently truncate
/// the value the programmer wrote out.
pub fn int_literal_kind(value: i64) -> IntKind {
    if i32::try_from(value).is_ok() {
        IntKind::I32
    } else {
        IntKind::I64
    }
}

/// The type yielded by indexing into `ty`. Reference and mutability wrappers are
/// seen through and re-applied to the element, so indexing a reference to an array
/// yields a reference to the element of the same kind: `ref(T[])[i]` is `ref(T)`
/// and `ref(mut(T[]))[i]` is `ref(mut(T))`. `None` when `ty` is not an array/slice
/// (possibly under such wrappers).
pub fn index_element(ty: &Type) -> Option<Type> {
    match ty {
        Type::Slice(e) | Type::Array(e, _) => Some((**e).clone()),
        Type::Ref(inner) => index_element(inner).map(|e| Type::Ref(Box::new(e))),
        Type::Mut(inner) => index_element(inner).map(|e| Type::Mut(Box::new(e))),
        Type::ConstOf(inner) => index_element(inner).map(|e| Type::ConstOf(Box::new(e))),
        _ => None,
    }
}

/// Whether two types belong to clearly different primitive value kinds (string
/// vs int, bool vs float, ...) that no coercion bridges. This is the shared
/// rule behind structural `if` folding: the back end skips emitting a then-arm
/// whose reachable `return` value kind-conflicts with the function's return
/// type, and the checker may fold (and tolerate) exactly the same arms -- both
/// sides must prune identically or a checker-tolerated arm would execute.
pub fn primitive_kind_conflict(a: &Type, b: &Type) -> bool {
    fn kind(t: &Type) -> Option<u8> {
        match t {
            Type::Str => Some(0),
            Type::Bool => Some(1),
            Type::Int(_) => Some(2),
            Type::Float(_) => Some(3),
            _ => None,
        }
    }
    matches!((kind(a), kind(b)), (Some(x), Some(y)) if x != y)
}

/// Whether `ty` contains no inference variable, recursing through every
/// component (array elements, nominal substitutions, function and tuple parts).
/// A bare nominal reference (empty substitution) is fully known: the name and id
/// are all the layout needs.
pub fn is_fully_known(ty: &Type) -> bool {
    match ty {
        Type::Unknown(_) => false,
        Type::Array(inner, _)
        | Type::Slice(inner)
        | Type::Nullable(inner)
        | Type::ConstOf(inner)
        | Type::Mut(inner)
        | Type::Ref(inner) => is_fully_known(inner),
        Type::Fun(params, ret) => params.iter().all(is_fully_known) && is_fully_known(ret),
        Type::Tuple(elems) => elems.iter().all(is_fully_known),
        Type::Record(n) | Type::Sum(n) => n.substitution.iter().all(|(_, t)| is_fully_known(t)),
        _ => true,
    }
}

/// The value type behind parameter-passing mode wrappers: `ref(T)`, `mut(T)` and
/// `const` views expose the underlying value's fields, elements and methods, so
/// member access and member type checks must look through them. Without this a
/// `ref(mut(Point))` base would silently skip field type checking (the match on
/// `Record`/`Sum` sees the wrapper, not the record) and ill-typed stores would
/// reach the unboxed back end.
pub fn peel_modes(ty: &Type) -> &Type {
    match ty {
        Type::Ref(t) | Type::Mut(t) | Type::ConstOf(t) => peel_modes(t),
        _ => ty,
    }
}

/// Split one caller-visible passing wrapper from its underlying value type.
/// `const` describes the source binding rather than the callee convention and
/// is therefore ignored. An open type has no fixed mode yet; callers that
/// compare modes should allow it to be unified before requiring equality.
pub fn split_passing_mode(ty: &Type) -> (PassingMode, &Type) {
    let ty = peel_const(ty);
    match ty {
        Type::Ref(inner) => split_reference_mode(peel_const(inner)),
        Type::Mut(inner) => (PassingMode::MutableCopy, peel_const(inner)),
        other => (PassingMode::Value, other),
    }
}

/// Whether two types can denote the same caller-visible passing convention.
/// A whole open type may still be instantiated with any convention; an open
/// value nested inside an explicit wrapper does not erase that wrapper.
pub fn passing_modes_match(a: &Type, b: &Type) -> bool {
    let a = peel_const(a);
    let b = peel_const(b);
    a.is_unknown() || b.is_unknown() || split_passing_mode(a).0 == split_passing_mode(b).0
}

fn split_reference_mode(ty: &Type) -> (PassingMode, &Type) {
    match ty {
        Type::Mut(inner) => (PassingMode::MutableReference, peel_const(inner)),
        other => (PassingMode::SharedReference, other),
    }
}

fn peel_const(ty: &Type) -> &Type {
    match ty {
        Type::ConstOf(inner) => peel_const(inner),
        other => other,
    }
}

/// Replace every `infer` placeholder ([`INFER_VAR`]) in a resolved type with a
/// distinct fresh type from `fresh`, recursing into composite types and into a
/// `Result`'s payload substitution. So each `infer` (and each `T!` error payload)
/// becomes its own inference variable -- `(infer, infer) -> infer` has three
/// independent unknowns -- rather than a single shared one. The caller owns the
/// fresh-variable source (the HIR unknown counter during lowering, or the solver
/// during checking), so the freshened ids slot into its inference namespace.
pub fn freshen_infer(ty: Type, fresh: &mut impl FnMut() -> Type) -> Type {
    match ty {
        Type::Unknown(INFER_VAR) => fresh(),
        Type::Array(t, n) => Type::Array(Box::new(freshen_infer(*t, fresh)), n),
        Type::Slice(t) => Type::Slice(Box::new(freshen_infer(*t, fresh))),
        Type::Nullable(t) => Type::Nullable(Box::new(freshen_infer(*t, fresh))),
        Type::ConstOf(t) => Type::ConstOf(Box::new(freshen_infer(*t, fresh))),
        Type::Mut(t) => Type::Mut(Box::new(freshen_infer(*t, fresh))),
        Type::Ref(t) => Type::Ref(Box::new(freshen_infer(*t, fresh))),
        Type::Fun(ps, r) => Type::Fun(
            ps.into_iter().map(|p| freshen_infer(p, fresh)).collect(),
            Box::new(freshen_infer(*r, fresh)),
        ),
        Type::Tuple(ts) => Type::Tuple(ts.into_iter().map(|t| freshen_infer(t, fresh)).collect()),
        // A nominal's payload substitution (e.g. a `T!` -> `Result`'s open error
        // type) is rewritten in place; the Record/Sum kind is preserved.
        Type::Record(n) => Type::Record(freshen_nominal(n, fresh)),
        Type::Sum(n) => Type::Sum(freshen_nominal(n, fresh)),
        other => other,
    }
}

/// Replace EVERY inference variable in `ty` with a fresh one, memoized so a
/// variable occurring twice stays one variable.
///
/// [`freshen_infer`] renews only the `infer` placeholder; this renews a resolved
/// type's whole variable set, which is what a PRECOMPUTED type needs before it
/// reaches a use site. The precompute inferred it once, in a single shared
/// instantiation, so handing it over verbatim would tie every site that reads it
/// to the first one that constrains it -- a witness-free `HashMap.new()` would
/// have its key/value slots pinned by the first `set` anywhere in the program
/// and left unrefined at every later site.
pub fn freshen_unknowns(ty: &Type, fresh: &mut impl FnMut() -> Type) -> Type {
    let mut vars = BTreeSet::new();
    collect_unknowns(ty, &mut vars);
    let map: BTreeMap<u32, Type> = vars.into_iter().map(|v| (v, fresh())).collect();
    substitute_vars(ty, &map)
}

/// Every inference variable occurring in `ty`, including inside a nominal's
/// payload substitution.
pub fn type_vars(ty: &Type) -> BTreeSet<u32> {
    let mut out = BTreeSet::new();
    collect_unknowns(ty, &mut out);
    out
}

/// Every inference variable occurring in `ty`, including inside a nominal's
/// payload substitution.
fn collect_unknowns(ty: &Type, out: &mut BTreeSet<u32>) {
    match ty {
        Type::Unknown(v) => {
            out.insert(*v);
        }
        Type::Array(inner, _)
        | Type::Slice(inner)
        | Type::Nullable(inner)
        | Type::ConstOf(inner)
        | Type::Mut(inner)
        | Type::Ref(inner) => collect_unknowns(inner, out),
        Type::Tuple(elems) => elems.iter().for_each(|e| collect_unknowns(e, out)),
        Type::Fun(params, ret) => {
            params.iter().for_each(|p| collect_unknowns(p, out));
            collect_unknowns(ret, out);
        }
        Type::Record(n) | Type::Sum(n) => n
            .substitution
            .iter()
            .for_each(|(_, t)| collect_unknowns(t, out)),
        _ => {}
    }
}

/// Replace each `Unknown(v)` whose `v` is a key of `map` with the mapped type,
/// recursing through every component. Used to instantiate a type's slot
/// variables (its parameters) with the types a refinement pins them to.
pub fn substitute_vars(ty: &Type, map: &BTreeMap<u32, Type>) -> Type {
    match ty {
        Type::Unknown(v) => map.get(v).cloned().unwrap_or_else(|| ty.clone()),
        Type::Array(inner, n) => Type::Array(Box::new(substitute_vars(inner, map)), *n),
        Type::Slice(inner) => Type::Slice(Box::new(substitute_vars(inner, map))),
        Type::Nullable(inner) => Type::Nullable(Box::new(substitute_vars(inner, map))),
        Type::ConstOf(inner) => Type::ConstOf(Box::new(substitute_vars(inner, map))),
        Type::Mut(inner) => Type::Mut(Box::new(substitute_vars(inner, map))),
        Type::Ref(inner) => Type::Ref(Box::new(substitute_vars(inner, map))),
        Type::Tuple(elems) => Type::Tuple(elems.iter().map(|e| substitute_vars(e, map)).collect()),
        Type::Fun(ps, r) => Type::Fun(
            ps.iter().map(|p| substitute_vars(p, map)).collect(),
            Box::new(substitute_vars(r, map)),
        ),
        Type::Record(n) => Type::Record(substitute_vars_nominal(n, map)),
        Type::Sum(n) => Type::Sum(substitute_vars_nominal(n, map)),
        other => other.clone(),
    }
}

/// Collapse nested nullability (`T??` -> `T?`) throughout a type. A nested
/// nullable carries no extra meaning (there is one `null`), and can arise when
/// a return wrapped in `?` over an open variable is instantiated with a type
/// that is itself nullable.
pub fn collapse_nullable(ty: &Type) -> Type {
    match ty {
        Type::Nullable(inner) => {
            let mut inner = collapse_nullable(inner);
            if let Type::Nullable(i) = inner {
                inner = *i;
            }
            Type::Nullable(Box::new(inner))
        }
        Type::Array(inner, n) => Type::Array(Box::new(collapse_nullable(inner)), *n),
        Type::Slice(inner) => Type::Slice(Box::new(collapse_nullable(inner))),
        Type::ConstOf(inner) => Type::ConstOf(Box::new(collapse_nullable(inner))),
        Type::Mut(inner) => Type::Mut(Box::new(collapse_nullable(inner))),
        Type::Ref(inner) => Type::Ref(Box::new(collapse_nullable(inner))),
        Type::Tuple(elems) => Type::Tuple(elems.iter().map(collapse_nullable).collect()),
        Type::Fun(ps, r) => Type::Fun(
            ps.iter().map(collapse_nullable).collect(),
            Box::new(collapse_nullable(r)),
        ),
        Type::Record(n) => Type::Record(collapse_nullable_nominal(n)),
        Type::Sum(n) => Type::Sum(collapse_nullable_nominal(n)),
        other => other.clone(),
    }
}

fn collapse_nullable_nominal(n: &NominalType) -> NominalType {
    if n.substitution.is_empty() {
        return n.clone();
    }
    let mut subst = Substitution::empty();
    for (k, v) in n.substitution.iter() {
        subst.insert(k.to_string(), collapse_nullable(v));
    }
    NominalType::with_substitution(n.id, n.name.clone(), subst)
}

fn substitute_vars_nominal(n: &NominalType, map: &BTreeMap<u32, Type>) -> NominalType {
    if n.substitution.is_empty() {
        return n.clone();
    }
    let mut subst = Substitution::empty();
    for (k, v) in n.substitution.iter() {
        subst.insert(k.to_string(), substitute_vars(v, map));
    }
    NominalType::with_substitution(n.id, n.name.clone(), subst)
}

fn freshen_nominal(mut n: NominalType, fresh: &mut impl FnMut() -> Type) -> NominalType {
    if n.substitution.is_empty() {
        return n;
    }
    let mut subst = Substitution::empty();
    for (k, v) in n.substitution.iter() {
        subst.insert(k.to_string(), freshen_infer(v.clone(), fresh));
    }
    n.substitution = subst;
    n
}

/// A collision-resistant key for one concrete type inside an instance symbol.
/// Unlike `Type::display`, every token is self-delimiting (no `_` inside a
/// token), constructors carry their arity, nominal types are keyed by id (two
/// same-named types from different modules stay distinct), and substitution
/// field names are length-prefixed. Joining keys with `_` is therefore a
/// uniquely decodable code: equal symbols imply equal type tuples.
pub fn type_key(ty: &Type) -> String {
    match ty {
        Type::Bool => "bool".into(),
        Type::Int(k) => k.name().into(),
        Type::Float(k) => k.name().into(),
        Type::Str => "str".into(),
        Type::Void => "void".into(),
        Type::Never => "never".into(),
        Type::Record(n) => nominal_key("rec", n),
        Type::Sum(n) => nominal_key("sum", n),
        Type::Array(e, len) => format!("arr{len}_{}", type_key(e)),
        Type::Slice(e) => format!("slice_{}", type_key(e)),
        Type::Tuple(es) => {
            let mut out = format!("tup{}", es.len());
            for e in es {
                out.push('_');
                out.push_str(&type_key(e));
            }
            out
        }
        Type::Fun(ps, ret) => {
            let mut out = format!("fn{}", ps.len());
            for p in ps {
                out.push('_');
                out.push_str(&type_key(p));
            }
            out.push('_');
            out.push_str(&type_key(ret));
            out
        }
        Type::Nullable(inner) => format!("opt_{}", type_key(inner)),
        // Passing modes do not change the value's concrete layout.
        Type::ConstOf(inner) | Type::Mut(inner) | Type::Ref(inner) => type_key(inner),
        Type::Unknown(id) => format!("unk{id}"),
        Type::SelfType => "selfty".into(),
    }
}

/// Key of a record/sum: nominal id plus every substitution entry, so two
/// instantiations of one generic container (`HashMap<string,int32>` vs
/// `HashMap<int32,int32>`) -- and two structural records with different fields --
/// get distinct instance symbols. Field names are length-prefixed because a
/// source identifier may itself contain `_`.
fn nominal_key(tag: &str, n: &NominalType) -> String {
    let entries: Vec<(&str, &Type)> = n.substitution.iter().collect();
    let mut out = format!("{tag}{}x{}", n.id, entries.len());
    // A negative id is a shared internal id (e.g. every structural record uses
    // `STRUCTURAL_RECORD_ID`), where identity also depends on the name -- mirror
    // `NominalType::same_nominal` and fold the name in.
    if n.id < 0 {
        out.push_str(&format!("_nm{}_{}", n.name.len(), n.name));
    }
    for (name, ty) in entries {
        out.push_str(&format!("_fld{}_{name}_{}", name.len(), type_key(ty)));
    }
    out
}

#[cfg(test)]
mod tests {
    use prepoly_parser::Span;
    use prepoly_parser::ast::TypeExpr;

    use super::{
        IntKind, NominalInfo, NominalType, Substitution, Type, collapse_nullable, mismatch_display,
        resolve,
    };

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

    /// `_`-prefixed substitution entries are implementation details and stay out
    /// of the rendered type; a nominal whose entries are all hidden displays as
    /// its bare name (identity still uses every entry).
    #[test]
    fn hidden_substitution_entries_stay_out_of_display() {
        let mixed = NominalType::with_substitution(1, "Table", {
            let mut subst = Substitution::empty();
            subst.insert("_entries", Type::Slice(Box::new(Type::Str)));
            subst.insert("size", Type::Int(IntKind::I64));
            subst
        });
        assert_eq!(mixed.to_string(), "Table<size=int64>");

        let all_hidden = NominalType::with_substitution(1, "Table", {
            let mut subst = Substitution::empty();
            subst.insert("_entries", Type::Slice(Box::new(Type::Str)));
            subst
        });
        assert_eq!(all_hidden.to_string(), "Table");
        assert!(!all_hidden.same_nominal(&NominalType::new(1, "Table")));
    }

    /// Hiding the private members can make two different instantiations print
    /// the same string, which would leave a type-mismatch diagnostic saying
    /// nothing (``cannot use `Box` where `Box` is required``). The mismatch
    /// renderer falls back to the unfiltered form for exactly that case, and
    /// only that case -- an ordinary mismatch keeps the pretty rendering.
    #[test]
    fn a_mismatch_of_identically_rendered_types_shows_the_private_members() {
        let boxed = |elem: Type| {
            Type::Record(NominalType::with_substitution(1, "Box", {
                let mut subst = Substitution::empty();
                subst.insert("_data", Type::Slice(Box::new(elem)));
                subst
            }))
        };
        let strings = boxed(Type::Str);
        let ints = boxed(Type::Int(IntKind::I32));
        assert_eq!(
            (strings.display(), ints.display()),
            ("Box".into(), "Box".into())
        );
        assert_eq!(
            mismatch_display(&ints, &strings),
            (
                "Box<_data=int32[]>".to_string(),
                "Box<_data=string[]>".to_string()
            )
        );

        // Two types that already read differently keep the pretty rendering,
        // and so does a mismatch against the bare nominal.
        assert_eq!(
            mismatch_display(&Type::Str, &Type::Int(IntKind::I32)),
            ("string".to_string(), "int32".to_string())
        );
        let bare = Type::Record(NominalType::new(1, "Box"));
        assert_eq!(
            mismatch_display(&ints, &bare),
            ("Box<_data=int32[]>".to_string(), "Box".to_string())
        );
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

    /// `T??` collapses to `T?` at any depth and inside composites; an already
    /// flat type is unchanged.
    #[test]
    fn nested_nullable_collapses() {
        let t = Type::Nullable(Box::new(Type::Nullable(Box::new(Type::Str))));
        assert_eq!(collapse_nullable(&t), Type::Nullable(Box::new(Type::Str)));

        let deep = Type::Slice(Box::new(Type::Nullable(Box::new(Type::Nullable(
            Box::new(Type::Int(IntKind::I32)),
        )))));
        assert_eq!(
            collapse_nullable(&deep),
            Type::Slice(Box::new(Type::Nullable(Box::new(Type::Int(IntKind::I32)))))
        );

        let flat = Type::Nullable(Box::new(Type::Str));
        assert_eq!(collapse_nullable(&flat), flat);
    }
}
