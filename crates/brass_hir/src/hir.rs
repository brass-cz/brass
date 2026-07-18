//! The high-level intermediate representation: the whole program collected
//! into global type and function tables with numeric type ids assigned for the
//! runtime. Records and sum types keep their members (as AST nodes, lowered
//! on demand by codegen); this is the "typed HIR" the back end consumes.

use std::collections::HashMap;
use std::rc::Rc;

use brass_parser::Span;
use brass_parser::ast::{FunDecl, Method, Module, Param, Stmt, TypeExpr};

use crate::types::{NominalType, Type};

/// Reserved id for the built-in `Result` type (matches the runtime).
pub use crate::types::RESULT_TYPE_ID;

/// Free-function names the runtime and the compiler own. A `.cz` definition of
/// one is rejected (it would capture the standard library's internal calls, or
/// -- for `error` -- be dead because `error(x)` desugars to `Result.Err`), and
/// the plugin-module loader renames a plugin function that lands on one rather
/// than synthesizing a module that cannot be checked.
pub const RESERVED_FUNCTION_NAMES: &[&str] =
    &["len", "spawn", "with", "sync", "error", "fields", "typeof"];

/// The canonical identity of a top-level definition: its local name plus the
/// module path it is defined in. The storage/codegen key (`symbol`) is its
/// `Display` form `name@a/b` -- the module path joins with `/`, never `.`, so the
/// key cannot collide with the `Type.Variant` separator used in method
/// qualifiers. Program tables are keyed by this string today; the struct gives
/// resolution a typed identity to pass around instead of re-parsing the symbol.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct QualifiedName {
    pub module: Vec<String>,
    pub name: String,
}

impl QualifiedName {
    pub fn new(name: impl Into<String>, module: &[String]) -> Self {
        Self {
            module: module.to_vec(),
            name: name.into(),
        }
    }

    /// The storage/codegen symbol (`name@a/b`).
    pub fn symbol(&self) -> String {
        self.to_string()
    }
}

impl std::fmt::Display for QualifiedName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}@{}", self.name, self.module.join("/"))
    }
}

/// Format the module-qualified storage symbol for a top-level name (the
/// [`QualifiedName`] `Display` form). Kept as a free function because most call
/// sites build the symbol from a `(name, module)` pair to key the program tables.
pub fn qualify(local: &str, module: &[String]) -> String {
    QualifiedName::new(local, module).symbol()
}

/// Resolve a bare top-level `name` referenced from `module` against a program
/// table keyed by qualified symbol: its own/unique definition, this module's
/// qualified definition, or the one imported into this module. This is the one
/// resolution rule shared by type, function, and annotation lookups.
pub fn resolve_qualified<'a, T>(
    table: &'a HashMap<String, T>,
    import_origins: &HashMap<Vec<String>, HashMap<String, Vec<String>>>,
    import_renames: &HashMap<Vec<String>, HashMap<String, String>>,
    module: &[String],
    name: &str,
) -> Option<&'a T> {
    // A renamed import (`import m.{ X as Y }`): the local name exists ONLY as
    // this module's alias for the origin's remote name, so it must not fall
    // through to the bare table -- an unrelated module's unique `Y` would
    // capture it. A rename colliding with a local declaration is rejected by
    // import checking, so resolving the rename first is safe.
    if let Some(remote) = import_renames.get(module).and_then(|m| m.get(name)) {
        let origin = import_origins.get(module)?.get(name)?;
        return table
            .get(&qualify(remote, origin))
            .or_else(|| table.get(remote.as_str()));
    }
    // The defining module's own qualified entry wins over a bare (unique)
    // definition elsewhere. For most names only one of the two forms exists
    // (a unique name keeps its bare symbol); `Result` is the exception -- the
    // prelude's declaration holds the bare key while a module's shadowing
    // declaration is always qualified, and the nearer scope must win.
    if let Some(v) = table.get(&qualify(name, module)) {
        return Some(v);
    }
    if let Some(v) = table.get(name) {
        return Some(v);
    }
    let origin = import_origins.get(module)?.get(name)?;
    table.get(&qualify(name, origin))
}

/// A parsed source file tagged with its module path.
#[derive(Clone, serde::Serialize, serde::Deserialize)]
pub struct LoadedModule {
    pub path: Vec<String>,
    pub ast: Module,
    /// Whether this is an implicit-prelude module (every `core/*.cz` module): its
    /// public names are visible everywhere with no import. Set by the loader
    /// that embeds the prelude; every other module -- including the nested
    /// standard-library ones -- requires an explicit import.
    pub is_prelude: bool,
}

#[derive(Clone, Debug)]
pub struct FieldInfo {
    pub name: String,
    pub ty: Option<TypeExpr>,
    pub resolved_ty: Option<Type>,
}

/// A callable parameter lowered into HIR-owned signature data.
#[derive(Clone, Debug)]
pub struct ParamInfo {
    pub name: String,
    pub ty: Option<TypeExpr>,
    pub resolved_ty: Option<Type>,
    pub span: Span,
}

impl From<&Param> for ParamInfo {
    fn from(param: &Param) -> Self {
        Self {
            name: param.name.clone(),
            ty: param.ty.clone(),
            resolved_ty: None,
            span: param.span,
        }
    }
}

/// A record type generalized together with its methods: the inferred type
/// parameters shared between the type's fields and its methods' signatures,
/// produced once per record type by co-checking its methods in one type
/// environment (see `brass_typeck`). `params` are the inference-variable ids
/// the generalization quantifies (the `K`/`V` of a `HashMap`); `fields` and
/// `methods` carry types expressed over those ids. A binding or call instantiates
/// the scheme by renaming `params` to fresh variables. A monomorphic record (no
/// inferred field, e.g. a fully-annotated `Point`) has an empty `params`.
#[derive(Clone, Debug, Default, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct TypeScheme {
    pub params: Vec<u32>,
    pub fields: Vec<(String, Type)>,
    pub methods: std::collections::BTreeMap<String, SchemeMethod>,
}

/// A method's signature within a [`TypeScheme`]: parameter types (including the
/// leading `self`) and the return type, all expressed over the scheme's `params`.
#[derive(Clone, Debug, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct SchemeMethod {
    pub params: Vec<(String, Type)>,
    pub ret: Type,
}

/// Function or method signature data owned by HIR.
#[derive(Clone, Debug)]
pub struct CallableSignature {
    pub name: String,
    pub params: Vec<ParamInfo>,
    pub ret: Option<TypeExpr>,
    pub ret_ty: Option<Type>,
    pub span: Span,
}

impl CallableSignature {
    pub fn from_function(decl: &FunDecl) -> Self {
        Self {
            name: decl.name.clone(),
            params: decl.params.iter().map(ParamInfo::from).collect(),
            ret: decl.ret.clone(),
            ret_ty: None,
            span: decl.span,
        }
    }

    pub fn from_method(method: &Method) -> Self {
        Self {
            name: method.name.clone(),
            params: method.params.iter().map(ParamInfo::from).collect(),
            ret: method.ret.clone(),
            ret_ty: None,
            span: method.span,
        }
    }
}

/// A method lowered into HIR. The signature is owned by HIR; the parser method
/// is retained while code generation still consumes AST bodies.
#[derive(Clone)]
pub struct MethodInfo {
    pub signature: CallableSignature,
    pub decl: Rc<Method>,
}

#[derive(Clone)]
pub struct VariantInfo {
    pub name: String,
    pub tag: i32,
    pub fields: Vec<FieldInfo>,
    pub methods: HashMap<String, MethodInfo>,
}

#[derive(Clone)]
pub enum TypeKind {
    Record {
        fields: Vec<FieldInfo>,
        methods: HashMap<String, MethodInfo>,
    },
    Sum {
        variants: Vec<VariantInfo>,
    },
}

#[derive(Clone)]
pub struct TypeInfo {
    pub name: String,
    pub id: i32,
    pub interfaces: Vec<String>,
    pub kind: TypeKind,
    pub module: Vec<String>,
    pub span: Span,
    /// Globally unique storage/codegen key. Equal to the bare `name` when only
    /// one module defines that name, and module-qualified (`Name@a.b`) when the
    /// same type name is defined in several modules, so both coexist with
    /// distinct symbols and method-dispatch keys.
    pub symbol: String,
    /// Type slots (fields declared `slot: type`): a record's type parameters,
    /// each paired with the inference variable that stands for it. A slot has no
    /// runtime storage (it is not in `fields`); its variable appears in the other
    /// fields' resolved types wherever they wrote `Self.slot`, and a refinement
    /// (`Base { slot: T }`) or use fills it. Empty for a type without slots.
    pub slots: Vec<(String, u32)>,
    /// Doc comment from the `type` declaration, shown by editor tooling.
    pub doc: Option<String>,
}

impl TypeInfo {
    pub fn nominal_ref(&self) -> NominalType {
        NominalType::new(self.id, &self.name)
    }

    pub fn type_ref(&self) -> Type {
        match self.kind {
            TypeKind::Record { .. } => Type::Record(self.nominal_ref()),
            TypeKind::Sum { .. } => Type::Sum(self.nominal_ref()),
        }
    }

    pub fn is_sum(&self) -> bool {
        matches!(self.kind, TypeKind::Sum { .. })
    }
    pub fn record_method(&self, name: &str) -> Option<&Rc<Method>> {
        match &self.kind {
            TypeKind::Record { methods, .. } => methods.get(name).map(|m| &m.decl),
            TypeKind::Sum { .. } => None,
        }
    }
    pub fn variant(&self, name: &str) -> Option<&VariantInfo> {
        match &self.kind {
            TypeKind::Sum { variants } => variants.iter().find(|v| v.name == name),
            TypeKind::Record { .. } => None,
        }
    }
}

pub struct FunInfo {
    pub signature: CallableSignature,
    pub decl: Rc<FunDecl>,
    pub module: Vec<String>,
    /// Globally unique storage/codegen key. Equal to the bare name when that
    /// name is defined in only one module; module-qualified (`name@a.b`) when
    /// the same local name is defined in several modules, so both definitions
    /// coexist with distinct symbols.
    pub symbol: String,
}

/// Top-level statements of one module, run once at initialization.
pub struct ModuleInit {
    pub path: Vec<String>,
    pub stmts: Vec<Stmt>,
}

/// The collected, id-assigned program.
pub struct Program {
    pub types: HashMap<String, TypeInfo>,
    /// One past the highest `Type::Unknown` id lowering minted into the
    /// resolved signature and field types above. Every solver that types
    /// against this program MUST seed its fresh-variable counter here
    /// (`Solver::seed_var_counter`): a solver-local variable that collides
    /// with an HIR-embedded id aliases an unrelated type, which surfaced as
    /// order-dependent phantom type errors.
    pub next_infer_var: u32,
    pub functions: HashMap<String, FunInfo>,
    pub inits: Vec<ModuleInit>,
    /// Paths of the implicit-prelude modules (see [`LoadedModule::is_prelude`]):
    /// their public names are visible in every module with no import. All other
    /// cross-module names -- including the nested standard-library modules --
    /// are visible only where imported.
    pub prelude_modules: std::collections::HashSet<Vec<String>>,
    /// Names each module brings into scope via `import` (the bare names from
    /// every `import a.b.{ x, y }` in that module). Used by name resolution to
    /// enforce per-module visibility: a public name defined in another module
    /// is only visible where it is imported.
    pub module_imports: HashMap<Vec<String>, Vec<String>>,
    /// For each importing module, the origin module path of each imported local
    /// name (`importing module -> local name -> source module path`). Lets name
    /// resolution find the module-qualified symbol of an imported name when the
    /// same local name is defined in several modules.
    /// On an ambiguous import the first origin is kept; the ambiguity itself is
    /// reported separately.
    pub import_origins: HashMap<Vec<String>, HashMap<String, Vec<String>>>,
    /// Per-module map from LOCAL imported name to its REMOTE (original) name,
    /// for `import m.{ X as Y }` renames. Only populated for names where
    /// `local != remote`; a missing entry means the local name IS the remote
    /// name. Used by [`resolve_qualified`] to find the storage symbol.
    pub import_renames: HashMap<Vec<String>, HashMap<String, String>>,
    /// Per-module qualifiers from whole-module imports:
    /// importing module -> alias -> imported module path.
    pub module_aliases: HashMap<Vec<String>, HashMap<String, Vec<String>>>,
    /// Fully-qualified form -> canonical storage symbol, for every top-level
    /// item whose canonical symbol is the bare name (unique program-wide).
    pub symbol_aliases: HashMap<String, String>,
    /// Methods the standard library implements on primitive/array types with
    /// `fun T.m(...)` (e.g. `fun string.split` / `fun infer[].map`). Keyed by
    /// `(dispatch class, method name)` -> the implementing function's storage
    /// symbol; the body itself lives in `functions` under that symbol. The
    /// dispatch class is the receiver's primitive class ([`Type::primitive_class`]):
    /// a scalar type word (`"string"`, `"int32"`, ...) or `"array"`. Used to
    /// route a `recv.m()` call on a primitive receiver, replacing UFCS.
    pub primitive_methods: HashMap<(String, String), String>,
    /// Type aliases (`type Alias = <type expression>`): the alias name resolves
    /// to a pre-resolved type, typically a refinement of a nominal record
    /// (`type JsonObject = HashMap { key: string, value: JsonValue }`). Keyed by
    /// the alias's unique symbol, mirroring [`Self::types`]. An alias is not a
    /// nominal of its own; name resolution substitutes its target type.
    pub type_aliases: HashMap<String, TypeAlias>,
}

/// The members a primitive class carries without a `fun T.m` definition: the
/// growable-array operations and `len`, which the runtime implements directly.
fn builtin_member(class: &str, name: &str) -> bool {
    match class {
        "array" => matches!(name, "push" | "pop" | "insert" | "remove" | "len"),
        "string" => name == "len",
        _ => false,
    }
}

/// A resolved `type Alias = <type expression>` binding: the module it is
/// declared in and the concrete type its name expands to.
#[derive(Clone, Debug)]
pub struct TypeAlias {
    pub module: Vec<String>,
    pub ty: Type,
    pub span: Span,
}

impl Program {
    pub fn type_by_id(&self, id: i32) -> Option<&TypeInfo> {
        self.types.values().find(|t| t.id == id)
    }

    /// The compile-time presence of an uncalled member `x.m`: `Some(true)` when
    /// the receiver's class or declared type carries a METHOD `m`, `Some(false)`
    /// when it carries nothing of that name at all (a primitive class without
    /// the method, a sum where no variant declares such a field or method), and
    /// `None` when this rule says nothing and ordinary field lookup applies (a
    /// record's fields -- whose absent read is already `never?` -- and a sum
    /// field, common or not).
    ///
    /// This is what lets one generic body branch on its argument's concrete type:
    /// a present member types as its own name (a truthy string constant) and an
    /// absent one as the always-null `never?`, so the `if` folds statically and
    /// only the arm that fits the instantiation is checked and emitted. A
    /// declared method answers exactly like a primitive's, so
    /// `if v.m { v.m() } else { .. }` dispatches on method presence for records
    /// and sums too.
    pub fn member_presence(&self, ty: &Type, name: &str) -> Option<bool> {
        // Every primitive class supports the presence test: a member a scalar
        // receiver lacks reads as absent (`never?`, statically false) instead
        // of a hard error, so a generic presence-dispatching body (`if
        // x.frames { .. }`) instantiates at scalars too.
        if let Some(class) = ty.primitive_class() {
            return Some(
                self.primitive_methods
                    .contains_key(&(class.to_string(), name.to_string()))
                    || builtin_member(class, name),
            );
        }
        match ty {
            Type::Record(n) | Type::Sum(n) => {
                match &self.type_by_id(n.id)?.kind {
                    // A record's non-method member falls through to field
                    // lookup, whose absent read is already the null presence
                    // value.
                    TypeKind::Record { methods, .. } => methods.contains_key(name).then_some(true),
                    // A sum method is injected into every variant, so any
                    // variant answers. A name that is a FIELD of some variant
                    // falls through to the common-field rule (accessing a
                    // per-variant field without a `match` stays an error); a
                    // name found nowhere is statically absent, so a presence
                    // dispatch can send a sum through its else arm. A
                    // variant-scoped MIR read (`Err.error`, emitted by match
                    // arms and the error-propagation rebuilds) is not a surface
                    // member name and belongs to the sum field machinery.
                    TypeKind::Sum { variants } => {
                        if name.contains('.') {
                            return None;
                        }
                        if variants.iter().any(|v| v.methods.contains_key(name)) {
                            Some(true)
                        } else if variants
                            .iter()
                            .any(|v| v.fields.iter().any(|f| f.name == name))
                        {
                            None
                        } else {
                            Some(false)
                        }
                    }
                }
            }
            _ => None,
        }
    }

    pub fn type_ref(&self, name: &str) -> Option<Type> {
        self.types.get(name).map(TypeInfo::type_ref)
    }

    /// Whether any loaded type has the bare display name `name`, regardless of
    /// the module it lives in. Used by validation passes that only need to know
    /// a name denotes some type (not which one), so they do not false-positive
    /// on a module-qualified symbol such as `Name@a.b`.
    /// Resolve a dotted marker `"alias.bare"` against this module's alias
    /// table. Returns `None` for non-marker names (no dot).
    fn resolve_marker<'a, T>(
        &'a self,
        table: &'a HashMap<String, T>,
        module: &[String],
        name: &str,
    ) -> Option<&'a T> {
        let (alias, bare) = name.split_once('.')?;
        let target = self.module_aliases.get(module)?.get(alias)?;
        let qualified = qualify(bare, target);
        table.get(&qualified).or_else(|| {
            self.symbol_aliases
                .get(&qualified)
                .and_then(|c| table.get(c))
        })
    }

    pub fn has_type_named(&self, name: &str) -> bool {
        self.types.contains_key(name)
            || self
                .types
                .keys()
                .any(|k| k.starts_with(name) && k[name.len()..].starts_with('@'))
    }

    /// Resolve a bare type name to its definition as seen from `module`: its
    /// own/unique symbol, this module's qualified definition, or the one imported
    /// into this module.
    pub fn resolve_type(&self, module: &[String], name: &str) -> Option<&TypeInfo> {
        if let Some(v) = self.resolve_marker(&self.types, module, name) {
            return Some(v);
        }
        resolve_qualified(
            &self.types,
            &self.import_origins,
            &self.import_renames,
            module,
            name,
        )
    }

    /// The `Result` instance the fallibility sugar (`T!`, `error(..)`, an
    /// inferred fallible return, Ok-wrapping) builds in `module`'s scope: the
    /// prelude's Result, or the module's shadowing `type Result` sum. A
    /// shadow's declared payload annotation pins the corresponding slot; an
    /// unannotated payload takes the caller's `ok`/`err` (the annotation's
    /// payload or a fresh inference variable). Returns the required-shape
    /// message when the shadow is not `| Ok { value } | Err { error }`; the
    /// caller reports it and falls back to the built-in Result.
    pub fn scoped_result_instance(
        &self,
        module: &[String],
        ok: &Type,
        err: &Type,
    ) -> Result<Type, String> {
        let Some(info) = self.resolve_type(module, crate::types::RESULT_TYPE_NAME) else {
            return Ok(Type::result(ok.clone(), err.clone()));
        };
        if info.id == crate::types::RESULT_TYPE_ID {
            return Ok(Type::result(ok.clone(), err.clone()));
        }
        let shape_err = || {
            format!(
                "`{}` shadows the prelude's `Result` but is not `| Ok {{ value }} | Err {{ error }}`, \
                 the shape the fallibility sugar (`T!`, `error(..)`, `!`) builds",
                info.name
            )
        };
        let TypeKind::Sum { variants } = &info.kind else {
            return Err(shape_err());
        };
        if variants.len() != 2
            || variants[0].name != "Ok"
            || variants[0].fields.len() != 1
            || variants[0].fields[0].name != "value"
            || variants[1].name != "Err"
            || variants[1].fields.len() != 1
            || variants[1].fields[0].name != "error"
        {
            return Err(shape_err());
        }
        // An annotated payload field is the declaration's pin for that slot;
        // an unannotated one is generic and takes the caller's payload.
        let pin = |v: &VariantInfo, fallback: &Type| -> Type {
            if v.fields[0].ty.is_some() {
                v.fields[0]
                    .resolved_ty
                    .clone()
                    .unwrap_or_else(|| fallback.clone())
            } else {
                fallback.clone()
            }
        };
        let mut n = NominalType::new(info.id, crate::types::RESULT_TYPE_NAME);
        n.substitution
            .insert(crate::types::RESULT_OK_VALUE, pin(&variants[0], ok));
        n.substitution
            .insert(crate::types::RESULT_ERR_ERROR, pin(&variants[1], err));
        Ok(Type::Sum(n))
    }

    /// Resolve a bare free-function name to its definition as seen from `module`,
    /// by the same rule as [`Program::resolve_type`]. The canonical home for
    /// function resolution; back ends call this instead of re-deriving the symbol.
    pub fn resolve_function(&self, module: &[String], name: &str) -> Option<&FunInfo> {
        if let Some(v) = self.resolve_marker(&self.functions, module, name) {
            return Some(v);
        }
        resolve_qualified(
            &self.functions,
            &self.import_origins,
            &self.import_renames,
            module,
            name,
        )
    }

    /// The storage symbol a bare function `name` resolves to from `module`, if any.
    pub fn resolve_fn_symbol(&self, module: &[String], name: &str) -> Option<String> {
        self.resolve_function(module, name)
            .map(|f| f.symbol.clone())
    }

    /// Every sum type that defines a variant named `variant`, sorted by type
    /// name (then symbol). Two sums may share a variant name; callers that must
    /// pick one owner do so deterministically from this order -- the type table
    /// is a `HashMap` whose iteration order must never decide accept/reject.
    pub fn sums_containing_variant(&self, variant: &str) -> Vec<&TypeInfo> {
        let mut sums: Vec<&TypeInfo> = self
            .types
            .values()
            .filter(|info| match &info.kind {
                TypeKind::Sum { variants } => variants.iter().any(|v| v.name == variant),
                TypeKind::Record { .. } => false,
            })
            .collect();
        sums.sort_by(|a, b| a.name.cmp(&b.name).then_with(|| a.symbol.cmp(&b.symbol)));
        sums
    }
}
