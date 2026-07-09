//! The high-level intermediate representation: the whole program collected
//! into global type and function tables with numeric type ids assigned for the
//! runtime. Records and sum types keep their members (as AST nodes, lowered
//! on demand by codegen); this is the "typed HIR" the back end consumes.

use std::collections::HashMap;
use std::rc::Rc;

use prepoly_parser::Span;
use prepoly_parser::ast::{FunDecl, Method, Module, Param, Stmt, TypeExpr};

use crate::types::{NominalType, Type};

/// Reserved id for the built-in `Result` type (matches the runtime).
pub use crate::types::RESULT_TYPE_ID;

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
    if let Some(v) = table.get(name) {
        return Some(v);
    }
    if let Some(v) = table.get(&qualify(name, module)) {
        return Some(v);
    }
    let origin = import_origins.get(module)?.get(name)?;
    table.get(&qualify(name, origin))
}

/// A parsed source file tagged with its module path.
#[derive(Clone)]
pub struct LoadedModule {
    pub path: Vec<String>,
    pub ast: Module,
    /// Whether this is an implicit-prelude module (`std/prelude/*.pp`): its
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
/// environment (see `prepoly_typeck`). `params` are the inference-variable ids
/// the generalization quantifies (the `K`/`V` of a `HashMap`); `fields` and
/// `methods` carry types expressed over those ids. A binding or call instantiates
/// the scheme by renaming `params` to fresh variables. A monomorphic record (no
/// inferred field, e.g. a fully-annotated `Point`) has an empty `params`.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct TypeScheme {
    pub params: Vec<u32>,
    pub fields: Vec<(String, Type)>,
    pub methods: std::collections::BTreeMap<String, SchemeMethod>,
}

/// A method's signature within a [`TypeScheme`]: parameter types (including the
/// leading `self`) and the return type, all expressed over the scheme's `params`.
#[derive(Clone, Debug, PartialEq)]
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
