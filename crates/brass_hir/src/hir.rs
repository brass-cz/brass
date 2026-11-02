//! The high-level intermediate representation: the whole program collected
//! into global type and function tables with numeric type ids assigned for the
//! runtime. Function and method bodies stay AST nodes: the checker types them
//! and MIR lowering lowers them, while the back ends read the type tables
//! (declared fields, variants, ids) to lay out values.

use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};
use std::rc::Rc;
use std::sync::Arc;

use brass_parser::Span;
use brass_parser::ast::{FunDecl, Method, Module, Param, Stmt, TypeExpr};

use crate::types::{NominalType, Type};

mod pattern_index;
pub use pattern_index::{PatternScope, PatternTypeHead};

/// Reserved id for the built-in `Result` type (matches the runtime).
pub use crate::types::RESULT_TYPE_ID;

/// Free-function names the runtime and the compiler own. A `.cz` definition of
/// one outside the prelude is rejected (it would capture the standard
/// library's internal calls, or -- for the prelude's `error` -- detach
/// `error(..)` from the fallibility sugar), and the plugin-module loader
/// renames a plugin function that lands on one rather than synthesizing a
/// module that cannot be checked.
pub const RESERVED_FUNCTION_NAMES: &[&str] =
    &["len", "spawn", "with", "sync", "error", "fields", "typeof"];

/// The canonical identity of a top-level definition: its local name plus the
/// module path it is defined in. The storage/codegen key (`symbol`) is its
/// `Display` form `name@a/b` -- the module path joins with `/`, never `.`, so the
/// key cannot collide with the `Type.Variant` separator used in method
/// qualifiers. Program tables are keyed by this string; the struct gives
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

const GENERATED_TYPE_PREFIX: &str = "\0brass-type:";

/// Encode a nominal id in an internal type-expression name. Reflective
/// specialization synthesizes annotations after module validation; carrying
/// the id prevents those annotations from reopening bare-name lookup in the
/// template's module or choosing the wrong same-named type.
pub fn generated_type_name(id: i32) -> String {
    format!("{GENERATED_TYPE_PREFIX}{id}")
}

/// Decode an internal nominal-id name produced by [`generated_type_name`].
/// Source text cannot spell the NUL-prefixed form, so it never bypasses normal
/// module visibility for user-written annotations.
pub fn generated_type_id(name: &str) -> Option<i32> {
    name.strip_prefix(GENERATED_TYPE_PREFIX)?.parse().ok()
}

/// Whether a definition from `definition_module` is visible under bare
/// `local_name` in `module`. Empty-module definitions are compiler intrinsics;
/// every other cross-module definition must be prelude-provided or imported
/// from its actual origin.
pub fn definition_is_visible(
    import_origins: &HashMap<Vec<String>, HashMap<String, Vec<String>>>,
    prelude_modules: &HashSet<Vec<String>>,
    module: &[String],
    local_name: &str,
    definition_module: &[String],
) -> bool {
    definition_module.is_empty()
        || definition_module == module
        || prelude_modules.contains(definition_module)
        || import_origins
            .get(module)
            .and_then(|origins| origins.get(local_name))
            .is_some_and(|origin| origin == definition_module)
}

/// Resolve a bare top-level `name` referenced from `module` against a program
/// table keyed by qualified symbol. `bare_is_visible` must validate the origin
/// of a program-wide unique bare entry; uniqueness alone does not put a name in
/// every module's scope. This is the one resolution rule shared by type,
/// function, and annotation lookups.
pub fn resolve_qualified<'a, T>(
    table: &'a HashMap<String, T>,
    import_origins: &HashMap<Vec<String>, HashMap<String, Vec<String>>>,
    import_renames: &HashMap<Vec<String>, HashMap<String, String>>,
    module: &[String],
    name: &str,
    bare_is_visible: impl Fn(&T) -> bool,
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
            .or_else(|| table.get(remote.as_str()).filter(|v| bare_is_visible(v)));
    }
    // The defining module's own qualified entry wins over a bare (unique)
    // definition elsewhere. For most names only one of the two forms exists
    // (a unique name keeps its bare symbol); `Result` is the exception -- the
    // prelude's declaration holds the bare key while a module's shadowing
    // declaration is always qualified, and the nearer scope must win.
    if let Some(v) = table.get(&qualify(name, module)) {
        return Some(v);
    }
    if let Some(origin) = import_origins
        .get(module)
        .and_then(|origins| origins.get(name))
        && let Some(v) = table.get(&qualify(name, origin))
    {
        return Some(v);
    }
    table.get(name).filter(|v| bare_is_visible(v))
}

/// The table key a dotted MARKER name denotes from `module`. The
/// qualified-use rewrite turns `alias.Name` (after a whole-module
/// `import a.b`) into the marker `"alias.Name"`; it denotes the definition of
/// `Name` in the module the alias names: its qualified symbol, or the bare
/// symbol a program-wide unique definition is stored under (found through
/// `symbol_aliases`). `in_table` answers whether a key is present in the table
/// being searched. `None` for a name without a dot, an alias `module` does
/// not have, or a definition the table does not hold.
///
/// Every resolution of a type or function name -- declaration annotations
/// during lowering as well as the checker and the back ends -- recognizes
/// markers through this one rule.
pub fn resolve_marker_key(
    module_aliases: &HashMap<Vec<String>, HashMap<String, Vec<String>>>,
    symbol_aliases: &HashMap<String, String>,
    module: &[String],
    name: &str,
    in_table: impl Fn(&str) -> bool,
) -> Option<String> {
    let (alias, bare) = name.split_once('.')?;
    let target = module_aliases.get(module)?.get(alias)?;
    let qualified = qualify(bare, target);
    if in_table(&qualified) {
        return Some(qualified);
    }
    symbol_aliases
        .get(&qualified)
        .filter(|canonical| in_table(canonical))
        .cloned()
}

/// A parsed source file tagged with its module path.
#[derive(Clone)]
pub struct LoadedModule {
    pub path: Vec<String>,
    pub ast: Module,
    /// Whether this is an implicit-prelude module (every `core/*.cz` module): its
    /// public names are visible everywhere with no import. Set by the loader
    /// that embeds the prelude; every other module -- including the nested
    /// standard-library ones -- requires an explicit import.
    pub is_prelude: bool,
    /// Shared resolver provenance; absent for AST graphs without a source route.
    pub source: Option<Arc<crate::ModuleSource>>,
}

/// A concrete method synthesized from a reflective `-> infer!` template.
///
/// Generated declarations are kept outside the parsed module graph so adding
/// one never mutates source ASTs; they are lowered after the unchanged
/// modules (see `lower_generated_into`).
#[derive(Clone, Debug)]
pub struct GeneratedDecl {
    pub module: Vec<String>,
    pub receiver: String,
    pub template: String,
    pub decl: FunDecl,
    pub key: Type,
}

/// A declared record field or variant payload field: its name, its written
/// annotation, and the type that annotation resolves to (filled by
/// declaration resolution).
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
    /// The signature of `fun name(..)` as written; the resolved types
    /// (`ParamInfo::resolved_ty`, `ret_ty`) are filled by annotation
    /// resolution.
    pub fn from_function(decl: &FunDecl) -> Self {
        Self {
            name: decl.name.clone(),
            params: decl.params.iter().map(ParamInfo::from).collect(),
            ret: decl.ret.clone(),
            ret_ty: None,
            span: decl.span,
        }
    }

    /// The signature of a method as written (see [`Self::from_function`]).
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
/// is retained for its body, which the checker and MIR lowering read as AST.
#[derive(Clone)]
pub struct MethodInfo {
    pub signature: CallableSignature,
    pub decl: Rc<Method>,
}

/// One variant of a sum type: its name, runtime tag, payload fields, and the
/// sum's methods (every variant carries the methods declared for the sum).
#[derive(Clone)]
pub struct VariantInfo {
    pub name: String,
    pub tag: i32,
    pub fields: Vec<FieldInfo>,
    pub methods: HashMap<String, MethodInfo>,
}

/// The shape of a declared type: a record (fields and methods) or a sum
/// (variants).
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

/// A declared record or sum type (`type T = ..`): its identity (`name`,
/// runtime `id`, storage `symbol`, defining `module`), its shape, and its
/// declaration metadata.
#[derive(Clone)]
pub struct TypeInfo {
    pub name: String,
    pub id: i32,
    pub interfaces: Vec<String>,
    /// Name-token spans corresponding to the implemented interfaces.
    pub interface_spans: Vec<Span>,
    pub kind: TypeKind,
    pub module: Vec<String>,
    pub span: Span,
    /// Globally unique storage/codegen key. Equal to the bare `name` when only
    /// one module defines that name, and module-qualified (`Name@a/b`) when the
    /// same type name is defined in several modules, so both coexist with
    /// distinct symbols and method-dispatch keys.
    pub symbol: String,
    /// Type slots (members declared `type slot`): a record's type parameters,
    /// each paired with the inference variable that stands for it. A slot has no
    /// runtime storage (it is not in `fields`); its variable appears in the other
    /// fields' resolved types wherever they wrote `Self.slot`, and a refinement
    /// (`Base { slot: T }`) or use fills it. Empty for a type without slots.
    pub slots: Vec<(String, u32)>,
    /// Doc comment from the `type` declaration, shown by editor tooling.
    pub doc: Option<String>,
}

impl TypeInfo {
    /// A bare reference to this type: its id and name, no substitution.
    pub fn nominal_ref(&self) -> NominalType {
        NominalType::new(self.id, &self.name)
    }

    /// [`Self::nominal_ref`] as a record or sum [`Type`].
    pub fn type_ref(&self) -> Type {
        match self.kind {
            TypeKind::Record { .. } => Type::Record(self.nominal_ref()),
            TypeKind::Sum { .. } => Type::Sum(self.nominal_ref()),
        }
    }

    pub fn is_sum(&self) -> bool {
        matches!(self.kind, TypeKind::Sum { .. })
    }
    /// Whether `T.from(v)` on this type is the builtin structural
    /// conversion: the type is a record with no declared static `from`.
    /// An instance method named `from` keeps structural conversion available;
    /// only a declaration without `self` shadows the static builtin.
    pub fn has_structural_from(&self) -> bool {
        !self.is_sum()
            && self.record_method("from").is_none_or(|method| {
                method
                    .params
                    .first()
                    .is_some_and(|param| param.name == "self")
            })
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

/// A top-level free function collected into the program. A primitive or
/// array method (`fun string.m(..)`, `fun T[].m(..)`) is stored as one too,
/// registered in [`Program::primitive_methods`].
pub struct FunInfo {
    pub signature: CallableSignature,
    pub decl: Rc<FunDecl>,
    pub module: Vec<String>,
    /// Globally unique storage/codegen key. Equal to the bare name when that
    /// name is defined in only one module; module-qualified (`name@a/b`) when
    /// the same local name is defined in several modules, so both definitions
    /// coexist with distinct symbols (a prelude function keeps the bare name;
    /// see `lower`).
    pub symbol: String,
}

/// Top-level statements of one module, run once at initialization.
pub struct ModuleInit {
    pub path: Vec<String>,
    pub stmts: Vec<Stmt>,
    /// Loader provenance for this module, including empty initializers. Absent
    /// for synthetic AST graphs without a source route.
    pub source: Option<Arc<crate::ModuleSource>>,
}

/// The collected, id-assigned program.
///
/// Changes to nominal identities, variant names/field counts, aliases or module
/// visibility must finish with [`Self::rebuild_resolution_indexes`] before any
/// resolution query. Field types and method bodies/signatures do not change
/// these indexes. Debug queries check declaration counts to catch missed rebuilds.
pub struct Program {
    pub types: HashMap<String, TypeInfo>,
    /// Nominal ids mapped to canonical symbols; rebuilt with the pattern indexes.
    pub(crate) types_by_id: HashMap<i32, String>,
    /// Canonical and local nominal names used for declaration membership tests.
    pub(crate) type_names: HashSet<String>,
    /// Declaration-only pattern facts, invalidated by topology changes.
    pub(crate) pattern_index: pattern_index::PatternIndex,
    /// One past the highest `Type::Unknown` id lowering minted into the
    /// resolved signature and field types above. Every solver that types
    /// against this program MUST seed its fresh-variable counter here
    /// (`Solver::seed_var_counter`): a solver-local variable that collides
    /// with an HIR-embedded id aliases an unrelated type and produces
    /// order-dependent phantom type errors.
    pub next_infer_var: u32,
    pub functions: HashMap<String, FunInfo>,
    /// The entry module's free `main`, independent of its storage-symbol spelling.
    pub(crate) entry_function: Option<String>,
    pub inits: Vec<ModuleInit>,
    /// Paths of the implicit-prelude modules (see [`LoadedModule::is_prelude`]):
    /// their public names are visible in every module with no import. All other
    /// cross-module names -- including the nested standard-library modules --
    /// are visible only where imported.
    pub prelude_modules: fxhash::FxHashSet<Vec<String>>,
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
    /// route a `recv.m()` call to a declared method on a primitive receiver.
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

/// How an unqualified braced pattern head resolves
/// ([`Program::braced_pattern_head`]). The checker and MIR lowering share
/// this, so a head is destructured the same way by both.
#[derive(Clone, Copy)]
pub enum BracedHead<'a> {
    /// A plain record pattern: fields are read by their own names.
    Record,
    /// A sum variant pattern: a tag test, then variant-scoped fields.
    Variant,
    /// The name is both a record type in scope and some sum's variant: a
    /// value of that record is destructured as the record, any other value
    /// as the variant (written `Sum.Name { .. }` to be explicit).
    RecordOrVariant(&'a TypeInfo),
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
    /// Construct a program with no declarations or module metadata.
    pub fn empty() -> Self {
        Self {
            types: HashMap::default(),
            types_by_id: HashMap::default(),
            type_names: HashSet::default(),
            pattern_index: pattern_index::PatternIndex::default(),
            next_infer_var: 0,
            functions: HashMap::default(),
            entry_function: None,
            inits: Vec::new(),
            prelude_modules: HashSet::default(),
            module_imports: HashMap::default(),
            import_origins: HashMap::default(),
            import_renames: HashMap::default(),
            module_aliases: HashMap::default(),
            symbol_aliases: HashMap::default(),
            primitive_methods: HashMap::default(),
            type_aliases: HashMap::default(),
        }
    }

    /// The entry module's free `main` storage symbol, if declared. Imported
    /// functions never become the entry, even when they have the only `main` name.
    pub fn entry_function(&self) -> Option<&str> {
        self.entry_function.as_deref()
    }

    /// The declaration with nominal identity `id`, when collected in this program.
    pub fn type_by_id(&self, id: i32) -> Option<&TypeInfo> {
        debug_assert_eq!(
            self.types.len(),
            self.types_by_id.len(),
            "rebuild resolution indexes after topology changes"
        );
        self.types_by_id
            .get(&id)
            .and_then(|symbol| self.types.get(symbol))
    }

    /// Find an implicit-prelude declaration independently of source-level
    /// shadowing. Compiler-synthesized values must use this identity.
    pub fn prelude_type(&self, name: &str) -> Option<&TypeInfo> {
        self.types
            .get(name)
            .filter(|info| self.prelude_modules.contains(&info.module))
            .or_else(|| {
                if !self.has_type_named(name) {
                    return None;
                }
                self.prelude_modules
                    .iter()
                    .find_map(|module| self.types.get(&qualify(name, module)))
            })
    }

    /// Whether a nominal id denotes the named implicit-prelude declaration.
    pub fn is_prelude_type(&self, id: i32, name: &str) -> bool {
        self.type_by_id(id)
            .is_some_and(|info| info.name == name && self.prelude_modules.contains(&info.module))
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

    /// A bare reference to the type stored under the symbol `name`.
    pub fn type_ref(&self, name: &str) -> Option<Type> {
        self.types.get(name).map(TypeInfo::type_ref)
    }

    /// Resolve a dotted marker `"alias.bare"` against this module's alias
    /// table. Returns `None` for non-marker names (no dot).
    fn resolve_marker<'a, T>(
        &'a self,
        table: &'a HashMap<String, T>,
        module: &[String],
        name: &str,
    ) -> Option<&'a T> {
        let key = resolve_marker_key(
            &self.module_aliases,
            &self.symbol_aliases,
            module,
            name,
            |k| table.contains_key(k),
        )?;
        table.get(&key)
    }

    /// Whether any loaded type has the bare display name `name`, regardless of
    /// the module it lives in. Used by validation passes that only need to know
    /// a name denotes some type (not which one), so they do not false-positive
    /// on a module-qualified symbol such as `Name@a.b`.
    pub fn has_type_named(&self, name: &str) -> bool {
        self.type_names.contains(name)
    }

    /// Whether any module declares a `type Alias = ..` named `name`, whatever
    /// module it lives in (its storage symbol is `name` or `name@a/b`). Like
    /// [`Self::has_type_named`], for passes that only need to know the name
    /// denotes some type.
    pub fn has_type_alias_named(&self, name: &str) -> bool {
        self.type_aliases.contains_key(name)
            || self.type_aliases.keys().any(|k| {
                k.strip_prefix(name)
                    .is_some_and(|rest| rest.starts_with('@'))
            })
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
            |info| {
                definition_is_visible(
                    &self.import_origins,
                    &self.prelude_modules,
                    module,
                    name,
                    &info.module,
                )
            },
        )
        .or_else(|| {
            let info = self.prelude_type(name)?;
            // A nearer alias shadows a colliding prelude nominal too.
            self.resolve_type_alias(module, name)
                .is_none()
                .then_some(info)
        })
    }

    /// Resolve a type alias as seen from `module`, preserving the alias's full
    /// target instance. Consumers that need a refinement's field substitution
    /// must use this instead of following only its nominal declaration.
    pub fn resolve_type_alias(&self, module: &[String], name: &str) -> Option<&TypeAlias> {
        if let Some(alias) = self.resolve_marker(&self.type_aliases, module, name) {
            return Some(alias);
        }
        resolve_qualified(
            &self.type_aliases,
            &self.import_origins,
            &self.import_renames,
            module,
            name,
            |alias| {
                definition_is_visible(
                    &self.import_origins,
                    &self.prelude_modules,
                    module,
                    name,
                    &alias.module,
                )
            },
        )
    }

    /// [`Self::resolve_type`], additionally seeing through a `type Alias =
    /// <nominal>` binding: an alias is not a nominal of its own and declares no
    /// methods, so a use that needs the underlying declaration -- a static
    /// method call's receiver, MIR call dispatch -- follows the alias to its
    /// target record/sum. A non-nominal alias target (e.g. `type Ints =
    /// int32[]`) yields `None`.
    pub fn resolve_type_or_alias(&self, module: &[String], name: &str) -> Option<&TypeInfo> {
        if let Some(v) = self.resolve_type(module, name) {
            return Some(v);
        }
        let alias = self.resolve_type_alias(module, name)?;
        match &alias.ty {
            Type::Record(n) | Type::Sum(n) => self.type_by_id(n.id),
            _ => None,
        }
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
            |info| {
                definition_is_visible(
                    &self.import_origins,
                    &self.prelude_modules,
                    module,
                    name,
                    &info.module,
                )
            },
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
        self.variant_owner_ids(variant)
            .iter()
            .filter_map(|id| self.type_by_id(*id))
            .collect()
    }

    /// Whether the variants of sum `info` are in scope in `module`, i.e.
    /// whether the sum itself is: declared there, declared in the implicit
    /// prelude, imported into `module` by name (including a rename or an
    /// imported alias of it), or exported by a module `module` imports whole
    /// (`import a` makes `a.Sum` and its variants reachable). A sum that is
    /// only reachable transitively, through a module some imported module
    /// imports, is not in scope.
    ///
    /// Bare unit-variant names resolve through this scope (see
    /// [`Self::is_unit_variant_in_scope`]); braced heads use global variant names.
    /// the checker and MIR lowering share it so they agree on which bare names
    /// are variant tests and which are bindings.
    pub fn sum_in_scope(&self, module: &[String], info: &TypeInfo) -> bool {
        if info.module.is_empty()
            || info.module == module
            || self.prelude_modules.contains(&info.module)
        {
            return true;
        }
        if self
            .module_aliases
            .get(module)
            .is_some_and(|aliases| aliases.values().any(|m| *m == info.module))
        {
            return true;
        }
        self.module_imports.get(module).is_some_and(|names| {
            names.iter().any(|local| {
                self.resolve_type_or_alias(module, local)
                    .is_some_and(|t| t.id == info.id)
            })
        })
    }

    /// Every sum in scope in `module` (see [`Self::sum_in_scope`]) that
    /// declares a variant named `variant`, in the deterministic order of
    /// [`Self::sums_containing_variant`].
    pub fn sums_in_scope_with_variant(&self, module: &[String], variant: &str) -> Vec<&TypeInfo> {
        self.pattern_scope(module)
            .owner_ids(variant)
            .iter()
            .filter_map(|id| self.type_by_id(*id))
            .collect()
    }

    /// Whether an unqualified bare-name pattern `name` written in `module` is
    /// a unit-variant test rather than a binding: some sum in scope there
    /// declares a FIELDLESS variant `name`. A variant of a sum that is not in
    /// scope never turns a binding into a test.
    pub fn is_unit_variant_in_scope(&self, module: &[String], name: &str) -> bool {
        self.pattern_scope(module).is_unit_variant(name)
    }

    /// How an unqualified braced pattern head `name { .. }` written in
    /// `module` resolves (see [`BracedHead`]). A dotted head is a
    /// module-qualified record type. Otherwise a record type in scope under
    /// that name and a sum variant spelled the same are told apart by the
    /// matched value; a head naming only a variant is that variant -- a braced
    /// head is never a binding, so the matched value's own sum decides which
    /// of several same-named variants it is.
    pub fn braced_pattern_head(&self, module: &[String], name: &str) -> BracedHead<'_> {
        self.pattern_scope(module).braced_head(name)
    }

    /// The record type an unqualified braced pattern head names in `module`,
    /// when one is in scope there (a type alias of a record included).
    pub fn record_pattern_head(&self, module: &[String], name: &str) -> Option<&TypeInfo> {
        match self.pattern_scope(module).type_head(name) {
            PatternTypeHead::Nominal(info) if !info.is_sum() => Some(info),
            _ => None,
        }
    }
}
