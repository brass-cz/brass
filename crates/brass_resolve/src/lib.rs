//! Name resolution for Brass: module loading, imports, visibility, and a
//! reusable lexical scope.

pub mod frontend;
pub mod loader;
pub mod module;
pub mod plugin;
pub mod qualified;
pub mod scope;
pub mod visibility;

pub use loader::{
    LoadError, Located, MODULE_PATH_CONST, ModuleFile, STDLIB, SearchPaths, SourceMap,
    canonicalize_imports, inject_module_path, is_prelude_path, load_module, module_source,
    parse_stdlib, prelude_module_names, prelude_source, qualified_core_path, reinject_module_path,
    resolve_module_file,
};
pub use module::{ResolveError, check_imports};
pub use qualified::resolve_qualified_uses;
pub use scope::Scope;
pub use visibility::{is_private_module, is_public};
