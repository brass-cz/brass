//! Name resolution for Brass: module loading, imports, and visibility.

pub mod frontend;
pub mod loader;
pub mod module;
pub mod plugin;
pub mod qualified;
pub mod visibility;

pub use loader::{
    LoadError, Located, MODULE_PATH_CONST, ModuleFile, STDLIB, SearchPaths, SourceMap,
    canonicalize_imports, inject_module_path, is_prelude_path, load_modules, module_source,
    parse_stdlib, prelude_module_names, prelude_source, qualified_core_path,
};
pub use module::{ResolveError, check_imports};
pub use qualified::resolve_qualified_uses;
pub use visibility::{is_private_module, is_public};
