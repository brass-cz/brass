//! Name resolution for Prepoly: module loading, imports, visibility, and a
//! reusable lexical scope.

pub mod loader;
pub mod module;
pub mod qualified;
pub mod scope;
pub mod visibility;

pub use loader::{
    LoadError, Located, STDLIB, STDLIB_NESTED, SourceMap, canonicalize_imports, is_prelude_path,
    load_module, load_std_nested, parse_stdlib, prelude_module_names, prelude_source,
};
pub use module::{ResolveError, check_imports};
pub use qualified::resolve_qualified_uses;
pub use scope::Scope;
pub use visibility::{is_private_module, is_public};
