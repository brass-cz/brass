//! Source identities independent of lowering order and storage-symbol spelling.

use crate::{MethodInfo, Program, TypeInfo};
use brass_parser::Span;
use std::path::{Path, PathBuf};
use std::sync::Arc;

/// A resolver root's identity, shared by modules loaded through that root.
/// Paths identify an in-process source graph, not a persistent cache entry.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PackageId(Arc<Path>);

impl PackageId {
    /// Name the root selected by the resolver without another filesystem search.
    pub fn new(root: &Path) -> Self {
        Self(Arc::from(root))
    }
}

/// A source location and its canonical loaded namespace. Import aliases and
/// span relocation do not affect it; two namespaces backed by one file differ.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ModuleId {
    location: Arc<Path>,
    namespace: Arc<[String]>,
}

impl ModuleId {
    /// Use the loader's source location, including labels for embedded sources.
    pub fn new(location: impl Into<PathBuf>, namespace: &[String]) -> Self {
        Self {
            location: Arc::from(location.into()),
            namespace: Arc::from(namespace),
        }
    }
}

/// Ownership follows the resolver route rather than physical path containment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SourceOrigin {
    /// Source supplied by the entry's local route or its owning package.
    Own(PackageId),
    /// Source supplied by a package map or an external include root.
    Dependency(PackageId),
    /// Embedded implicit-prelude source.
    Core,
    /// Wrapper synthesized from a native library's manifest.
    Plugin(PackageId),
}

/// Loader provenance retained by HIR, including the source-local span conversion.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModuleSource {
    /// Captured source location, shared by context-only and combined lowering.
    pub location: PathBuf,
    /// Ownership assigned by resolution, never inferred from declaration names.
    pub origin: SourceOrigin,
    /// Offset added by parsing to every source-local byte position.
    pub base: usize,
    /// Source byte length, excluding the separator between parsed sources.
    pub len: usize,
}

impl ModuleSource {
    /// Build an identity from captured provenance and the containing module's
    /// canonical namespace, without consulting the filesystem again.
    pub fn module_id(&self, namespace: &[String]) -> ModuleId {
        ModuleId::new(self.location.clone(), namespace)
    }
}

/// Distinguishes declaration categories that can share a source position.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ItemKind {
    /// A source function, including primitive receiver functions.
    Function,
    /// A nominal declaration or alias.
    Type,
    /// The ordered statements belonging to one loaded module.
    Initializer,
}

/// A source declaration's identity; global span shifts and symbol collisions do
/// not affect it. Generated specializations require their own keyed identity.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ItemId {
    /// The declaration's source module.
    pub module: ModuleId,
    /// Byte position within that source, not the assembled program.
    pub offset: usize,
    /// Declaration category at that position.
    pub kind: ItemKind,
}

/// A source method body in a particular nominal/variant checking context.
/// Copies of a sum method share the source position but have different tags.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MethodBodyId {
    /// Nominal declaration that owns this method.
    pub owner: ItemId,
    /// The method's declaration source, which can share its owner's namespace
    /// without sharing its file (an imported `main` and the entry, for example).
    pub module: ModuleId,
    /// Method declaration position within its own source.
    pub offset: usize,
    /// Declaration name, including the canonical key suffix of a generated
    /// specialization. Generated bodies retain their template's source offset.
    pub name: String,
    /// The sum variant's declaration-order tag; absent for records.
    pub variant: Option<i32>,
}

/// Why an item is observed as a checking root or dependency. Observation does
/// not imply selection and never changes the checker's current work order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Reason {
    /// An explicitly owned source declaration.
    Own,
    /// A loaded module's initialization statements.
    Initializer,
    /// A resolved source-level use.
    ExplicitUse,
    /// Dispatch introduced by a language operation.
    ImplicitUse,
    /// A body checked to prepare shared inference state.
    SharedInference,
    /// A concrete reflective specialization.
    Generated,
    /// A body requested by the execution driver.
    Demand,
}

impl Program {
    /// Read provenance by namespace and source span. Namespace alone cannot
    /// distinguish an imported `main` from the entry. Synthetic graphs and spans
    /// outside a matching source return none.
    pub fn module_source(&self, module: &[String], span: Span) -> Option<&ModuleSource> {
        self.inits
            .iter()
            .filter(|init| init.path == module)
            .filter_map(|init| init.source.as_deref())
            .find(|source| {
                span.lo >= source.base && span.hi >= span.lo && span.hi - source.base <= source.len
            })
    }

    /// Find a source item's identity without relying on its storage symbol.
    /// Synthetic programs without loader provenance have no source identity.
    pub fn item_id(&self, module: &[String], span: Span, kind: ItemKind) -> Option<ItemId> {
        let source = self.module_source(module, span)?;
        Some(ItemId {
            module: source.module_id(module),
            offset: span.lo.checked_sub(source.base)?,
            kind,
        })
    }

    /// Identify an ordinary method in its exact variant checking context.
    pub fn method_body_id(
        &self,
        owner: &TypeInfo,
        method: &MethodInfo,
        variant: Option<i32>,
    ) -> Option<MethodBodyId> {
        let id = self.item_id(&owner.module, owner.span, ItemKind::Type)?;
        let source = self.module_source(&owner.module, method.decl.span)?;
        Some(MethodBodyId {
            owner: id,
            module: source.module_id(&owner.module),
            offset: method.decl.span.lo.checked_sub(source.base)?,
            variant,
            name: method.signature.name.clone(),
        })
    }
}
