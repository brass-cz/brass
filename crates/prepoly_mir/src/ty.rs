//! The type reference a MIR local carries.
//!
//! MIR is built *before* type concretization: the control
//! flow graph is type-independent, so every local starts as a fresh type
//! *variable*. Monomorphization walks the body for a concrete
//! call instance and replaces each variable with a `Known` concrete type, after
//! which type-driven codegen selects instructions purely from these types. The
//! `Known` variant also lets a future lowering seed types it already knows (for
//! example from a parameter annotation) without changing the IR shape.

use std::fmt;

use prepoly_hir::Type;

/// A local's type, possibly still abstract.
#[derive(Clone, Debug, PartialEq)]
pub enum TypeRef {
    /// An unresolved type variable, identified within its body. Lowering assigns
    /// each local a distinct variable; monomorphization binds them.
    Var(u32),
    /// A concrete (or partially-known) type already resolved during lowering.
    /// May itself contain `Type::Unknown` for genuinely deferred positions.
    Known(Type),
}

impl TypeRef {
    pub fn var(id: u32) -> Self {
        TypeRef::Var(id)
    }

    pub fn known(ty: Type) -> Self {
        TypeRef::Known(ty)
    }

    /// The concrete type, if this reference has already been resolved.
    pub fn as_known(&self) -> Option<&Type> {
        match self {
            TypeRef::Known(ty) => Some(ty),
            TypeRef::Var(_) => None,
        }
    }
}

impl fmt::Display for TypeRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeRef::Var(id) => write!(f, "?{id}"),
            TypeRef::Known(ty) => f.write_str(&ty.display()),
        }
    }
}
