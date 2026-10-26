//! The type reference a MIR local carries.
//!
//! MIR is built *before* type concretization: the control
//! flow graph is type-independent, so a local starts as a fresh type
//! *variable*. Monomorphization walks the body for a concrete
//! call instance and replaces each variable with a `Known` concrete type, after
//! which a back end selects operations purely from these types. Lowering
//! starts a local as `Known` only where its type is fixed before any instance
//! is typed: a resolvable source annotation, or a type the checker recorded
//! for the expression (see `BodyBuilder::fresh_local_typed` and
//! `BodyBuilder::fresh_seeded_local`).

use std::fmt;

use brass_hir::Type;

/// A local's type, possibly still abstract.
#[derive(Clone, Debug, PartialEq)]
pub enum TypeRef {
    /// An unresolved type variable, identified within its body. Lowering assigns
    /// each local a distinct variable; monomorphization binds them.
    Var(u32),
    /// An unresolved variable bound to the JOIN of the values the local is
    /// assigned: the result of a value-producing `if`/`if let`/`match`, which
    /// each arm writes. Monomorphization types it like the checker types the
    /// expression -- numeric arm values meet by `brass_typesys::join_values`
    /// (a literal arm adapts, `int32` widens to `int64`) -- rather than from
    /// whichever arm it types first.
    Join(u32),
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
            TypeRef::Var(_) | TypeRef::Join(_) => None,
        }
    }

    /// Whether this is a join variable ([`TypeRef::Join`]).
    pub fn is_join(&self) -> bool {
        matches!(self, TypeRef::Join(_))
    }
}

impl fmt::Display for TypeRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeRef::Var(id) => write!(f, "?{id}"),
            TypeRef::Join(id) => write!(f, "?join{id}"),
            TypeRef::Known(ty) => f.write_str(&ty.display()),
        }
    }
}
