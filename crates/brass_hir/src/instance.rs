//! The identity of one instance of a generic callable body.
//!
//! The checker elaborates a callable's body once per call-site instantiation
//! (its concrete argument types), and monomorphization types the same body
//! once per instance. Facts that differ between instances -- the type a
//! witness-free constructor builds, the specialization a reflective call
//! dispatches to -- cannot live in a channel keyed by source span alone, since
//! one span is shared by every instance. Such facts are keyed by
//! `(span, InstanceKey)` instead: the checker records them under the instance
//! it is elaborating, and monomorphization looks them up under the instance it
//! is typing. [`InstanceKey`] is the identity both sides compute the same way
//! from the callable, effective argument types and completed storage contract.

use brass_parser::Span;
use fxhash::FxHashMap;

use crate::hir::{Program, TypeKind};
use crate::types::{NominalType, Substitution, Type, is_fully_known, peel_modes};

/// The instance-specific values of a span-keyed checker channel. Entries hold
/// differing observations or contracts that cannot seed unseen instances, such
/// as numeric scalar storage. A span absent from the map may have a shared
/// value in its span-keyed channel. An instance missing from a span's entry
/// has no value there -- never another instance's.
pub type InstanceChannel<T> = FxHashMap<Span, FxHashMap<InstanceKey, T>>;

/// Primitive storage and call contracts in deterministic structural order.
/// Each path identifies a declaration or argument relative to its callable body.
/// Completed contracts are immutable and shared across keys and observations.
pub type NumericLayout = std::sync::Arc<Vec<(Vec<(usize, usize)>, Type)>>;

/// Body contracts selected at source calls or closure creation sites.
pub type NumericCalls = FxHashMap<(Span, Option<InstanceKey>), Option<NumericLayout>>;

/// One body-contract channel observation.
pub type NumericCallEntry = ((Span, Option<InstanceKey>), Option<NumericLayout>);

/// The callable an [`InstanceKey`] instantiates.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum InstanceCallable {
    /// A free function -- including a primitive/array method, which is stored
    /// and instantiated as a function -- by its storage symbol.
    Function(String),
    /// A record or sum method, by its owning type's storage symbol and its
    /// name. A whole-sum method is one callable however its call was qualified.
    Method { owner: String, method: String },
    /// A source closure, identified by its body span.
    Closure { lo: usize, hi: usize },
}

/// One instance of a callable: the callable plus the concrete types its body
/// is elaborated at, in parameter order. For an instance method the receiver
/// type comes first; a static method has no receiver entry.
///
/// The argument types are normalized by [`instance_key_type`], so the
/// checker's spelling of a type (a bare nominal, a `const` view) and
/// monomorphization's (a nominal carrying its declared field types) produce
/// the same key. A key exists only for fully known argument types: an
/// instance whose arguments are still open is not one monomorphization can
/// ever type.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct InstanceKey {
    pub callable: InstanceCallable,
    pub args: Vec<Type>,
    /// Completed local storage and nested call contracts at these effective inputs.
    pub numeric_layout: Option<NumericLayout>,
}

impl InstanceKey {
    /// The key of `callable` instantiated at `args`, or `None` when an argument
    /// type is not fully known.
    pub fn new(program: &Program, callable: InstanceCallable, args: &[Type]) -> Option<Self> {
        let args: Vec<Type> = args
            .iter()
            .map(|arg| instance_key_type(program, arg))
            .collect();
        args.iter().all(is_fully_known).then_some(InstanceKey {
            callable,
            args,
            numeric_layout: None,
        })
    }

    /// The key of free function `symbol` at `args` (see [`InstanceKey::new`]).
    pub fn function(program: &Program, symbol: &str, args: &[Type]) -> Option<Self> {
        Self::new(
            program,
            InstanceCallable::Function(symbol.to_string()),
            args,
        )
    }

    /// The key of method `method` of the type stored as `owner`, at `args`
    /// (receiver first for an instance method; see [`InstanceKey::new`]).
    pub fn method(program: &Program, owner: &str, method: &str, args: &[Type]) -> Option<Self> {
        Self::new(
            program,
            InstanceCallable::Method {
                owner: owner.to_string(),
                method: method.to_string(),
            },
            args,
        )
    }
}

/// The canonical spelling of `ty` inside an [`InstanceKey`]: passing modes are
/// dropped at every level (they do not change a value's representation), and
/// a declared record or sum keeps only the substitution entries its
/// declaration leaves open -- an annotated member has one type in every
/// instance, so whether a spelling carries it is no part of the identity.
/// Structural records keep every entry: their members are their identity.
pub fn instance_key_type(program: &Program, ty: &Type) -> Type {
    match peel_modes(ty) {
        Type::Record(n) => Type::Record(key_nominal(program, n)),
        Type::Sum(n) => Type::Sum(key_nominal(program, n)),
        Type::Nullable(inner) => Type::Nullable(Box::new(instance_key_type(program, inner))),
        Type::Slice(inner) => Type::Slice(Box::new(instance_key_type(program, inner))),
        Type::Array(inner, len) => Type::Array(Box::new(instance_key_type(program, inner)), *len),
        Type::Tuple(elems) => Type::Tuple(
            elems
                .iter()
                .map(|elem| instance_key_type(program, elem))
                .collect(),
        ),
        Type::Fun(params, ret) => Type::Fun(
            params
                .iter()
                .map(|param| instance_key_type(program, param))
                .collect(),
            Box::new(instance_key_type(program, ret)),
        ),
        other => other.clone(),
    }
}

/// [`instance_key_type`] of a nominal: the entries of members whose declared
/// type is fully known are dropped, the rest are normalized in turn.
fn key_nominal(program: &Program, n: &NominalType) -> NominalType {
    let info = (n.id >= 0).then(|| program.type_by_id(n.id)).flatten();
    let declared_known = |key: &str| -> bool {
        let Some(info) = info else {
            return false;
        };
        let fields = match &info.kind {
            TypeKind::Record { fields, .. } => fields.iter().find(|f| f.name == key),
            TypeKind::Sum { variants } => key.split_once('.').and_then(|(variant, field)| {
                variants
                    .iter()
                    .find(|v| v.name == variant)?
                    .fields
                    .iter()
                    .find(|f| f.name == field)
            }),
        };
        fields
            .and_then(|f| f.resolved_ty.as_ref())
            .is_some_and(is_fully_known)
    };
    let mut substitution = Substitution::empty();
    for (key, ty) in n.substitution.iter() {
        if !declared_known(key) {
            substitution.insert(key, instance_key_type(program, ty));
        }
    }
    NominalType::with_substitution(n.id, n.name.clone(), substitution)
}

/// Encode an exact completed body contract in an internal monomorphic base symbol.
/// Delimited spans and primitive type names preserve every structural key component.
pub fn numeric_instance_base(base: &str, layout: Option<&NumericLayout>) -> String {
    let Some(layout) = layout else {
        return base.to_owned();
    };
    use std::fmt::Write;
    let mut symbol = format!("{base}$numeric");
    for (path, ty) in layout.iter() {
        symbol.push('$');
        for (lo, hi) in path {
            write!(&mut symbol, "{lo:x}_{hi:x}.").unwrap();
        }
        symbol.push('=');
        for byte in format!("{ty:?}").bytes() {
            write!(&mut symbol, "{byte:02x}").unwrap();
        }
    }
    symbol
}
