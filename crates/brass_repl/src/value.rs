//! The runtime value of the REPL interpreter.
//!
//! Unlike the typed LLVM back end, which unboxes every value to a concrete
//! machine representation, the interpreter walks monomorphized MIR with a single
//! boxed `Value`. The concrete type of each operand is still known (the engine
//! resolved it during monomorphization), so the interpreter consults the operand
//! type for width/sign-sensitive integer arithmetic and for rendering -- the
//! `Value` itself only needs to distinguish the runtime shapes. Heap shapes
//! (strings, arrays, records, variants, closures) are reference-counted via `Rc`
//! so aliasing matches the language's reference semantics, and `RefCell` gives the
//! in-place field/element mutation `obj.f = v` and `arr[i] = v` perform.

use fxhash::FxHashMap as HashMap;
use std::cell::RefCell;
use std::rc::Rc;

use brass_hir::Type;
use brass_mir::ClosureId;

/// The deepest nesting a single value may be walked to (rendering, deep copy)
/// before the walk errs out. Self-referential record types can build reference
/// cycles, which would otherwise recurse without bound; the limit mirrors the
/// interpreter's call-depth cap (`MAX_DEPTH` in [`crate::interp`]).
pub(crate) const MAX_VALUE_DEPTH: usize = 8000;

/// A boxed runtime value. Integers of every width are carried in an `i64`,
/// normalized to their declared width/sign after each operation (see
/// [`crate::interp`]); a present nullable is represented by its inner value and an
/// absent one by [`Value::Null`], so the nullable cell is implicit.
#[derive(Clone)]
pub enum Value {
    Int(i64),
    Float(f64),
    Bool(bool),
    Str(Rc<str>),
    /// A growable/fixed array; the element values share the same boxed `Value`.
    Array(Rc<RefCell<Vec<Value>>>),
    /// A record object: its fields keyed by name (declaration order is recovered
    /// from the type when rendering, so insertion order does not matter).
    Record(Rc<RefCell<HashMap<String, Value>>>),
    /// A sum-type value: the active variant name plus that variant's fields.
    Variant(Rc<VariantObj>),
    /// A closure value: the captured environment plus the type tuple needed to
    /// resolve its monomorphized instance on an indirect call.
    Closure(Rc<ClosureObj>),
    /// The `null` of a nullable (a null pointer in the typed back end).
    Null,
    /// The unit value of `void` (a discarded result).
    Void,
}

/// A constructed sum-type value.
pub struct VariantObj {
    pub variant: String,
    pub fields: RefCell<HashMap<String, Value>>,
}

/// A closure value. The capture and parameter types are retained so an indirect
/// call can recompute the closure's instance symbol
/// (`brass_engine::closure_symbol`) and look up its monomorphized body, exactly
/// as the typed back end resolves the function pointer it stores at construction.
pub struct ClosureObj {
    pub id: ClosureId,
    pub capture_types: Vec<Type>,
    pub captures: Vec<Value>,
    pub param_types: Vec<Type>,
}

impl Value {
    /// The `i64`-carried integer, for arithmetic and indexing. Callers only invoke
    /// this where the operand type already proved the value is an integer.
    pub fn as_int(&self) -> i64 {
        match self {
            Value::Int(v) => *v,
            Value::Bool(b) => *b as i64,
            _ => 0,
        }
    }

    pub fn as_float(&self) -> f64 {
        match self {
            Value::Float(v) => *v,
            Value::Int(v) => *v as f64,
            _ => 0.0,
        }
    }

    pub fn as_bool(&self) -> bool {
        match self {
            Value::Bool(b) => *b,
            Value::Null => false,
            _ => true,
        }
    }

    pub fn as_str(&self) -> &str {
        match self {
            Value::Str(s) => s,
            _ => "",
        }
    }

    pub fn is_null(&self) -> bool {
        matches!(self, Value::Null)
    }

    pub fn str(s: impl Into<String>) -> Value {
        Value::Str(Rc::from(s.into().as_str()))
    }
}
