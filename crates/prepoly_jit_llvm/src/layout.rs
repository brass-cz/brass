//! The LLVM ABI layer: the typed (unboxed) LLVM representation of Prepoly types
//! and lazy declarations of the runtime's C-ABI primitives that compiled code
//! calls (DESIGN.md 8.1, 9.1).

use inkwell::AddressSpace;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum, FunctionType};
use inkwell::values::FunctionValue;

use prepoly_hir::{IntKind, Type};

/// ABI helpers bound to a module/context for the lifetime of code generation.
pub struct Abi<'ctx> {
    pub ctx: &'ctx Context,
}

impl<'ctx> Abi<'ctx> {
    pub fn new(ctx: &'ctx Context) -> Self {
        Abi { ctx }
    }

    pub fn i64t(&self) -> inkwell::types::IntType<'ctx> {
        self.ctx.i64_type()
    }

    pub fn ptr(&self) -> inkwell::types::PointerType<'ctx> {
        self.ctx.ptr_type(AddressSpace::default())
    }

    /// The typed (unboxed) LLVM representation of a Prepoly type, for the typed
    /// monomorphized backend (DESIGN.md 8.1; PLAN.md R5). Primitives map to LLVM
    /// primitives (`bool` -> `i1`, `intN`/`uintN` -> `iN`, `float32/64` ->
    /// `f32/f64`); every heap or reference value (string, record, sum, slice,
    /// array, closure, nullable, `Result`, and not-yet-typed unknowns) is a
    /// pointer-sized typed handle. `void` has no value representation and is
    /// reported by [`Abi::typed_return`].
    pub fn typed_basic(&self, ty: &Type) -> BasicTypeEnum<'ctx> {
        match ty {
            Type::Bool => self.ctx.bool_type().into(),
            Type::Int(k) => match int_bits(*k) {
                8 => self.ctx.i8_type().into(),
                16 => self.ctx.i16_type().into(),
                32 => self.ctx.i32_type().into(),
                _ => self.ctx.i64_type().into(),
            },
            Type::Float(prepoly_hir::FloatKind::F32) => self.ctx.f32_type().into(),
            Type::Float(prepoly_hir::FloatKind::F64) => self.ctx.f64_type().into(),
            Type::ConstOf(inner) | Type::Mut(inner) | Type::Ref(inner) => self.typed_basic(inner),
            // Heap/reference values and anything not yet given a typed layout
            // cross as an opaque pointer handle.
            _ => self.ptr().into(),
        }
    }

    /// The typed LLVM return representation: `None` for `void` (no value).
    pub fn typed_return(&self, ty: &Type) -> Option<BasicTypeEnum<'ctx>> {
        match ty {
            Type::Void => None,
            _ => Some(self.typed_basic(ty)),
        }
    }

    /// The typed LLVM function signature for a fully-known callable, e.g.
    /// `fun add(a: int32, b: int32) -> int32` becomes `i32 (i32, i32)` -- the
    /// unboxed signature the monomorphized backend emits (PLAN.md R5).
    pub fn typed_fn_type(&self, params: &[Type], ret: &Type) -> FunctionType<'ctx> {
        let param_tys: Vec<BasicMetadataTypeEnum> =
            params.iter().map(|t| self.typed_basic(t).into()).collect();
        match self.typed_return(ret) {
            Some(r) => r.fn_type(&param_tys, false),
            None => self.ctx.void_type().fn_type(&param_tys, false),
        }
    }

    /// The typed LLVM signature of a closure instance: a leading environment
    /// pointer (the closure object, from which captures are read) followed by the
    /// declared parameter types. `(x) -> x + n` capturing `n` becomes
    /// `i32 (ptr, i32)`.
    pub fn typed_closure_fn_type(&self, params: &[Type], ret: &Type) -> FunctionType<'ctx> {
        let mut param_tys: Vec<BasicMetadataTypeEnum> = vec![self.ptr().into()];
        param_tys.extend(
            params
                .iter()
                .map(|t| -> BasicMetadataTypeEnum { self.typed_basic(t).into() }),
        );
        match self.typed_return(ret) {
            Some(r) => r.fn_type(&param_tys, false),
            None => self.ctx.void_type().fn_type(&param_tys, false),
        }
    }

    /// Declare (or fetch) a runtime function by name with a given signature.
    pub fn runtime_fn(
        &self,
        module: &Module<'ctx>,
        name: &str,
        ty: FunctionType<'ctx>,
    ) -> FunctionValue<'ctx> {
        module
            .get_function(name)
            .unwrap_or_else(|| module.add_function(name, ty, None))
    }
}

/// Bit width of an integer kind, for its unboxed LLVM `iN` type.
fn int_bits(k: IntKind) -> u32 {
    match k {
        IntKind::I8 | IntKind::U8 => 8,
        IntKind::I16 | IntKind::U16 => 16,
        IntKind::I32 | IntKind::U32 => 32,
        IntKind::I64 | IntKind::U64 => 64,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use inkwell::types::BasicTypeEnum;
    use prepoly_hir::FloatKind;

    /// The typed backend (PLAN.md R5) lowers `fun add(a: int32, b: int32) ->
    /// int32` to the unboxed signature `i32 (i32, i32)`.
    #[test]
    fn typed_signature_unboxes_primitives() {
        let ctx = Context::create();
        let abi = Abi::new(&ctx);
        let i32t = Type::Int(IntKind::I32);
        let fty = abi.typed_fn_type(&[i32t.clone(), i32t.clone()], &i32t);

        let params = fty.get_param_types();
        assert_eq!(params.len(), 2);
        assert!(
            params
                .iter()
                .all(|p| matches!(p, BasicMetadataTypeEnum::IntType(t) if t.get_bit_width() == 32))
        );
        let ret = fty.get_return_type().expect("non-void return");
        assert!(matches!(ret, BasicTypeEnum::IntType(t) if t.get_bit_width() == 32));
    }

    #[test]
    fn typed_layout_maps_each_primitive() {
        let ctx = Context::create();
        let abi = Abi::new(&ctx);
        assert!(
            matches!(abi.typed_basic(&Type::Bool), BasicTypeEnum::IntType(t) if t.get_bit_width() == 1)
        );
        assert!(
            matches!(abi.typed_basic(&Type::Int(IntKind::U8)), BasicTypeEnum::IntType(t) if t.get_bit_width() == 8)
        );
        assert!(
            matches!(abi.typed_basic(&Type::Int(IntKind::I64)), BasicTypeEnum::IntType(t) if t.get_bit_width() == 64)
        );
        assert!(matches!(
            abi.typed_basic(&Type::Float(FloatKind::F32)),
            BasicTypeEnum::FloatType(_)
        ));
        assert!(matches!(
            abi.typed_basic(&Type::Float(FloatKind::F64)),
            BasicTypeEnum::FloatType(_)
        ));
        // Heap/reference values are opaque typed handles (pointers).
        assert!(matches!(
            abi.typed_basic(&Type::Str),
            BasicTypeEnum::PointerType(_)
        ));
    }

    /// A `void` return has no value type; the function type returns void.
    #[test]
    fn typed_void_return_has_no_value() {
        let ctx = Context::create();
        let abi = Abi::new(&ctx);
        assert!(abi.typed_return(&Type::Void).is_none());
        let fty = abi.typed_fn_type(&[Type::Int(IntKind::I32)], &Type::Void);
        assert!(fty.get_return_type().is_none(), "void fn returns no value");
    }
}
