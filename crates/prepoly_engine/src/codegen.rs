//! The backend-agnostic, *typed* code-generation trait.
//!
//! [`Codegen`] is the seam between the engine and a concrete back end. Unlike a
//! boxed uniform-value ABI, every value here has a concrete type: the engine has
//! already monomorphized the program (see [`crate::mono`]) so each local, each
//! operand, and each call has a known [`prepoly_hir::Type`]. The trait splits in
//! two:
//!
//!  - *Leaf* methods perform one typed low-level operation -- materialize a typed
//!    constant, an `iN`/`fN` arithmetic op, a typed call, a branch -- and are the
//!    only methods a back end implements. They are where inkwell (or any target)
//!    lives; this crate names no such dependency.
//!  - *Default* methods walk the monomorphized MIR and compose the leaves,
//!    resolving the concrete type of every operand/result from the instance's
//!    `local_types` and passing it to the leaves.
//!
//! The associated [`Codegen::Value`] is the back end's typed value handle (an
//! LLVM SSA value, or a debug string in tests); the default methods only move it
//! between leaves and never inspect it.

use prepoly_hir::Type;
use prepoly_mir::{
    BlockId, Callee, ClosureId, Literal, LocalId, MirStmt, Operand, Projection, Rvalue, Terminator,
};
use prepoly_parser::ast::{BinOp, UnaryOp};

use crate::mono::{
    MonoFunction, MonoProgram, binary_operand_type, float_kind_name, instance_symbol,
    int_kind_name, is_comparison, method_symbol, numeric_conv_ret, operand_type_of,
    prim_method_instance, static_symbol, unwrap_nullable,
};

/// Whether a type is a reference-counted heap object the back end tracks with
/// retain/release: strings, records, sums, and arrays/slices.
/// Closures are excluded (see below). An array's heap elements and a sum's heap
/// fields are not yet released recursively, so they leak rather than
/// use-after-free (they were retained on store); scalar-content aggregates and all
/// strings/records reclaim fully.
pub fn rc_managed(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Str
            | Type::Record(..)
            | Type::Sum(..)
            | Type::Slice(..)
            | Type::Array(..)
            | Type::Fun(..)
            // A tuple is a fixed heterogeneous heap aggregate (a pointer), tracked
            // and reclaimed like a record.
            | Type::Tuple(..)
            // A nullable is a heap cell (a pointer, null = null), so it is
            // reference-counted: retained when aliased, released when dropped. A cell
            // of a managed value also owns that value (its destructor releases it).
            | Type::Nullable(..)
    )
}

/// Whether storing a `value_ty` value into a `dest_ty` slot is a nullable wrap: a
/// non-nullable value flowing into a nullable cell. `nullable_wrap` builds a fresh
/// cell that already owns its content, so the storing slot takes that ownership
/// without an extra retain (retaining the fresh cell would over-count it -- it is an
/// intermediate, never separately dropped).
fn is_nullable_wrap(dest_ty: &Type, value_ty: &Type) -> bool {
    matches!(dest_ty, Type::Nullable(_)) && !matches!(value_ty, Type::Nullable(_))
}

/// The locals moved out by a `spawn` (their reference is transferred to the new
/// thread, which releases the closure when it finishes). R6's capture analysis
/// guarantees such a value is not live after the spawn, so excluding it from the
/// spawner's end-of-scope releases is the move -- not a leak or a use-after-free.
fn spawn_moved_locals(f: &MonoFunction) -> std::collections::HashSet<LocalId> {
    let mut moved = std::collections::HashSet::new();
    let mut scan = |rv: &Rvalue| {
        if let Rvalue::Call(Callee::Builtin(name), args) = rv
            && name == "spawn"
            && let Some(Operand::Local(id)) = args.first()
        {
            moved.insert(*id);
        }
    };
    for block in &f.body.blocks {
        for s in &block.stmts {
            match s {
                MirStmt::Assign(_, rv) | MirStmt::Eval(rv) => scan(rv),
                _ => {}
            }
        }
    }
    moved
}

/// Whether an rvalue yields a *second reference to an existing object* (an alias)
/// rather than a freshly-owned value. Aliases must be retained when bound; fresh
/// values (call results, constructions, literals) already own their single
/// reference.
fn is_alias_rvalue(rv: &Rvalue) -> bool {
    matches!(
        rv,
        Rvalue::Use(Operand::Local(_)) | Rvalue::Load(_) | Rvalue::Global(_)
    )
}

/// Whether an operand is an alias of an existing object (a local read), as opposed to
/// a fresh value (a literal constant). Storing an alias into an aggregate must retain
/// it (a second reference); a fresh constant is already owned at count 1 and the
/// aggregate takes that ownership -- retaining it would leak, since a constant has no
/// local binding whose drop would balance the retain.
fn operand_is_alias(op: &Operand) -> bool {
    matches!(op, Operand::Local(_))
}

/// Whether an rvalue *bound to a local* yields an alias of an existing managed
/// object and so must be retained: a plain alias rvalue, or `to_string`/`string.from`
/// of a string (its identity result is a second reference to the argument). The
/// conversion is recognized here rather than in the back end's leaf so that an
/// unbound, transient conversion (e.g. inside `print`) is not retained and leaked.
fn binds_alias(rv: &Rvalue, local_types: &[Type]) -> bool {
    if is_alias_rvalue(rv) {
        return true;
    }
    // Rendering a string is the identity, so the result aliases the argument. Both
    // the implicit interpolation builtin (`to_string`) and the explicit `string.from`
    // static call lower to that same identity leaf, so a bound result of either must
    // be retained -- otherwise its later drop over-releases the borrowed argument
    // (e.g. `let a = string.from(key)` used twice double-frees `key`). For a
    // non-string argument the conversion allocates a fresh owned string, not an alias.
    let str_identity_arg = match rv {
        Rvalue::Call(Callee::Builtin(name), args) if name == "to_string" => args.first(),
        Rvalue::Call(Callee::Static { ty, method }, args) if ty == "string" && method == "from" => {
            args.first()
        }
        _ => None,
    };
    if let Some(arg) = str_identity_arg {
        return matches!(operand_type_of(arg, local_types), Type::Str);
    }
    if let Rvalue::Call(Callee::Builtin(name), args) = rv
        && name == "__nonnull"
        && let Some(arg) = args.first()
    {
        return rc_managed(unwrap_nullable(&operand_type_of(arg, local_types)));
    }
    false
}

/// Whether the program uses `with` -- and so opens regions and needs the write
/// barrier on heap stores. A back end consults this so a sequential (region-free)
/// program emits no barriers and pays no barrier cost.
pub fn program_uses_with(program: &MonoProgram) -> bool {
    fn rv_with(rv: &Rvalue) -> bool {
        // `_with_all` is the auto-acquire pass's group form of `with`; a program
        // whose only guards are group wraps still shares cowns across threads, so
        // it needs the same barriers.
        matches!(rv, Rvalue::Call(Callee::Builtin(n), _) if n == "with" || n == "_with_all")
    }
    program.functions.iter().any(|f| {
        f.body.blocks.iter().any(|b| {
            b.stmts.iter().any(|s| match s {
                MirStmt::Assign(_, rv) | MirStmt::Eval(rv) => rv_with(rv),
                _ => false,
            })
        })
    })
}

/// A typed code-generation back end for monomorphized MIR.
pub trait Codegen {
    /// The back end's typed value handle.
    type Value: Copy;

    // ===== program / body lifecycle (leaf) =====

    /// Declare every instance's function (typed signature) before any body is
    /// emitted, so calls and recursion resolve.
    fn begin_program(&mut self, program: &MonoProgram);

    /// Finish emission: verify and build the executable form (e.g. the JIT
    /// engine).
    fn finalize(&mut self) -> Result<(), String>;

    /// Run the entry point (`main`) if present.
    fn execute(&mut self) -> Result<(), String>;

    /// Enter an instance body: select its typed function, position at its entry,
    /// prepare a block per MIR block, allocate typed local storage, and bind the
    /// typed parameters.
    fn begin_body(&mut self, func: &MonoFunction);

    /// Leave the current body.
    fn end_body(&mut self);

    /// Position emission at the start of MIR block `id`.
    fn begin_block(&mut self, id: BlockId);

    // ===== locals (leaf) =====
    // The back end knows each local's concrete type from `begin_body`.

    fn load_local(&mut self, id: LocalId) -> Self::Value;
    fn store_local(&mut self, id: LocalId, v: Self::Value);

    // ===== typed constants (leaf) =====

    fn const_int(&mut self, v: i64, ty: &Type) -> Self::Value;
    fn const_float(&mut self, v: f64, ty: &Type) -> Self::Value;
    fn const_bool(&mut self, v: bool) -> Self::Value;
    /// A string literal (a typed string handle).
    fn const_str(&mut self, s: &str) -> Self::Value;
    /// The `null` value of a nullable type (a null pointer).
    fn const_null(&mut self) -> Self::Value;
    /// Truthiness of a non-bool condition `v` of type `ty` (a nullable is truthy
    /// when non-null); yields an `i1`.
    fn truthy(&mut self, v: Self::Value, ty: &Type) -> Self::Value;
    /// Coerce `v` from type `from` to type `to`. The only nontrivial cases are
    /// integer width changes (a narrower loop counter compared against a wider
    /// `len`, sign/zero extended) and float widening; otherwise identity.
    fn coerce(&mut self, v: Self::Value, from: &Type, to: &Type) -> Self::Value;
    /// The unit value of `void` (never observed; used for discarded results).
    fn unit(&mut self) -> Self::Value;

    // ===== strings (leaf) =====

    /// The byte length of string `s` (the `len` builtin).
    fn string_len(&mut self, s: Self::Value) -> Self::Value;
    /// Render value `v` of type `ty` as a string (string interpolation).
    fn to_string(&mut self, v: Self::Value, ty: &Type) -> Self::Value;
    /// The substring `[start, end)` of `s` (`_string_slice`).
    fn string_slice(&mut self, s: Self::Value, start: Self::Value, end: Self::Value)
    -> Self::Value;
    /// The bytes of `s` as a `uint8[]` (`_string_bytes`).
    fn string_to_bytes(&mut self, s: Self::Value) -> Self::Value;
    /// The byte index of `sub` in `s`, or null (`_string_find`): an `int64?`.
    fn string_find(&mut self, s: Self::Value, sub: Self::Value) -> Self::Value;
    /// Concatenate two strings (`_string_concat`; also what `+` lowers to).
    fn string_concat(&mut self, a: Self::Value, b: Self::Value) -> Self::Value;
    /// Lexicographic comparison of two strings (`_string_cmp`): an `int32` -1/0/1.
    fn string_cmp(&mut self, a: Self::Value, b: Self::Value) -> Self::Value;
    /// The character at byte offset `i` of `s`, or null (`_string_char_at`).
    fn string_char_at(&mut self, s: Self::Value, i: Self::Value) -> Self::Value;
    /// A string from a `uint8[]` (`_string_from_bytes`): a `Result<string, string>`.
    fn string_from_bytes(&mut self, bytes: Self::Value) -> Self::Value;
    /// `open(path, mode)`: a `Result<File, string>`.
    fn file_open(&mut self, path: Self::Value, mode: Self::Value) -> Self::Value;
    /// A standard stream as a `File`: `which` is 0 = stdin, 1 = stdout, 2 = stderr
    /// (`File.stdin`/`File.stdout`/`File.stderr`).
    fn file_std(&mut self, which: u8) -> Self::Value;
    /// `file.read(n)`: a `Result<uint8[], string>` of up to `n` bytes.
    fn file_read(&mut self, file: Self::Value, n: Self::Value) -> Self::Value;
    /// `file.write(bytes)`: a `Result<int64, string>` (bytes written).
    fn file_write(&mut self, file: Self::Value, bytes: Self::Value) -> Self::Value;
    /// `file.size()`: a `Result<int64, string>`.
    fn file_size(&mut self, file: Self::Value) -> Self::Value;
    /// `file.seek(pos)`: a `Result<void, string>` (reposition the cursor).
    fn file_seek(&mut self, file: Self::Value, pos: Self::Value) -> Self::Value;
    /// `file.close()`: a `Result<void, string>`.
    fn file_close(&mut self, file: Self::Value) -> Self::Value;
    /// A numeric conversion `target.method(arg)` (`from`/`parse`): returns a
    /// typed `Result` for fallible cases, or the value for infallible `float.from`.
    fn convert(
        &mut self,
        target: &Type,
        method: &str,
        arg_ty: &Type,
        arg: Self::Value,
    ) -> Self::Value;
    /// `_int_widen(x, from_bits, to_bits, signed)`: widen an integer to a larger
    /// width (always succeeds), returning the `int64`-carried value.
    fn int_widen(
        &mut self,
        x: Self::Value,
        from_bits: Self::Value,
        to_bits: Self::Value,
        signed: Self::Value,
    ) -> Self::Value;
    /// `_int_narrow(x, from_bits, to_bits, signed)`: narrow an integer, returning a
    /// typed `Result<int64, string>` that is `Err` on overflow.
    fn int_narrow(
        &mut self,
        x: Self::Value,
        from_bits: Self::Value,
        to_bits: Self::Value,
        signed: Self::Value,
    ) -> Self::Value;

    // ===== typed primitive operations (leaf) =====

    /// A non-short-circuiting binary operator on two operands of type
    /// `operand_ty` (e.g. an `i32` add or an `f64` compare).
    fn bin_op(
        &mut self,
        op: BinOp,
        a: Self::Value,
        b: Self::Value,
        operand_ty: &Type,
    ) -> Self::Value;
    fn un_op(&mut self, op: UnaryOp, a: Self::Value, operand_ty: &Type) -> Self::Value;

    // ===== typed call (leaf) =====

    /// Call the instance named `symbol`, returning a value of type `ret` (the
    /// back end returns [`Codegen::unit`] for a `void` callee).
    fn call(&mut self, symbol: &str, args: &[Self::Value], ret: &Type) -> Self::Value;

    /// Deferred dispatch: resolve-or-compile the consumer named
    /// `consumer` for the runtime type named `type_name`, then call it on `value`,
    /// returning its `int32` result. The back end emits a call to the runtime
    /// dispatch trampoline for the resolution and an indirect call for the
    /// dispatch.
    fn deferred_dispatch(
        &mut self,
        consumer: &str,
        type_name: &str,
        value: Self::Value,
    ) -> Self::Value;

    // ===== records (leaf) =====

    /// Construct a record of type `record_ty` (a `Type::Record` whose
    /// substitution gives each field's concrete type) from its named field
    /// values, returning a typed handle to the heap object.
    fn make_record(&mut self, record_ty: &Type, fields: &[(&str, Self::Value)]) -> Self::Value;
    /// Read field `field` of an aggregate `base` (record or sum, of type
    /// `base_ty`).
    fn load_field(&mut self, base: Self::Value, base_ty: &Type, field: &str) -> Self::Value;
    /// Store `v` into field `field` of record `base` (of type `base_ty`).
    fn store_field(&mut self, base: Self::Value, base_ty: &Type, field: &str, v: Self::Value);

    // ===== sum types (leaf) =====

    /// Construct the `variant` of sum type `sum_ty` from its named field values.
    fn make_variant(
        &mut self,
        sum_ty: &Type,
        variant: &str,
        fields: &[(&str, Self::Value)],
    ) -> Self::Value;
    /// A boolean: whether `subj` (of type `subj_ty`) is the named variant (for a
    /// sum, a tag comparison; a record always matches its sole shape).
    fn pattern_matches(&mut self, subj: Self::Value, subj_ty: &Type, variant: &str) -> Self::Value;
    /// Abort with a runtime message (the unmatched-`match` fallthrough).
    fn emit_panic(&mut self, msg: &str);
    /// Abort with a runtime string `msg` *value* (the user-facing `_panic(msg)`,
    /// where the message is computed, not a compile-time literal).
    fn runtime_panic(&mut self, msg: Self::Value);

    // ===== I/O (leaf) =====

    /// Write string `s` to stdout, with a trailing newline for `println`.
    fn emit_print(&mut self, s: Self::Value, newline: bool);

    // ===== concurrency (leaf) =====

    /// Run a zero-argument closure on a new thread (`spawn`).
    fn spawn(&mut self, closure: Self::Value);
    /// Promote a `spawn` capture to a shared owner before the spawn, so its
    /// reference count is maintained atomically once it is reachable from another
    /// thread: `freeze` deep-freezes a read-only capture to immutable; `make_cown`
    /// makes a mutated capture a cown (still mutated under its `with` lock).
    fn freeze(&mut self, value: Self::Value);
    fn make_cown(&mut self, value: Self::Value);
    /// Join every thread spawned so far (`sync`), so their effects are observable
    /// before execution continues.
    fn thread_join_all(&mut self);
    /// Increment a heap value's reference count: a new persistent reference to it
    /// is being created. The engine calls this only for
    /// reference-counted (heap) values; scalars never reach it.
    fn retain(&mut self, value: Self::Value);
    /// Decrement a heap value's reference count, freeing the (leaf) object at zero.
    /// Used for strings; records go through [`Codegen::release_record`].
    fn release(&mut self, value: Self::Value);
    /// Decrement an aggregate's reference count and, at zero, release the heap
    /// contents it owns before freeing it (a per-type destructor): a record's
    /// string/record fields, or an array's element buffer. `ty` gives the layout.
    fn release_obj(&mut self, value: Self::Value, ty: &Type);
    /// Release a closure: invoke the capture-releasing destructor stored in the
    /// closure object (the `Fun` type hides the capture types, so the destructor is
    /// emitted at construction and dispatched through the object).
    fn release_closure(&mut self, value: Self::Value);
    /// Acquire / release a cown object's lock around `with`-guarded access.
    fn cown_lock(&mut self, obj: Self::Value);
    fn cown_unlock(&mut self, obj: Self::Value);
    /// Acquire / release every cown in an array, for `with([c1, c2], f)`.
    fn cown_lock_all(&mut self, arr: Self::Value);
    fn cown_unlock_all(&mut self, arr: Self::Value);
    /// Acquire / release a group of individually typed cown values, for the
    /// compiler-inserted `_with_all(f, c0, c1, ...)` wrap. The runtime acquires
    /// them in address order, so overlapping groups emitted in any textual order
    /// share one global lock order and cannot deadlock each other.
    fn cown_lock_many(&mut self, objs: &[Self::Value]);
    fn cown_unlock_many(&mut self, objs: &[Self::Value]);

    /// Open a region with `bridge` as its entry object; returns
    /// the region id, which `region_close` consumes.
    fn region_open(&mut self, bridge: Self::Value) -> Self::Value;
    /// Verify closedness on region release: the back end aborts if
    /// a reference into the region escaped during the `with` scope.
    fn region_close(&mut self, region_id: Self::Value);
    /// The write barrier: maintain region membership and the local
    /// reference count when `value` is stored into `container`.
    fn region_write(&mut self, container: Self::Value, value: Self::Value);
    /// Whether to emit region write barriers -- true when the program uses `with`,
    /// so a sequential program pays no barrier cost (the default).
    fn emit_region_barrier(&self) -> bool {
        false
    }

    /// A pure float math primitive (`_float_sqrt`/`_float_floor`/`_float_ceil`/
    /// `_float_pow`), e.g. an LLVM intrinsic.
    fn float_builtin(&mut self, name: &str, args: &[Self::Value]) -> Self::Value;

    // ===== globals (leaf) =====

    /// Write `v` to module-level global `name` (of type `ty`).
    fn store_global(&mut self, name: &str, ty: &Type, v: Self::Value);
    /// Read module-level global `name` (of type `ty`).
    fn load_global(&mut self, name: &str, ty: &Type) -> Self::Value;

    // ===== arrays (leaf) =====

    /// Build a fixed array of element type `elem_ty` from its elements.
    fn make_array(&mut self, elem_ty: &Type, elems: &[Self::Value]) -> Self::Value;
    /// Build a fixed-length tuple from its element values (each with its own type).
    fn make_tuple(&mut self, elem_types: &[Type], elems: &[Self::Value]) -> Self::Value;
    /// Read element `index` of `tup` (a tuple of `elem_types`) at a static position.
    fn tuple_field(&mut self, tup: Self::Value, elem_types: &[Type], index: usize) -> Self::Value;
    /// Read element `idx` of array `arr` (of type `arr_ty`).
    fn load_index(&mut self, arr: Self::Value, arr_ty: &Type, idx: Self::Value) -> Self::Value;
    /// Store `v` into element `idx` of array `arr` (of type `arr_ty`).
    fn store_index(&mut self, arr: Self::Value, arr_ty: &Type, idx: Self::Value, v: Self::Value);
    /// The element count of array `arr`.
    fn array_len(&mut self, arr: Self::Value) -> Self::Value;
    /// Append `v` (of element type `elem_ty`) to growable array `arr`.
    fn push(&mut self, arr: Self::Value, elem_ty: &Type, v: Self::Value);
    /// Insert `v` (of element type `elem_ty`) at index `idx` of growable array
    /// `arr`, shifting later elements toward the end.
    fn insert(&mut self, arr: Self::Value, elem_ty: &Type, idx: Self::Value, v: Self::Value);
    /// Remove and return the element at index `idx` of growable array `arr` (of
    /// element type `elem_ty`), shifting later elements toward the front.
    fn remove(&mut self, arr: Self::Value, elem_ty: &Type, idx: Self::Value) -> Self::Value;
    /// Remove and return the last element of growable array `arr` as a nullable
    /// (`elem_ty?`): the element value, or null when `arr` is empty.
    fn pop(&mut self, arr: Self::Value, elem_ty: &Type) -> Self::Value;
    /// A fresh, independent deep copy of `value` of type `ty` (the value-passing of
    /// a non-reference heap argument): an aggregate (array/slice/record/sum/tuple)
    /// is recursively copied; any other value is returned with its reference count
    /// balanced so the caller-side temporary owns a reference.
    fn deep_copy(&mut self, value: Self::Value, ty: &Type) -> Self::Value;

    // ===== closures (leaf) =====

    /// Build a closure value of type `fun_ty` (a `Fun` type) for closure `id`,
    /// capturing the given (type, value) pairs into its environment.
    fn make_closure(
        &mut self,
        fun_ty: &Type,
        id: ClosureId,
        captures: &[(Type, Self::Value)],
    ) -> Self::Value;
    /// Call a closure value `callee` (of `Fun` type `callee_ty`) with `args`.
    fn call_indirect(
        &mut self,
        callee: Self::Value,
        callee_ty: &Type,
        args: &[Self::Value],
    ) -> Self::Value;

    // ===== terminators (leaf) =====

    /// Return from the current body: `Some(v)` for a value, `None` for `void`.
    fn emit_return(&mut self, v: Option<Self::Value>);
    fn emit_goto(&mut self, target: BlockId);
    /// Branch on a boolean (`i1`) condition.
    fn emit_cond_branch(&mut self, cond: Self::Value, then: BlockId, els: BlockId);
    fn emit_unreachable(&mut self);

    // ===== default dispatch (provided) =====

    fn codegen_program(&mut self, program: &MonoProgram) {
        for f in &program.functions {
            self.codegen_function(program, f);
        }
    }

    fn codegen_function(&mut self, program: &MonoProgram, f: &MonoFunction) {
        self.begin_body(f);
        // A statically-folded `if` (a `never?` or non-nullable condition) leaves
        // one arm unreachable. Such an arm may hold values the back end cannot
        // emit -- a bare `null` narrowed to `never` -- so it is skipped, its
        // block terminated as `unreachable` to stay well-formed. The matching
        // `CondBranch` folds to a direct jump (see `codegen_terminator`).
        let reachable = crate::mono::reachable_blocks(f.body, &f.local_types, &f.ret);
        for (i, live) in reachable.iter().enumerate() {
            let id = BlockId(i as u32);
            if *live {
                self.codegen_block(program, f, id);
            } else {
                self.begin_block(id);
                self.emit_unreachable();
            }
        }
        self.end_body();
    }

    fn codegen_block(&mut self, program: &MonoProgram, f: &MonoFunction, id: BlockId) {
        self.begin_block(id);
        let block = f.body.block(id);
        for s in &block.stmts {
            self.codegen_stmt(program, f, s);
        }
        self.codegen_terminator(program, f, &block.term);
    }

    fn codegen_stmt(&mut self, program: &MonoProgram, f: &MonoFunction, s: &MirStmt) {
        match s {
            MirStmt::Assign(local, rv) => {
                let dest = f.local_type(*local).clone();
                // Reassigning a managed local drops its previous value. Snapshot it
                // first (the rvalue may read the old value), release it after the
                // new value is stored. Parameters are skipped: they are borrowed
                // from the caller, who owns the original. A closure moved into a
                // `spawn` is skipped too: the thread now owns it and releases it, so
                // the spawner must not release it here -- otherwise reassigning the
                // local (a `spawn` in a loop) frees a closure a thread still runs.
                let old = if rc_managed(&dest)
                    && !f.body.params.contains(local)
                    && !(matches!(dest, Type::Fun(..)) && spawn_moved_locals(f).contains(local))
                {
                    Some(self.load_local(*local))
                } else {
                    None
                };
                let v = self.codegen_rvalue(program, f, rv, &dest);
                self.store_local(*local, v);
                // An alias binding (copy of a local, field/index/global read, or
                // `to_string` of a string) makes a second reference to an existing
                // object, so the count must rise; a fresh value (other call
                // results, construction) is already owned at count 1.
                // A nullable wrap is fresh too (the cell already owns its content), so
                // an aliased value wrapped into a nullable is not retained again.
                let wrap = match rv {
                    Rvalue::Use(op) => {
                        is_nullable_wrap(&dest, &operand_type_of(op, &f.local_types))
                    }
                    _ => false,
                };
                if rc_managed(&dest) && binds_alias(rv, &f.local_types) && !wrap {
                    self.retain(v);
                }
                if let Some(old) = old {
                    self.emit_release(old, &dest);
                }
            }
            // A call run for its side effect; the result (if any) is discarded.
            MirStmt::Eval(rv) => {
                let _ = self.codegen_rvalue(program, f, rv, &Type::Void);
            }
            // Store into a record field or an array element. The container gains a
            // reference to the stored value, so a managed value is retained.
            MirStmt::Store(place, op) => match place.proj.as_slice() {
                [Projection::Field(field)] => {
                    let raw_ty = f.local_type(place.local).clone();
                    let base = self.load_local(place.local);
                    let (base, base_ty) = self.unwrap_narrowed(base, &raw_ty);
                    let fty = record_field_type(&base_ty, field);
                    let op_ty = operand_type_of(op, &f.local_types);
                    let v = self.codegen_operand(program, f, op, &fty);
                    self.store_field(base, &base_ty, field, v);
                    // Retain an aliased managed value (a second reference). A fresh
                    // constant is owned at 1, and a coerced nullable wrap is a fresh
                    // cell that already owns its content -- both transfer ownership to
                    // the field without an extra retain.
                    if rc_managed(&fty) && operand_is_alias(op) && !is_nullable_wrap(&fty, &op_ty) {
                        self.retain(v);
                        // Region write barrier: the container now references `v`.
                        if self.emit_region_barrier() {
                            self.region_write(base, v);
                        }
                    }
                }
                [Projection::Index(idx)] => {
                    let raw_ty = f.local_type(place.local).clone();
                    let arr = self.load_local(place.local);
                    let (arr, arr_ty) = self.unwrap_narrowed(arr, &raw_ty);
                    let elem_ty = element_type(&arr_ty);
                    let op_ty = operand_type_of(op, &f.local_types);
                    let v = self.codegen_operand(program, f, op, &elem_ty);
                    let iv = self.codegen_operand(program, f, idx, &index_type(idx, f));
                    self.store_index(arr, &arr_ty, iv, v);
                    if rc_managed(&elem_ty)
                        && operand_is_alias(op)
                        && !is_nullable_wrap(&elem_ty, &op_ty)
                    {
                        self.retain(v);
                        if self.emit_region_barrier() {
                            self.region_write(arr, v);
                        }
                    }
                }
                _ => {}
            },
            // Write a module-level global with its concrete (init) type.
            MirStmt::SetGlobal(name, op) => {
                let gty = program.global_type(name).cloned().unwrap_or(Type::Void);
                let v = self.codegen_operand(program, f, op, &gty);
                self.store_global(name, &gty, v);
                if rc_managed(&gty) {
                    self.retain(v);
                }
            }
        }
    }

    /// Release a managed value according to its type: a record runs its recursive
    /// destructor (releasing the heap fields it owns), a string (or other leaf
    /// managed value) the plain release.
    fn emit_release(&mut self, value: Self::Value, ty: &Type) {
        match ty {
            // Aggregates with owned heap contents (record fields, array elements +
            // buffer, a sum variant's payload fields) run a per-type destructor; a
            // closure runs the capture-releasing destructor stored in its object; a
            // string is a leaf, freed directly.
            Type::Record(..) | Type::Slice(..) | Type::Array(..) | Type::Sum(..) => {
                self.release_obj(value, ty)
            }
            // A nullable cell runs a destructor too: it releases its value (when that
            // value is itself managed), then frees the cell.
            Type::Nullable(..) => self.release_obj(value, ty),
            Type::Fun(..) => self.release_closure(value),
            _ => self.release(value),
        }
    }

    /// Release every managed local that is dead at a return: not a parameter (the
    /// caller owns those), not a capture (the closure environment owns those), not
    /// the value being returned (moved to the caller), and not a closure moved out
    /// by `spawn` (the thread now owns it and releases it). A local unassigned on
    /// this path is null-initialized, so its release is a no-op.
    fn emit_drops(&mut self, f: &MonoFunction, returned: Option<LocalId>) {
        let spawn_moved = spawn_moved_locals(f);
        for (i, ty) in f.local_types.iter().enumerate() {
            if !rc_managed(ty) {
                continue;
            }
            let id = LocalId(i as u32);
            if Some(id) == returned
                || f.body.params.contains(&id)
                || f.captures.contains(&id)
                || spawn_moved.contains(&id)
            {
                continue;
            }
            let ty = ty.clone();
            let v = self.load_local(id);
            self.emit_release(v, &ty);
        }
    }

    fn codegen_terminator(&mut self, program: &MonoProgram, f: &MonoFunction, t: &Terminator) {
        match t {
            Terminator::Return(op) => {
                // A non-void function's synthesized fall-through return (the MIR
                // builder terminates an unterminated final block with
                // `Return(void)`): unreachable when the checker accepted the body
                // -- every real return sits inside a loop that never exits (e.g.
                // `while true`). Emitting it would return a unit placeholder at
                // the wrong machine type (an LLVM verifier error); terminate the
                // path with a trap instead, defined if a checker hole ever
                // reaches it. A *fallible* body is exempt: its return type is
                // `Result<void, ..>`-like while the body's fall-through is a bare
                // `void` that the wrapping below turns into a real `Ok` value.
                if !f.fallible
                    && !matches!(f.ret, Type::Void)
                    && matches!(op, Operand::Const(Literal::Void))
                {
                    self.emit_panic("missing return");
                    self.emit_unreachable();
                    return;
                }
                let returned = op.as_local();
                // A returned parameter is borrowed from the caller, so hand the
                // caller a counted reference; a returned non-parameter local is
                // moved out (excluded from the drops below).
                if let Some(x) = returned {
                    let xty = f.local_type(x).clone();
                    if rc_managed(&xty) && f.body.params.contains(&x) {
                        let rv = self.load_local(x);
                        self.retain(rv);
                    }
                }
                self.emit_drops(f, returned);
                if matches!(f.ret, Type::Void) {
                    self.emit_return(None);
                } else {
                    let op_ty = operand_type_of(op, &f.local_types);
                    // A fallible callable implicitly wraps a bare (non-Result)
                    // return value as `Result.Ok { value: v }`.
                    if f.fallible && !is_result_ty(&op_ty) {
                        let ok_ty = result_ok_type(&f.ret);
                        let v = self.codegen_operand(program, f, op, &ok_ty);
                        let ret = f.ret.clone();
                        let wrapped = self.make_variant(&ret, "Ok", &[("value", v)]);
                        self.emit_return(Some(wrapped));
                    } else {
                        let ret = f.ret.clone();
                        let v = self.codegen_operand(program, f, op, &ret);
                        self.emit_return(Some(v));
                    }
                }
            }
            Terminator::Goto(b) => self.emit_goto(*b),
            Terminator::CondBranch { cond, then, els } => {
                // A statically-known condition folds to a direct jump, leaving the
                // dead arm (skipped in `codegen_function`) without a predecessor.
                // The fold also covers a structural `if` whose then-branch cannot
                // type for this concrete value (see `cond_static_truthiness`).
                let cty = operand_type_of(cond, &f.local_types);
                match crate::mono::cond_static_truthiness(
                    f.body,
                    &f.local_types,
                    &f.ret,
                    cond,
                    *then,
                ) {
                    Some(true) => self.emit_goto(*then),
                    Some(false) => self.emit_goto(*els),
                    // A bool branches directly; any other (runtime) type is reduced
                    // to an i1 truthiness test (a nullable tests non-null).
                    None => {
                        let c = if matches!(cty, Type::Bool) {
                            self.codegen_operand(program, f, cond, &Type::Bool)
                        } else {
                            let v = self.codegen_operand(program, f, cond, &cty);
                            self.truthy(v, &cty)
                        };
                        self.emit_cond_branch(c, *then, *els);
                    }
                }
            }
            Terminator::Unreachable => self.emit_unreachable(),
        }
    }

    fn codegen_rvalue(
        &mut self,
        program: &MonoProgram,
        f: &MonoFunction,
        rv: &Rvalue,
        dest_ty: &Type,
    ) -> Self::Value {
        match rv {
            Rvalue::Use(op) => self.codegen_operand(program, f, op, dest_ty),
            Rvalue::Bin(op, a, b) => {
                // Comparisons yield bool but operate on the operands' type;
                // arithmetic/bitwise/shift operate on (and yield) the dest type.
                let operand_ty = if is_comparison(*op) {
                    binary_operand_type(a, b, &f.local_types)
                } else {
                    dest_ty.clone()
                };
                let va = self.codegen_operand(program, f, a, &operand_ty);
                let vb = self.codegen_operand(program, f, b, &operand_ty);
                self.bin_op(*op, va, vb, &operand_ty)
            }
            // `!x` is logical/null negation; pass the operand's own type so the
            // back end can test a nullable for null (vs. negate a bool).
            Rvalue::Un(UnaryOp::Not, a) => {
                let aty = operand_type_of(a, &f.local_types);
                let va = self.codegen_operand(program, f, a, &aty);
                self.un_op(UnaryOp::Not, va, &aty)
            }
            Rvalue::Un(op, a) => {
                let va = self.codegen_operand(program, f, a, dest_ty);
                self.un_op(*op, va, dest_ty)
            }
            Rvalue::Call(callee, args) => {
                let from = self
                    .call_result_type(program, f, callee, args, dest_ty)
                    .unwrap_or_else(|| dest_ty.clone());
                let v = self.codegen_call(program, f, callee, args, dest_ty);
                if matches!(dest_ty, Type::Void) {
                    v
                } else {
                    self.coerce(v, &from, dest_ty)
                }
            }
            // Construct a record: `dest_ty` is its concrete type, carrying each
            // field's type in its substitution.
            Rvalue::Record { fields, .. } => {
                let mut named: Vec<(&str, Self::Value)> = Vec::with_capacity(fields.len());
                let mut managed: Vec<Self::Value> = Vec::new();
                for (name, op) in fields {
                    let fty = record_field_type(dest_ty, name);
                    let op_ty = operand_type_of(op, &f.local_types);
                    let v = self.codegen_operand(program, f, op, &fty);
                    // Same ownership rule as `MirStmt::Store`: a nullable wrap is a
                    // fresh cell that already owns its content, so retaining it too
                    // would over-count the cell (it is never separately dropped).
                    if rc_managed(&fty) && operand_is_alias(op) && !is_nullable_wrap(&fty, &op_ty) {
                        managed.push(v);
                    }
                    named.push((name.as_str(), v));
                }
                let rec = self.make_record(dest_ty, &named);
                // The record now references each managed field value; retain the ones
                // that are aliases (a fresh constant is already owned at count 1).
                for v in managed {
                    self.retain(v);
                }
                rec
            }
            // `T.from(v)`: a fallible structural conversion. `dest_ty` is `T?`; per
            // instance the source's concrete type is known, so the branch is decided
            // here. When the source record has every field `T` declares (with a
            // matching type) the record is built by reading those fields and wrapped
            // nullable; otherwise the conversion fails and yields null. This is the
            // "branch by the actual argument type" resolved at monomorphization time.
            Rvalue::RecordFrom { source, .. } => {
                let target = match dest_ty {
                    Type::Nullable(inner) => inner.as_ref().clone(),
                    other => other.clone(),
                };
                let src_ty = operand_type_of(source, &f.local_types);
                if !record_from_succeeds(&src_ty, &target) {
                    return self.const_null();
                }
                let src = self.codegen_operand(program, f, source, &src_ty);
                let field_names = record_field_names(&target);
                let mut named: Vec<(&str, Self::Value)> = Vec::with_capacity(field_names.len());
                let mut managed: Vec<Self::Value> = Vec::new();
                for name in &field_names {
                    let fty = record_field_type(&target, name);
                    // The field is read out of `src` (an alias into the source
                    // record), so the new record must retain a managed one.
                    let v = self.load_field(src, &src_ty, name);
                    if rc_managed(&fty) {
                        managed.push(v);
                    }
                    named.push((name.as_str(), v));
                }
                let rec = self.make_record(&target, &named);
                for v in managed {
                    self.retain(v);
                }
                // Wrap the freshly built record into the nullable result (`T` -> `T?`).
                self.coerce(rec, &target, dest_ty)
            }
            // Construct a sum-type variant: `dest_ty` is the sum type.
            Rvalue::Variant {
                variant, fields, ..
            } => {
                let mut named: Vec<(&str, Self::Value)> = Vec::with_capacity(fields.len());
                let mut managed: Vec<Self::Value> = Vec::new();
                for (name, op) in fields {
                    let fty = operand_type_of(op, &f.local_types);
                    let v = self.codegen_operand(program, f, op, &fty);
                    if rc_managed(&fty) && operand_is_alias(op) {
                        managed.push(v);
                    }
                    named.push((name.as_str(), v));
                }
                let var = self.make_variant(dest_ty, variant, &named);
                // Retain aliased payloads (a fresh constant is already owned at 1).
                for v in managed {
                    self.retain(v);
                }
                var
            }
            // A closure value: `dest_ty` is the closure's `Fun` type.
            Rvalue::Closure { id, captures } => {
                let mut caps: Vec<(Type, Self::Value)> = Vec::with_capacity(captures.len());
                let mut managed: Vec<Self::Value> = Vec::new();
                for op in captures {
                    let cty = operand_type_of(op, &f.local_types);
                    let v = self.codegen_operand(program, f, op, &cty);
                    if rc_managed(&cty) {
                        managed.push(v);
                    }
                    caps.push((cty, v));
                }
                let clo = self.make_closure(dest_ty, *id, &caps);
                // The closure environment now references each managed capture.
                for v in managed {
                    self.retain(v);
                }
                clo
            }
            // A bracket literal: an array when `dest_ty` is a slice/array, a tuple
            // when it is a `Tuple` (heterogeneous elements, each at its own type).
            Rvalue::Array(es) => {
                if let Type::Tuple(elem_types) = dest_ty {
                    let mut vals: Vec<Self::Value> = Vec::with_capacity(es.len());
                    for (op, ety) in es.iter().zip(elem_types) {
                        vals.push(self.codegen_operand(program, f, op, ety));
                    }
                    let tup = self.make_tuple(elem_types, &vals);
                    // The tuple references each managed element (its destructor
                    // releases them). Same ownership rule as `MirStmt::Store`: only
                    // an *aliased* element's count rises -- a fresh constant and a
                    // nullable-wrap cell are already owned at 1 and transfer that
                    // ownership to the tuple (retaining them too would leak).
                    for ((op, v), ety) in es.iter().zip(&vals).zip(elem_types) {
                        let op_ty = operand_type_of(op, &f.local_types);
                        if rc_managed(ety) && operand_is_alias(op) && !is_nullable_wrap(ety, &op_ty)
                        {
                            self.retain(*v);
                        }
                    }
                    tup
                } else {
                    let elem_ty = element_type(dest_ty);
                    let mut vals: Vec<Self::Value> = Vec::with_capacity(es.len());
                    for op in es {
                        vals.push(self.codegen_operand(program, f, op, &elem_ty));
                    }
                    let arr = self.make_array(&elem_ty, &vals);
                    // Same ownership rule as `MirStmt::Store` (see the tuple arm
                    // above): retaining a fresh constant or wrap cell leaked one
                    // reference per element.
                    if rc_managed(&elem_ty) {
                        for (op, v) in es.iter().zip(&vals) {
                            let op_ty = operand_type_of(op, &f.local_types);
                            if operand_is_alias(op) && !is_nullable_wrap(&elem_ty, &op_ty) {
                                self.retain(*v);
                            }
                        }
                    }
                    arr
                }
            }
            // Read an aggregate field or an array element. A narrowed nullable base
            // (`a: T?` proven non-null by a guard) is unwrapped to its inner value.
            Rvalue::Load(place) => match place.proj.as_slice() {
                [Projection::Field(field)] => {
                    let base = self.load_local(place.local);
                    let raw_ty = f.local_type(place.local).clone();
                    let (base, base_ty) = self.unwrap_narrowed(base, &raw_ty);
                    self.load_field(base, &base_ty, field)
                }
                [Projection::Index(idx)] => {
                    let arr = self.load_local(place.local);
                    let raw_ty = f.local_type(place.local).clone();
                    let (arr, arr_ty) = self.unwrap_narrowed(arr, &raw_ty);
                    if let Type::Tuple(elem_types) = &arr_ty {
                        // A tuple is read at a constant position (the type checker
                        // requires a constant index).
                        let k = crate::mono::const_operand_index(idx)
                            .expect("tuple index must be a constant (checked by typeck)");
                        self.tuple_field(arr, elem_types, k)
                    } else {
                        let iv = self.codegen_operand(program, f, idx, &index_type(idx, f));
                        self.load_index(arr, &arr_ty, iv)
                    }
                }
                _ => self.unit(),
            },
            // Read a module-level global.
            Rvalue::Global(name) => {
                let gty = program.global_type(name).cloned().unwrap_or(Type::Void);
                self.load_global(name, &gty)
            }
        }
    }

    /// Generate a call, routing free / instance-method / static calls to the
    /// matching monomorphized instance (computed from the argument types the same
    /// way the monomorphizer did).
    fn codegen_call(
        &mut self,
        program: &MonoProgram,
        f: &MonoFunction,
        callee: &Callee,
        args: &[Operand],
        dest_ty: &Type,
    ) -> Self::Value {
        let arg_types: Vec<Type> = args
            .iter()
            .map(|a| operand_type_of(a, &f.local_types))
            .collect();
        let target = match callee {
            // `arr.push(v)`: a growable-array append, not a user method. The receiver
            // type is stripped of a top-level nullable (a narrowed `T[]?`), and the
            // operand is loaded at that stripped type so the cell is unwrapped.
            Callee::Method(name)
                if name == "push"
                    && matches!(arg_types.first().map(unwrap_nullable), Some(Type::Slice(_))) =>
            {
                let aty = unwrap_nullable(&arg_types[0]);
                let elem = element_type(aty);
                let arr = self.codegen_operand(program, f, &args[0], aty);
                let v = self.codegen_operand(program, f, &args[1], &elem);
                self.push(arr, &elem, v);
                // The array now holds a reference to a managed element. Same
                // ownership rule as `MirStmt::Store`: only an aliased element's
                // count rises -- a fresh constant and a nullable-wrap cell already
                // own their single reference and hand it to the array (retaining
                // them too leaked one reference per push).
                if rc_managed(&elem)
                    && operand_is_alias(&args[1])
                    && !is_nullable_wrap(&elem, &operand_type_of(&args[1], &f.local_types))
                {
                    self.retain(v);
                }
                return self.unit();
            }
            // `arr.insert(i, v)`: a growable-array insertion (`_array_insert`), not a user method.
            Callee::Method(name)
                if name == "insert"
                    && matches!(arg_types.first().map(unwrap_nullable), Some(Type::Slice(_))) =>
            {
                let aty = unwrap_nullable(&arg_types[0]);
                let elem = element_type(aty);
                let arr = self.codegen_operand(program, f, &args[0], aty);
                let idx = self.codegen_operand(program, f, &args[1], &arg_types[1]);
                let v = self.codegen_operand(program, f, &args[2], &elem);
                self.insert(arr, &elem, idx, v);
                // The array now holds a reference to a managed element (its
                // destructor releases it). Aliased elements only -- see `push`.
                if rc_managed(&elem)
                    && operand_is_alias(&args[2])
                    && !is_nullable_wrap(&elem, &operand_type_of(&args[2], &f.local_types))
                {
                    self.retain(v);
                }
                return self.unit();
            }
            // `arr.remove(i)`: a growable-array removal (`_array_remove`) returning the removed element. Ownership of a managed
            // element transfers to the caller, so no retain/release is needed.
            Callee::Method(name)
                if name == "remove"
                    && matches!(arg_types.first().map(unwrap_nullable), Some(Type::Slice(_))) =>
            {
                let aty = unwrap_nullable(&arg_types[0]);
                let elem = element_type(aty);
                let arr = self.codegen_operand(program, f, &args[0], aty);
                let idx = self.codegen_operand(program, f, &args[1], &arg_types[1]);
                return self.remove(arr, &elem, idx);
            }
            // `arr.pop()`: a growable-array removal of the last element (`_array_pop`) returning it as a nullable. Ownership of a managed
            // element transfers to the caller (the nullable cell), so no
            // retain/release is needed.
            Callee::Method(name)
                if name == "pop"
                    && matches!(arg_types.first().map(unwrap_nullable), Some(Type::Slice(_))) =>
            {
                let aty = unwrap_nullable(&arg_types[0]);
                let elem = element_type(aty);
                let arr = self.codegen_operand(program, f, &args[0], aty);
                return self.pop(arr, &elem);
            }
            // `arr.len()` / `s.len()`: the length builtin in UFCS method form.
            Callee::Method(name)
                if name == "len"
                    && matches!(
                        arg_types.first().map(unwrap_nullable),
                        Some(Type::Slice(_) | Type::Array(..) | Type::Str)
                    ) =>
            {
                let aty = unwrap_nullable(&arg_types[0]);
                let v = self.codegen_operand(program, f, &args[0], aty);
                return match aty {
                    Type::Slice(_) | Type::Array(..) => self.array_len(v),
                    _ => self.string_len(v),
                };
            }
            // File I/O methods: the receiver is the builtin `File`
            // record, so map to the runtime file primitives rather than a user
            // method.
            Callee::Method(name)
                if matches!(name.as_str(), "read" | "write" | "close" | "size" | "seek")
                    && matches!(arg_types.first(), Some(Type::Record(r)) if r.is_name("File")) =>
            {
                let file = self.codegen_operand(program, f, &args[0], &arg_types[0]);
                return match name.as_str() {
                    "read" => {
                        let n = self.codegen_operand(program, f, &args[1], &arg_types[1]);
                        self.file_read(file, n)
                    }
                    "write" => {
                        let b = self.codegen_operand(program, f, &args[1], &arg_types[1]);
                        self.file_write(file, b)
                    }
                    "seek" => {
                        let pos = self.codegen_operand(program, f, &args[1], &arg_types[1]);
                        self.file_seek(file, pos)
                    }
                    "size" => self.file_size(file),
                    _ => self.file_close(file),
                };
            }
            // Instance method (`arg_types[0]` is the receiver). A nominal method
            // instance is keyed by `method_symbol`; a stdlib primitive/array
            // method (`fun string.split`) by its class-qualified symbol. The type
            // checker has already rejected any other `recv.m()`.
            Callee::Method(name) => {
                let msym = method_symbol(name, &arg_types);
                if program.lookup(&msym).is_some() {
                    msym
                } else if let Some(psym) = prim_method_instance(program, name, &arg_types) {
                    psym
                } else {
                    instance_symbol(name, &arg_types)
                }
            }
            // Runtime-recognized numeric/string conversions (not user statics).
            Callee::Static { ty, method } if numeric_conv_ret(ty, method).is_some() => {
                return self.codegen_conv(program, f, ty, method, args);
            }
            // `File.stdin()`/`stdout()`/`stderr()`: a standard stream object.
            Callee::Static { ty, method } if ty == "File" => {
                return self.file_std(match method.as_str() {
                    "stdin" => 0,
                    "stdout" => 1,
                    _ => 2,
                });
            }
            // The destination type keys a return-polymorphic, no-argument
            // constructor (a witness-free `new()`) to the same instance the
            // monomorphizer created for this result type.
            Callee::Static { ty, method } => static_symbol(ty, method, &arg_types, Some(dest_ty)),
            // Typed I/O: `print`/`println` write to stdout directly.
            Callee::Free(base) if base == "print" || base == "println" => {
                return self.codegen_io(program, f, base, args);
            }
            Callee::Free(base) => instance_symbol(base, &arg_types),
            // MIR-internal builtins used by `match` lowering.
            Callee::Builtin(name) => return self.codegen_builtin(program, f, name, args),
            // Indirect (closure) call through a runtime function pointer.
            Callee::Indirect(callee) => return self.codegen_indirect(program, f, callee, args),
        };
        let Some(inst) = program.lookup(&target) else {
            // Should not happen for validated MIR.
            return self.unit();
        };
        let params = inst.type_args.clone();
        let ret = inst.ret.clone();
        let symbol = inst.symbol.clone();
        let vals: Vec<Self::Value> = args
            .iter()
            .zip(&params)
            .map(|(a, pty)| self.codegen_operand(program, f, a, pty))
            .collect();
        self.call(&symbol, &vals, &ret)
    }

    /// Deferred dispatch: `__rt_dispatch("consumer", type_id,
    /// value)`. Evaluates the runtime type id and the value, then hands them with
    /// the consumer's source name to the back end's [`Codegen::deferred_dispatch`]
    /// leaf, which (via the runtime dispatch service) JIT-compiles the consumer
    /// specialized for that type on first use and calls it. The consumer name is a
    /// string literal; the result is `int32`.
    fn codegen_deferred_dispatch(
        &mut self,
        program: &MonoProgram,
        f: &MonoFunction,
        args: &[Operand],
    ) -> Self::Value {
        // `__rt_dispatch("consumer", "TypeName", value)`: the consumer and the
        // runtime type are string literals; the value is evaluated.
        let consumer = str_const(&args[0]).unwrap_or_default();
        let type_name = str_const(&args[1]).unwrap_or_default();
        let val_ty = operand_type_of(&args[2], &f.local_types);
        let value = self.codegen_operand(program, f, &args[2], &val_ty);
        self.deferred_dispatch(consumer, type_name, value)
    }

    /// MIR-internal builtins emitted by `match` lowering: `value_matches` (a
    /// variant test) and `panic` (the unmatched fallthrough).
    fn codegen_builtin(
        &mut self,
        program: &MonoProgram,
        f: &MonoFunction,
        name: &str,
        args: &[Operand],
    ) -> Self::Value {
        match name {
            "value_matches" => {
                let subj_ty = operand_type_of(&args[0], &f.local_types);
                let subj = self.codegen_operand(program, f, &args[0], &subj_ty);
                let variant = str_const(&args[1]).unwrap_or_default();
                self.pattern_matches(subj, &subj_ty, variant)
            }
            // `__deep_copy(x)`: a fresh, independent copy of an aggregate argument
            // (the default value-passing for a non-reference heap parameter). The
            // leaf balances reference counts for non-aggregates.
            "__deep_copy" => {
                let ty = operand_type_of(&args[0], &f.local_types);
                let v = self.codegen_operand(program, f, &args[0], &ty);
                self.deep_copy(v, &ty)
            }
            // `__present(x)`: the `if let x = e` presence test. Only a genuinely
            // nullable subject reaches runtime (non-nullable subjects fold in
            // `cond_static_truthiness`), where truthiness of a nullable is the
            // non-null test.
            "__present" => {
                let ty = operand_type_of(&args[0], &f.local_types);
                let v = self.codegen_operand(program, f, &args[0], &ty);
                self.truthy(v, &ty)
            }
            // `__nonnull(x)`: narrow a nullable to its inner value -- the binding of
            // an `if let p = <nullable>` on the (proven non-null) then-arm, so `p`
            // has the value type, not the nullable. A non-nullable argument passes
            // through (coercion from a type to itself is identity).
            "__nonnull" => {
                let ty = operand_type_of(&args[0], &f.local_types);
                let v = self.codegen_operand(program, f, &args[0], &ty);
                let inner = unwrap_nullable(&ty).clone();
                self.coerce(v, &ty, &inner)
            }
            // `result_is_ok(r)` is the `Ok` tag test of the `r!` operator.
            "result_is_ok" => {
                let subj_ty = operand_type_of(&args[0], &f.local_types);
                let subj = self.codegen_operand(program, f, &args[0], &subj_ty);
                self.pattern_matches(subj, &subj_ty, "Ok")
            }
            "panic" => {
                let msg = str_const(&args[0]).unwrap_or_default();
                self.emit_panic(msg);
                self.unit()
            }
            // `_panic(msg)`: abort with a computed string message (std `assert`).
            "_panic" => {
                let mty = operand_type_of(&args[0], &f.local_types);
                let target = unwrap_nullable(&mty).clone();
                let m = self.codegen_operand(program, f, &args[0], &target);
                self.runtime_panic(m);
                self.unit()
            }
            // Deferred dispatch: `__rt_dispatch("consumer",
            // "TypeName", value)`.
            "__rt_dispatch" => self.codegen_deferred_dispatch(program, f, args),
            "len" => {
                // Strip a top-level nullable (a narrowed `T[]?`/`string?`) so the
                // operand is loaded at its inner type and the cell is unwrapped.
                let ty = operand_type_of(&args[0], &f.local_types);
                let ty = unwrap_nullable(&ty).clone();
                let v = self.codegen_operand(program, f, &args[0], &ty);
                // `len` applies to both strings and arrays.
                match ty {
                    Type::Slice(_) | Type::Array(..) => self.array_len(v),
                    _ => self.string_len(v),
                }
            }
            "array_len" => {
                let ty = operand_type_of(&args[0], &f.local_types);
                let ty = unwrap_nullable(&ty).clone();
                let v = self.codegen_operand(program, f, &args[0], &ty);
                self.array_len(v)
            }
            "to_string" => {
                let ty = operand_type_of(&args[0], &f.local_types);
                let v = self.codegen_operand(program, f, &args[0], &ty);
                self.to_string(v, &ty)
            }
            "print" | "println" => self.codegen_io(program, f, name, args),
            // `spawn(f)` runs the closure on a new thread.
            "spawn" => {
                let cty = operand_type_of(&args[0], &f.local_types);
                let clo = self.codegen_operand(program, f, &args[0], &cty);
                self.spawn(clo);
                self.unit()
            }
            // `sync()` joins every spawned thread so their effects are observable
            // before the program continues (R6 value-observability).
            "sync" => {
                self.thread_join_all();
                self.unit()
            }
            // `_freeze(c)` / `_cown(c)` promote a `spawn` capture to a shared owner
            // before the spawn, so its reference count is atomic across threads: a
            // read-only capture is frozen (immutable), a mutated one is made a cown.
            // The driver's auto-acquire pass inserts these; both yield no value.
            "_freeze" | "_cown" => {
                let ty = operand_type_of(&args[0], &f.local_types);
                // Only a heap-managed capture has an object header to retag and an
                // atomic reference count to promote. A primitive capture (int,
                // float, bool) is copied by value across the spawn boundary, so it
                // needs neither -- and feeding its scalar value to the runtime's
                // `void(ptr)` promotion would be a type mismatch (and a wild header
                // write). Skip promotion for such captures.
                if rc_managed(unwrap_nullable(&ty)) {
                    let v = self.codegen_operand(program, f, &args[0], &ty);
                    if name == "_freeze" {
                        self.freeze(v);
                    } else {
                        self.make_cown(v);
                    }
                }
                self.unit()
            }
            // `with(obj, f)` acquires `obj`'s lock, runs `f(obj)`, releases, and
            // yields the closure's result -- the cown access made data-race-free.
            "with" => {
                let obj_ty = operand_type_of(&args[0], &f.local_types);
                let obj = self.codegen_operand(program, f, &args[0], &obj_ty);
                let cty = operand_type_of(&args[1], &f.local_types);
                let clo = self.codegen_operand(program, f, &args[1], &cty);
                // A `with` on a value that has no heap object -- a primitive (which
                // the auto-acquire guard may wrap when a captured primitive was
                // classified a cown, and which a user could write directly) -- has
                // nothing to lock or put in a region: the value is copied, not
                // shared, so it cannot race. Just run the closure on it.
                if !rc_managed(unwrap_nullable(&obj_ty)) {
                    return self.call_indirect(clo, &cty, &[obj]);
                }
                // `with([c1, c2], f)` acquires every cown in the array (in a
                // deadlock-free order); `with(obj, f)` acquires the single cown.
                // The multi form applies ONLY to arrays of records -- the shape
                // the explicit group syntax produces. Any other array shared
                // with a task (an `int32[]` or `string[]` capture the
                // auto-acquire pass wrapped) is itself the single cown:
                // element-locking would chase raw scalars as object pointers
                // (a crash), and a push's realloc would change the element set
                // between lock and unlock.
                let multi = match unwrap_nullable(&obj_ty) {
                    Type::Slice(e) | Type::Array(e, _) => matches!(**e, Type::Record(_)),
                    _ => false,
                };
                // A single-cown `with` opens a region with the guarded object as
                // its bridge; closedness is verified on release.
                // The lock (data-race-freedom) is kept around the region: acquire it
                // first, so the region open/close and the body all run under it.
                // Otherwise concurrent `with`s on the same cown race on the region
                // setup -- `region_open` writes the bridge's header, and the body's
                // write barrier mutates region metadata -- which corrupts the heap.
                if multi {
                    self.cown_lock_all(obj);
                } else {
                    self.cown_lock(obj);
                }
                let region = (!multi).then(|| self.region_open(obj));
                let result = self.call_indirect(clo, &cty, &[obj]);
                if let Some(region_id) = region {
                    self.region_close(region_id);
                }
                if multi {
                    self.cown_unlock_all(obj);
                } else {
                    self.cown_unlock(obj);
                }
                result
            }
            // `_with_all(f, c0, c1, ...)` -- inserted by the spawn auto-acquire pass
            // when one guarded body touches several cowns -- acquires every heap
            // cown in the group through the runtime's address-ordered group lock,
            // runs the zero-argument closure `f`, releases, and yields `f`'s
            // result. Address ordering (not the emission order) is what makes two
            // groups over the same cowns deadlock-free regardless of capture
            // names. A primitive in the group has no heap object to lock -- it is
            // copied, not shared -- so it is skipped, exactly as single `with`
            // skips a primitive.
            "_with_all" => {
                let cty = operand_type_of(&args[0], &f.local_types);
                let clo = self.codegen_operand(program, f, &args[0], &cty);
                let cowns: Vec<Self::Value> = args[1..]
                    .iter()
                    .filter(|a| rc_managed(unwrap_nullable(&operand_type_of(a, &f.local_types))))
                    .map(|a| {
                        let ty = operand_type_of(a, &f.local_types);
                        self.codegen_operand(program, f, a, &ty)
                    })
                    .collect();
                if cowns.is_empty() {
                    return self.call_indirect(clo, &cty, &[]);
                }
                self.cown_lock_many(&cowns);
                let result = self.call_indirect(clo, &cty, &[]);
                self.cown_unlock_many(&cowns);
                result
            }
            "_float_sqrt" | "_float_floor" | "_float_ceil" | "_float_pow" => {
                let ty = Type::Float(prepoly_hir::FloatKind::F64);
                let vals: Vec<Self::Value> = args
                    .iter()
                    .map(|a| self.codegen_operand(program, f, a, &ty))
                    .collect();
                self.float_builtin(name, &vals)
            }
            "_string_slice" => {
                let s = self.codegen_operand(program, f, &args[0], &Type::Str);
                let i64t = Type::Int(prepoly_hir::IntKind::I64);
                let start = self.codegen_operand(program, f, &args[1], &i64t);
                let end = self.codegen_operand(program, f, &args[2], &i64t);
                self.string_slice(s, start, end)
            }
            "_string_bytes" => {
                let s = self.codegen_operand(program, f, &args[0], &Type::Str);
                self.string_to_bytes(s)
            }
            "_string_find" => {
                let s = self.codegen_operand(program, f, &args[0], &Type::Str);
                let sub = self.codegen_operand(program, f, &args[1], &Type::Str);
                self.string_find(s, sub)
            }
            "_string_char_at" => {
                let s = self.codegen_operand(program, f, &args[0], &Type::Str);
                let i = self.codegen_operand(
                    program,
                    f,
                    &args[1],
                    &Type::Int(prepoly_hir::IntKind::I64),
                );
                self.string_char_at(s, i)
            }
            "_string_from_bytes" => {
                let aty = operand_type_of(&args[0], &f.local_types);
                let a = self.codegen_operand(program, f, &args[0], &aty);
                self.string_from_bytes(a)
            }
            // `_string_concat(a, b)` is what the `+` operator lowers to; exposed as a
            // named primitive too.
            "_string_concat" => {
                let a = self.codegen_operand(program, f, &args[0], &Type::Str);
                let b = self.codegen_operand(program, f, &args[1], &Type::Str);
                self.string_concat(a, b)
            }
            // `_string_cmp(a, b) -> int32` lexicographic comparison.
            "_string_cmp" => {
                let a = self.codegen_operand(program, f, &args[0], &Type::Str);
                let b = self.codegen_operand(program, f, &args[1], &Type::Str);
                self.string_cmp(a, b)
            }
            // Numeric-to-string renderings: the argument keeps its
            // own numeric type so `to_string` selects the right rendering.
            "_int_to_string" | "_float_to_string" => {
                let aty = operand_type_of(&args[0], &f.local_types);
                let v = self.codegen_operand(program, f, &args[0], &aty);
                self.to_string(v, &aty)
            }
            // String-to-number parses: a typed `Result`.
            "_int_parse" | "_float_parse" => {
                let s = self.codegen_operand(program, f, &args[0], &Type::Str);
                let target = if name == "_int_parse" {
                    Type::Int(prepoly_hir::IntKind::I64)
                } else {
                    Type::Float(prepoly_hir::FloatKind::F64)
                };
                self.convert(&target, "parse", &Type::Str, s)
            }
            // `_int_to_float(x, float_bits)` widens an integer to float; the bits
            // operand selects the float width but the typed value is f64-carried.
            "_int_to_float" => {
                let i64t = Type::Int(prepoly_hir::IntKind::I64);
                let x = self.codegen_operand(program, f, &args[0], &i64t);
                self.convert(&Type::Float(prepoly_hir::FloatKind::F64), "from", &i64t, x)
            }
            // `_float_to_int(x, int_bits, signed)` truncates a float to an integer,
            // range-checked: a typed `Result<int64, string>`.
            "_float_to_int" => {
                let f64t = Type::Float(prepoly_hir::FloatKind::F64);
                let x = self.codegen_operand(program, f, &args[0], &f64t);
                self.convert(&Type::Int(prepoly_hir::IntKind::I64), "from", &f64t, x)
            }
            // `open(path, mode) -> File!`.
            "open" => {
                let p = self.codegen_operand(program, f, &args[0], &Type::Str);
                let m = self.codegen_operand(program, f, &args[1], &Type::Str);
                self.file_open(p, m)
            }
            // Integer width conversions: widen is infallible, narrow
            // returns a range-checked Result.
            "_int_widen" | "_int_narrow" => {
                let i64t = Type::Int(prepoly_hir::IntKind::I64);
                let x = self.codegen_operand(program, f, &args[0], &i64t);
                let from = self.codegen_operand(program, f, &args[1], &i64t);
                let to = self.codegen_operand(program, f, &args[2], &i64t);
                let signed = self.codegen_operand(program, f, &args[3], &Type::Bool);
                if name == "_int_widen" {
                    self.int_widen(x, from, to, signed)
                } else {
                    self.int_narrow(x, from, to, signed)
                }
            }
            // Other builtins are rejected during monomorphization.
            _ => self.unit(),
        }
    }

    /// The type a call produces before any destination-context coercion.
    ///
    /// Most calls already return the type expected by their destination, but
    /// nullable-returning primitives such as `_string_char_at` may flow into a
    /// non-null slot after a guard or loop invariant proves they are present. The
    /// call result must then be unwrapped explicitly (`T? -> T`) instead of storing
    /// the nullable cell pointer where the inner value pointer is expected.
    fn call_result_type(
        &self,
        program: &MonoProgram,
        f: &MonoFunction,
        callee: &Callee,
        args: &[Operand],
        dest_ty: &Type,
    ) -> Option<Type> {
        let arg_types: Vec<Type> = args
            .iter()
            .map(|a| operand_type_of(a, &f.local_types))
            .collect();
        match callee {
            Callee::Builtin(name) => builtin_result_type(name, args, &f.local_types),
            Callee::Free(base) if base == "print" || base == "println" => Some(Type::Void),
            Callee::Free(base) => program
                .lookup(&instance_symbol(base, &arg_types))
                .map(|inst| inst.ret.clone()),
            Callee::Method(name)
                if name == "push"
                    && matches!(arg_types.first().map(unwrap_nullable), Some(Type::Slice(_))) =>
            {
                Some(Type::Void)
            }
            Callee::Method(name)
                if name == "insert"
                    && matches!(arg_types.first().map(unwrap_nullable), Some(Type::Slice(_))) =>
            {
                Some(Type::Void)
            }
            Callee::Method(name)
                if name == "remove"
                    && matches!(arg_types.first().map(unwrap_nullable), Some(Type::Slice(_))) =>
            {
                let aty = unwrap_nullable(&arg_types[0]);
                Some(element_type(aty))
            }
            Callee::Method(name)
                if name == "pop"
                    && matches!(arg_types.first().map(unwrap_nullable), Some(Type::Slice(_))) =>
            {
                let aty = unwrap_nullable(&arg_types[0]);
                Some(Type::Nullable(Box::new(element_type(aty))))
            }
            Callee::Method(name)
                if name == "len"
                    && matches!(
                        arg_types.first().map(unwrap_nullable),
                        Some(Type::Slice(_) | Type::Array(..) | Type::Str)
                    ) =>
            {
                Some(Type::Int(prepoly_hir::IntKind::I64))
            }
            Callee::Method(name)
                if matches!(name.as_str(), "read" | "write" | "close" | "size" | "seek")
                    && matches!(arg_types.first(), Some(Type::Record(r)) if r.is_name("File")) =>
            {
                None
            }
            Callee::Method(name) => {
                let msym = method_symbol(name, &arg_types);
                let target = if program.lookup(&msym).is_some() {
                    msym
                } else {
                    instance_symbol(name, &arg_types)
                };
                program.lookup(&target).map(|inst| inst.ret.clone())
            }
            Callee::Static { ty, method } if numeric_conv_ret(ty, method).is_some() => {
                numeric_conv_ret(ty, method)
            }
            Callee::Static { ty, method } if ty == "File" => Some(match method.as_str() {
                "stdin" | "stdout" | "stderr" => {
                    Type::Record(prepoly_hir::NominalType::new(-1, "File"))
                }
                _ => Type::Void,
            }),
            Callee::Static { ty, method } => program
                .lookup(&static_symbol(ty, method, &arg_types, Some(dest_ty)))
                .map(|inst| inst.ret.clone()),
            Callee::Indirect(callee) => match operand_type_of(callee, &f.local_types) {
                Type::Fun(_, ret) => Some(*ret),
                _ => None,
            },
        }
    }

    /// Generate a `print`/`println`: a string argument is written directly, a
    /// scalar via `to_string`; `println` adds a trailing newline.
    fn codegen_io(
        &mut self,
        program: &MonoProgram,
        f: &MonoFunction,
        name: &str,
        args: &[Operand],
    ) -> Self::Value {
        let newline = name == "println";
        let s = match args.first() {
            None => self.const_str(""),
            Some(op) => {
                let ty = operand_type_of(op, &f.local_types);
                let v = self.codegen_operand(program, f, op, &ty);
                if matches!(ty, Type::Str) {
                    v
                } else {
                    self.to_string(v, &ty)
                }
            }
        };
        self.emit_print(s, newline);
        self.unit()
    }

    /// Generate an indirect (closure) call: evaluate the callee and the
    /// arguments (typed by the callee's `Fun` parameter types) and call through.
    fn codegen_indirect(
        &mut self,
        program: &MonoProgram,
        f: &MonoFunction,
        callee: &Operand,
        args: &[Operand],
    ) -> Self::Value {
        let callee_ty = operand_type_of(callee, &f.local_types);
        let callee_val = self.codegen_operand(program, f, callee, &callee_ty);
        let params: Vec<Type> = match &callee_ty {
            Type::Fun(p, _) => p.clone(),
            _ => Vec::new(),
        };
        let vals: Vec<Self::Value> = args
            .iter()
            .enumerate()
            .map(|(i, a)| {
                let pty = params.get(i).cloned().unwrap_or(Type::Void);
                self.codegen_operand(program, f, a, &pty)
            })
            .collect();
        self.call_indirect(callee_val, &callee_ty, &vals)
    }

    /// Generate a numeric/string conversion `ty.method(arg)`.
    fn codegen_conv(
        &mut self,
        program: &MonoProgram,
        f: &MonoFunction,
        ty: &str,
        method: &str,
        args: &[Operand],
    ) -> Self::Value {
        let arg_ty = operand_type_of(&args[0], &f.local_types);
        let v = self.codegen_operand(program, f, &args[0], &arg_ty);
        // `string.from(x)` is just `to_string`.
        if ty == "string" {
            return self.to_string(v, &arg_ty);
        }
        let target = if let Some(k) = int_kind_name(ty) {
            Type::Int(k)
        } else if let Some(k) = float_kind_name(ty) {
            Type::Float(k)
        } else {
            return self.unit();
        };
        self.convert(&target, method, &arg_ty, v)
    }

    fn codegen_operand(
        &mut self,
        _program: &MonoProgram,
        f: &MonoFunction,
        op: &Operand,
        expected_ty: &Type,
    ) -> Self::Value {
        match op {
            Operand::Local(id) => {
                let v = self.load_local(*id);
                let from = f.local_type(*id).clone();
                self.coerce(v, &from, expected_ty)
            }
            Operand::Const(lit) => self.codegen_const(lit, expected_ty),
        }
    }

    /// Resolve an aggregate-operation receiver to its non-null form. An `if a`
    /// guard proves a nullable non-null but does not retype the MIR local, so a
    /// narrowed `T?` still carries the declared nullable; unwrap the cell (the
    /// `Nullable -> inner` `coerce`) and return the stripped type. A non-nullable
    /// base passes through unchanged, so this is safe to apply to every receiver.
    fn unwrap_narrowed(&mut self, base: Self::Value, base_ty: &Type) -> (Self::Value, Type) {
        match base_ty {
            Type::Nullable(inner) => (self.coerce(base, base_ty, inner), (**inner).clone()),
            _ => (base, base_ty.clone()),
        }
    }

    fn codegen_const(&mut self, lit: &Literal, expected_ty: &Type) -> Self::Value {
        // A non-null literal flowing into a nullable position is built at the
        // element type and wrapped into the nullable cell, mirroring the `Local`
        // operand path (which coerces). Without this, a literal passed to a nullable
        // parameter (`f(5)` for `f(x: int32?)`) would be a bare value where a cell
        // pointer is expected. The null literal stays the null pointer.
        if let Type::Nullable(inner) = expected_ty
            && !matches!(lit, Literal::Null)
        {
            let v = self.codegen_const(lit, inner);
            let cell = self.coerce(v, inner, expected_ty);
            // The wrap retained `v` (the cell's destructor releases it), but a
            // fresh managed constant's own reference has no other owner: unlike a
            // local, no binding ever drops it. Release it here so the cell holds
            // the constant's only reference -- otherwise every `"x"` wrapped into
            // a `string?` slot leaked the string.
            if rc_managed(inner) {
                self.emit_release(v, inner);
            }
            return cell;
        }
        match lit {
            // An integer literal in a float context (e.g. `e * 2` where `e` is a
            // float) is the corresponding float constant.
            Literal::Int(v) if matches!(expected_ty, Type::Float(_)) => {
                self.const_float(*v as f64, expected_ty)
            }
            Literal::Int(v) => self.const_int(*v, expected_ty),
            Literal::Float(v) => self.const_float(*v, expected_ty),
            Literal::Bool(b) => self.const_bool(*b),
            Literal::Str(s) => self.const_str(s),
            Literal::Void => self.unit(),
            Literal::Null => self.const_null(),
        }
    }
}

/// Whether a type is a `Result` (its bare returns are implicitly `Ok`-wrapped).
fn is_result_ty(ty: &Type) -> bool {
    matches!(ty, Type::Sum(n) if n.id == prepoly_hir::RESULT_TYPE_ID)
}

/// The `Ok` payload type of a `Result` return type (`void` if not a `Result`).
fn result_ok_type(ret: &Type) -> Type {
    match ret {
        Type::Sum(n) => n
            .result_payloads()
            .map(|(ok, _)| ok.clone())
            .unwrap_or(Type::Void),
        _ => Type::Void,
    }
}

/// The concrete type of field `name` in a record type, or `void` if absent.
fn record_field_type(record_ty: &Type, name: &str) -> Type {
    match unwrap_nullable(record_ty) {
        Type::Record(n) => n.substitution.get(name).cloned().unwrap_or(Type::Void),
        _ => Type::Void,
    }
}

/// The field names of a record type, in its substitution's (sorted) order.
fn record_field_names(record_ty: &Type) -> Vec<String> {
    match record_ty {
        Type::Record(n) => n
            .substitution
            .iter()
            .map(|(name, _)| name.to_string())
            .collect(),
        _ => Vec::new(),
    }
}

/// See through reference/mutability/const wrappers (erased before the back ends,
/// but peeled defensively) to the underlying type.
fn strip_wrappers(ty: &Type) -> &Type {
    match ty {
        Type::Ref(inner) | Type::Mut(inner) | Type::ConstOf(inner) => strip_wrappers(inner),
        other => other,
    }
}

/// Whether `T.from(source)` succeeds for a concrete (per-instance) `src_ty` and
/// target record `target`: the source must be a record carrying every field
/// `target` declares, each with a matching type. A mismatch (a missing field or a
/// differently-typed one) means the conversion yields null rather than reading a
/// field that is absent or laid out differently.
fn record_from_succeeds(src_ty: &Type, target: &Type) -> bool {
    let (Type::Record(s), Type::Record(t)) = (strip_wrappers(src_ty), target) else {
        return false;
    };
    t.substitution
        .iter()
        .all(|(name, tty)| s.substitution.get(name).is_some_and(|sty| sty == tty))
}

/// The string payload of a constant string operand (the variant/panic argument
/// of a MIR-internal builtin call), if it is one.
fn str_const(op: &Operand) -> Option<&str> {
    match op {
        Operand::Const(Literal::Str(s)) => Some(s),
        _ => None,
    }
}

/// Typed return shapes for compiler/runtime builtins that are not backed by a
/// monomorphized function instance. Unknown shapes are left as `None`; callers
/// then assume the destination type already matches.
fn builtin_result_type(name: &str, args: &[Operand], local_types: &[Type]) -> Option<Type> {
    match name {
        "value_matches" | "result_is_ok" => Some(Type::Bool),
        "__deep_copy" => args.first().map(|op| operand_type_of(op, local_types)),
        "__nonnull" => args
            .first()
            .map(|op| unwrap_nullable(&operand_type_of(op, local_types)).clone()),
        "panic" | "_panic" | "print" | "println" | "spawn" | "sync" | "_freeze" | "_cown" => {
            Some(Type::Void)
        }
        // The group-acquire wrap yields its closure's result, like `with`.
        "_with_all" => match args.first().map(|op| operand_type_of(op, local_types)) {
            Some(Type::Fun(_, ret)) => Some(*ret),
            _ => None,
        },
        "len" | "array_len" => Some(Type::Int(prepoly_hir::IntKind::I64)),
        "to_string" => Some(Type::Str),
        "_float_sqrt" | "_float_floor" | "_float_ceil" | "_float_pow" => {
            Some(Type::Float(prepoly_hir::FloatKind::F64))
        }
        "_string_slice" | "_string_concat" => Some(Type::Str),
        "_string_bytes" => Some(Type::Slice(Box::new(Type::Int(prepoly_hir::IntKind::U8)))),
        "_string_find" => Some(Type::Nullable(Box::new(Type::Int(
            prepoly_hir::IntKind::I64,
        )))),
        "_string_char_at" => Some(Type::Nullable(Box::new(Type::Str))),
        "_string_cmp" => Some(Type::Int(prepoly_hir::IntKind::I32)),
        "_int_to_string" | "_float_to_string" => Some(Type::Str),
        "_int_to_float" => Some(Type::Float(prepoly_hir::FloatKind::F64)),
        _ => None,
    }
}

/// The element type of an array/slice type, or `void` if not a sequence. A
/// narrowed nullable array (`int32[]?` proven non-null) is unwrapped first.
pub fn element_type(ty: &Type) -> Type {
    match unwrap_nullable(ty) {
        Type::Slice(e) | Type::Array(e, _) => (**e).clone(),
        _ => Type::Void,
    }
}

/// The concrete type of an index operand (the loop counter / index expression).
fn index_type(idx: &Operand, f: &MonoFunction) -> Type {
    operand_type_of(idx, &f.local_types)
}
