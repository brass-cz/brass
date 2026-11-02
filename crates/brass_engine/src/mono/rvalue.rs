//! Typing an rvalue and its operands inside an instance body: operators,
//! builtins, loads, constructions, and calls (resolved to their callee
//! instances by the `call` module), plus the typed `print`/`println` path
//! and its preference for a user `display` method.

use super::*;

impl Monomorphizer<'_, '_> {
    #[allow(clippy::too_many_arguments)] // the fixpoint's full typing context
    pub(super) fn rvalue_type(
        &mut self,
        rv: &Rvalue,
        cur_sym: &str,
        module: &[String],
        local_types: &[Option<Type>],
        cur_ret: &Option<Type>,
        fallible: bool,
        expected: Option<&Type>,
    ) -> Result<Option<Type>, String> {
        if let Rvalue::Call(Callee::Numeric { inner, site }, args) = rv {
            let previous = self
                .active_numeric_call
                .replace((*site, self.numeric_call_flavor(*site)));
            let result = self.rvalue_type(
                &Rvalue::Call((**inner).clone(), args.clone()),
                cur_sym,
                module,
                local_types,
                cur_ret,
                fallible,
                expected,
            );
            self.active_numeric_call = previous;
            return result;
        }
        match rv {
            Rvalue::Call(Callee::Numeric { .. }, _) => unreachable!("handled above"),
            Rvalue::Use(op) => self.operand_type(op, local_types),
            // `typeof(x)`: always a string. The name itself is derived from the
            // operand's concrete type by the back ends once the instance is
            // fully typed; nothing here depends on the operand being resolved
            // yet, so the result does not wait on it.
            Rvalue::TypeName(_) => Ok(Some(Type::Str)),
            // A type test: always a bool; the answer is folded per instance
            // from the operand's monomorphized type (see `fold`).
            Rvalue::TypeTest(..) | Rvalue::FieldsTest { .. } => Ok(Some(Type::Bool)),
            Rvalue::Bin(op, a, b) => {
                if is_comparison(*op) || matches!(op, BinOp::And | BinOp::Or) {
                    Ok(Some(Type::Bool))
                } else {
                    self.binary_operand_type(a, b, local_types)
                }
            }
            Rvalue::Un(UnaryOp::Not, _) => Ok(Some(Type::Bool)),
            Rvalue::Un(_, a) => self.operand_type(a, local_types),
            // `print`/`println` are typed as I/O directly (rendering through a
            // user `display` when the value's type declares one) rather than by
            // instantiating the prelude's bodies.
            Rvalue::Call(Callee::Free(base), args) if base == "print" || base == "println" => {
                self.io_call_type(args, cur_sym, cur_ret, local_types)
            }
            Rvalue::Call(Callee::Free(base), args) => {
                let Some(arg_types) = self.arg_types(args, local_types)? else {
                    return Ok(None);
                };
                self.resolve_free(cur_sym, cur_ret, base, arg_types)
            }
            Rvalue::Call(Callee::NumericFree { base, site }, args) => {
                let Some(arg_types) = self.arg_types(args, local_types)? else {
                    return Ok(None);
                };
                let previous = self
                    .active_numeric_call
                    .replace((*site, self.numeric_call_flavor(*site)));
                let result = self.resolve_numeric_free(cur_sym, cur_ret, base, arg_types, None);
                self.active_numeric_call = previous;
                result
            }
            // Nominal declarations own their methods even when a method shares
            // a name with an array or string operation.
            Rvalue::Call(Callee::Method(name), args)
                if matches!(
                    self.operand_type(args.first().unwrap_or(&Operand::void()), local_types)?
                        .as_ref()
                        .map(unwrap_nullable),
                    Some(Type::Record(_) | Type::Sum(_))
                ) =>
            {
                self.method_call_type(name, args, cur_sym, cur_ret, local_types)
            }
            // `arr.push(v)`/`arr.insert(i, v)` are growable-array mutations (void),
            // not user methods.
            // The receiver may be a narrowed nullable array (`int32[]?` proven
            // non-null by an `if a` / `if a != null` guard). A guard does not retype
            // the MIR local, so it still carries the declared nullable; strip the
            // top-level nullable here, exactly as the back end unwraps the cell.
            Rvalue::Call(Callee::Method(name), args) if name == "push" || name == "insert" => {
                match self.operand_type(args.first().unwrap_or(&Operand::void()), local_types)? {
                    Some(t) => match unwrap_nullable(&t) {
                        Type::Slice(_) => Ok(Some(Type::Void)),
                        other => Err(format!(
                            "internal error: {name} on non-array `{}`",
                            other.display()
                        )),
                    },
                    None => Ok(None),
                }
            }
            // `arr.remove(i) -> T` returns the removed element.
            Rvalue::Call(Callee::Method(name), args) if name == "remove" => {
                match self.operand_type(args.first().unwrap_or(&Operand::void()), local_types)? {
                    Some(t) => match unwrap_nullable(&t) {
                        Type::Slice(inner) => Ok(Some((**inner).clone())),
                        other => Err(format!(
                            "internal error: remove on non-array `{}`",
                            other.display()
                        )),
                    },
                    None => Ok(None),
                }
            }
            // `arr.pop() -> T?` returns the last element as a nullable (`_array_pop`).
            Rvalue::Call(Callee::Method(name), args) if name == "pop" => {
                match self.operand_type(args.first().unwrap_or(&Operand::void()), local_types)? {
                    Some(t) => match unwrap_nullable(&t) {
                        Type::Slice(inner) => Ok(Some(Type::Nullable(inner.clone()))),
                        other => Err(format!(
                            "internal error: pop on non-array `{}`",
                            other.display()
                        )),
                    },
                    None => Ok(None),
                }
            }
            // `arr.len()` / `s.len()`: the array/string length builtin in method
            // form (`len(x)` and `x.len()` are equivalent), an `int64`.
            Rvalue::Call(Callee::Method(name), args) if name == "len" => {
                match self.operand_type(args.first().unwrap_or(&Operand::void()), local_types)? {
                    Some(t) => match unwrap_nullable(&t) {
                        Type::Slice(_) | Type::Array(..) | Type::Str => {
                            Ok(Some(Type::Int(IntKind::I64)))
                        }
                        other => Err(format!(
                            "internal error: len on `{}` (expected an array or string)",
                            other.display()
                        )),
                    },
                    None => Ok(None),
                }
            }
            Rvalue::Call(Callee::Method(name), args) => {
                self.method_call_type(name, args, cur_sym, cur_ret, local_types)
            }
            Rvalue::Call(Callee::Keyed { method, site }, args) => {
                let target = self.keyed_target(*site, method)?;
                self.method_call_type(&target, args, cur_sym, cur_ret, local_types)
            }
            Rvalue::Call(Callee::Static { ty, method }, args) => self.static_call_type(
                ty,
                method,
                args,
                cur_sym,
                cur_ret,
                module,
                local_types,
                expected,
            ),
            // `value_matches` (variant test) yields bool; `panic` yields void;
            // other builtins are out of scope.
            Rvalue::Call(Callee::Builtin(name), args) => match name.as_str() {
                "value_matches" => Ok(Some(Type::Bool)),
                // `__deep_copy(x)` produces a value of the same type as `x` (a fresh
                // copy of an aggregate; a balanced pass-through otherwise).
                "__deep_copy" => match args.first() {
                    Some(op) => self.operand_type(op, local_types),
                    None => Ok(Some(Type::Void)),
                },
                // `__present(x)` is the `if let x = e` presence test: false for a
                // null, true for anything else. Non-nullable subjects fold
                // statically (see `cond_static_truthiness`).
                "__present" | "__null_prop_present" | "__nullable_context_present" => {
                    Ok(Some(Type::Bool))
                }
                // `__nonnull(x)` narrows a nullable to its inner type (the if-let
                // binding of a nullable, proven non-null); a non-nullable is itself.
                "__nonnull" => match args.first() {
                    Some(op) => Ok(self
                        .operand_type(op, local_types)?
                        .map(|t| unwrap_nullable(&t).clone())),
                    None => Ok(Some(Type::Void)),
                },
                // `r!` lowers to `result_is_ok(r)` + an Ok-payload load + Err
                // propagation; the first is a tag test (bool).
                "result_is_ok" => Ok(Some(Type::Bool)),
                "panic" => Ok(Some(Type::Void)),
                // `_panic(msg)`: the user-facing runtime abort (std `assert`), with
                // a runtime string message (vs. the codegen-internal `panic`).
                "_panic" => Ok(Some(Type::Void)),
                "len" | "array_len" => Ok(Some(Type::Int(IntKind::I64))),
                // Pure float math primitives map to LLVM intrinsics.
                "_float_sqrt" | "_float_floor" | "_float_ceil" | "_float_pow" => {
                    Ok(Some(Type::Float(FloatKind::F64)))
                }
                // Integer width conversions: widen is infallible
                // (int64), narrow yields a range-checked Result.
                "_int_widen" => Ok(Some(Type::Int(IntKind::I64))),
                "_int_narrow" => Ok(Some(result_type(Type::Int(IntKind::I64), Type::Str))),
                // String primitives over typed strings/arrays.
                "_string_slice" => Ok(Some(Type::Str)),
                "_string_bytes" => Ok(Some(Type::Slice(Box::new(Type::Int(IntKind::U8))))),
                // `_string_find` -> position or null.
                "_string_find" => Ok(Some(Type::Nullable(Box::new(Type::Int(IntKind::I64))))),
                "_string_char_at" => Ok(Some(Type::Nullable(Box::new(Type::Str)))),
                "_string_from_bytes" => Ok(Some(result_type(Type::Str, Type::Str))),
                // Named numeric/string conversion primitives,
                // callable directly as well as through the `Type.from`/`parse` and
                // `+` forms.
                "_string_concat" => Ok(Some(Type::Str)),
                "_string_cmp" => Ok(Some(Type::Int(IntKind::I32))),
                "_int_to_string" | "_float_to_string" => Ok(Some(Type::Str)),
                "_int_parse" => Ok(Some(result_type(Type::Int(IntKind::I64), Type::Str))),
                "_float_parse" => Ok(Some(result_type(Type::Float(FloatKind::F64), Type::Str))),
                "_int_to_float" => Ok(Some(Type::Float(FloatKind::F64))),
                "_float_to_int" => Ok(Some(result_type(Type::Int(IntKind::I64), Type::Str))),
                // Standalone stdio primitives (the prelude's `print`/`println`
                // bodies and `input`), no `File` involved.
                "_print_str" | "_println_str" => Ok(Some(Type::Void)),
                "_stdin_read" => Ok(Some(result_type(
                    Type::Slice(Box::new(Type::Int(IntKind::U8))),
                    Type::Str,
                ))),
                "_argv" => Ok(Some(Type::Slice(Box::new(Type::Str)))),
                "_flush" => Ok(Some(Type::Void)),
                // Prepare implicit nominal renderers before either back end emits them.
                "to_string" => match args.first() {
                    Some(op) => match self.operand_type(op, local_types)? {
                        Some(t) if is_printable(&t) => Ok(self
                            .prepare_rendering(
                                &t,
                                crate::render::RenderForm::Display,
                                cur_sym,
                                cur_ret,
                            )?
                            .then_some(Type::Str)),
                        Some(t) => Err(format!(
                            "to_string of `{}` is unsupported on the typed backend",
                            t.display()
                        )),
                        None => Ok(None),
                    },
                    None => Ok(Some(Type::Str)),
                },
                "print" | "println" => self.io_call_type(args, cur_sym, cur_ret, local_types),
                // `spawn(f)` runs `f` on a thread and yields nothing. `with(obj,
                // f)` acquires `obj` and yields `f`'s result (its closure return).
                "spawn" => Ok(Some(Type::Void)),
                // `sync()` joins all spawned threads.
                "sync" => Ok(Some(Type::Void)),
                // `_cown(c)` / `_freeze(c)` promote a spawn capture to a shared
                // owner before the spawn; each yields nothing.
                "_cown" | "_freeze" => Ok(Some(Type::Void)),
                "with" => match args.get(1) {
                    Some(op) => match self.operand_type(op, local_types)? {
                        Some(Type::Fun(_, ret)) => Ok(Some(*ret)),
                        Some(other) => Err(format!(
                            "internal error: `with` expects a closure, found `{}`",
                            other.display()
                        )),
                        None => Ok(None),
                    },
                    None => Err("`with` expects (cown, closure)".into()),
                },
                // `_with_all(f, c0, ...)` yields the guarded body closure's result.
                "_with_all" => match args.first() {
                    Some(op) => match self.operand_type(op, local_types)? {
                        Some(Type::Fun(_, ret)) => Ok(Some(*ret)),
                        Some(other) => Err(format!(
                            "internal error: `_with_all` expects a closure, found `{}`",
                            other.display()
                        )),
                        None => Ok(None),
                    },
                    None => Err("`_with_all` expects (closure, cowns...)".into()),
                },
                // Native-plugin dispatch (`_plugin_[f]call_<t>`) carries its
                // return in the name's suffix; see the shared decoder. Read in
                // the fallthrough so the name decodes once, and a name that is
                // neither still reports as unsupported.
                other => match brass_hir::plugin_builtin_return(other) {
                    Some(ret) => Ok(Some(ret)),
                    None => Err(format!(
                        "internal error: builtin `{other}` is unsupported on the typed backend"
                    )),
                },
            },
            // Indirect (closure) call: the callee local's `Fun` type gives the
            // result. The closure instance was created when the local was typed.
            Rvalue::Call(Callee::Indirect(callee), _) => {
                match self.operand_type(callee, local_types)? {
                    Some(Type::Fun(_, ret)) => Ok(Some(*ret)),
                    Some(other) => Err(format!(
                        "internal error: indirect call of non-function `{}`",
                        other.display()
                    )),
                    None => Ok(None),
                }
            }
            // A narrowed nullable aggregate (`p: P?` / `a: int32[]?` proven non-null
            // by a guard) keeps its declared nullable on the MIR local, so strip the
            // top-level nullable before reading a field or element.
            Rvalue::Load(place) => match place.proj.as_slice() {
                [Projection::Field(field)] => {
                    match local_types[place.local.index()]
                        .as_ref()
                        .map(unwrap_nullable)
                    {
                        // A member that can only be a method is the compile-time
                        // presence value the checker typed: the method's own name,
                        // or null when a primitive class has no such member (see
                        // `Program::member_presence`). Everything else is an
                        // ordinary record/sum field read.
                        Some(ty) => match self.program.member_presence(ty, field) {
                            Some(true) => Ok(Some(Type::Str)),
                            Some(false) => Ok(Some(Type::null())),
                            None => match ty {
                                Type::Record(n) => self.record_field_type(n, field),
                                Type::Sum(n) => self.sum_field_type(n, field),
                                other => Err(format!(
                                    "internal error: field access `.{field}` on non-aggregate `{}`",
                                    other.display()
                                )),
                            },
                        },
                        None => Ok(None),
                    }
                }
                // Array/slice element read: the element type is the sequence's. A
                // tuple is read at a constant position, yielding that element's type.
                [Projection::Index(idx)] => {
                    match local_types[place.local.index()]
                        .as_ref()
                        .map(unwrap_nullable)
                    {
                        Some(Type::Slice(elem) | Type::Array(elem, _)) => {
                            Ok(Some((**elem).clone()))
                        }
                        Some(Type::Tuple(elems)) => match const_operand_index(idx) {
                            Some(k) if k < elems.len() => Ok(Some(elems[k].clone())),
                            Some(k) => {
                                Err(format!("internal error: tuple index {k} out of bounds"))
                            }
                            None => Err(
                                "internal error: a tuple must be indexed by a constant integer"
                                    .into(),
                            ),
                        },
                        Some(other) => Err(format!(
                            "internal error: indexing non-array `{}`",
                            other.display()
                        )),
                        None => Ok(None),
                    }
                }
                _ => Err("nested projections are unsupported on the typed backend".into()),
            },
            Rvalue::Record { ty, fields } => self.record_type(module, ty, fields, local_types),
            // `T.from(v)` always types `T?`; the per-instance codegen yields the
            // record (when the concrete source has every field) or null. Build `T`'s
            // declared record type and wrap nullable.
            Rvalue::RecordFrom { ty, .. } => match record_from_target(self.program, module, ty) {
                Some(t) => Ok(Some(Type::Nullable(Box::new(t)))),
                None => Err(format!(
                    "`{ty}.from`: every field of the target record needs a declared type"
                )),
            },
            // The view of a callee parameter's row over this instance's concrete
            // structural source: the canonical structural record whose type_key
            // collapses every argument shape with the same view into one callee
            // instance. Guarded fields are nullable slots (absent/mismatched ->
            // null at construction). A non-structural or row-less source (a
            // defensive case lowering should not produce) passes through as the
            // identity, keeping type and value in agreement with codegen.
            Rvalue::RecordView {
                callee,
                param,
                source,
            } => {
                let Some(src) = self.operand_type(source, local_types)? else {
                    return Ok(None);
                };
                match (
                    brass_hir::peel_modes(&src),
                    self.rows().function_param(callee, *param),
                ) {
                    (Type::Record(n), Some(prow))
                        if n.id == brass_hir::STRUCTURAL_RECORD_ID && prow.eligible =>
                    {
                        brass_typesys::view_type(&prow.row, n).map(Some)
                    }
                    _ => Ok(Some(src)),
                }
            }
            // A `Result` construction takes its destination's or the enclosing
            // fallible callable's inferred `Result` type; other (annotated)
            // sums resolve directly.
            Rvalue::Variant {
                ty,
                variant,
                fields,
            } => {
                if ty == "Result" {
                    // The enclosing return may be `Result<..>?` (a body that
                    // also propagates a null); the construction is the Result.
                    let ctx = expected
                        .filter(|t| t.is_result_type())
                        .cloned()
                        .or_else(|| {
                            cur_ret
                                .as_ref()
                                .map(|t| unwrap_nullable(t).clone())
                                .filter(|t| t.is_result_type())
                        });
                    if let Some(ctx) = ctx {
                        return self.result_construction_type(ctx, variant, fields, local_types);
                    }
                    // A fallible body's ret is still forming: wait for it
                    // (the fixpoint supplies it, including for an err-only
                    // body -- see `infer_result_ret`'s defaults). Only a
                    // NON-fallible context (`println(error(..))` at a top
                    // level) never gets one, so the construction itself
                    // carries its variant's payload and the OTHER side --
                    // uninhabited for this value -- defaults to void.
                    if fallible {
                        return Ok(None);
                    }
                    let (mut ok, mut err) = (Type::Void, Type::Void);
                    for (fname, op) in fields {
                        let Some(t) = self.operand_type(op, local_types)? else {
                            return Ok(None);
                        };
                        match (variant.as_str(), fname.as_str()) {
                            ("Ok", "value") => ok = t,
                            ("Err", "error") => err = t,
                            _ => {}
                        }
                    }
                    Ok(Some(result_type(ok, err)))
                } else {
                    self.variant_type(module, ty, variant, fields, local_types)
                }
            }
            Rvalue::Array(es) => self.array_type(es, cur_sym, local_types),
            // A global read: its type is recorded when its init body is typed.
            Rvalue::Global(name) => Ok(self.global_types.get(name).cloned()),
            Rvalue::Closure { .. } => Err("closures are unsupported on the typed backend".into()),
        }
    }

    /// Type a `print`/`println` call: void, accepted only for a printable
    /// (scalar or string) argument so its output matches the boxed path.
    fn io_call_type(
        &mut self,
        args: &[Operand],
        cur_sym: &str,
        cur_ret: &Option<Type>,
        local_types: &[Option<Type>],
    ) -> Result<Option<Type>, String> {
        match args.first() {
            None => Ok(Some(Type::Void)),
            Some(op) => match self.operand_type(op, local_types)? {
                Some(t) if is_printable(&t) => Ok(self
                    .prepare_rendering(&t, crate::render::RenderForm::Display, cur_sym, cur_ret)?
                    .then_some(Type::Void)),
                Some(t) => Err(format!(
                    "print of `{}` is unsupported on the typed backend",
                    t.display()
                )),
                None => Ok(None),
            },
        }
    }

    /// Concrete types of every argument operand, or `None` if one is not yet
    /// resolvable.
    pub(super) fn arg_types(
        &self,
        args: &[Operand],
        local_types: &[Option<Type>],
    ) -> Result<Option<Vec<Type>>, String> {
        let mut out = Vec::with_capacity(args.len());
        for a in args {
            match self.operand_type(a, local_types)? {
                Some(t) => out.push(t),
                None => return Ok(None),
            }
        }
        Ok(Some(out))
    }

    pub(super) fn operand_type(
        &self,
        op: &Operand,
        local_types: &[Option<Type>],
    ) -> Result<Option<Type>, String> {
        match op {
            Operand::Local(id) => Ok(local_types[id.index()].clone()),
            Operand::Const(lit) => const_type(lit).map(Some),
        }
    }

    pub(super) fn binary_operand_type(
        &self,
        a: &Operand,
        b: &Operand,
        local_types: &[Option<Type>],
    ) -> Result<Option<Type>, String> {
        let ta = self.operand_type(a, local_types)?;
        let tb = self.operand_type(b, local_types)?;
        // Both operand types known: the shared operand rule (also used by the
        // back ends for comparison operands) decides, so the typer and codegen
        // can never disagree on literal adaptation or the common numeric type.
        // With one side still open, a typed LOCAL operand stands in for the
        // result (a recursive call's result is typed only through the value
        // this computes). A constant never does: a literal adapts to the other
        // operand, so `i + 1` read at the literal's `int32` would freeze the
        // sum narrower than an `i` that later types `int64`.
        Ok(match (&ta, &tb) {
            (Some(ta), Some(tb)) => Some(binary_operand_common((ta, a), (tb, b))),
            (Some(t), None) if matches!(a, Operand::Local(_)) => Some(unwrap_nullable(t).clone()),
            (None, Some(t)) if matches!(b, Operand::Local(_)) => Some(unwrap_nullable(t).clone()),
            _ => None,
        })
    }
}
