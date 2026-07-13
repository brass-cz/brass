//! Typing of builtin runtime functions and primitive methods:
//! the `_`-prefixed runtime helpers, concurrency builtins, and the
//! array/string method surface that has no user-level signature.

use super::*;

impl<'a> Checker<'a> {
    pub(super) fn builtin_function_type(
        &mut self,
        name: &str,
        args: &[Arg],
        span: prepoly_parser::Span,
        scopes: &mut ScopeStack,
    ) -> Option<Type> {
        // `len` is a runtime primitive usable as a free
        // function. Its result is always `int64`, and its single argument must
        // be a collection or string; a concrete non-collection argument is a
        // static error rather than a deferred runtime panic.
        if name == "len" {
            self.check_arg_count("len", 1, args.len(), span);
            let arg_ty = args
                .first()
                .map(|a| self.check_expr(&a.expr, scopes))
                .unwrap_or(Type::Void);
            for a in args.iter().skip(1) {
                self.check_expr(&a.expr, scopes);
            }
            if let Some(arg) = args.first() {
                let resolved = self.resolve(&arg_ty);
                if !is_maybe_indexable(&resolved) {
                    self.errors.push(TypeError {
                        message: format!(
                            "`len` expects an array or string, found `{}`",
                            resolved.display()
                        ),
                        span: arg.expr.span(),
                    });
                }
            }
            return Some(Type::Int(IntKind::I64));
        }
        if matches!(name, "print" | "println") {
            args.iter().for_each(|a| {
                self.check_expr(&a.expr, scopes);
            });
            return Some(Type::Void);
        }
        if name == "input" && self.lookup_function("input").is_none() {
            // The stdlib defines the real `input` (an inferred-fallible
            // `string!`); resolution above prefers it. This fallback keeps the
            // same static type when no stdlib is loaded, so the checker never
            // hands out an unconstrained unknown for the name.
            self.check_arg_count("input", 0, args.len(), span);
            args.iter().for_each(|a| {
                self.check_expr(&a.expr, scopes);
            });
            return Some(Type::result(Type::Str, Type::Str));
        }
        if let Some(ret) = self.array_builtin_type(name, args, span, scopes) {
            return Some(ret);
        }
        if let Some(ret) = self.string_builtin_type(name, args, span, scopes) {
            return Some(ret);
        }
        if let Some(ret) = self.numeric_helper_type(name, args, span, scopes) {
            return Some(ret);
        }
        if let Some(ret) = self.concurrency_builtin_type(name, args, span, scopes) {
            return Some(ret);
        }
        // The standalone stdio primitives behind the prelude's
        // `print`/`println`/`input`, so those stay import-free with no `File`
        // value involved.
        if name == "_print_str" || name == "_println_str" {
            self.check_builtin_args_against(name, args, &[Type::Str], span, scopes);
            return Some(Type::Void);
        }
        if name == "_stdin_read" {
            // `_stdin_read(n: int64) -> uint8[]!`: up to `n` bytes from stdin.
            let i64_ty = Type::Int(IntKind::I64);
            self.check_builtin_args_against(name, args, &[i64_ty], span, scopes);
            return Some(Type::result(
                Type::Slice(Box::new(Type::Int(IntKind::U8))),
                Type::Str,
            ));
        }
        if name == "_flush" {
            // `_flush()`: push buffered output to the operating system.
            self.check_arg_count(name, 0, args.len(), span);
            return Some(Type::Void);
        }
        if name == "_argv" {
            // `_argv() -> string[]`: the program's argument vector (the
            // program file, then everything after it on the command line).
            // The primitive behind the env library's `args()`.
            self.check_arg_count(name, 0, args.len(), span);
            return Some(Type::Slice(Box::new(Type::Str)));
        }
        if let Some(ret) = prepoly_hir::plugin_builtin_return(name) {
            self.check_plugin_call(name, args, span, scopes);
            return Some(ret);
        }
        None
    }

    /// `_plugin_[f]call_<t>(path, name, sig, payload...)`: the loader
    /// synthesizes these with three leading string literals, but the builtin is
    /// nameable from user source, and the runtime reads each payload slot as
    /// the signature's type without re-checking it. A wrong slot is therefore
    /// undefined behaviour, so the payload is typed here against the signature
    /// -- which must be a literal for that to be possible at all.
    fn check_plugin_call(
        &mut self,
        name: &str,
        args: &[Arg],
        span: prepoly_parser::Span,
        scopes: &mut ScopeStack,
    ) {
        if args.len() < 3 {
            self.errors.push(TypeError {
                message: format!("`{name}` expects at least 3 arguments (path, name, sig)"),
                span,
            });
            for a in args {
                self.check_expr(&a.expr, scopes);
            }
            return;
        }
        for a in &args[..3] {
            self.check_expr_against(&a.expr, &Type::Str, scopes);
        }
        let payload = &args[3..];
        let Some(sig) = str_literal(&args[2].expr) else {
            self.errors.push(TypeError {
                message: format!("`{name}` signature must be a string literal"),
                span: args[2].expr.span(),
            });
            for a in payload {
                self.check_expr(&a.expr, scopes);
            }
            return;
        };
        let Some((params, _, _)) = prepoly_hir::plugin_sig_types(&sig) else {
            self.errors.push(TypeError {
                message: format!("malformed plugin call signature `{sig}`"),
                span: args[2].expr.span(),
            });
            for a in payload {
                self.check_expr(&a.expr, scopes);
            }
            return;
        };
        if payload.len() != params.len() {
            self.errors.push(TypeError {
                message: format!(
                    "`{name}` passes {} argument(s), signature `{sig}` has {}",
                    payload.len(),
                    params.len()
                ),
                span,
            });
        }
        for (a, want) in payload.iter().zip(&params) {
            self.check_expr_against(&a.expr, want, scopes);
        }
        for a in payload.iter().skip(params.len()) {
            self.check_expr(&a.expr, scopes);
        }
    }

    /// Static contracts for the numeric runtime helpers. These
    /// map onto LLVM/runtime primitives, so the value class of each argument
    /// must be correct before the runtime reads its payload bits: passing a
    /// float to `_int_to_string`, for example, would reinterpret a bit pattern
    /// as an integer. Concrete wrong classes are static errors; unknown
    /// arguments stay deferred to the runtime tag checks.
    fn numeric_helper_type(
        &mut self,
        name: &str,
        args: &[Arg],
        span: prepoly_parser::Span,
        scopes: &mut ScopeStack,
    ) -> Option<Type> {
        let i64_ty = Type::Int(IntKind::I64);
        let f64_ty = Type::Float(FloatKind::F64);
        let (params, ret): (Vec<NumericClass>, Type) = match name {
            "_int_to_string" => (vec![NumericClass::Int], Type::Str),
            "_float_to_string" => (vec![NumericClass::Float], Type::Str),
            "_int_parse" => (vec![NumericClass::Str], Type::result(i64_ty, Type::Str)),
            "_float_parse" => (vec![NumericClass::Str], Type::result(f64_ty, Type::Str)),
            "_int_to_float" => (vec![NumericClass::Int, NumericClass::Int], f64_ty),
            "_float_to_int" => (
                vec![NumericClass::Float, NumericClass::Int, NumericClass::Bool],
                Type::result(i64_ty, Type::Str),
            ),
            "_float_sqrt" | "_float_floor" | "_float_ceil" => (vec![NumericClass::Float], f64_ty),
            "_float_pow" => (vec![NumericClass::Float, NumericClass::Float], f64_ty),
            // Integer width conversions: widening always succeeds;
            // narrowing range-checks and yields a Result. Bits/signedness are passed
            // so the runtime matches the target type.
            "_int_widen" => (
                vec![
                    NumericClass::Int,
                    NumericClass::Int,
                    NumericClass::Int,
                    NumericClass::Bool,
                ],
                i64_ty,
            ),
            "_int_narrow" => (
                vec![
                    NumericClass::Int,
                    NumericClass::Int,
                    NumericClass::Int,
                    NumericClass::Bool,
                ],
                Type::result(i64_ty, Type::Str),
            ),
            _ => return None,
        };
        self.check_arg_count(name, params.len(), args.len(), span);
        for (idx, class) in params.iter().enumerate() {
            let Some(arg) = args.get(idx) else { continue };
            let got = self.check_expr(&arg.expr, scopes);
            let resolved = self.resolve(&got);
            if resolved.is_unknown() {
                continue;
            }
            if !class.accepts(&resolved) {
                self.errors.push(TypeError {
                    message: format!(
                        "`{name}` expects {} for argument {}, found `{}`",
                        class.describe(),
                        idx + 1,
                        resolved.display()
                    ),
                    span: arg.expr.span(),
                });
            }
        }
        for arg in args.iter().skip(params.len()) {
            self.check_expr(&arg.expr, scopes);
        }
        Some(ret)
    }

    /// Minimal static contracts for the concurrency primitives.
    /// `spawn(f: () -> void) -> void` and `with(c, f) -> U` are the only
    /// programmer-facing concurrency API. Until cown typing is real the first
    /// `with` argument stays untyped (the closure parameter is deferred), but
    /// the callable shape and `spawn`'s zero-arity are enforced now.
    fn concurrency_builtin_type(
        &mut self,
        name: &str,
        args: &[Arg],
        span: prepoly_parser::Span,
        scopes: &mut ScopeStack,
    ) -> Option<Type> {
        match name {
            "spawn" => {
                self.check_arg_count("spawn", 1, args.len(), span);
                if let Some(arg) = args.first() {
                    let got = self.check_expr(&arg.expr, scopes);
                    match self.resolve(&got) {
                        Type::Fun(params, _) if !params.is_empty() => {
                            self.errors.push(TypeError {
                                message: "`spawn` expects a zero-argument closure `() -> void`"
                                    .to_string(),
                                span: arg.expr.span(),
                            });
                        }
                        Type::Fun(_, _) | Type::Unknown(_) => {}
                        other => {
                            self.errors.push(TypeError {
                                message: format!(
                                    "`spawn` expects a closure `() -> void`, found `{}`",
                                    other.display()
                                ),
                                span: arg.expr.span(),
                            });
                        }
                    }
                }
                for arg in args.iter().skip(1) {
                    self.check_expr(&arg.expr, scopes);
                }
                Some(Type::Void)
            }
            "with" => {
                self.check_arg_count("with", 2, args.len(), span);
                if let Some(arg) = args.first() {
                    self.check_expr(&arg.expr, scopes);
                }
                let ret = match args.get(1) {
                    Some(arg) => {
                        let got = self.check_expr(&arg.expr, scopes);
                        match self.resolve(&got) {
                            Type::Fun(params, ret) => {
                                if params.len() != 1 {
                                    self.errors.push(TypeError {
                                        message:
                                            "`with` expects a one-argument closure as its second \
                                             argument"
                                                .to_string(),
                                        span: arg.expr.span(),
                                    });
                                }
                                *ret
                            }
                            Type::Unknown(_) => self.fresh_unknown(),
                            other => {
                                self.errors.push(TypeError {
                                    message: format!(
                                        "`with` expects a closure as its second argument, found \
                                         `{}`",
                                        other.display()
                                    ),
                                    span: arg.expr.span(),
                                });
                                self.fresh_unknown()
                            }
                        }
                    }
                    None => self.fresh_unknown(),
                };
                for arg in args.iter().skip(2) {
                    self.check_expr(&arg.expr, scopes);
                }
                Some(ret)
            }
            // `sync()` joins every thread spawned so far, so values mutated by a
            // `spawn` become observable before the program continues (R6
            // value-observability / structured-concurrency barrier).
            "sync" => {
                self.check_arg_count("sync", 0, args.len(), span);
                for arg in args {
                    self.check_expr(&arg.expr, scopes);
                }
                Some(Type::Void)
            }
            // `_cown(c)` / `_freeze(c)` are inserted by the spawn auto-acquire pass
            // to promote a capture to an atomic-count owner before the spawn; each
            // takes the capture and yields nothing.
            "_cown" | "_freeze" => {
                self.check_arg_count(name, 1, args.len(), span);
                for arg in args {
                    self.check_expr(&arg.expr, scopes);
                }
                Some(Type::Void)
            }
            // `_with_all(f, c0, c1, ...)` is the auto-acquire pass's group form of
            // `with`: acquire every cown in the group (address-ordered at runtime),
            // run the zero-argument closure `f`, and yield its result.
            "_with_all" => {
                let ret = match args.first() {
                    Some(arg) => {
                        let got = self.check_expr(&arg.expr, scopes);
                        match self.resolve(&got) {
                            Type::Fun(_, ret) => *ret,
                            _ => self.fresh_unknown(),
                        }
                    }
                    None => self.fresh_unknown(),
                };
                for arg in args.iter().skip(1) {
                    self.check_expr(&arg.expr, scopes);
                }
                Some(ret)
            }
            _ => None,
        }
    }

    pub(super) fn builtin_function_type_light(&self, name: &str) -> Option<Type> {
        if let Some(ret) = prepoly_hir::plugin_builtin_return(name) {
            return Some(ret);
        }
        match name {
            "_print_str" | "_println_str" => Some(Type::Void),
            "_stdin_read" => Some(Type::result(
                Type::Slice(Box::new(Type::Int(IntKind::U8))),
                Type::Str,
            )),
            "_argv" => Some(Type::Slice(Box::new(Type::Str))),
            "_flush" => Some(Type::Void),
            "input" => Some(Type::result(Type::Str, Type::Str)),
            "len" => Some(Type::Int(IntKind::I64)),
            "print" | "println" | "assert" => Some(Type::Void),
            "_string_concat" | "_string_slice" | "_string_char_at" => Some(Type::Str),
            "_string_bytes" => Some(Type::Slice(Box::new(Type::Int(IntKind::U8)))),
            "_string_from_bytes" => Some(Type::result(Type::Str, Type::Str)),
            "_string_find" => Some(Type::Nullable(Box::new(Type::Int(IntKind::I64)))),
            "_string_cmp" => Some(Type::Int(IntKind::I32)),
            "_int_to_string" | "_float_to_string" => Some(Type::Str),
            "_int_parse" => Some(Type::result(Type::Int(IntKind::I64), Type::Str)),
            "_float_parse" => Some(Type::result(Type::Float(FloatKind::F64), Type::Str)),
            "_int_to_float" | "_float_sqrt" | "_float_floor" | "_float_ceil" | "_float_pow" => {
                Some(Type::Float(FloatKind::F64))
            }
            "_float_to_int" | "_int_narrow" => {
                Some(Type::result(Type::Int(IntKind::I64), Type::Str))
            }
            "_int_widen" => Some(Type::Int(IntKind::I64)),
            "spawn" | "sync" | "_cown" | "_freeze" => Some(Type::Void),
            _ => None,
        }
    }

    fn array_builtin_type(
        &mut self,
        name: &str,
        args: &[Arg],
        span: prepoly_parser::Span,
        scopes: &mut ScopeStack,
    ) -> Option<Type> {
        match name {
            "_array_push" => {
                self.check_arg_count(name, 2, args.len(), span);
                let arr_ty = args
                    .first()
                    .map(|arg| self.check_expr(&arg.expr, scopes))
                    .unwrap_or(Type::Void);
                let elem_ty = match self.resolve(&arr_ty) {
                    Type::Slice(inner) => *inner,
                    Type::Array(_, _) => {
                        if let Some(arg) = args.first() {
                            self.errors.push(TypeError {
                                message: "`_array_push` expects a slice, found fixed array"
                                    .to_string(),
                                span: arg.expr.span(),
                            });
                        }
                        self.fresh_unknown()
                    }
                    Type::Unknown(_) => self.fresh_unknown(),
                    other => {
                        if let Some(arg) = args.first() {
                            self.errors.push(TypeError {
                                message: format!(
                                    "`_array_push` expects a slice, found `{}`",
                                    other.display()
                                ),
                                span: arg.expr.span(),
                            });
                        }
                        self.fresh_unknown()
                    }
                };
                if let Some(value) = args.get(1) {
                    let got = self.check_expr(&value.expr, scopes);
                    self.expect_expr_assignable(&got, &elem_ty, &value.expr);
                    if matches!(self.resolve(&elem_ty), Type::Unknown(_)) {
                        let _ = self.solver.unify(&elem_ty, &got);
                    }
                }
                for arg in args.iter().skip(2) {
                    self.check_expr(&arg.expr, scopes);
                }
                Some(Type::Void)
            }
            "_array_pop" => {
                self.check_arg_count(name, 1, args.len(), span);
                let arr_ty = args
                    .first()
                    .map(|arg| self.check_expr(&arg.expr, scopes))
                    .unwrap_or(Type::Void);
                for arg in args.iter().skip(1) {
                    self.check_expr(&arg.expr, scopes);
                }
                let elem_ty = match self.resolve(&arr_ty) {
                    Type::Slice(inner) => *inner,
                    Type::Array(_, _) => {
                        if let Some(arg) = args.first() {
                            self.errors.push(TypeError {
                                message: "`_array_pop` expects a slice, found fixed array"
                                    .to_string(),
                                span: arg.expr.span(),
                            });
                        }
                        self.fresh_unknown()
                    }
                    Type::Unknown(_) => self.fresh_unknown(),
                    other => {
                        if let Some(arg) = args.first() {
                            self.errors.push(TypeError {
                                message: format!(
                                    "`_array_pop` expects a slice, found `{}`",
                                    other.display()
                                ),
                                span: arg.expr.span(),
                            });
                        }
                        self.fresh_unknown()
                    }
                };
                Some(Type::Nullable(Box::new(elem_ty)))
            }
            // `_array_insert(arr, idx, elem)` / `_array_remove(arr, idx)` primitives: the slice's element type drives the index/element
            // checks. Insert yields void; remove yields the removed element.
            "_array_insert" | "_array_remove" => {
                let want_args = if name == "_array_insert" { 3 } else { 2 };
                self.check_arg_count(name, want_args, args.len(), span);
                let arr_ty = args
                    .first()
                    .map(|arg| self.check_expr(&arg.expr, scopes))
                    .unwrap_or(Type::Void);
                let elem_ty = match self.resolve(&arr_ty) {
                    Type::Slice(inner) => *inner,
                    Type::Unknown(_) => self.fresh_unknown(),
                    other => {
                        if let Some(arg) = args.first() {
                            self.errors.push(TypeError {
                                message: format!(
                                    "`{name}` expects a slice, found `{}`",
                                    other.display()
                                ),
                                span: arg.expr.span(),
                            });
                        }
                        self.fresh_unknown()
                    }
                };
                // The index argument is an int64 offset.
                if let Some(idx) = args.get(1) {
                    let got = self.check_expr(&idx.expr, scopes);
                    self.expect_expr_assignable(&got, &Type::Int(IntKind::I64), &idx.expr);
                }
                if name == "_array_insert" {
                    if let Some(value) = args.get(2) {
                        let got = self.check_expr(&value.expr, scopes);
                        self.expect_expr_assignable(&got, &elem_ty, &value.expr);
                        if matches!(self.resolve(&elem_ty), Type::Unknown(_)) {
                            let _ = self.solver.unify(&elem_ty, &got);
                        }
                    }
                    for arg in args.iter().skip(3) {
                        self.check_expr(&arg.expr, scopes);
                    }
                    Some(Type::Void)
                } else {
                    for arg in args.iter().skip(2) {
                        self.check_expr(&arg.expr, scopes);
                    }
                    Some(elem_ty)
                }
            }
            _ => None,
        }
    }

    fn string_builtin_type(
        &mut self,
        name: &str,
        args: &[Arg],
        span: prepoly_parser::Span,
        scopes: &mut ScopeStack,
    ) -> Option<Type> {
        if name == "_string_find" {
            self.check_arg_count(name, 2, args.len(), span);
            args.iter().for_each(|arg| {
                self.check_expr(&arg.expr, scopes);
            });
            return Some(Type::Nullable(Box::new(Type::Int(IntKind::I64))));
        }
        let i64_ty = Type::Int(IntKind::I64);
        let bytes_ty = Type::Slice(Box::new(Type::Int(IntKind::U8)));
        let (params, ret) = match name {
            "_string_concat" => (vec![Type::Str, Type::Str], Type::Str),
            "_string_slice" => (vec![Type::Str, i64_ty.clone(), i64_ty.clone()], Type::Str),
            "_string_bytes" => (vec![Type::Str], bytes_ty),
            "_string_from_bytes" => (vec![bytes_ty], Type::result(Type::Str, Type::Str)),
            "_string_char_at" => (vec![Type::Str, i64_ty], Type::Str),
            "_string_cmp" => (vec![Type::Str, Type::Str], Type::Int(IntKind::I32)),
            _ => return None,
        };
        self.check_builtin_args_against(name, args, &params, span, scopes);
        Some(ret)
    }

    fn check_builtin_args_against(
        &mut self,
        name: &str,
        args: &[Arg],
        params: &[Type],
        span: prepoly_parser::Span,
        scopes: &mut ScopeStack,
    ) {
        self.check_arg_count(name, params.len(), args.len(), span);
        for (arg, want) in args.iter().zip(params) {
            self.check_expr_against(&arg.expr, want, scopes);
        }
        for arg in args.iter().skip(params.len()) {
            self.check_expr(&arg.expr, scopes);
        }
    }

    pub(super) fn builtin_method_type(
        &mut self,
        recv_ty: &Type,
        method: &str,
        args: &[Arg],
        scopes: &mut ScopeStack,
        span: prepoly_parser::Span,
    ) -> Option<Type> {
        self.array_method_type(recv_ty, method, args, scopes, span)
    }

    /// Type the builtin collection methods so their element types are enforced:
    /// `push(self: T[], value: T) -> void`,
    /// `pop(self: T[]) -> T?`, and `len(self) -> int64`. Element checking turns
    /// `[1].push("x")` into a static error.
    ///
    /// `push`/`pop` are slice-only: a fixed array `T[n]` has a statically fixed
    /// length (modeled as an inline `[n x T]`), so a
    /// length-changing call on one is rejected. `len` and indexing remain valid
    /// for both `T[n]` and `T[]` (indexing is handled in the `Index`/place
    /// paths).
    fn array_method_type(
        &mut self,
        recv_ty: &Type,
        method: &str,
        args: &[Arg],
        scopes: &mut ScopeStack,
        span: prepoly_parser::Span,
    ) -> Option<Type> {
        let resolved = self.resolve(recv_ty);
        // `ref(..)`/`mut(..)` are transparent wrappers, so a method on
        // `ref(mut(T[]))` reaches the same collection as one on `T[]`. Peeling
        // them lets `push`/`len`/... be recognised -- and lets `push` pin the
        // element variable to the pushed value -- through a reference.
        let base = peel_ref_mut(&resolved);
        let (elem, is_fixed) = match base {
            Type::Slice(inner) => (Some((**inner).clone()), false),
            Type::Array(inner, _) => (Some((**inner).clone()), true),
            _ => (None, false),
        };
        match (method, &elem) {
            ("push" | "pop" | "insert" | "remove", Some(elem)) if is_fixed => {
                args.iter().for_each(|arg| {
                    self.check_expr(&arg.expr, scopes);
                });
                self.errors.push(TypeError {
                    message: format!(
                        "fixed array type `{}` has no method `{method}`",
                        resolved.display()
                    ),
                    span,
                });
                // Return the shape the slice method would have had so the call
                // site does not also report a cascading "no method" error.
                Some(match method {
                    "push" | "insert" => Type::Void,
                    "remove" => elem.clone(),
                    _ => Type::Nullable(Box::new(elem.clone())),
                })
            }
            ("push", Some(elem)) => {
                if let Some(arg) = args.first() {
                    let got = self.check_expr(&arg.expr, scopes);
                    self.expect_element_assignable(&got, elem, &arg.expr);
                }
                self.reject_extra_args(method, args, 1, scopes, span);
                Some(Type::Void)
            }
            ("pop", Some(elem)) => {
                args.iter().for_each(|arg| {
                    self.check_expr(&arg.expr, scopes);
                });
                Some(Type::Nullable(Box::new(elem.clone())))
            }
            // `arr.insert(idx, v)`: idx is int64, v is the element.
            ("insert", Some(elem)) => {
                if let Some(idx) = args.first() {
                    let got = self.check_expr(&idx.expr, scopes);
                    self.expect_expr_assignable(&got, &Type::Int(IntKind::I64), &idx.expr);
                }
                if let Some(value) = args.get(1) {
                    let got = self.check_expr(&value.expr, scopes);
                    self.expect_element_assignable(&got, elem, &value.expr);
                }
                self.reject_extra_args(method, args, 2, scopes, span);
                Some(Type::Void)
            }
            // `arr.remove(idx) -> T`: removes and returns the element.
            ("remove", Some(elem)) => {
                if let Some(idx) = args.first() {
                    let got = self.check_expr(&idx.expr, scopes);
                    self.expect_expr_assignable(&got, &Type::Int(IntKind::I64), &idx.expr);
                }
                for arg in args.iter().skip(1) {
                    self.check_expr(&arg.expr, scopes);
                }
                Some(elem.clone())
            }
            ("len", Some(_)) => {
                args.iter().for_each(|arg| {
                    self.check_expr(&arg.expr, scopes);
                });
                Some(Type::Int(IntKind::I64))
            }
            _ if method == "len" && matches!(base, Type::Str) => {
                args.iter().for_each(|arg| {
                    self.check_expr(&arg.expr, scopes);
                });
                Some(Type::Int(IntKind::I64))
            }
            _ => None,
        }
    }

    /// Report (and still type-check, to surface their own errors) arguments beyond
    /// the fixed arity of a builtin slice mutator, so `a.push(x, y)` is rejected
    /// rather than silently dropping `y` -- which previously let `a.push(a, 2)`
    /// parse as a self-push.
    fn reject_extra_args(
        &mut self,
        method: &str,
        args: &[Arg],
        arity: usize,
        scopes: &mut ScopeStack,
        span: prepoly_parser::Span,
    ) {
        for arg in args.iter().skip(arity) {
            self.check_expr(&arg.expr, scopes);
        }
        if args.len() > arity {
            self.errors.push(TypeError {
                message: format!(
                    "method `{method}` takes {arity} argument(s), found {}",
                    args.len()
                ),
                span,
            });
        }
    }
}

/// Value class expected by a numeric runtime helper argument. Used to reject a
/// concrete wrong class (e.g. a float where an integer is required) before the
/// runtime reinterprets payload bits.
enum NumericClass {
    Int,
    Float,
    Str,
    Bool,
}

impl NumericClass {
    fn accepts(&self, ty: &Type) -> bool {
        match self {
            NumericClass::Int => matches!(ty, Type::Int(_)),
            NumericClass::Float => matches!(ty, Type::Float(_)),
            NumericClass::Str => matches!(ty, Type::Str),
            NumericClass::Bool => matches!(ty, Type::Bool),
        }
    }

    fn describe(&self) -> &'static str {
        match self {
            NumericClass::Int => "an integer",
            NumericClass::Float => "a float",
            NumericClass::Str => "a string",
            NumericClass::Bool => "a bool",
        }
    }
}

/// The text of `expr` when it is an interpolation-free string literal. `""`
/// lexes to no segments at all, so an empty segment list is the empty string.
fn str_literal(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Str(segs, _) => segs
            .iter()
            .map(|s| match s {
                StrSeg::Lit(t) => Some(t.as_str()),
                StrSeg::Expr(_) => None,
            })
            .collect(),
        _ => None,
    }
}

pub(super) fn primitive_static_return(tname: &str, method: &str) -> Option<Type> {
    if let Some(k) = IntKind::from_name(tname) {
        return match method {
            "from" | "parse" => Some(Type::result(Type::Int(k), Type::Str)),
            _ => None,
        };
    }
    match (tname, method) {
        ("float32", "from") => Some(Type::Float(FloatKind::F32)),
        ("float32", "parse") => Some(Type::result(Type::Float(FloatKind::F32), Type::Str)),
        ("float64", "from") => Some(Type::Float(FloatKind::F64)),
        ("float64", "parse") => Some(Type::result(Type::Float(FloatKind::F64), Type::Str)),
        ("string", "from") => Some(Type::Str),
        _ => None,
    }
}
