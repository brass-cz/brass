//! Typing of the callables that have no user-level signature to elaborate:
//! the runtime builtins (`len`, the concurrency primitives, the `_`-prefixed
//! runtime helpers), the prelude's `print`/`println`, the builtin methods
//! (array `push`/`pop`/`insert`/`remove`/`len`, string `len`, nullable
//! `context`, the built-in `debug`) and the static methods of the primitive
//! type words (`T.from`, `T.parse`, `T.default()`). It also owns the
//! renderability rule every rendering site shares (`expect_renderable`).
//!
//! `spawn` and `with` are language constructs in call position. Any other
//! builtin or prelude name is typed here only where the call reaches it: a
//! local binding, or a function the current module declares or imports under
//! that name, shadows it in that scope or module only.

use super::*;

impl<'a> Checker<'a> {
    /// The type of a call of the builtin function `name` -- a runtime
    /// primitive, or a prelude function typed without elaborating its body
    /// (`print`, `println`, the `input` stand-in) -- with its arguments
    /// checked. `spawn` and `with` always denote constructs. For other names,
    /// `None` when the name is not a builtin or a visible binding or function
    /// shadows it, matching MIR's ordinary call resolution.
    pub(super) fn builtin_function_type(
        &mut self,
        name: &str,
        args: &[Arg],
        span: brass_parser::Span,
        scopes: &mut ScopeStack,
    ) -> Option<Type> {
        if !matches!(name, "spawn" | "with")
            && !self.calls_prelude_function(name, self.lookup(scopes, name).is_some())
        {
            return None;
        }
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
                // A `ref`/`mut`/`const` view has the length of what it views.
                let resolved = self.resolve(&arg_ty);
                if !is_maybe_indexable(brass_hir::peel_modes(&resolved)) {
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
        // The prelude's `print`/`println` only render their argument; they are
        // typed here rather than by elaborating their bodies.
        if matches!(name, "print" | "println") {
            for a in args {
                let ty = self.check_expr(&a.expr, scopes);
                self.expect_renderable(&ty, a.expr.span(), "cannot print");
                self.invalidate_after_rendering(&ty, scopes);
            }
            return Some(Type::Void);
        }
        if name == "input" && self.lookup_function("input").is_none() {
            // The prelude defines the real `input` (an inferred-fallible
            // `string!`), and a call of it is elaborated like any function's.
            // This stand-in keeps a static type for the name in a program
            // without the prelude, so the checker never hands out an
            // unconstrained unknown for it.
            self.check_arg_count("input", 0, args.len(), span);
            args.iter().for_each(|a| {
                self.check_expr(&a.expr, scopes);
            });
            return Some(Type::result(Type::Str, Type::Str));
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
        if name == "_panic" {
            // `_panic(msg)`: abort the program with `msg` (the primitive
            // behind `assert`). It yields no value, as on the back ends.
            self.check_builtin_args_against(name, args, &[Type::Str], span, scopes);
            return Some(Type::Void);
        }
        if name == "_flush" {
            // `_flush()`: push buffered output to the operating system.
            self.check_arg_count(name, 0, args.len(), span);
            for arg in args {
                self.check_expr(&arg.expr, scopes);
            }
            return Some(Type::Void);
        }
        if name == "_argv" {
            // `_argv() -> string[]`: the program's argument vector (the
            // program file, then everything after it on the command line).
            // The primitive behind the env library's `args()`.
            self.check_arg_count(name, 0, args.len(), span);
            for arg in args {
                self.check_expr(&arg.expr, scopes);
            }
            return Some(Type::Slice(Box::new(Type::Str)));
        }
        if let Some(ret) = brass_hir::plugin_builtin_return(name) {
            self.check_plugin_call(name, args, span, scopes);
            return Some(ret);
        }
        None
    }

    /// Reject rendering a value of type `ty` (the operand at `span`) as text
    /// when some part of it has no rendering (see
    /// [`brass_hir::unrenderable_part`]): a `void` -- the expression produces
    /// no value -- or a function value. Every rendering site (`print`,
    /// `println`, a `"{v}"` segment, `string.from`, the built-in `debug`)
    /// shares this rule, so the back ends never meet such an operand. `what`
    /// leads the message (`"cannot print"`). A still-open type is decided by
    /// the per-instantiation checks of its generic body.
    pub(super) fn expect_renderable(&mut self, ty: &Type, span: brass_parser::Span, what: &str) {
        let resolved = self.resolve(ty);
        let Some(part) = brass_hir::unrenderable_part(&resolved) else {
            return;
        };
        let reason = match part {
            Type::Void => "the expression produces no value",
            _ => "a function value has no text rendering",
        };
        self.errors.push(TypeError {
            message: format!("{what} `{}`: {reason}", resolved.display()),
            span,
        });
    }

    /// `_plugin_[f]call_<t>(logical_id, name, sig, payload...)`: the loader
    /// synthesizes these with three leading string literals, but the builtin is
    /// nameable from user source, and the runtime reads each payload slot as
    /// the signature's type without re-checking it. A wrong slot is therefore
    /// undefined behaviour, so the payload is typed here against the signature
    /// -- which must be a literal for that to be possible at all.
    fn check_plugin_call(
        &mut self,
        name: &str,
        args: &[Arg],
        span: brass_parser::Span,
        scopes: &mut ScopeStack,
    ) {
        if args.len() < 3 {
            self.errors.push(TypeError {
                message: format!("`{name}` expects at least 3 arguments (logical id, name, sig)"),
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
        let Some((params, _, _)) = brass_hir::plugin_sig_types(&sig) else {
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
    /// as an integer. Concrete wrong classes are static errors; a still-open
    /// argument is judged by the check of each instantiation.
    fn numeric_helper_type(
        &mut self,
        name: &str,
        args: &[Arg],
        span: brass_parser::Span,
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

    /// Static contracts for the concurrency primitives: the programmer-facing
    /// `spawn(f: () -> void)`, `sync()` and `with(c, f) -> U`, and the
    /// `_cown`/`_freeze`/`_with_all` forms the spawn auto-acquire pass
    /// inserts.
    fn concurrency_builtin_type(
        &mut self,
        name: &str,
        args: &[Arg],
        span: brass_parser::Span,
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
                        Type::Fun(_, ret) => {
                            let ret = self.resolve(&ret);
                            if !matches!(ret, Type::Void | Type::Unknown(_)) {
                                self.errors.push(TypeError {
                                    message: format!(
                                        "`spawn` expects a closure returning `void`, found \
                                         `() -> {}`",
                                        ret.display()
                                    ),
                                    span: arg.expr.span(),
                                });
                            }
                        }
                        Type::Unknown(_) => {}
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
            // `with(obj, f)` acquires `obj` and yields `f(obj)`: `f` is
            // checked against `(typeof obj) -> R` like a closure argument of
            // any call, so an unannotated parameter takes `obj`'s type, the
            // body is checked at it, and the call's type is the closure's
            // result `R` -- the type the guarded expression had before the
            // spawn auto-guard wrapped it in a `with`.
            "with" => {
                self.check_arg_count("with", 2, args.len(), span);
                let obj = match args.first() {
                    Some(arg) => self.check_expr(&arg.expr, scopes),
                    None => self.fresh_unknown(),
                };
                let ret = match args.get(1) {
                    Some(arg) => {
                        let result = self.fresh_unknown();
                        let expected = Type::Fun(vec![obj], Box::new(result.clone()));
                        self.last_closure_result = None;
                        let got = self.check_expr_against(&arg.expr, &expected, scopes);
                        // Checking a literal against the expected type only
                        // probes its result; this call applies it, so what the
                        // body returns at `obj`'s type is the result, as an
                        // application of any closure value commits it.
                        if let Some(observed) = self.last_closure_result.take()
                            && !brass_hir::is_fully_known(&self.resolve(&result))
                        {
                            let _ = self.solver.unify(&result, &observed);
                        }
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
            // `spawn` become observable before the program continues (the
            // structured-concurrency barrier).
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

    /// The light pass's return types for builtin callees, and for the prelude
    /// functions typed as builtins (`print`, `assert`, ...). Each applies only
    /// when the call reaches it rather than a shadowing local binding or
    /// function (see the module doc); the caller checks that.
    pub(super) fn builtin_function_type_light(&self, name: &str) -> Option<Type> {
        if let Some(ret) = brass_hir::plugin_builtin_return(name) {
            return Some(ret);
        }
        match name {
            "_print_str" | "_println_str" => Some(Type::Void),
            "_stdin_read" => Some(Type::result(
                Type::Slice(Box::new(Type::Int(IntKind::U8))),
                Type::Str,
            )),
            "_argv" => Some(Type::Slice(Box::new(Type::Str))),
            "_flush" | "_panic" => Some(Type::Void),
            // The prelude declares the real `input` (an inferred-fallible
            // `string!` whose Err is the prelude `Error`); its return comes
            // from the precompute table like any function's. This type only
            // stands in for a program without the prelude, as in the full
            // check (`builtin_function_type`).
            "input" if self.lookup_function("input").is_none() => {
                Some(Type::result(Type::Str, Type::Str))
            }
            "len" => Some(Type::Int(IntKind::I64)),
            "print" | "println" | "assert" => Some(Type::Void),
            "_string_concat" | "_string_slice" => Some(Type::Str),
            // The character at a byte offset, or null past the end or inside a
            // multibyte character.
            "_string_char_at" => Some(Type::Nullable(Box::new(Type::Str))),
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

    fn string_builtin_type(
        &mut self,
        name: &str,
        args: &[Arg],
        span: brass_parser::Span,
        scopes: &mut ScopeStack,
    ) -> Option<Type> {
        let i64_ty = Type::Int(IntKind::I64);
        let bytes_ty = Type::Slice(Box::new(Type::Int(IntKind::U8)));
        let (params, ret) = match name {
            "_string_concat" => (vec![Type::Str, Type::Str], Type::Str),
            "_string_slice" => (vec![Type::Str, i64_ty.clone(), i64_ty.clone()], Type::Str),
            "_string_bytes" => (vec![Type::Str], bytes_ty),
            "_string_from_bytes" => (vec![bytes_ty], Type::result(Type::Str, Type::Str)),
            "_string_char_at" => (vec![Type::Str, i64_ty], Type::Nullable(Box::new(Type::Str))),
            "_string_cmp" => (vec![Type::Str, Type::Str], Type::Int(IntKind::I32)),
            "_string_find" => (
                vec![Type::Str, Type::Str],
                Type::Nullable(Box::new(Type::Int(IntKind::I64))),
            ),
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
        span: brass_parser::Span,
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

    /// The type of the call `recv.method(args)` when `method` is a builtin
    /// method of the receiver (nullable `context`, the built-in `debug`, an
    /// array or string method), with its arguments checked; `None` when it is
    /// not one and the call resolves like any method call.
    pub(super) fn builtin_method_type(
        &mut self,
        recv_ty: &Type,
        method: &str,
        args: &[Arg],
        scopes: &mut ScopeStack,
        span: brass_parser::Span,
    ) -> Option<Type> {
        if let Some(ret) = self.nullable_context_method_type(recv_ty, method, args, scopes, span) {
            return Some(ret);
        }
        if let Some(ret) = self.debug_method_type(recv_ty, method, args, scopes, span) {
            return Some(ret);
        }
        self.array_method_type(recv_ty, method, args, scopes, span)
    }

    /// The nullable `context` surface turns absence into the same traced error
    /// value as `error(message)`. A nullable prelude Result is deliberately
    /// returned as its inner Result, because exposing a second Result layer
    /// would preserve the ambiguity this method resolves.
    fn nullable_context_method_type(
        &mut self,
        recv_ty: &Type,
        method: &str,
        args: &[Arg],
        scopes: &mut ScopeStack,
        span: brass_parser::Span,
    ) -> Option<Type> {
        if method != "context" {
            return None;
        }
        let resolved = self.resolve(recv_ty);
        let Type::Nullable(inner) = brass_hir::peel_modes(&resolved) else {
            return None;
        };

        if !(1..=2).contains(&args.len()) {
            self.errors.push(TypeError {
                message: format!("`context` expects 1 to 2 argument(s), got {}", args.len()),
                span,
            });
        }
        if let Some(message) = args.first() {
            self.check_expr_against(&message.expr, &Type::Str, scopes);
        }
        if let Some(location) = args.get(1) {
            let location_ty = self
                .program
                .prelude_type("Location")
                .map(brass_hir::TypeInfo::type_ref)
                .unwrap_or_else(|| self.fresh_unknown());
            self.check_expr_against(&location.expr, &location_ty, scopes);
        }
        for arg in args.iter().skip(2) {
            self.check_expr(&arg.expr, scopes);
        }

        let inner = (**inner).clone();
        if matches!(&inner, Type::Sum(result) if result.id == brass_hir::RESULT_TYPE_ID) {
            return Some(inner);
        }
        let error = match self.program.prelude_type("Error") {
            Some(info) => {
                let mut error = NominalType::new(info.id, &info.name);
                error.substitution.insert("value", Type::Str);
                Type::Record(error)
            }
            None => Type::Str,
        };
        Some(Type::result(inner, error))
    }

    /// The built-in `debug` renderer: every value can `v.debug()` itself into a
    /// string (every type satisfies the `Debug` protocol). The scalar
    /// primitives implement `debug` in core (`fun string.debug` carries the
    /// quoting) and a user type may declare its own, so this claims the name
    /// only for the REMAINING receivers -- records/sums without a user `debug`,
    /// arrays, tuples, and still-open generics -- whose rendering is the
    /// built-in structural one (what `"{v}"` emits for a value whose type
    /// declares no `display`).
    fn debug_method_type(
        &mut self,
        recv_ty: &Type,
        method: &str,
        args: &[Arg],
        scopes: &mut ScopeStack,
        span: brass_parser::Span,
    ) -> Option<Type> {
        if method != "debug" {
            return None;
        }
        let base = brass_hir::peel_modes(&self.resolve(recv_ty)).clone();
        // A nullable receiver narrows first, like any other method call.
        if matches!(base, Type::Nullable(_)) {
            return None;
        }
        // Scalars dispatch to core's primitive methods.
        if let Some(class) = base.primitive_class()
            && class != "array"
        {
            return None;
        }
        // A user-declared `debug` wins over the built-in renderer.
        if let Type::Record(n) | Type::Sum(n) = &base
            && let Some(info) = self.program.type_by_id(n.id)
        {
            let declared = match &info.kind {
                TypeKind::Record { methods, .. } => methods.contains_key("debug"),
                TypeKind::Sum { variants } => {
                    variants.iter().any(|v| v.methods.contains_key("debug"))
                }
            };
            if declared {
                return None;
            }
        }
        args.iter().for_each(|arg| {
            self.check_expr(&arg.expr, scopes);
        });
        if !args.is_empty() {
            self.errors.push(TypeError {
                message: format!("`debug` takes no arguments, found {}", args.len()),
                span,
            });
        }
        self.expect_renderable(&base, span, "`debug` cannot render");
        Some(Type::Str)
    }

    /// Type the builtin collection methods so their element types are enforced:
    /// on a `T[]`, `push(value: T) -> void`, `insert(idx: int64, value: T) ->
    /// void`, `pop() -> T?`, `remove(idx: int64) -> T` and `len() -> int64`
    /// (also on a `string`). Element checking turns `[1].push("x")` into a
    /// static error.
    ///
    /// `push`/`pop`/`insert`/`remove` are slice-only: a fixed array `T[n]` has
    /// a statically fixed length (modeled as an inline `[n x T]`), so a
    /// length-changing call on one is rejected. `len` and indexing remain valid
    /// for both `T[n]` and `T[]` (indexing is handled in the `Index`/place
    /// paths).
    fn array_method_type(
        &mut self,
        recv_ty: &Type,
        method: &str,
        args: &[Arg],
        scopes: &mut ScopeStack,
        span: brass_parser::Span,
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
                    self.check_element_value(&arg.expr, elem, scopes);
                }
                self.check_method_arg_count(method, args, 1, scopes, span);
                Some(Type::Void)
            }
            ("pop", Some(elem)) => {
                self.check_method_arg_count(method, args, 0, scopes, span);
                Some(Type::Nullable(Box::new(elem.clone())))
            }
            // `arr.insert(idx, v)`: idx is int64, v is the element.
            ("insert", Some(elem)) => {
                if let Some(idx) = args.first() {
                    let got = self.check_expr(&idx.expr, scopes);
                    self.expect_expr_assignable(&got, &Type::Int(IntKind::I64), &idx.expr);
                }
                if let Some(value) = args.get(1) {
                    self.check_element_value(&value.expr, elem, scopes);
                }
                self.check_method_arg_count(method, args, 2, scopes, span);
                Some(Type::Void)
            }
            // `arr.remove(idx) -> T`: removes and returns the element.
            ("remove", Some(elem)) => {
                if let Some(idx) = args.first() {
                    let got = self.check_expr(&idx.expr, scopes);
                    self.expect_expr_assignable(&got, &Type::Int(IntKind::I64), &idx.expr);
                }
                self.check_method_arg_count(method, args, 1, scopes, span);
                Some(elem.clone())
            }
            ("len", Some(_)) => {
                self.check_method_arg_count(method, args, 0, scopes, span);
                Some(Type::Int(IntKind::I64))
            }
            _ if method == "len" && matches!(base, Type::Str) => {
                self.check_method_arg_count(method, args, 0, scopes, span);
                Some(Type::Int(IntKind::I64))
            }
            _ => None,
        }
    }

    /// Enforce a builtin method's fixed arity while still checking every excess
    /// expression, so an arity error does not hide independent nested diagnostics.
    fn check_method_arg_count(
        &mut self,
        method: &str,
        args: &[Arg],
        arity: usize,
        scopes: &mut ScopeStack,
        span: brass_parser::Span,
    ) {
        for arg in args.iter().skip(arity) {
            self.check_expr(&arg.expr, scopes);
        }
        if args.len() != arity {
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

/// The result type of the builtin static method `tname.method` of a
/// primitive type word: `T.default()`, the fallible `intN.from`/`intN.parse`,
/// `floatN.from`, the fallible `floatN.parse`, and `string.from`, which renders
/// its argument exactly like `"{x}"`. `None` for anything else.
pub(super) fn primitive_static_return(tname: &str, method: &str) -> Option<Type> {
    // `T.default()`: the zero value of every primitive class (the `Default`
    // protocol's builtin implementations; MIR folds the call to a constant).
    if method == "default" {
        return primitive_default_type(tname);
    }
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

/// The type `T.default()` produces for a primitive type word.
pub(super) fn primitive_default_type(tname: &str) -> Option<Type> {
    if let Some(k) = IntKind::from_name(tname) {
        return Some(Type::Int(k));
    }
    match tname {
        "float32" => Some(Type::Float(FloatKind::F32)),
        "float64" => Some(Type::Float(FloatKind::F64)),
        "bool" => Some(Type::Bool),
        "string" => Some(Type::Str),
        _ => None,
    }
}
