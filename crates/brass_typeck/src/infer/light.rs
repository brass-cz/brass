//! Light (best-effort) inference pass used before full checking:
//! return-type discovery for unannotated functions and a cheap
//! expression walker that types bodies without reporting errors.

use super::*;

impl<'a> Checker<'a> {
    pub(super) fn infer_returns_block(
        &mut self,
        block: &Block,
        env: &mut HashMap<String, Type>,
        normal: &mut Vec<(Type, Span)>,
        props: &mut LightProps,
    ) {
        for stmt in &block.stmts {
            match stmt {
                Stmt::Let { pat, value, .. } => {
                    let ty = match value {
                        Some(value) => self.infer_expr_light(value, env, props),
                        // Uninitialized `let`: the light pass has no annotation
                        // resolution; the full check types the binding.
                        None => Type::Unknown(brass_hir::INFER_VAR),
                    };
                    self.bind_pattern_light(pat, &ty, env);
                }
                Stmt::Assign { value, .. } => {
                    self.infer_expr_light(value, env, props);
                }
                Stmt::Expr(value) => {
                    // Grow a locally-built collection's element type: a
                    // `result = []` then `result.push(x)` pins `result`'s element
                    // to `x`, so an unannotated function that returns the built
                    // collection (e.g. `slice`/`map`) infers its element type from
                    // the values pushed -- which the rest of this light pass would
                    // otherwise miss, leaving the return an unconstrained `?[]`.
                    self.track_collection_growth(value, env, props);
                    self.infer_returns_expr(value, env, normal, props);
                }
                Stmt::While { cond, body, .. } => {
                    self.infer_expr_light(cond, env, props);
                    self.infer_returns_block(body, &mut env.clone(), normal, props);
                }
                Stmt::For {
                    pat, iter, body, ..
                } => {
                    let iter_ty = self.infer_expr_light(iter, env, props);
                    let item_ty =
                        brass_hir::index_element(&iter_ty).unwrap_or_else(|| self.fresh_unknown());
                    let mut inner = env.clone();
                    self.bind_pattern_light(pat, &item_ty, &mut inner);
                    self.infer_returns_block(body, &mut inner, normal, props);
                }
                Stmt::Return(Some(expr), _) => {
                    let ty = self.infer_expr_light(expr, env, props);
                    let resolved = self.resolve(&ty);
                    match resolved.result_payloads() {
                        Some((ok, err)) if ok.is_unknown() => {
                            // A forwarded error is re-raised lifted into the
                            // prelude `Error` (see the full check's
                            // `link_forwarded_error`).
                            let lifted = crate::lift_err_payload(self.program, self.resolve(err));
                            props.errors.push((lifted, expr.span()))
                        }
                        _ => normal.push((ty, expr.span())),
                    }
                }
                Stmt::Return(None, span) => normal.push((Type::Void, *span)),
                Stmt::Break(_) | Stmt::Continue(_) => {}
            }
        }
    }

    fn infer_returns_expr(
        &mut self,
        expr: &Expr,
        env: &mut HashMap<String, Type>,
        normal: &mut Vec<(Type, Span)>,
        props: &mut LightProps,
    ) {
        match expr {
            Expr::If(cond, then, els, _) => {
                self.infer_expr_light(cond, env, props);
                self.infer_returns_block(then, &mut env.clone(), normal, props);
                if let Some(els) = els {
                    self.infer_returns_expr(els, &mut env.clone(), normal, props);
                }
            }
            Expr::IfLet(_, scrut, then, els, _) => {
                self.infer_expr_light(scrut, env, props);
                self.infer_returns_block(then, &mut env.clone(), normal, props);
                if let Some(els) = els {
                    self.infer_returns_expr(els, &mut env.clone(), normal, props);
                }
            }
            Expr::Match(scrut, arms, _) => {
                self.infer_expr_light(scrut, env, props);
                for arm in arms {
                    self.infer_returns_expr(&arm.body, &mut env.clone(), normal, props);
                }
            }
            Expr::Block(block, _) => {
                self.infer_returns_block(block, &mut env.clone(), normal, props)
            }
            other => {
                self.infer_expr_light(other, env, props);
            }
        }
    }

    /// If `expr` is `recv.push(value)` or `recv.insert(idx, value)` where `recv`
    /// is a slice/array, unify its element type with the pushed value's type.
    /// This pins the (fresh, local) element variable of a collection being built
    /// up, so the light return-inference pass sees the grown element type. It
    /// only ever binds the local's own element variable, not the function's
    /// parameter variables.
    fn track_collection_growth(
        &mut self,
        expr: &Expr,
        env: &HashMap<String, Type>,
        props: &mut LightProps,
    ) {
        if let Expr::Call(callee, args, _) = expr
            && let Expr::Field(recv, method, _) = callee.as_ref()
            && matches!(method.as_str(), "push" | "insert")
            && let Some(value_arg) = args.last()
        {
            let recv_ty = self.infer_expr_light(recv, env, props);
            if let Some(elem) = brass_hir::index_element(&self.resolve(&recv_ty)) {
                let value_ty = self.infer_expr_light(&value_arg.expr, env, props);
                let _ = self.solver.unify(&elem, &value_ty);
            }
        }
    }

    pub(super) fn infer_expr_light(
        &mut self,
        expr: &Expr,
        env: &HashMap<String, Type>,
        props: &mut LightProps,
    ) -> Type {
        match expr {
            Expr::Int(v, _) => Type::Int(int_literal_kind(*v)),
            Expr::Float(..) => Type::Float(FloatKind::F64),
            Expr::Bool(..) => Type::Bool,
            Expr::Null(_) => Type::null(),
            Expr::Str(..) => Type::Str,
            Expr::Ident(name, _) => env
                .get(name)
                .cloned()
                .unwrap_or_else(|| self.fresh_unknown()),
            Expr::SelfExpr(_) => env
                .get("self")
                .cloned()
                .unwrap_or_else(|| self.fresh_unknown()),
            Expr::Unary(_, inner, _) => self.infer_expr_light(inner, env, props),
            Expr::Binary(op, left, right, _) => {
                let left = self.infer_expr_light(left, env, props);
                let right = self.infer_expr_light(right, env, props);
                self.infer_binary_light(*op, left, right)
            }
            Expr::Call(callee, args, _) => self.infer_call_light(callee, args, env, props),
            Expr::Field(base, name, _) => self.infer_field_light(base, name, env, props),
            Expr::Index(base, _, _) => match self.infer_expr_light(base, env, props) {
                ref bt if brass_hir::index_element(bt).is_some() => {
                    brass_hir::index_element(bt).unwrap()
                }
                Type::Str => Type::Str,
                _ => self.fresh_unknown(),
            },
            Expr::ErrorProp(inner, span) => {
                let ty = self.infer_expr_light(inner, env, props);
                if let Some((ok, err)) = ty.result_payloads() {
                    {
                        let lifted = crate::lift_err_payload(self.program, self.resolve(err));
                        props.errors.push((lifted, *span));
                    }
                    ok.clone()
                } else if let Type::Nullable(inner_ty) = &ty {
                    // `e!` on a nullable unwraps the value; the null case
                    // returns null from the enclosing callable, whose return
                    // type therefore gains an outer `?` (no error payload).
                    props.nulls.push(*span);
                    (**inner_ty).clone()
                } else {
                    self.fresh_unknown()
                }
            }
            Expr::Closure(params, body, _) => {
                let mut inner = env.clone();
                for param in params {
                    let ty = param
                        .ty
                        .as_ref()
                        .and_then(|t| self.resolve_type(t).ok())
                        .unwrap_or_else(|| self.fresh_unknown());
                    inner.insert(param.name.clone(), ty);
                }
                let ret = self.infer_expr_light(body, &inner, props);
                Type::Fun(
                    params
                        .iter()
                        .map(|p| {
                            inner
                                .get(&p.name)
                                .cloned()
                                .unwrap_or_else(|| self.fresh_unknown())
                        })
                        .collect(),
                    Box::new(ret),
                )
            }
            Expr::Array(items, _) => {
                let elem_tys: Vec<Type> = items
                    .iter()
                    .map(|e| self.infer_expr_light(e, env, props))
                    .collect();
                // Mirror the full check's array-vs-tuple classification and its
                // null handling. The light pass seeds `global_scope`: a global
                // typed `int32[]` here while module init (and the back end)
                // types the same literal as a tuple would let function bodies
                // read tuple slots at the wrong type.
                if let Some(tuple) = self.tuple_of_elements(items, &elem_tys) {
                    Type::Tuple(tuple)
                } else {
                    let base = elem_tys
                        .iter()
                        .zip(items)
                        .find(|(_, e)| !matches!(e, Expr::Null(_)))
                        .map(|(t, _)| t.clone())
                        .unwrap_or_else(|| self.fresh_empty_array_elem());
                    let saw_null = items.iter().any(|e| matches!(e, Expr::Null(_)));
                    if saw_null && !matches!(self.resolve(&base), Type::Nullable(_)) {
                        Type::Slice(Box::new(Type::Nullable(Box::new(base))))
                    } else {
                        Type::Slice(Box::new(base))
                    }
                }
            }
            // Mirror the full check's range rule: the element type is the
            // bounds' common integer type, a literal bound adapting to the
            // other side (so `[0..n]` follows `n`'s width, not the literal's).
            Expr::Range(lo, hi, _) => {
                let lo_ty = self.infer_expr_light(lo, env, props);
                let hi_ty = self.infer_expr_light(hi, env, props);
                let lo_r = self.resolve(&lo_ty);
                let hi_r = self.resolve(&hi_ty);
                let elem = if matches!(hi_r, Type::Int(_)) && integer_literal_fits(lo, &hi_r) {
                    hi_r
                } else if matches!(lo_r, Type::Int(_)) && integer_literal_fits(hi, &lo_r) {
                    lo_r
                } else {
                    common_numeric_type(&lo_r, &hi_r).unwrap_or(lo_r)
                };
                Type::Slice(Box::new(elem))
            }
            Expr::TypeLit(name, fields, _) => self.infer_type_lit_light(name, fields, env, props),
            Expr::VariantLit(name, variant, fields, _) => {
                self.infer_variant_lit_light(name, variant, fields, env, props)
            }
            Expr::If(_, then, els, _) => {
                let then_ty = self.infer_block_value_light(then, &mut env.clone(), props);
                let else_ty = els
                    .as_ref()
                    .map(|e| self.infer_expr_light(e, env, props))
                    .unwrap_or(Type::Void);
                self.common_type_or_unknown(then_ty, else_ty)
            }
            Expr::IfLet(_, scrut, then, els, _) => {
                self.infer_expr_light(scrut, env, props);
                let then_ty = self.infer_block_value_light(then, &mut env.clone(), props);
                let else_ty = els
                    .as_ref()
                    .map(|e| self.infer_expr_light(e, env, props))
                    .unwrap_or(Type::Void);
                self.common_type_or_unknown(then_ty, else_ty)
            }
            Expr::Match(scrut, arms, _) => {
                self.infer_expr_light(scrut, env, props);
                let tys: Vec<Type> = arms
                    .iter()
                    .map(|arm| self.infer_expr_light(&arm.body, env, props))
                    .collect();
                self.common_type_list(&tys)
                    .unwrap_or_else(|| self.fresh_unknown())
            }
            Expr::Block(block, _) => self.infer_block_value_light(block, &mut env.clone(), props),
        }
    }

    fn infer_call_light(
        &mut self,
        callee: &Expr,
        args: &[Arg],
        env: &HashMap<String, Type>,
        props: &mut LightProps,
    ) -> Type {
        if let Expr::Ident(name, _) = callee {
            // Mirror the full check's `error(x)` typing (the prelude Error
            // wrap; see check_call) so entries assembled by this pass carry
            // the same payload shape.
            if name == "error" {
                let value_ty = args
                    .first()
                    .map(|a| self.infer_expr_light(&a.expr, env, props))
                    .unwrap_or(Type::Void);
                for a in args.iter().skip(1) {
                    self.infer_expr_light(&a.expr, env, props);
                }
                // A program without the prelude keeps the legacy raw payload.
                let err_ty = match self.program.types.get("Error") {
                    Some(err_info) => {
                        let mut err = NominalType::new(err_info.id, &err_info.name);
                        err.substitution.insert("value", self.resolve(&value_ty));
                        Type::Record(err)
                    }
                    None => self.resolve(&value_ty),
                };
                let ok = self.fresh_unknown();
                return Type::result(ok, err_ty);
            }
            if let Some(ret) = self.builtin_function_type_light(name) {
                args.iter().for_each(|arg| {
                    self.infer_expr_light(&arg.expr, env, props);
                });
                return ret;
            }
            // The table is keyed by SYMBOL. A bare unique name is its own symbol, but
            // a module-qualified call (`percent.decode`, which the resolve pass
            // rewrote to a dotted marker) and a renamed import are not -- and a
            // missed lookup here costs the caller its whole error type: the `!` on
            // the call records an unknown Err, so `url`'s `path_segments` inferred no
            // error type at all despite propagating one.
            let symbol = self
                .function_returns
                .contains_key(name)
                .then(|| name.clone())
                .or_else(|| self.lookup_function(name).map(|f| f.symbol.clone()));
            if let Some(ret) = symbol.and_then(|s| self.function_returns.get(&s).cloned()) {
                args.iter().for_each(|arg| {
                    self.infer_expr_light(&arg.expr, env, props);
                });
                return ret;
            }
        }
        if let Expr::Field(base, method, _) = callee {
            if let Expr::Ident(tname, _) = &**base
                && env.get(tname).is_none()
            {
                let ret = self.primitive_static_type(tname, method);
                if ret.is_some() {
                    args.iter().for_each(|arg| {
                        self.infer_expr_light(&arg.expr, env, props);
                    });
                }
                if let Some(ret) = ret {
                    return ret;
                }
                // A user type's STATIC method (`File.open(..)`, `HttpClient.http(..)`):
                // the base names a type rather than a value, so there is no receiver
                // to infer and the receiver-keyed lookup below cannot fire.
                //
                // A fully-known annotation IS the answer. Otherwise -- an unannotated
                // constructor, or a `T!` whose Err payload the annotation leaves open
                // -- the precompute table has it, and is read FRESHENED. That table
                // holds the variables of one shared instantiation, so handing it over
                // verbatim would let the first call site that constrains them pin them
                // for every other: a witness-free `HashMap.new()`, whose key/value
                // slots are meant to be fixed by each binding's own use, would take
                // the first `set` in the program and leave every later binding
                // unrefined. Fresh variables per site keep that inference intact while
                // still telling the light pass WHICH type the call built -- without
                // which a local bound from a constructor stays unknown and every method
                // called on it is unknown too (`http`'s `fetch` came out as
                // `Result<unknown, string>`), and a caller of `File.open(..)!` could
                // not see the Err type it propagates.
                // Resolved MODULE-AWARE, not by bare key: a type whose name is also
                // declared elsewhere (serv's `type HttpServer = Server` alias next
                // to serve's nominal) has only module-qualified symbols, and the
                // bare lookup missing made `HttpServer.new(..)!` type as unknown --
                // the caller then lost its whole inferred fallibility.
                if self.resolve_type_symbol(tname).is_some()
                    && let Some(resolved) = self.method_for_qualifier(tname, method)
                {
                    let declared = resolved.signature.ret_ty.clone();
                    let ret = match &declared {
                        Some(ty) if brass_hir::is_fully_known(ty) => declared,
                        _ => {
                            let key = (resolved.qualifier.clone(), method.clone());
                            let from_table = self.method_returns.get(&key).cloned().map(|ty| {
                                let ty = self.resolve(&ty);
                                self.freshen(&ty)
                            });
                            // A CONSTRUCTOR (`HashMap.new()`) is rebuilt from the
                            // type's SCHEME rather than taken from the table. The
                            // light pass infers the constructor's body without the
                            // scheme, so its `Self { .. }` carries the field types it
                            // could see there (`_entries: never?[]`, from a slot array
                            // sized with `null`) rather than the ones the scheme
                            // expresses over the type's parameters
                            // (`_Entry<key, value>?[]`). That shape is not merely
                            // imprecise, it is a DIFFERENT type: nothing can pin the
                            // element types through it, and it does not even unify
                            // with what the full check builds. A fresh scheme instance
                            // is what the full check hands back.
                            let instance = from_table
                                .as_ref()
                                .map(|ty| self.resolve(ty))
                                .and_then(|ty| self.fresh_scheme_instance(&ty));
                            instance.or(from_table).or(declared)
                        }
                    };
                    if let Some(ret) = ret {
                        args.iter().for_each(|arg| {
                            self.infer_expr_light(&arg.expr, env, props);
                        });
                        return ret;
                    }
                }
            }
            let recv = self.infer_expr_light(base, env, props);
            // A user method's precomputed return: methods of a nominal
            // receiver (peeling a narrowed nullable) resolve through the same
            // table the full pass consults, so a body that propagates another
            // type's fallible method infers fallible itself. The precompute
            // runs twice, so a cross-type chain sees its callee's entry.
            let peeled = match self.resolve(&recv) {
                Type::Nullable(inner) => *inner,
                other => other,
            };
            if let Type::Record(n) | Type::Sum(n) = &peeled
                && let Some(ret) = self
                    .method_returns
                    .get(&(n.name.clone(), method.clone()))
                    .cloned()
            {
                args.iter().for_each(|arg| {
                    self.infer_expr_light(&arg.expr, env, props);
                });
                return ret;
            }
        }
        args.iter().for_each(|arg| {
            self.infer_expr_light(&arg.expr, env, props);
        });
        self.fresh_unknown()
    }

    /// A fresh instance of `ty`'s nominal built from its SCHEME: every scheme
    /// parameter takes its own variable, and each field is the scheme's field type
    /// over them. `None` when `ty` is not a record with a scheme.
    ///
    /// Restricted to a record with declared type SLOTS (`key: type`). Those are the
    /// witness-free containers whose element types a use has to pin, and whose
    /// constructor the light pass gets wrong. Every other record's fields are
    /// whatever its constructor built, and the scheme's view of them -- a
    /// generalization over the co-checked bodies -- is not the same thing: rebuilding
    /// an `HttpClient` from it replaces the closure its `_connect` field actually
    /// holds.
    fn fresh_scheme_instance(&mut self, ty: &Type) -> Option<Type> {
        let Type::Record(n) = ty else {
            return None;
        };
        let info = self.program.type_by_id(n.id)?;
        if info.slots.is_empty() {
            return None;
        }
        let scheme = self.schemes.get(n.name())?.clone();
        let mut map: HashMap<u32, Type> = HashMap::default();
        for p in &scheme.params {
            let fresh = self.fresh_unknown();
            map.insert(*p, fresh);
        }
        let mut subst = brass_hir::Substitution::empty();
        for (name, fty) in &scheme.fields {
            subst.insert(
                name.clone(),
                super::instantiate::apply_scheme_param_map(fty, &map),
            );
        }
        Some(Type::Record(brass_hir::NominalType::with_substitution(
            n.id,
            n.name().to_string(),
            subst,
        )))
    }

    fn infer_field_light(
        &mut self,
        base: &Expr,
        name: &str,
        env: &HashMap<String, Type>,
        props: &mut LightProps,
    ) -> Type {
        let shadowed = matches!(base, Expr::Ident(n, _) if env.contains_key(n));
        if let Some(ty) = self.unit_variant_type(base, name, shadowed) {
            return ty;
        }
        // Resolve the base before matching: an indexed element or other
        // intermediate may still be an open inference variable that the solver has
        // since pinned to a record (e.g. `self._entries[idx]` is the map's entry
        // type once a `push` fixed it). Without resolving, the match falls through
        // and the field type is lost as a fresh unknown.
        let base_ty = self.infer_expr_light(base, env, props);
        match self.resolve(&base_ty) {
            Type::Record(record) => record.substitution.get(name).cloned().unwrap_or_else(|| {
                self.program
                    .types
                    .get(record.name())
                    .and_then(|info| match &info.kind {
                        TypeKind::Record { fields, .. } => fields.iter().find(|f| f.name == name),
                        TypeKind::Sum { .. } => None,
                    })
                    .and_then(|f| f.resolved_ty.clone())
                    .unwrap_or_else(|| self.fresh_unknown())
            }),
            Type::Sum(sum) => self
                .self_variant_field_type(base, &sum, name)
                .or_else(|| self.common_sum_field_type(&sum, name))
                .unwrap_or_else(|| self.fresh_unknown()),
            _ => self.fresh_unknown(),
        }
    }

    fn infer_type_lit_light(
        &mut self,
        name: &str,
        fields: &[(String, Expr)],
        env: &HashMap<String, Type>,
        props: &mut LightProps,
    ) -> Type {
        if name.is_empty() {
            let field_tys: Vec<(String, Type)> = fields
                .iter()
                .map(|(fname, e)| (fname.clone(), self.infer_expr_light(e, env, props)))
                .collect();
            return brass_hir::structural_record(field_tys);
        }
        let tn = self.resolve_self_name(name);
        let resolved = self
            .resolve_type_symbol(&tn)
            .and_then(|symbol| self.program.types.get(&symbol))
            .and_then(|info| {
                let TypeKind::Record { fields, .. } = &info.kind else {
                    return None;
                };
                Some((info.type_ref(), fields.clone()))
            });
        let Some((ret, declared)) = resolved else {
            fields.iter().for_each(|(_, expr)| {
                self.infer_expr_light(expr, env, props);
            });
            return self.fresh_unknown();
        };
        let substitution = self.infer_lit_field_substitution(None, &declared, fields, env, props);
        apply_nominal_substitution(ret, substitution)
    }

    fn infer_variant_lit_light(
        &mut self,
        type_name: &str,
        variant: &str,
        fields: &[(String, Expr)],
        env: &HashMap<String, Type>,
        props: &mut LightProps,
    ) -> Type {
        let tn = self.resolve_self_name(type_name);
        let resolved = self
            .resolve_type_symbol(&tn)
            .and_then(|symbol| self.program.types.get(&symbol))
            .and_then(|info| {
                let variant = info.variant(variant)?;
                Some((info.type_ref(), variant.fields.clone()))
            });
        let Some((ret, declared)) = resolved else {
            fields.iter().for_each(|(_, expr)| {
                self.infer_expr_light(expr, env, props);
            });
            return self.fresh_unknown();
        };
        let substitution =
            self.infer_lit_field_substitution(Some(variant), &declared, fields, env, props);
        apply_nominal_substitution(ret, substitution)
    }

    fn infer_lit_field_substitution(
        &mut self,
        variant: Option<&str>,
        declared: &[brass_hir::FieldInfo],
        fields: &[(String, Expr)],
        env: &HashMap<String, Type>,
        props: &mut LightProps,
    ) -> Substitution {
        let mut substitution = Substitution::empty();
        for field in declared {
            if let Some((_, expr)) = fields.iter().find(|(name, _)| name == &field.name) {
                let got = self.infer_expr_light(expr, env, props);
                if field.resolved_ty.as_ref().is_some_and(Type::is_unknown) {
                    substitution.insert(field_substitution_key(variant, &field.name), got);
                }
            }
        }
        substitution
    }

    fn infer_block_value_light(
        &mut self,
        block: &Block,
        env: &mut HashMap<String, Type>,
        props: &mut LightProps,
    ) -> Type {
        let mut last = Type::Void;
        for stmt in &block.stmts {
            match stmt {
                Stmt::Let { pat, value, .. } => {
                    let ty = match value {
                        Some(value) => self.infer_expr_light(value, env, props),
                        None => Type::Unknown(brass_hir::INFER_VAR),
                    };
                    self.bind_pattern_light(pat, &ty, env);
                    last = Type::Void;
                }
                Stmt::Expr(expr) => last = self.infer_expr_light(expr, env, props),
                Stmt::Return(Some(expr), _) => return self.infer_expr_light(expr, env, props),
                _ => last = Type::Void,
            }
        }
        last
    }

    fn infer_binary_light(&mut self, op: BinOp, left: Type, right: Type) -> Type {
        match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => {
                if self.can_unify(&left, &right) {
                    left
                } else {
                    self.fresh_unknown()
                }
            }
            BinOp::Eq
            | BinOp::Ne
            | BinOp::Lt
            | BinOp::Gt
            | BinOp::Le
            | BinOp::Ge
            | BinOp::And
            | BinOp::Or => Type::Bool,
            BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr => {
                if self.can_unify(&left, &right) {
                    left
                } else {
                    self.fresh_unknown()
                }
            }
        }
    }

    pub(super) fn common_type_list(&mut self, types: &[Type]) -> Option<Type> {
        let (first, rest) = types.split_first()?;
        let mut common = first.clone();
        for ty in rest {
            if let Some(nullable) = common_nullable_type(&common, ty) {
                common = nullable;
                continue;
            }
            if !self.can_unify(&common, ty) {
                return Some(self.fresh_unknown());
            }
        }
        Some(common)
    }

    pub(super) fn bind_pattern_light(
        &mut self,
        pat: &Pattern,
        ty: &Type,
        env: &mut HashMap<String, Type>,
    ) {
        match pat {
            Pattern::Binding(name, _) if !self.is_unit_variant_name(name) => {
                env.insert(name.clone(), ty.clone());
            }
            Pattern::Record(variant, fields, _) => {
                let field_types = self.pattern_field_types(ty, variant);
                for field in fields {
                    let fty = field_types
                        .get(&field.name)
                        .cloned()
                        .unwrap_or_else(|| self.fresh_unknown());
                    if let Some(subpat) = &field.pat {
                        self.bind_pattern_light(subpat, &fty, env);
                    } else {
                        env.insert(field.name.clone(), fty);
                    }
                }
            }
            Pattern::Array(pats, _) => match self.resolve(ty) {
                Type::Tuple(elems) => {
                    for (pat, ety) in pats.iter().zip(&elems) {
                        self.bind_pattern_light(pat, ety, env);
                    }
                }
                Type::Array(inner, _) | Type::Slice(inner) => {
                    for pat in pats {
                        self.bind_pattern_light(pat, &inner, env);
                    }
                }
                // The subject's shape is not known here. Each position gets its OWN
                // variable, rather than the subject itself: the positions of a
                // destructuring are independent values, and binding every one to the
                // whole subject makes `[k, v]` claim that `k` and `v` each ARE the
                // pair -- so a `m.set(k, v)` pins the map's key and value to the
                // pair, and the map's element types come out as tuples.
                _ => {
                    for pat in pats {
                        let elem = self.fresh_unknown();
                        self.bind_pattern_light(pat, &elem, env);
                    }
                }
            },
            _ => {}
        }
    }
}
