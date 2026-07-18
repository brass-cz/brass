//! Resolution of source type annotations to checker types: named
//! types and aliases, composite type expressions, and refinement
//! annotations over a base nominal type.

use super::*;

impl<'a> Checker<'a> {
    pub(super) fn resolve_type(&mut self, te: &TypeExpr) -> Result<Type, String> {
        match te {
            TypeExpr::Named(name, _) => self.resolve_named(name),
            TypeExpr::Array(inner, Some(n), _) => {
                Ok(Type::Array(Box::new(self.resolve_type(inner)?), *n))
            }
            TypeExpr::Array(inner, None, _) => Ok(Type::Slice(Box::new(self.resolve_type(inner)?))),
            TypeExpr::Fun(params, ret, _) => {
                let mut ps = Vec::with_capacity(params.len());
                for p in params {
                    ps.push(self.resolve_type(p)?);
                }
                Ok(Type::Fun(ps, Box::new(self.resolve_type(ret)?)))
            }
            TypeExpr::Nullable(inner, _) => Ok(Type::Nullable(Box::new(self.resolve_type(inner)?))),
            // `T!` is the fallible `Result` in scope (a shadowing declaration
            // included); the error payload is a fresh unknown so it is inferred
            // from the body's error sites (like `infer`), unless the scope's
            // Result pins it.
            TypeExpr::Fallible(inner, span) => {
                let ok = self.resolve_type(inner)?;
                let err = self.fresh_unknown();
                Ok(self.scoped_result(ok, err, *span))
            }
            TypeExpr::Tuple(elems, _) => {
                let mut ts = Vec::with_capacity(elems.len());
                for e in elems {
                    ts.push(self.resolve_type(e)?);
                }
                Ok(Type::Tuple(ts))
            }
            TypeExpr::Anonymous(fields, _) => {
                let mut resolved = Vec::with_capacity(fields.len());
                for (name, fty) in fields {
                    resolved.push((name.clone(), self.resolve_type(fty)?));
                }
                Ok(brass_hir::structural_record(resolved))
            }
            TypeExpr::Mut(inner, _) => Ok(Type::Mut(Box::new(self.resolve_type(inner)?))),
            TypeExpr::Ref(inner, _) => Ok(Type::Ref(Box::new(self.resolve_type(inner)?))),
            // `typeof(v)` outside a value-scope context (e.g. a signature) has no
            // binding to tie to; it becomes a fresh inference variable. Inside a
            // local `let` it is instead resolved against the binding's scope by
            // `resolve_annotation_scoped`, which ties it to v's type.
            TypeExpr::TypeOf(..) => Ok(self.fresh_unknown()),
            // `Base { field: T, .. }` refinement (also the target of a
            // `type Alias = Base { .. }`): pin the named slots/fields of the base
            // record and instantiate.
            TypeExpr::Refine(base, entries, _) => self.resolve_refine_annotation(base, entries),
            // A `type` slot is a declaration-only marker; it is not a value type.
            TypeExpr::TypeSlot(_) => {
                Err("`type` is only valid as a record field's declared type".into())
            }
            // `Self.field` names a field's type; it is meaningful only inside a
            // type declaration, resolved during lowering, not in a value position.
            TypeExpr::SelfField(field, _) => Err(format!(
                "`Self.{field}` is only valid inside a type declaration"
            )),
        }
    }

    /// Resolve an inline refinement `Base { field: T, .. }` to a concrete record
    /// instance: pin each named slot/field and substitute into the base's
    /// declared field types. Mirrors the resolution `type Alias = Base { .. }`
    /// gets during lowering, so an inline annotation and an alias agree.
    fn resolve_refine_annotation(
        &mut self,
        base: &TypeExpr,
        entries: &[(String, TypeExpr)],
    ) -> Result<Type, String> {
        let TypeExpr::Named(bname, _) = base else {
            return Err("a refinement base must be a named record type".into());
        };
        let info = self
            .program
            .resolve_type(&self.current_module, bname)
            .ok_or_else(|| format!("unknown type `{bname}` in refinement"))?;
        let TypeKind::Record { fields, .. } = &info.kind else {
            return Err(format!(
                "`{bname}` is not a record type and cannot be refined"
            ));
        };
        let (id, name) = (info.id, info.name.clone());
        let slots = info.slots.clone();
        let base_fields: Vec<(String, Option<Type>)> = fields
            .iter()
            .map(|f| (f.name.clone(), f.resolved_ty.clone()))
            .collect();
        // Pin each entry to a resolved type: a slot variable, or a field override.
        let mut slot_pins: std::collections::BTreeMap<u32, Type> =
            std::collections::BTreeMap::new();
        let mut field_pins: fxhash::FxHashMap<String, Type> = fxhash::FxHashMap::default();
        for (fname, fte) in entries {
            let t = self.resolve_type(fte)?;
            if let Some((_, v)) = slots.iter().find(|(n, _)| n == fname) {
                slot_pins.insert(*v, t);
            } else if let Some((_, declared)) = base_fields.iter().find(|(n, _)| n == fname) {
                // A concrete base field may only be pinned to the same type.
                if let Some(d) = declared
                    && brass_hir::is_fully_known(d)
                    && brass_hir::is_fully_known(&t)
                    && *d != t
                {
                    return Err(format!(
                        "refining field `{fname}` of `{name}`: its type is `{}`, not `{}`",
                        d.display(),
                        t.display()
                    ));
                }
                field_pins.insert(fname.clone(), t);
            } else {
                return Err(format!("`{name}` has no field or slot `{fname}` to refine"));
            }
        }
        // Every slot variable maps to its pin, or a fresh unknown when omitted.
        let slot_map: std::collections::BTreeMap<u32, Type> = slots
            .iter()
            .map(|(_, v)| {
                (
                    *v,
                    slot_pins
                        .get(v)
                        .cloned()
                        .unwrap_or_else(|| self.fresh_unknown()),
                )
            })
            .collect();
        let mut subst = Substitution::empty();
        for (fname, declared) in base_fields {
            let ty = if let Some(t) = field_pins.get(&fname) {
                t.clone()
            } else if let Some(d) = declared {
                brass_hir::substitute_vars(&d, &slot_map)
            } else {
                self.fresh_unknown()
            };
            subst.insert(fname, ty);
        }
        Ok(Type::Record(NominalType::with_substitution(
            id, name, subst,
        )))
    }

    fn resolve_named(&mut self, name: &str) -> Result<Type, String> {
        if let Some(k) = IntKind::from_name(name) {
            return Ok(Type::Int(k));
        }
        match name {
            "bool" => Ok(Type::Bool),
            "float32" => Ok(Type::Float(FloatKind::F32)),
            "float64" => Ok(Type::Float(FloatKind::F64)),
            "string" => Ok(Type::Str),
            "void" => Ok(Type::Void),
            // `infer` is an unknown filled in by inference (for `infer[]` etc.).
            "infer" => Ok(self.fresh_unknown()),
            "Self" => self
                .self_type
                .as_ref()
                .map(|s| self.type_by_name(s))
                .unwrap_or(Type::SelfType)
                .pipe(Ok),
            _ => {
                // A `type Alias = ..` name expands to its pre-resolved target
                // (an `infer` slot the alias left open is freshened per use).
                if let Some(t) = self.resolve_alias(name) {
                    return Ok(t);
                }
                self.resolve_type_ref(name)
                    .ok_or_else(|| format!("unknown type `{name}`"))
            }
        }
    }

    /// The target type of a `type Alias = ..` declaration named `name`, as seen
    /// from the current module, with any `infer` slot freshened so distinct uses
    /// do not share a variable.
    fn resolve_alias(&mut self, name: &str) -> Option<Type> {
        let alias = brass_hir::resolve_qualified(
            &self.program.type_aliases,
            &self.program.import_origins,
            &self.program.import_renames,
            &self.current_module,
            name,
        )?;
        let ty = alias.ty.clone();
        Some(brass_hir::freshen_infer(ty, &mut || self.fresh_unknown()))
    }

    pub(super) fn type_by_name(&self, name: &str) -> Type {
        self.resolve_type_ref(name)
            .unwrap_or_else(|| Type::Record(NominalType::new(-1, name)))
    }

    /// The `Result` the fallibility sugar (`T!`, `error(..)`, an inferred
    /// fallible return) builds in the current scope: the prelude's Result or
    /// the module's shadowing `type Result` sum, with `ok`/`err` pinned into
    /// the payload slots (a shadow's declared payload annotation wins). A
    /// shadow that does not have the required shape -- or a `type Result = ..`
    /// alias, which cannot carry the sugar's identity -- is reported once and
    /// falls back to the built-in Result so checking continues.
    pub(super) fn scoped_result(&mut self, ok: Type, err: Type, span: brass_parser::Span) -> Type {
        // Sites with no real source position (inferred-return assembly) leave
        // reporting to a positioned site (`T!`, `error(..)`), which the same
        // body necessarily contains; they still fall back consistently.
        let report = span != brass_parser::Span::new(0, 0);
        // An alias named `Result` would make a written `Result` annotation and
        // the sugar disagree (the sugar needs a nominal named Result); reject
        // it explicitly instead of silently ignoring the alias.
        if self.resolve_alias(brass_hir::RESULT_TYPE_NAME).is_some() {
            if report && self.reported_result_shadow.insert(i32::MIN) {
                self.errors.push(TypeError {
                    message: "a `type Result = ..` alias cannot shadow the fallibility sugar's \
                              `Result`; declare a sum type named `Result` (or name the aliased \
                              type explicitly)"
                        .to_string(),
                    span,
                });
            }
            return Type::result(ok, err);
        }
        match self
            .program
            .scoped_result_instance(&self.current_module, &ok, &err)
        {
            Ok(t) => {
                // A shadow's declared payload pin and the annotation's payload
                // must agree; the pin wins, so a silent drop would mistype the
                // body. Report the conflict at the annotation.
                if let Some((got_ok, got_err)) = self.resolve(&t).result_payloads() {
                    for (got, want, slot) in [(got_ok, &ok, "success"), (got_err, &err, "error")] {
                        if brass_hir::is_fully_known(got)
                            && brass_hir::is_fully_known(want)
                            && got != want
                        {
                            self.errors.push(TypeError {
                                message: format!(
                                    "the `Result` in scope pins its {slot} payload to `{}`, \
                                     but this annotation says `{}`",
                                    got.display(),
                                    want.display()
                                ),
                                span,
                            });
                        }
                    }
                }
                t
            }
            Err(message) => {
                let id = self
                    .program
                    .resolve_type(&self.current_module, brass_hir::RESULT_TYPE_NAME)
                    .map(|info| info.id)
                    .unwrap_or(i32::MIN);
                if report && self.reported_result_shadow.insert(id) {
                    self.errors.push(TypeError { message, span });
                }
                Type::result(ok, err)
            }
        }
    }
}
