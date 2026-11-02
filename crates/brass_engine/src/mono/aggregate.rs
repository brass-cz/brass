//! Typing aggregate values: the concrete record, sum, array, or tuple type
//! a construction produces, and the type of a field read from a record or
//! sum instance.

use super::*;

impl Monomorphizer<'_, '_> {
    /// The concrete record type produced by constructing `ty { fields }`: the
    /// nominal type with a substitution mapping each declared field to its value's
    /// type.
    pub(super) fn record_type(
        &self,
        module: &[String],
        ty: &str,
        fields: &[(String, Operand)],
        local_types: &[Option<Type>],
    ) -> Result<Option<Type>, String> {
        // An anonymous structure literal `{ f: v, ... }` (empty type name) is a
        // structural record: its field types come straight from the field values.
        if ty.is_empty() {
            let mut out = Vec::with_capacity(fields.len());
            for (name, op) in fields {
                match self.operand_type(op, local_types)? {
                    Some(t) => out.push((name.clone(), t)),
                    None => return Ok(None),
                }
            }
            return Ok(Some(brass_hir::structural_record(out)));
        }
        let info = self
            .program
            .resolve_type(module, ty)
            .or_else(|| self.program.types.get(ty))
            .ok_or_else(|| format!("internal error: unknown type `{ty}`"))?;
        let TypeKind::Record { fields: decl, .. } = &info.kind else {
            return Err(format!("internal error: `{ty}` is not a record type"));
        };
        let mut subst = Substitution::empty();
        for fdecl in decl {
            let value = fields
                .iter()
                .find(|(n, _)| *n == fdecl.name)
                .ok_or_else(|| {
                    format!("internal error: missing field `{}` of `{ty}`", fdecl.name)
                })?;
            let t = match self.operand_type(&value.1, local_types)? {
                // A declared numeric field fixes its stored representation,
                // even when an unseeded literal has its default width. The
                // construction coerces the operand at the field store, so its
                // type describes that destination rather than the raw operand.
                Some(Type::Int(_) | Type::Float(_))
                    if let Some(declared @ (Type::Int(_) | Type::Float(_))) =
                        &fdecl.resolved_ty =>
                {
                    declared.clone()
                }
                // A declared-nullable field keeps its declared type whatever
                // initializes it: a `null` carries the bare `Nullable(Never)` and
                // coerces to it, and a NON-null value is wrapped into the
                // nullable cell at the store -- recording the raw value type
                // (`Node { next: head }` recording `next=Node`) would make every
                // reader reinterpret the cell as the bare value and crash.
                // Essential for self-referential records. A declared type that
                // is not fully concrete (an `infer?` slot) still takes its type
                // from the constructed value.
                Some(got)
                    if matches!(&fdecl.resolved_ty,
                        Some(decl @ Type::Nullable(_)) if brass_hir::is_fully_known(decl))
                        && !matches!(&got,
                            Type::Nullable(inner) if !matches!(**inner, Type::Never)) =>
                {
                    fdecl.resolved_ty.clone().unwrap()
                }
                Some(t) => t,
                None => return Ok(None),
            };
            subst.insert(fdecl.name.clone(), t);
        }
        Ok(Some(Type::Record(NominalType::with_substitution(
            info.id,
            info.name.clone(),
            subst,
        ))))
    }

    /// The concrete sum type produced by constructing `ty.variant { fields }`. An
    /// annotated variant field's layout comes from the HIR, so only this variant's
    /// *unannotated* (dynamic) fields are recorded in the substitution -- keyed
    /// `Variant.field` -- with their constructed value's type, so a later match
    /// reads the field at its real type (mirrors `record_type` for records, and the
    /// front end's `check_lit_fields`).
    pub(super) fn variant_type(
        &self,
        module: &[String],
        ty: &str,
        variant: &str,
        fields: &[(String, Operand)],
        local_types: &[Option<Type>],
    ) -> Result<Option<Type>, String> {
        let info = self
            .program
            .resolve_type_or_alias(module, ty)
            .or_else(|| self.program.types.get(ty))
            .ok_or_else(|| format!("internal error: unknown type `{ty}`"))?;
        let TypeKind::Sum { variants } = &info.kind else {
            return Err(format!("internal error: `{ty}` is not a sum type"));
        };
        let v = variants
            .iter()
            .find(|v| v.name == variant)
            .ok_or_else(|| format!("internal error: `{ty}` has no variant `{variant}`"))?;
        // Every variant field must be layoutable by the typed back end (a sized
        // scalar, a heap pointer, or an opaque unaccessed slot).
        for var in variants {
            for fld in &var.fields {
                if !variant_field_layoutable(self.program, &fld.resolved_ty) {
                    return Err(format!(
                        "internal error: variant field `{}.{}` has no concrete typed layout",
                        var.name, fld.name
                    ));
                }
            }
        }
        let mut subst = Substitution::empty();
        for fld in &v.fields {
            if fld.resolved_ty.as_ref().is_none_or(|t| t.is_unknown())
                && let Some((_, op)) = fields.iter().find(|(n, _)| n == &fld.name)
            {
                match self.operand_type(op, local_types)? {
                    Some(t) => subst.insert(format!("{variant}.{}", fld.name), t),
                    None => return Ok(None),
                }
            }
        }
        Ok(Some(Type::Sum(NominalType::with_substitution(
            info.id,
            info.name.clone(),
            subst,
        ))))
    }

    /// The concrete slice type of an array literal: a slice of the (uniform)
    /// element type. An empty literal cannot be typed on the typed backend.
    pub(super) fn array_type(
        &self,
        es: &[Operand],
        cur_sym: &str,
        local_types: &[Option<Type>],
    ) -> Result<Option<Type>, String> {
        if es.is_empty() {
            return Err(format!(
                "the element type of an empty array literal in expression position is unknown: \
                 bind it first with an annotated `let` (e.g. `let x: T[] = []`) (in `{cur_sym}`)"
            ));
        }
        let mut tys = Vec::with_capacity(es.len());
        for e in es {
            match self.operand_type(e, local_types)? {
                Some(t) => tys.push(t),
                None => return Ok(None),
            }
        }
        // A bracket literal whose elements all share a type is an array; one with
        // differing element types is a fixed-length tuple (matches the type
        // checker's classification of `[1, "s"]`). Instances of one nominal
        // declaration that differ only in refinement share a type, exactly as
        // the checker unifies them (`[Opt.Nothing, Opt.Some { v: 1 }]`).
        let (first, rest) = tys.split_first().expect("non-empty literal");
        if let Some(elem) = rest
            .iter()
            .try_fold(first.clone(), |acc, t| join_refinements(&acc, t))
        {
            return Ok(Some(Type::Slice(Box::new(elem))));
        }
        // Numbers of different types share their value join, the checker's
        // rule (`brass_typesys::numeric_element_join`): `[big, 1]` with
        // `big: int64` is an `int64` sequence, not a tuple.
        let operands: Vec<brass_typesys::JoinOperand> = es
            .iter()
            .zip(&tys)
            .filter(|(_, t)| !t.is_null())
            .map(|(e, t)| brass_typesys::JoinOperand {
                ty: t.clone(),
                literal: match e {
                    Operand::Const(Literal::Int(v)) => Some(brass_typesys::NumericLiteral::Int(*v)),
                    Operand::Const(Literal::Float(v)) => {
                        Some(brass_typesys::NumericLiteral::Float(*v))
                    }
                    _ => None,
                },
            })
            .collect();
        match brass_typesys::numeric_element_join(self.program, &operands) {
            Some(joined) => {
                let elem = if tys.iter().any(Type::is_null) && !matches!(joined, Type::Nullable(_))
                {
                    Type::Nullable(Box::new(joined))
                } else {
                    joined
                };
                Ok(Some(Type::Slice(Box::new(elem))))
            }
            None => Ok(Some(Type::Tuple(tys))),
        }
    }

    /// The concrete type of field `field` of sum type `n`: a generic `Result`
    /// reads it from the nominal substitution (keyed `Variant.field`); an
    /// annotated sum reads the declared type in whichever variant defines it.
    pub(super) fn sum_field_type(
        &self,
        n: &NominalType,
        field: &str,
    ) -> Result<Option<Type>, String> {
        let info = self
            .program
            .type_by_id(n.id)
            .ok_or_else(|| format!("internal error: unknown sum type id {}", n.id))?;
        let TypeKind::Sum { variants } = &info.kind else {
            return Err(format!("internal error: type id {} is not a sum", n.id));
        };
        // A variant-qualified field (`Variant.field`, from a variant pattern
        // binding) resolves in that variant; a bare name resolves in the first
        // variant that declares it (a field common to every variant).
        let (want_variant, fname) = match field.split_once('.') {
            Some((v, f)) => (Some(v), f),
            None => (None, field),
        };
        for v in variants {
            if want_variant.is_some_and(|w| w != v.name) {
                continue;
            }
            if v.fields.iter().any(|f| f.name == fname) {
                if let Some(t) = n.substitution.get(&format!("{}.{fname}", v.name)) {
                    return Ok(Some(resolve_nominal(self.program, t)));
                }
                let fld = v.fields.iter().find(|f| f.name == fname).unwrap();
                return Ok(fld
                    .resolved_ty
                    .clone()
                    .map(|t| resolve_nominal(self.program, &t)));
            }
        }
        Err(format!(
            "internal error: sum `{}` has no field `{field}`",
            info.name
        ))
    }

    /// A record field's concrete type. A constructed/generic record carries it in
    /// the nominal substitution; a bare reference (a declared nominal field type,
    /// e.g. a sum variant's `center: Point` once bound) falls back to the field's
    /// declared type in the HIR, so reading a nested record field still resolves.
    pub(super) fn record_field_type(
        &self,
        n: &NominalType,
        field: &str,
    ) -> Result<Option<Type>, String> {
        if let Some(t) = n.substitution.get(field) {
            return Ok(Some(resolve_nominal(self.program, t)));
        }
        // A declared record contributes its field's declared type (or `None` --
        // deferred -- for a present-but-unannotated field); a structural record (no
        // declaration, e.g. an anonymous structure) has only its substitution fields.
        if let Some(info) = self.program.type_by_id(n.id)
            && let TypeKind::Record { fields, .. } = &info.kind
            && let Some(f) = fields.iter().find(|f| f.name == field)
        {
            return Ok(f
                .resolved_ty
                .clone()
                .map(|t| resolve_nominal(self.program, &t)));
        }
        // Accessing a field the structure does not have reads as null (matches the
        // type checker, which types such an access nullable).
        Ok(Some(Type::null()))
    }
}
