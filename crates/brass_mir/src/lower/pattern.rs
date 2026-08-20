//! Pattern lowering: the test that decides whether a pattern matches a subject,
//! and the bindings it introduces on success.
//!
//! Tests and bindings are split (mirroring codegen): [`lower_pattern_cond`]
//! produces a boolean operand for a branch, and [`lower_pattern_bind`] runs in
//! the taken arm to bind the pattern's variables. A bare name that names a
//! sum-variant is a unit-variant *test* binding nothing; any other bare name is
//! an irrefutable binding.
//!
//! A nested pattern's refutable sub-patterns (a literal, a unit-variant name, a
//! nested variant/array) are tested too, conjoined with short-circuit control
//! flow: a sub-pattern's field/element is loaded -- and dereferenced -- only after
//! the enclosing test has already matched, so a non-matching value never reads a
//! field at a wrong-variant offset.

use brass_parser::ast::{BinOp, Pattern};

use crate::cfg::{MirStmt, Terminator};
use crate::ids::LocalId;
use crate::lower::FnLower;
use crate::value::{Callee, Literal, Operand, Place, Projection, Rvalue};

impl FnLower<'_, '_> {
    /// A boolean operand that is true when `pat` matches the value in `subj`.
    pub(crate) fn lower_pattern_cond(&mut self, pat: &Pattern, subj: LocalId) -> Operand {
        match pat {
            Pattern::Wildcard(_) => Operand::Const(Literal::Bool(true)),
            Pattern::Binding(name, _) => {
                if self.is_variant_name(name) {
                    self.value_matches(subj, name)
                } else {
                    // A fresh binding always matches.
                    Operand::Const(Literal::Bool(true))
                }
            }
            Pattern::Literal(expr, _) => {
                let lit = self.lower_expr(expr);
                self.b
                    .emit(Rvalue::Bin(BinOp::Eq, Operand::Local(subj), lit))
            }
            Pattern::Record(name, fps, _) => {
                // The variant tag test (constant-true for a plain struct), then each
                // refutable field sub-pattern, guarded so its field is loaded only
                // when the variant already matched.
                let mut cond = self.value_matches(subj, name);
                let variant = self.is_record_variant_name(name).then(|| name.clone());
                for fp in fps {
                    let Some(subpat) = &fp.pat else { continue };
                    if !self.pattern_is_refutable(subpat) {
                        continue;
                    }
                    let field = field_proj_name(&variant, &fp.name);
                    cond = self.and_then_cond(cond, move |s| {
                        let fv = s.b.emit(Rvalue::Load(Place::projected(
                            subj,
                            vec![Projection::Field(field)],
                        )));
                        let fl = s.b.make_local(fv);
                        s.lower_pattern_cond(subpat, fl)
                    });
                }
                cond
            }
            Pattern::Array(pats, _) => {
                let len = self.b.emit(Rvalue::Call(
                    Callee::Builtin("array_len".into()),
                    vec![Operand::Local(subj)],
                ));
                let mut cond = self.b.emit(Rvalue::Bin(
                    BinOp::Eq,
                    len,
                    Operand::Const(Literal::Int(pats.len() as i64)),
                ));
                for (i, p) in pats.iter().enumerate() {
                    if !self.pattern_is_refutable(p) {
                        continue;
                    }
                    cond = self.and_then_cond(cond, move |s| {
                        let elem = s.b.emit(Rvalue::Load(Place::projected(
                            subj,
                            vec![Projection::Index(Operand::Const(Literal::Int(i as i64)))],
                        )));
                        let el = s.b.make_local(elem);
                        s.lower_pattern_cond(p, el)
                    });
                }
                cond
            }
        }
    }

    /// Bind the variables of `pat`, having already established it matches `subj`.
    pub(crate) fn lower_pattern_bind(&mut self, pat: &Pattern, subj: LocalId) {
        match pat {
            Pattern::Wildcard(_) | Pattern::Literal(_, _) => {}
            Pattern::Binding(name, _) => {
                // A variant name binds nothing; any other name binds the subject.
                if !self.is_variant_name(name) {
                    self.bind_value(name, Operand::Local(subj));
                }
            }
            Pattern::Record(name, fps, _) => {
                // A sum-variant pattern (`Variant { field }`) qualifies each field
                // with its variant (`Variant.field`) so the back end resolves the
                // field's type and offset in the matched variant -- several variants
                // may declare a field of the same name with different types. A plain
                // record (struct) pattern uses the bare field name.
                let variant = self.is_record_variant_name(name).then(|| name.clone());
                for fp in fps {
                    let field = field_proj_name(&variant, &fp.name);
                    let fv = self.b.emit(Rvalue::Load(Place::projected(
                        subj,
                        vec![Projection::Field(field)],
                    )));
                    match &fp.pat {
                        Some(sub) => {
                            let sub_local = self.b.make_local(fv);
                            self.lower_pattern_bind(sub, sub_local);
                        }
                        None => self.bind_value(&fp.name, fv),
                    }
                }
            }
            Pattern::Array(pats, _) => {
                for (i, p) in pats.iter().enumerate() {
                    let elem = self.b.emit(Rvalue::Load(Place::projected(
                        subj,
                        vec![Projection::Index(Operand::Const(Literal::Int(i as i64)))],
                    )));
                    let elem = self.b.make_local(elem);
                    self.lower_pattern_bind(p, elem);
                }
            }
        }
    }

    /// Whether `pat` can fail to match (and so needs a runtime test). A wildcard or
    /// a plain binding always matches; a literal, a unit-variant name, or a
    /// variant/array pattern (or a struct pattern with a refutable field) can fail.
    fn pattern_is_refutable(&self, pat: &Pattern) -> bool {
        match pat {
            Pattern::Wildcard(_) => false,
            Pattern::Binding(name, _) => self.is_variant_name(name),
            Pattern::Literal(_, _) | Pattern::Array(_, _) => true,
            Pattern::Record(name, fps, _) => {
                self.is_record_variant_name(name)
                    || fps.iter().any(|fp| {
                        fp.pat
                            .as_ref()
                            .is_some_and(|p| self.pattern_is_refutable(p))
                    })
            }
        }
    }

    /// `acc && f()`, short-circuiting: `f` (which loads and tests a sub-pattern's
    /// field/element) runs only when `acc` already holds, so a non-matching value
    /// never dereferences a field read at the wrong variant's offset.
    fn and_then_cond(&mut self, acc: Operand, f: impl FnOnce(&mut Self) -> Operand) -> Operand {
        let res = self.b.fresh_local(None);
        let then_bb = self.b.new_block();
        let else_bb = self.b.new_block();
        let merge_bb = self.b.new_block();
        self.b.terminate(Terminator::CondBranch {
            cond: acc,
            then: then_bb,
            els: else_bb,
        });

        self.b.switch_to(then_bb);
        let r = f(&mut *self);
        self.b.push(MirStmt::Assign(res, Rvalue::Use(r)));
        self.b.terminate(Terminator::Goto(merge_bb));

        self.b.switch_to(else_bb);
        self.b.push(MirStmt::Assign(
            res,
            Rvalue::Use(Operand::Const(Literal::Bool(false))),
        ));
        self.b.terminate(Terminator::Goto(merge_bb));

        self.b.switch_to(merge_bb);
        Operand::Local(res)
    }

    pub(crate) fn is_variant_name(&self, name: &str) -> bool {
        self.ctx.tables.variant_names.contains(name)
    }

    fn is_record_variant_name(&self, name: &str) -> bool {
        self.ctx.tables.record_variant_names.contains(name)
    }

    fn value_matches(&mut self, subj: LocalId, name: &str) -> Operand {
        self.b.emit(Rvalue::Call(
            Callee::Builtin("value_matches".into()),
            vec![
                Operand::Local(subj),
                Operand::Const(Literal::Str(name.to_string())),
            ],
        ))
    }
}

/// The projection field name for a pattern field: `Variant.field` for a sum-variant
/// pattern (so the back end picks the matched variant's slot), else the bare name.
fn field_proj_name(variant: &Option<String>, fname: &str) -> String {
    match variant {
        Some(v) => format!("{v}.{fname}"),
        None => fname.to_string(),
    }
}
