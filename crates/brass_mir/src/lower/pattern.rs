//! Pattern lowering: the test that decides whether a pattern matches a subject,
//! and the bindings it introduces on success.
//!
//! Tests and bindings are split: [`lower_pattern_cond`] produces a boolean
//! operand for a branch, and [`lower_pattern_bind`] runs in the taken arm to
//! bind the pattern's variables. A refutable pattern matches only a present
//! value, so on a nullable subject `null` falls through to a later arm. A
//! qualified name, or a bare name that names a unit variant of a sum in scope
//! in this module, is a unit-variant *test* binding nothing; any other bare
//! name is an irrefutable binding. A braced head is a variant pattern when
//! qualified, and otherwise resolves through
//! `brass_hir::Program::braced_pattern_head` -- the same rules the checker
//! applies. A head that is both a record type in scope and a variant is decided
//! per monomorphized instance: a type test on the subject selects the record
//! destructuring for a value of that record and the variant destructuring for
//! anything else.
//!
//! A nested pattern's refutable sub-patterns (a literal, a unit-variant name, a
//! nested variant/array) are tested too, conjoined with short-circuit control
//! flow: a sub-pattern's field/element is loaded -- and dereferenced -- only after
//! the enclosing test has already matched, so a non-matching value never reads a
//! field at a wrong-variant offset.

use brass_hir::{BracedHead, Type};
use brass_parser::ast::{BinOp, FieldPat, Pattern};

use crate::cfg::{MirStmt, Terminator};
use crate::ids::LocalId;
use crate::lower::FnLower;
use crate::value::{Callee, Literal, Operand, Place, Projection, Rvalue};

impl<'p> FnLower<'_, 'p> {
    /// A boolean operand that is true when `pat` matches the value in `subj`.
    pub(crate) fn lower_pattern_cond(&mut self, pat: &Pattern, subj: LocalId) -> Operand {
        match pat {
            Pattern::Wildcard(_) => Operand::Const(Literal::Bool(true)),
            Pattern::Binding(name, qualifier, _) => {
                if qualifier.is_some() || self.is_variant_name(name) {
                    // A unit variant matches only a present value: on a
                    // nullable subject the tag is tested on the narrowed value
                    // after a presence test (folded away for a non-nullable
                    // subject), so `null` falls through to a later arm.
                    let present = self.b.emit(Rvalue::Call(
                        Callee::Builtin("__present".into()),
                        vec![Operand::Local(subj)],
                    ));
                    self.and_then_cond(present, move |s| {
                        let inner = s.b.emit(Rvalue::Call(
                            Callee::Builtin("__nonnull".into()),
                            vec![Operand::Local(subj)],
                        ));
                        let inner = s.b.make_local(inner);
                        s.value_matches(inner, name)
                    })
                } else {
                    // A fresh binding always matches.
                    Operand::Const(Literal::Bool(true))
                }
            }
            // `null` is an identity test on the subject itself.
            Pattern::Literal(expr, _) if matches!(**expr, brass_parser::ast::Expr::Null(_)) => {
                let lit = self.lower_expr(expr);
                self.b
                    .emit(Rvalue::Bin(BinOp::Eq, Operand::Local(subj), lit))
            }
            // A value literal matches only a present value equal to it: on a
            // nullable subject the comparison reads the narrowed value after a
            // presence test, which folds to always-true for a non-nullable
            // subject (`cond_static_truthiness`).
            Pattern::Literal(expr, _) => {
                let present = self.b.emit(Rvalue::Call(
                    Callee::Builtin("__present".into()),
                    vec![Operand::Local(subj)],
                ));
                self.and_then_cond(present, move |s| {
                    let inner = s.b.emit(Rvalue::Call(
                        Callee::Builtin("__nonnull".into()),
                        vec![Operand::Local(subj)],
                    ));
                    let inner = s.b.make_local(inner);
                    let lit = s.lower_expr(expr);
                    s.b.emit(Rvalue::Bin(BinOp::Eq, Operand::Local(inner), lit))
                })
            }
            Pattern::Record(..) | Pattern::Array(..) => {
                // A destructuring pattern matches only a present value: on a
                // nullable subject the structure is tested on the narrowed value
                // after a presence test, which folds to always-true for a
                // non-nullable subject (`cond_static_truthiness`).
                let present = self.b.emit(Rvalue::Call(
                    Callee::Builtin("__present".into()),
                    vec![Operand::Local(subj)],
                ));
                self.and_then_cond(present, move |s| {
                    let inner = s.b.emit(Rvalue::Call(
                        Callee::Builtin("__nonnull".into()),
                        vec![Operand::Local(subj)],
                    ));
                    let inner = s.b.make_local(inner);
                    s.lower_structure_cond(pat, inner)
                })
            }
        }
    }

    /// The structural test of a record/variant or array pattern against a
    /// present (non-null) `subj`.
    fn lower_structure_cond(&mut self, pat: &Pattern, subj: LocalId) -> Operand {
        match pat {
            Pattern::Record(name, qualifier, fps, _) => {
                match self.braced_head(name, qualifier.is_some()) {
                    BracedHead::Record => self.lower_braced_cond(subj, name, fps, false),
                    BracedHead::Variant => self.lower_braced_cond(subj, name, fps, true),
                    BracedHead::RecordOrVariant(record) => {
                        let is_record = self.record_type_test(subj, record);
                        self.select_cond(
                            is_record,
                            |s| s.lower_braced_cond(subj, name, fps, false),
                            |s| s.lower_braced_cond(subj, name, fps, true),
                        )
                    }
                }
            }
            Pattern::Array(pats, _) => {
                let len = self.b.emit(Rvalue::Call(
                    Callee::Builtin("array_len".into()),
                    vec![Operand::Local(subj)],
                ));
                let mut cond = self.b.emit(Rvalue::Bin(
                    BinOp::Eq,
                    len,
                    Operand::Const(Literal::Int(pats.len() as i128)),
                ));
                for (i, p) in pats.iter().enumerate() {
                    if !self.pattern_is_refutable(p) {
                        continue;
                    }
                    cond = self.and_then_cond(cond, move |s| {
                        let elem = s.b.emit(Rvalue::Load(Place::projected(
                            subj,
                            vec![Projection::Index(Operand::Const(Literal::Int(i as i128)))],
                        )));
                        let el = s.b.make_local(elem);
                        s.lower_pattern_cond(p, el)
                    });
                }
                cond
            }
            _ => self.lower_pattern_cond(pat, subj),
        }
    }

    /// Bind the variables of `pat`, having already established it matches `subj`.
    pub(crate) fn lower_pattern_bind(&mut self, pat: &Pattern, subj: LocalId) {
        match pat {
            Pattern::Wildcard(_) | Pattern::Literal(_, _) => {}
            Pattern::Binding(name, qualifier, _) => {
                // A variant name binds nothing; any other name binds the subject.
                if qualifier.is_none() && !self.is_variant_name(name) {
                    self.bind_value(name, Operand::Local(subj));
                }
            }
            Pattern::Record(name, qualifier, fps, _) => {
                match self.braced_head(name, qualifier.is_some()) {
                    BracedHead::Record => self.lower_braced_bind(subj, name, fps, false),
                    BracedHead::Variant => self.lower_braced_bind(subj, name, fps, true),
                    BracedHead::RecordOrVariant(record) => {
                        let is_record = self.record_type_test(subj, record);
                        self.select_bind(
                            pat,
                            is_record,
                            |s| s.lower_braced_bind(subj, name, fps, false),
                            |s| s.lower_braced_bind(subj, name, fps, true),
                        );
                    }
                }
            }
            Pattern::Array(pats, _) => {
                for (i, p) in pats.iter().enumerate() {
                    let elem = self.b.emit(Rvalue::Load(Place::projected(
                        subj,
                        vec![Projection::Index(Operand::Const(Literal::Int(i as i128)))],
                    )));
                    let elem = self.b.make_local(elem);
                    self.lower_pattern_bind(p, elem);
                }
            }
        }
    }

    /// Whether `pat` can fail to match (and so needs a runtime test). A wildcard or
    /// a plain binding always matches; a literal, a unit-variant name, or a
    /// record/variant/array pattern can fail. A plain struct pattern counts too:
    /// lowering is type-independent and the field it destructures may be
    /// nullable, so its presence is tested (the test folds away per instance
    /// when the field is not nullable).
    fn pattern_is_refutable(&self, pat: &Pattern) -> bool {
        match pat {
            Pattern::Wildcard(_) => false,
            Pattern::Binding(name, qualifier, _) => {
                qualifier.is_some() || self.is_variant_name(name)
            }
            Pattern::Literal(_, _) | Pattern::Array(_, _) | Pattern::Record(..) => true,
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

    fn pattern_scope(&self) -> &brass_hir::PatternScope<'p> {
        self.patterns
            .get_or_init(|| self.ctx.program.pattern_scope(&self.module))
    }

    /// Whether an UNQUALIFIED bare-name pattern `name` is a unit-variant test
    /// in this module (a unit variant of a sum in scope) rather than a binding.
    pub(crate) fn is_variant_name(&self, name: &str) -> bool {
        self.pattern_scope().is_unit_variant(name)
    }

    /// How a braced pattern head `name { .. }` destructures in this module: a
    /// qualified head is always a variant, any other resolves through
    /// [`brass_hir::Program::braced_pattern_head`].
    fn braced_head(&self, name: &str, qualified: bool) -> BracedHead<'p> {
        if qualified {
            return BracedHead::Variant;
        }
        self.pattern_scope().braced_head(name)
    }

    /// A per-instance type test: whether the value in `subj` is an instance of
    /// `record`. The test looks through a nullable subject (bindings run on
    /// the matched, possibly still nullable-typed subject; `__nonnull` is the
    /// identity otherwise) and folds statically once the subject's type is
    /// known.
    fn record_type_test(&mut self, subj: LocalId, record: &brass_hir::TypeInfo) -> Operand {
        let value = self.b.emit(Rvalue::Call(
            Callee::Builtin("__nonnull".into()),
            vec![Operand::Local(subj)],
        ));
        let pattern = Type::Record(brass_hir::NominalType::new(record.id, record.name.clone()));
        self.b
            .emit_known(Rvalue::TypeTest(value, pattern), Type::Bool)
    }

    /// The structural test of a braced pattern: the variant tag test
    /// (constant-true for a plain record), then each refutable field
    /// sub-pattern, guarded so its field is loaded only when the variant
    /// already matched.
    fn lower_braced_cond(
        &mut self,
        subj: LocalId,
        name: &str,
        fps: &[FieldPat],
        variant: bool,
    ) -> Operand {
        let mut cond = self.value_matches(subj, name);
        let variant = variant.then(|| name.to_string());
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

    /// Bind a braced pattern's fields. A sum-variant pattern (`Variant {
    /// field }`) qualifies each field with its variant (`Variant.field`) so
    /// the back end resolves the field's type and offset in the matched
    /// variant -- several variants may declare a field of the same name with
    /// different types. A plain record pattern uses the bare field name.
    fn lower_braced_bind(&mut self, subj: LocalId, name: &str, fps: &[FieldPat], variant: bool) {
        let variant = variant.then(|| name.to_string());
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

    /// `if cond { then() } else { els() }` as a boolean operand.
    fn select_cond(
        &mut self,
        cond: Operand,
        then: impl FnOnce(&mut Self) -> Operand,
        els: impl FnOnce(&mut Self) -> Operand,
    ) -> Operand {
        let res = self.b.fresh_local(None);
        let then_bb = self.b.new_block();
        let else_bb = self.b.new_block();
        let merge_bb = self.b.new_block();
        self.b.terminate(Terminator::CondBranch {
            cond,
            then: then_bb,
            els: else_bb,
        });
        for (bb, arm) in [
            (
                then_bb,
                Box::new(then) as Box<dyn FnOnce(&mut Self) -> Operand>,
            ),
            (else_bb, Box::new(els)),
        ] {
            self.b.switch_to(bb);
            let r = arm(self);
            self.b.push(MirStmt::Assign(res, Rvalue::Use(r)));
            self.b.terminate(Terminator::Goto(merge_bb));
        }
        self.b.switch_to(merge_bb);
        Operand::Local(res)
    }

    /// Bind `pat`'s names on whichever of two destructurings `cond` selects.
    /// Each arm binds in a scope of its own and copies its bindings into
    /// shared locals, which are then bound in the enclosing scope, so the code
    /// after the pattern sees one set of names whichever arm ran.
    fn select_bind(
        &mut self,
        pat: &Pattern,
        cond: Operand,
        then: impl FnOnce(&mut Self),
        els: impl FnOnce(&mut Self),
    ) {
        let names: Vec<String> = pat
            .bound_names()
            .into_iter()
            .filter(|n| !self.is_variant_name(n))
            .map(str::to_string)
            .collect();
        let shared: Vec<LocalId> = names
            .iter()
            .map(|n| self.b.fresh_local(Some(n.clone())))
            .collect();
        let then_bb = self.b.new_block();
        let else_bb = self.b.new_block();
        let merge_bb = self.b.new_block();
        self.b.terminate(Terminator::CondBranch {
            cond,
            then: then_bb,
            els: else_bb,
        });
        for (bb, arm) in [
            (then_bb, Box::new(then) as Box<dyn FnOnce(&mut Self)>),
            (else_bb, Box::new(els)),
        ] {
            self.b.switch_to(bb);
            self.push_scope();
            arm(self);
            for (name, local) in names.iter().zip(&shared) {
                if self.lookup(name).is_some() {
                    let value = self.lower_ident(name);
                    self.b.push(MirStmt::Assign(*local, Rvalue::Use(value)));
                }
            }
            self.pop_scope();
            self.b.terminate(Terminator::Goto(merge_bb));
        }
        self.b.switch_to(merge_bb);
        for (name, local) in names.iter().zip(shared) {
            self.bind_value(name, Operand::Local(local));
        }
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
