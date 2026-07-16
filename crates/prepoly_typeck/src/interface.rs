//! Interface enforcement: `type B: A` requires B to provide
//! every field and method of A with compatible types. For a sum type, every
//! variant must satisfy the interface.

use std::collections::HashMap;

use prepoly_hir::{FieldInfo, MethodInfo, Program, TypeKind};

use crate::TypeError;

pub fn check(program: &Program) -> Vec<TypeError> {
    let mut errors = Vec::new();
    for info in program.types.values() {
        // Two interfaces a type implements may declare the same field name with
        // incompatible types. Each parent is otherwise checked independently
        // against the implementer, so this conflict between the parents
        // themselves would go unreported (an unannotated implementing field even
        // bypasses the per-parent invariance check). Detect it directly from the
        // parents' own declarations, before checking each parent.
        check_parent_field_conflicts(
            info.name.as_str(),
            &info.interfaces,
            program,
            info.span,
            &mut errors,
        );
        for iface_name in &info.interfaces {
            let Some(iface) = program.types.get(iface_name) else {
                errors.push(TypeError {
                    message: format!("unknown interface `{iface_name}`"),
                    span: info.span,
                });
                continue;
            };
            // A sum parent (`type MyResult: Result`) declares structural sum
            // subtyping: the child must cover exactly the parent's variant
            // set, and each child variant's record must satisfy the parent
            // variant's (width allowed, annotated fields invariant). The
            // declaration is also the gate for the value coercion (SumView)
            // at flow sites, mirroring records' declared-id gating.
            if let TypeKind::Sum {
                variants: ivariants,
            } = &iface.kind
            {
                let TypeKind::Sum { variants } = &info.kind else {
                    errors.push(TypeError {
                        message: format!(
                            "`{}` is a record and cannot implement the sum interface `{iface_name}`",
                            info.name
                        ),
                        span: info.span,
                    });
                    continue;
                };
                for iv in ivariants {
                    let Some(v) = variants.iter().find(|v| v.name == iv.name) else {
                        errors.push(TypeError {
                            message: format!(
                                "`{}` does not satisfy `{iface_name}`: missing variant `{}`",
                                info.name, iv.name
                            ),
                            span: info.span,
                        });
                        continue;
                    };
                    // Only the FIELDS must conform: a sum subtype is rebuilt
                    // as the parent at every flow site, so the parent's
                    // methods always run on a parent value -- the child never
                    // needs them (unlike record interfaces, whose values flow
                    // by identity).
                    report(
                        &format!("{}.{}", info.name, v.name),
                        iface_name,
                        &v.fields,
                        &v.methods,
                        &iv.fields,
                        &HashMap::new(),
                        program,
                        info.span,
                        true,
                        &mut errors,
                    );
                }
                // An extra variant would build values the parent cannot
                // represent, so the coercion would have no arm for them.
                for v in variants {
                    if !ivariants.iter().any(|iv| iv.name == v.name) {
                        errors.push(TypeError {
                            message: format!(
                                "`{}` does not satisfy `{iface_name}`: variant `{}` does not \
                                 exist in `{iface_name}`",
                                info.name, v.name
                            ),
                            span: info.span,
                        });
                    }
                }
                continue;
            }
            let TypeKind::Record {
                fields: ifields,
                methods: imethods,
            } = &iface.kind
            else {
                errors.push(TypeError {
                    message: format!("interface `{iface_name}` must be a record type"),
                    span: info.span,
                });
                continue;
            };
            match &info.kind {
                TypeKind::Record { fields, methods } => {
                    report(
                        &info.name,
                        iface_name,
                        fields,
                        methods,
                        ifields,
                        imethods,
                        program,
                        info.span,
                        true,
                        &mut errors,
                    );
                }
                TypeKind::Sum { variants } => {
                    for v in variants {
                        let who = format!("{}.{}", info.name, v.name);
                        report(
                            &who,
                            iface_name,
                            &v.fields,
                            &v.methods,
                            ifields,
                            imethods,
                            program,
                            info.span,
                            true,
                            &mut errors,
                        );
                    }
                }
            }
        }
    }
    errors
}

/// Report when two of `interfaces` declare the same field name with mutually
/// incompatible types. Fields are mutable, so a value reaching a type through one
/// parent interface could be written through the other; the two field types must
/// therefore be invariant. Only fields that both parents annotate with a known
/// resolved type can conflict; unannotated or still-unknown fields are skipped.
fn check_parent_field_conflicts(
    who: &str,
    interfaces: &[String],
    program: &Program,
    span: prepoly_parser::Span,
    errors: &mut Vec<TypeError>,
) {
    // field name -> (parent interface name, resolved field type)
    let mut seen: HashMap<&str, (&str, &prepoly_hir::Type)> = HashMap::new();
    for iface_name in interfaces {
        let Some(iface) = program.types.get(iface_name) else {
            continue;
        };
        let TypeKind::Record { fields, .. } = &iface.kind else {
            continue;
        };
        for f in fields {
            let Some(ty) = &f.resolved_ty else { continue };
            if ty.is_unknown() {
                continue;
            }
            match seen.get(f.name.as_str()) {
                Some((prev_iface, prev_ty)) => {
                    if !crate::structural::types_invariant(program, prev_ty, ty) {
                        errors.push(TypeError {
                            message: format!(
                                "`{who}` inherits conflicting types for field `{}`: `{}` requires `{}` but `{}` requires `{}`",
                                f.name,
                                prev_iface,
                                prev_ty.display(),
                                iface_name,
                                ty.display(),
                            ),
                            span,
                        });
                    }
                }
                None => {
                    seen.insert(f.name.as_str(), (iface_name.as_str(), ty));
                }
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn report(
    who: &str,
    iface: &str,
    fields: &[FieldInfo],
    methods: &HashMap<String, MethodInfo>,
    ifields: &[FieldInfo],
    imethods: &HashMap<String, MethodInfo>,
    program: &Program,
    span: prepoly_parser::Span,
    report_missing: bool,
    errors: &mut Vec<TypeError>,
) {
    for ifld in ifields {
        match fields.iter().find(|f| f.name == ifld.name) {
            None if report_missing => errors.push(TypeError {
                message: format!(
                    "`{who}` does not satisfy `{iface}`: missing field `{}`",
                    ifld.name
                ),
                span,
            }),
            None => {}
            Some(have) => {
                if ifld.ty.is_some()
                    && have.ty.is_some()
                    && let (Some(w), Some(g)) = (&ifld.resolved_ty, &have.resolved_ty)
                {
                    // Fields are mutable, so an interface field type must be
                    // matched invariantly: a covariant override would let a
                    // write through the interface install an incompatible
                    // value.
                    if !w.is_unknown()
                        && !g.is_unknown()
                        && !crate::structural::types_invariant(program, g, w)
                    {
                        errors.push(TypeError {
                            message: format!(
                                "`{who}` field `{}` has type `{}` but `{iface}` requires `{}`",
                                ifld.name,
                                g.display(),
                                w.display()
                            ),
                            span,
                        });
                    }
                }
            }
        }
    }
    for (mname, m) in imethods {
        match methods.get(mname) {
            None => errors.push(TypeError {
                message: format!("`{who}` does not satisfy `{iface}`: missing method `{mname}`"),
                span,
            }),
            Some(have) => {
                if have.signature.params.len() != m.signature.params.len() {
                    errors.push(TypeError {
                        message: format!(
                            "`{who}` method `{mname}` has {} parameter(s) but `{iface}` requires {}",
                            have.signature.params.len(),
                            m.signature.params.len()
                        ),
                        span,
                    });
                } else if !crate::structural::signature_satisfies(
                    program,
                    &have.signature,
                    &m.signature,
                ) {
                    errors.push(TypeError {
                        message: format!(
                            "`{who}` method `{mname}` signature is not compatible with `{iface}`"
                        ),
                        span,
                    });
                }
            }
        }
    }
}
