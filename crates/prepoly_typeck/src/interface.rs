//! Interface enforcement: `type B: A` requires B to provide
//! every field and method of A with compatible types. For a sum type, every
//! variant must satisfy the interface.

use std::collections::HashMap;

use prepoly_hir::{FieldInfo, MethodInfo, Program, TypeKind};

use crate::TypeError;

pub fn check(program: &Program) -> Vec<TypeError> {
    let mut errors = Vec::new();
    for info in program.types.values() {
        for iface_name in &info.interfaces {
            let Some(iface) = program.types.get(iface_name) else {
                errors.push(TypeError {
                    message: format!("unknown interface `{iface_name}`"),
                    span: info.span,
                });
                continue;
            };
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

#[allow(clippy::too_many_arguments)]
fn report(
    who: &str,
    iface: &str,
    fields: &[FieldInfo],
    methods: &HashMap<String, MethodInfo>,
    ifields: &[FieldInfo],
    imethods: &HashMap<String, MethodInfo>,
    program: &Program,
    span: prepoly_lexer::Span,
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
