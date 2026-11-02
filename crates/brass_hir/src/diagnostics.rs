//! Optional diagnostic ownership, independent of reporting policy. Declaration
//! failures are catalog facts; a body span never erases a diagnostic by itself.

use crate::{ItemId, ItemKind, MethodBodyId, Program, TypeKind};
use brass_parser::{Span, TokenKind};

/// A diagnostic's source owner. The consumer decides whether to report it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DiagnosticOwner {
    /// A declaration, import, unusable parser boundary, or unknown source.
    Catalog,
    /// A function body, including a primitive extension.
    Function(ItemId),
    /// A method source shared by its variant checking contexts.
    Method(Vec<MethodBodyId>),
    /// A statement belonging to a loaded module's initialization sequence.
    Initializer(ItemId),
}

/// Explicit ownership sidecar. Constructing it is optional and never changes the
/// original diagnostic's text, order, span, or storage representation.
pub struct DiagnosticOwners {
    bodies: Vec<BodyExtent>,
    initializers: Vec<(Span, DiagnosticOwner)>,
}

/// Body-local diagnostics can also cite the enclosing signature's full span.
struct BodyExtent {
    body: Span,
    declaration: Span,
    owner: DiagnosticOwner,
}

impl DiagnosticOwners {
    /// Index body extents from the complete catalog, including unreached bodies.
    pub fn new(program: &Program) -> Self {
        let mut this = Self {
            bodies: Vec::new(),
            initializers: Vec::new(),
        };
        for f in program.functions.values() {
            if let Some(id) = program.item_id(&f.module, f.decl.span, ItemKind::Function) {
                this.bodies.push(BodyExtent {
                    body: f.decl.body.span,
                    declaration: f.signature.span,
                    owner: DiagnosticOwner::Function(id),
                });
            }
        }
        for t in program.types.values() {
            let groups = match &t.kind {
                TypeKind::Record { methods, .. } => vec![(None, methods)],
                TypeKind::Sum { variants } => {
                    variants.iter().map(|v| (Some(v.tag), &v.methods)).collect()
                }
            };
            for (variant, methods) in groups {
                for m in methods.values() {
                    if let (Some(body), Some(id)) =
                        (&m.decl.body, program.method_body_id(t, m, variant))
                    {
                        if let Some(BodyExtent {
                            owner: DiagnosticOwner::Method(ids),
                            ..
                        }) = this.bodies.iter_mut().find(|entry| entry.body == body.span)
                        {
                            ids.push(id);
                        } else {
                            this.bodies.push(BodyExtent {
                                body: body.span,
                                declaration: m.signature.span,
                                owner: DiagnosticOwner::Method(vec![id]),
                            });
                        }
                    }
                }
            }
        }
        for init in &program.inits {
            let Some(source) = &init.source else {
                continue;
            };
            let span = Span::new(source.base, source.base);
            let Some(id) = program.item_id(&init.path, span, ItemKind::Initializer) else {
                continue;
            };
            for statement in &init.stmts {
                this.initializers
                    .push((statement.span(), DiagnosticOwner::Initializer(id.clone())));
            }
        }
        this.bodies
            .sort_by_key(|entry| (entry.body.lo, entry.body.hi));
        this
    }

    /// Attribute a body-pass diagnostic. Catalog-pass callers must keep
    /// `Catalog`, even if their error happens to point into a body expression.
    /// A body warning may cite the full signature; its exact span is owned too.
    pub fn body_owner(&self, span: Span) -> DiagnosticOwner {
        self.bodies
            .iter()
            .find(|entry| contains(entry.body, span) || entry.declaration == span)
            .map(|entry| entry.owner.clone())
            .or_else(|| {
                self.initializers
                    .iter()
                    .find(|(body, _)| contains(*body, span))
                    .map(|(_, owner)| owner.clone())
            })
            .unwrap_or(DiagnosticOwner::Catalog)
    }

    /// A recoverable syntax error belongs to a body only when its declaration
    /// and closing delimiter survive, and no swallowed `fun`/`type` boundary is
    /// inside that body. Lexing failure or uncertain boundaries stay catalog
    /// errors. This conservative check is optional; it does not parse a new AST.
    pub fn syntax_owner(&self, span: Span, source: &str, base: usize) -> DiagnosticOwner {
        let Some(BodyExtent { body, owner, .. }) = self
            .bodies
            .iter()
            .find(|entry| entry.body.lo < span.lo && span.hi < entry.body.hi)
        else {
            return DiagnosticOwner::Catalog;
        };
        let Some(text) = body
            .lo
            .checked_sub(base)
            .and_then(|lo| body.hi.checked_sub(base).and_then(|hi| source.get(lo..hi)))
        else {
            return DiagnosticOwner::Catalog;
        };
        let Ok(tokens) = brass_parser::lex(text) else {
            return DiagnosticOwner::Catalog;
        };
        let mut depth = 0usize;
        for token in &tokens {
            match token.kind {
                TokenKind::Fun | TokenKind::Type => return DiagnosticOwner::Catalog,
                TokenKind::LBrace => depth += 1,
                TokenKind::RBrace => {
                    let Some(next) = depth.checked_sub(1) else {
                        return DiagnosticOwner::Catalog;
                    };
                    depth = next;
                }
                _ => {}
            }
        }
        if depth == 0 && text.ends_with('}') {
            owner.clone()
        } else {
            DiagnosticOwner::Catalog
        }
    }
}

fn contains(outer: Span, inner: Span) -> bool {
    outer.lo <= inner.lo && inner.hi <= outer.hi
}
