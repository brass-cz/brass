//! Direct effects collected during the selection authority's syntax traversal.
//! Unknown aliasing, structural member reads and closures retain their owner.
//! Local scope unions may add effects but cannot conceal a global dependency.

use super::{Edges, Expr, Stmt};

mod rootless;
use crate::reachability::certificate::closed_layout;

impl Edges<'_, '_> {
    fn site(&self, expr: &Expr, operation: &str) -> String {
        format!("{}:{}:{operation}", self.module.join("/"), expr.span().lo)
    }

    // This matches checker global precedence without resolving a type: defining
    // module, imported definition/rename, then sorted core definitions.
    fn global(&self, name: &str) -> Option<(Vec<String>, String)> {
        let defines = |module: &[String], name: &str| {
            self.index
                .globals
                .get(module)
                .is_some_and(|names| names.contains(name))
        };
        if let Some((alias, member)) = name.split_once('.') {
            let module = self
                .index
                .program
                .module_aliases
                .get(self.module)?
                .get(alias)?;
            return defines(module, member).then(|| (module.clone(), member.into()));
        }
        if defines(self.module, name) {
            return Some((self.module.to_vec(), name.into()));
        }
        if let Some(origin) = self
            .index
            .program
            .import_origins
            .get(self.module)
            .and_then(|m| m.get(name))
        {
            let remote = self
                .index
                .program
                .import_renames
                .get(self.module)
                .and_then(|m| m.get(name))
                .map_or(name, String::as_str);
            if defines(origin, remote) {
                return Some((origin.clone(), remote.into()));
            }
        }
        self.index
            .program
            .inits
            .iter()
            .filter(|init| {
                init.path.first().is_some_and(|s| s == "core") && defines(&init.path, name)
            })
            .map(|init| &init.path)
            .min()
            .map(|module| (module.clone(), name.into()))
    }

    /// Record mutations even in nested blocks visited by the expression walker.
    pub(super) fn statement_effects(&mut self, statement: &Stmt) {
        if !self.summaries {
            return;
        }
        if let Stmt::Assign { target, .. } = statement {
            match target {
                Expr::Ident(name, _) => {
                    if let Some(global) = self.global(name) {
                        self.effects.global_writes.insert(global);
                    } else if !self.locals.contains(name) {
                        let site = self.site(target, "unbound assignment");
                        self.effects.shared_cells.insert(site.clone());
                        self.rootless.shared_cells.insert(site);
                    }
                }
                _ => {
                    self.effects
                        .shared_cells
                        .insert(self.site(target, "member/index assignment"));
                    if let Expr::Field(base, name, _) = target
                        && let Expr::Ident(alias, _) = base.as_ref()
                        && let Some(global) = self.global(&format!("{alias}.{name}"))
                    {
                        self.effects.global_writes.insert(global);
                    }
                }
            }
        }
    }

    /// Collect may-effects; only statically resolved source calls have a summary.
    pub(super) fn expression_effects(&mut self, expr: &Expr) {
        if !self.summaries {
            return;
        }
        if self.globals_only {
            match expr {
                Expr::Ident(name, _) => {
                    if let Some(function) = self.names.function(name) {
                        self.calls
                            .push(self.index.functions[function.symbol.as_str()]);
                    }
                    if let Some(global) = self.global(name) {
                        self.effects.global_reads.insert(global);
                    }
                }
                Expr::Call(callee, _, _) => self.calls.extend(self.exact_call_targets(callee)),
                Expr::Field(base, name, _) => {
                    if let Expr::Ident(alias, _) = base.as_ref()
                        && let Some(global) = self.global(&format!("{alias}.{name}"))
                    {
                        self.effects.global_reads.insert(global);
                    }
                }
                _ => {}
            }
            return;
        }
        self.rootless_expression(expr);
        match expr {
            Expr::Ident(name, _) => {
                // Lazy checking can elaborate a function VALUE to discover its
                // keyed callees. Selection already follows this name edge;
                // its shared effects must follow it too, even without a call.
                if let Some(function) = self.names.function(name) {
                    let key = self.index.functions[function.symbol.as_str()];
                    if !self.calls.contains(&key) {
                        self.calls.push(key);
                    }
                }
                if let Some(global) = self.global(name) {
                    self.effects.global_reads.insert(global);
                } else if !self.locals.contains(name)
                    && !self.callees.contains(&expr.span())
                    && self.names.function(name).is_none()
                    && self.names.nominal(name).is_none()
                    && self.names.variants(name).is_empty()
                    && brass_hir::Type::primitive_class_of_name(name, false).is_none()
                    && !matches!(name.as_str(), "Self" | "infer")
                {
                    self.effects.captures.insert(self.site(expr, name));
                }
            }
            Expr::Call(callee, _, _) => {
                self.callees.insert(callee.span());
                let targets = self.exact_call_targets(callee);
                if targets.is_empty() {
                    let label = match callee.as_ref() {
                        Expr::Ident(name, _) | Expr::Field(_, name, _) => name.as_str(),
                        _ => "dynamic expression",
                    };
                    self.effects.unknown_calls.insert(self.site(expr, label));
                }
                for key in targets {
                    // These same targets are selected by the ordinary visitor.
                    self.edge(key, brass_hir::Reason::ExplicitUse);
                    if !self.calls.contains(&key) {
                        self.calls.push(key);
                    }
                }
            }
            Expr::Field(base, name, _) => {
                if let Expr::Ident(alias, _) = base.as_ref()
                    && let Some(global) = self.global(&format!("{alias}.{name}"))
                {
                    self.effects.global_reads.insert(global);
                }
                if !self.callees.contains(&expr.span()) {
                    // Closed literal/self fields cannot refine a shared layout.
                    let closed = self
                        .receiver(base)
                        .and_then(|id| self.index.program.type_by_id(id))
                        .is_some_and(|owner| {
                            closed_layout(self.index.program, &owner.type_ref())
                                && match &owner.kind {
                                    brass_hir::TypeKind::Record { fields, .. } => {
                                        fields.iter().any(|f| &f.name == name)
                                    }
                                    brass_hir::TypeKind::Sum { variants } => variants
                                        .iter()
                                        .all(|v| v.fields.iter().any(|f| &f.name == name)),
                                }
                        });
                    if !closed {
                        self.effects
                            .shared_cells
                            .insert(self.site(expr, "unproved member read"));
                    }
                }
            }
            Expr::Closure(..) => {
                self.effects
                    .captures
                    .insert(self.site(expr, "closure environment"));
            }
            Expr::Index(..) => {
                self.effects
                    .shared_cells
                    .insert(self.site(expr, "unproved index read"));
            }
            Expr::TypeLit(name, _, _) | Expr::VariantLit(name, _, _, _) => {
                let owner = if name == "Self" {
                    self.owner
                } else {
                    self.names.nominal(name)
                };
                if owner.is_none_or(|t| !closed_layout(self.index.program, &t.type_ref())) {
                    self.effects
                        .shared_cells
                        .insert(self.site(expr, "open construction"));
                }
            }
            Expr::Str(parts, _)
                if parts
                    .iter()
                    .any(|p| matches!(p, brass_parser::ast::StrSeg::Expr(_))) =>
            {
                self.effects
                    .unknown_calls
                    .insert(self.site(expr, "implicit display"));
            }
            _ => {}
        }
    }
}
