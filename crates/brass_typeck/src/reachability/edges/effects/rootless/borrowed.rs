//! A nominal type-test view can expose declaration cells without a constructor.
//! Merely inspecting its type name cannot constrain those cells; any value use
//! in the narrowed arm stays conservative, including calls and returned aliases.

use super::{Edges, Expr};
use crate::reachability::{certificate::borrows_layout, layout};
use crate::walk::{self, ExprVisitor};
use brass_parser::ast::{Block, Pattern, TypeExpr};

struct Tests<'a>(Vec<(&'a str, &'a TypeExpr, bool)>);

// The borrowed syntax is collected explicitly instead of escaping references
// from ExprVisitor's short-lived callback.
fn tests<'a>(expr: &'a Expr, out: &mut Tests<'a>, uncertain: bool) {
    match expr {
        Expr::TypeTest(value, ty, negated, _) => {
            if let Expr::Ident(name, _) = value.as_ref() {
                out.0.push((name, ty, uncertain || *negated));
            }
        }
        Expr::Binary(_, a, b, _) => {
            tests(a, out, uncertain);
            tests(b, out, uncertain);
        }
        Expr::Unary(_, value, _) => tests(value, out, true),
        _ => {}
    }
}

fn uses_value(block: &Block, name: &str) -> bool {
    struct Uses<'a> {
        name: &'a str,
        used: bool,
        type_names: Vec<brass_parser::Span>,
    }
    impl ExprVisitor for Uses<'_> {
        fn visit(&mut self, expr: &Expr) {
            if let Expr::Call(callee, args, _) = expr
                && matches!(callee.as_ref(), Expr::Ident(name, _) if name == "typeof")
            {
                self.type_names.extend(args.iter().filter_map(|arg| {
                    matches!(&arg.expr, Expr::Ident(name, _) if name == self.name)
                        .then_some(arg.expr.span())
                }));
            }
            if matches!(expr, Expr::Ident(name, _) if name == self.name)
                && !self.type_names.contains(&expr.span())
            {
                self.used = true;
            }
        }
    }
    let mut uses = Uses {
        name,
        used: false,
        type_names: Vec::new(),
    };
    walk::walk_block(block, &mut uses);
    uses.used
}

impl Edges<'_, '_> {
    fn fixed_result(&self, expr: &Expr) -> bool {
        let Expr::Call(callee, _, _) = expr else {
            return false;
        };
        match callee.as_ref() {
            Expr::Ident(name, _)
                if !self.locals.contains(name) && self.names.function(name).is_none() =>
            {
                brass_hir::builtin_returns::builtin_return(name, || false)
                    .is_some_and(|ty| ty.result_payloads().is_some())
            }
            Expr::Field(base, name, _) => self.qualifier_class(base).is_some_and(|class| {
                // Integer from/parse and floating parse have fixed scalar/str
                // Result payloads. Other conversions do not promise a Result.
                !self
                    .index
                    .program
                    .primitive_methods
                    .contains_key(&(class.into(), name.clone()))
                    && ((brass_hir::IntKind::from_name(class).is_some()
                        && matches!(name.as_str(), "from" | "parse"))
                        || (matches!(class, "float32" | "float64") && name == "parse"))
            }),
            _ => false,
        }
    }

    /// Keep a borrowed nominal view when its narrowed value can affect solving.
    pub(super) fn borrowed_pattern_effect(&mut self, expr: &Expr) {
        // Fixed builtin Result payloads are instance cells. An arbitrary call
        // may still return an open subject; it must keep the match barrier.
        if let Expr::Match(subject, arms, _) = expr
            && !matches!(subject.as_ref(), Expr::SelfExpr(_))
            && !self.fixed_result(subject)
        {
            for arm in arms {
                let owners = match &arm.pattern {
                    Pattern::Binding(_, Some(owner), _) | Pattern::Record(_, Some(owner), _, _) => {
                        self.names.nominal(&owner.ty).into_iter().collect()
                    }
                    Pattern::Binding(name, None, _) | Pattern::Record(name, None, _, _) => {
                        self.names.variants(name).to_vec()
                    }
                    _ => Vec::new(),
                };
                if owners
                    .iter()
                    .any(|owner| borrows_layout(self.index, &owner.type_ref()))
                {
                    self.rootless
                        .shared_cells
                        .insert(self.site(expr, "borrowed match layout"));
                }
            }
        }
        if let Expr::TypeTest(value, annotation, _, _) = expr
            && !matches!(value.as_ref(), Expr::Ident(..))
            && layout::annotation(self.index.program, self.module, annotation)
                .is_some_and(|ty| borrows_layout(self.index, &ty))
        {
            self.rootless
                .shared_cells
                .insert(self.site(expr, "borrowed expression view"));
        }
        let Expr::If(condition, body, _, _) = expr else {
            return;
        };
        let mut views = Tests(Vec::new());
        tests(condition, &mut views, false);
        for (name, annotation, uncertain) in views.0 {
            if layout::annotation(self.index.program, self.module, annotation)
                .is_some_and(|ty| borrows_layout(self.index, &ty))
                && (uncertain || uses_value(body, name))
            {
                self.rootless
                    .shared_cells
                    .insert(self.site(expr, "borrowed type-test layout"));
            }
        }
    }
}
