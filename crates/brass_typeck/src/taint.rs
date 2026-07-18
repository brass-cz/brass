//! Which callables can reach a reflective keyed (`-> infer!`) method call.
//!
//! The lazy profile types some calls from their signatures without
//! re-elaborating the callee body (see `Checker::lazy_profile`). A keyed
//! call, however, must be SEEN by the checker's first pass: discovering one
//! later restarts the whole analysis, which is recoverable before execution
//! but fatal mid-run. Skipping is therefore forbidden for any callable that
//! can transitively reach a keyed call, and this module computes that set.
//!
//! The reachability is deliberately name-based and conservative: a method
//! call is `Expr::Call` on an `Expr::Field` callee, which is syntactically
//! identical to a qualified free-function call, so both feed the same
//! name-level call graph. Over-tainting merely keeps the eager elaboration
//! for a call that did not need it; under-tainting would surface as a
//! mid-run restart, so precision loses to safety here.

use std::collections::{HashMap, HashSet};

use brass_hir::{Program, TypeKind};
use brass_parser::ast::Expr;

use crate::walk::{self, ExprVisitor};

/// One callable's call-graph contribution: whether its body contains a
/// keyed-named method call directly, and every callee NAME it mentions.
struct Calls<'k> {
    keyed: &'k HashSet<String>,
    direct: bool,
    names: HashSet<String>,
}

impl ExprVisitor for Calls<'_> {
    fn visit(&mut self, e: &Expr) {
        if let Expr::Call(callee, _, _) = e {
            match &**callee {
                Expr::Field(_, name, _) => {
                    if self.keyed.contains(name) {
                        self.direct = true;
                    }
                    self.names.insert(name.clone());
                }
                Expr::Ident(name, _) => {
                    self.names.insert(name.clone());
                }
                _ => {}
            }
        }
    }
}

/// The names of every declared keyed (`-> infer!`) method.
fn keyed_method_names(program: &Program) -> HashSet<String> {
    let mut keyed_names: HashSet<String> = HashSet::new();
    let mut each_method = |methods: &HashMap<String, brass_hir::MethodInfo>| {
        for (name, m) in methods {
            if brass_hir::keyed_return(m.decl.ret.as_ref()) {
                keyed_names.insert(name.clone());
            }
        }
    };
    for t in program.types.values() {
        match &t.kind {
            TypeKind::Record { methods, .. } => each_method(methods),
            TypeKind::Sum { variants } => {
                for v in variants {
                    each_method(&v.methods);
                }
            }
        }
    }
    keyed_names
}

/// Whether any body in the program CALLS a keyed (`-> infer!`) method, by
/// name. The lazy driver routes such a program to the eager pipeline up
/// front: keyed specialization restarts the analysis over a rewritten
/// program, which a lazy run only ever survives by falling back to the
/// eager verdict -- after paying for its own gate first.
pub fn has_keyed_calls(program: &Program) -> bool {
    let keyed_names = keyed_method_names(program);
    if keyed_names.is_empty() {
        return false;
    }
    struct Any<'k> {
        keyed: &'k HashSet<String>,
        found: bool,
    }
    impl ExprVisitor for Any<'_> {
        fn visit(&mut self, e: &Expr) {
            if let Expr::Call(callee, _, _) = e
                && let Expr::Field(_, name, _) = &**callee
                && self.keyed.contains(name)
            {
                self.found = true;
            }
        }
    }
    let mut v = Any {
        keyed: &keyed_names,
        found: false,
    };
    walk::walk_program_exprs(program, &mut v);
    v.found
}

/// The set of free-function SYMBOLS that can reach a keyed method call,
/// transitively through free-function and method calls. Empty when the
/// program declares no keyed method at all (the common case, which then
/// costs one scan of the type tables and nothing else).
pub(crate) fn keyed_reachable(program: &Program) -> HashSet<String> {
    let keyed_names = keyed_method_names(program);
    if keyed_names.is_empty() {
        return HashSet::new();
    }

    // Nodes: free functions (keyed by symbol) and methods (keyed by a
    // synthetic "Type.m" the result never exposes); each carries its bare
    // callable NAME, since edges are name-level.
    struct Node {
        key: String,
        name: String,
        direct: bool,
        names: HashSet<String>,
    }
    let scan = |keyed: &HashSet<String>, body: &brass_parser::ast::Block| {
        let mut v = Calls {
            keyed,
            direct: false,
            names: HashSet::new(),
        };
        walk::walk_block(body, &mut v);
        (v.direct, v.names)
    };
    let mut nodes: Vec<Node> = Vec::new();
    for (sym, f) in &program.functions {
        let (direct, names) = scan(&keyed_names, &f.decl.body);
        nodes.push(Node {
            key: sym.clone(),
            name: f.signature.name.clone(),
            direct,
            names,
        });
    }
    for t in program.types.values() {
        let mut each = |methods: &HashMap<String, brass_hir::MethodInfo>| {
            for (name, m) in methods {
                if let Some(body) = &m.decl.body {
                    let (direct, names) = scan(&keyed_names, body);
                    nodes.push(Node {
                        key: format!("{}.{}", t.name, name),
                        name: name.clone(),
                        direct,
                        names,
                    });
                }
            }
        };
        match &t.kind {
            TypeKind::Record { methods, .. } => each(methods),
            TypeKind::Sum { variants } => {
                for v in variants {
                    each(&v.methods);
                }
            }
        }
    }

    // Fixpoint: a node is tainted when its body calls a keyed method
    // directly, or mentions the NAME of any tainted node.
    let mut tainted: Vec<bool> = nodes.iter().map(|n| n.direct).collect();
    let mut dangerous: HashSet<&str> = nodes
        .iter()
        .zip(&tainted)
        .filter(|(_, t)| **t)
        .map(|(n, _)| n.name.as_str())
        .collect();
    loop {
        let mut changed = false;
        for (i, node) in nodes.iter().enumerate() {
            if !tainted[i] && node.names.iter().any(|n| dangerous.contains(n.as_str())) {
                tainted[i] = true;
                changed |= dangerous.insert(node.name.as_str());
            }
        }
        if !changed {
            break;
        }
    }
    nodes
        .iter()
        .zip(&tainted)
        .filter(|(_, t)| **t)
        .filter(|(n, _)| program.functions.contains_key(&n.key))
        .map(|(n, _)| n.key.clone())
        .collect()
}
