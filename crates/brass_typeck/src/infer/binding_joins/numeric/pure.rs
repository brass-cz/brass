//! Immutable eligibility for provenance replay across local call graphs.

use super::*;

/// Call-only arithmetic functions whose transitive callees have no local storage
/// or external reads. Removing impure nodes propagates through reverse edges,
/// including cycles, without walking the same chain for each instantiation.
pub(in crate::infer) fn bodies(program: &Program) -> HashSet<String> {
    eligible(program, false)
}

/// Straight-line local call graphs with no numeric literals or nonlocal value reads.
/// Without incoming origins these bodies cannot create a negotiable root.
pub(in crate::infer) fn closed_bodies(program: &Program) -> HashSet<String> {
    eligible(program, true)
}

fn eligible(program: &Program, closed: bool) -> HashSet<String> {
    let mut names: HashMap<&str, Vec<&str>> = HashMap::default();
    for info in program.functions.values() {
        names
            .entry(&info.signature.name)
            .or_default()
            .push(&info.symbol);
    }
    let mut pure = HashSet::default();
    let mut reverse: HashMap<String, Vec<String>> = HashMap::default();
    let mut rejected = Vec::new();
    for info in program.functions.values() {
        let mut params: HashSet<&str> = info
            .signature
            .params
            .iter()
            .map(|p| p.name.as_str())
            .collect();
        let mut dependencies = Vec::new();
        let admitted = if closed {
            info.decl.body.stmts.iter().all(|stmt| match stmt {
                Stmt::Let {
                    pat: Pattern::Binding(name, None, _),
                    ty: None,
                    value: Some(value),
                    ..
                } => {
                    let valid = expression(value, &params, &names, &mut dependencies, true);
                    valid && params.insert(name.as_str())
                }
                Stmt::Expr(value) | Stmt::Return(Some(value), _) => {
                    expression(value, &params, &names, &mut dependencies, true)
                }
                _ => false,
            })
        } else {
            match info.decl.body.stmts.as_slice() {
                [Stmt::Return(Some(value), _)] => {
                    expression(value, &params, &names, &mut dependencies, false)
                }
                _ => false,
            }
        };
        if admitted {
            pure.insert(info.symbol.clone());
        } else {
            rejected.push(info.symbol.clone());
        }
        for dependency in dependencies {
            reverse
                .entry(dependency)
                .or_default()
                .push(info.symbol.clone());
        }
    }
    while let Some(symbol) = rejected.pop() {
        for caller in reverse.get(&symbol).into_iter().flatten() {
            if pure.remove(caller) {
                rejected.push(caller.clone());
            }
        }
    }
    pure
}

fn expression(
    expr: &Expr,
    params: &HashSet<&str>,
    names: &HashMap<&str, Vec<&str>>,
    dependencies: &mut Vec<String>,
    closed: bool,
) -> bool {
    match expr {
        Expr::Int(..) | Expr::Float(..) => !closed,
        Expr::Str(parts, _) => {
            closed
                && parts
                    .iter()
                    .all(|part| matches!(part, brass_parser::ast::StrSeg::Lit(_)))
        }
        Expr::Bool(..) | Expr::Null(..) => closed,
        Expr::Ident(name, _) => params.contains(name.as_str()),
        Expr::Unary(_, inner, _) => expression(inner, params, names, dependencies, closed),
        Expr::Binary(_, left, right, _) => {
            expression(left, params, names, dependencies, closed)
                && expression(right, params, names, dependencies, closed)
        }
        Expr::Call(callee, args, _) => {
            let Expr::Ident(name, _) = &**callee else {
                return false;
            };
            if params.contains(name.as_str()) {
                return false;
            }
            if let Some(candidates) = names.get(name.as_str()) {
                dependencies.extend(candidates.iter().map(|symbol| (*symbol).to_owned()));
            } else if !(closed && matches!(name.as_str(), "print" | "println" | "len")) {
                return false;
            }
            args.iter()
                .all(|arg| expression(&arg.expr, params, names, dependencies, closed))
        }
        _ => false,
    }
}
