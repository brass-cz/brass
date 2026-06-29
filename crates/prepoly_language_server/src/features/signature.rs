//! Hover markdown for a function: its generic signature, then -- when it is
//! called with concrete types -- a separated section binding each `unknown_N` to
//! the concrete type it takes at the call site, e.g.
//!
//! ```text
//! fun f(a: unknown_0, b: unknown_1) -> unknown_0
//! ---
//! unknown_0 = int32, unknown_1 = string
//! ```

use std::collections::{HashMap, HashSet};

use prepoly_hir::{FunInfo, Type};

use crate::analysis::FullAnalysis;
use crate::features::nav;
use crate::render::{UnknownNamer, render_signature_into, render_type};

/// Base for synthetic variable ids given to unannotated parameters that have no
/// body use (so no recorded inference variable), high enough not to collide with
/// real ids. They still bind from the call site by position.
const SYNTH_BASE: u32 = 0xFFFF_0000;

/// The hover markdown for free function `f`. When `call_args` is given (the
/// cursor is on a call), a bindings section maps each `unknown_N` to the type
/// that specific call instantiates it with; otherwise only the generic
/// signature is shown.
pub fn function_markdown(full: &FullAnalysis, f: &FunInfo, call_args: Option<&[Type]>) -> String {
    let body_span = f.decl.body.span;

    // For each parameter, the type rendered (`overrides[i]` overrides an
    // unannotated slot) and the type bound against the call argument
    // (`param_types[i]`, which is the annotation when present).
    let mut overrides: Vec<Option<Type>> = Vec::with_capacity(f.signature.params.len());
    let mut param_types: Vec<Option<Type>> = Vec::with_capacity(f.signature.params.len());
    for (i, p) in f.signature.params.iter().enumerate() {
        if p.name == "self" && p.resolved_ty.is_none() {
            overrides.push(None);
            param_types.push(None);
        } else if let Some(annotated) = &p.resolved_ty {
            overrides.push(None);
            param_types.push(Some(annotated.clone()));
        } else {
            let generic = nav::generic_param_type(full, body_span, &p.name)
                .unwrap_or(Type::Unknown(SYNTH_BASE + i as u32));
            overrides.push(Some(generic.clone()));
            param_types.push(Some(generic));
        }
    }

    // A return that depends on a parameter variable is shown as that variable;
    // otherwise the inferred (call-site) return, which carries the real wrapping
    // (e.g. a fallible `Result`). An annotated return is left to the renderer.
    let ret_override = if f.signature.ret_ty.is_some() {
        None
    } else {
        let param_vars: HashSet<u32> = param_types
            .iter()
            .flatten()
            .flat_map(nav::free_vars)
            .collect();
        match nav::generic_return_type(full, f) {
            Some(g) if nav::free_vars(&g).iter().any(|v| param_vars.contains(v)) => Some(g),
            _ => nav::inferred_return(full, &f.signature.name),
        }
    };

    let mut namer = UnknownNamer::default();
    let sig = render_signature_into(&f.signature, &overrides, ret_override.as_ref(), &mut namer);

    // Bind the signature's variables to the concrete arguments of the call
    // under the cursor.
    let mut bound: HashMap<u32, Type> = HashMap::new();
    if let Some(args) = call_args {
        for (i, param) in param_types.iter().enumerate() {
            if let (Some(generic), Some(concrete)) = (param, args.get(i)) {
                nav::collect_bindings(generic, concrete, &mut bound);
            }
        }
    }

    let mut lines: Vec<(usize, String)> = Vec::new();
    for (id, n) in namer.assignments() {
        if let Some(concrete) = bound.get(&id) {
            // Only show a concrete instantiation. A binding whose value still has
            // inference variables comes from a recursive (or otherwise generic)
            // call -- e.g. `gcd`'s recursion maps one of its own type variables to
            // another -- and would just restate the signature's variables, so it
            // is dropped rather than shown as a misleading `unknown_j = unknown_i`.
            if !nav::free_vars(concrete).is_empty() {
                continue;
            }
            let mut cn = UnknownNamer::default();
            lines.push((
                n,
                format!("unknown_{n} = {}", render_type(concrete, &mut cn)),
            ));
        }
    }
    lines.sort_by_key(|(n, _)| *n);

    let mut value = format!("```prepoly\n{sig}\n```");
    if !lines.is_empty() {
        let bindings = lines
            .into_iter()
            .map(|(_, s)| s)
            .collect::<Vec<_>>()
            .join(", ");
        value.push_str(&format!("\n\n---\n\n```prepoly\n{bindings}\n```"));
    }
    value
}
