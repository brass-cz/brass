//! Type and signature rendering for hover.
//!
//! The compiler's `Type::display` prints every inference variable as a bare
//! `?`, which is ambiguous when several appear. For hover output we instead
//! number them `unknown_N` by order of first appearance, as the language
//! server's contract requires: a function whose parameters carry no annotation
//! has each unannotated slot shown as a distinct `unknown_N`, numbered in the
//! order the parameters (then the return) occur.

use std::collections::{BTreeMap, HashMap};

use prepoly_hir::{
    CallableSignature, FieldInfo, Substitution, Type, TypeInfo, TypeKind, VariantInfo,
};

/// Assigns stable `unknown_N` names to inference variables, numbered by order
/// of first appearance. Share one namer across everything that should agree on
/// numbering -- e.g. all parameters and the return type of one signature.
#[derive(Default)]
pub struct UnknownNamer {
    /// Names already assigned to a concrete `Type::Unknown(id)`, so the same
    /// variable renders identically wherever it recurs.
    by_id: HashMap<u32, usize>,
    next: usize,
    /// Display names fixed up front for specific variables, overriding the
    /// `unknown_N` numbering -- a record's type-slot variables render as
    /// `Self.<slot>` inside the record's own field types.
    fixed: HashMap<u32, String>,
}

impl UnknownNamer {
    /// Fix the display name of inference variable `id` (e.g. to a type slot's
    /// `Self.<name>` form) instead of numbering it `unknown_N`.
    pub(crate) fn fix(&mut self, id: u32, name: String) {
        self.fixed.insert(id, name);
    }

    /// A namer sharing this one's fixed names but with fresh `unknown_N`
    /// numbering -- each member of a type's member list numbers its own open
    /// variables from zero while slot variables keep their `Self.<slot>` names.
    fn fresh_child(&self) -> Self {
        Self {
            by_id: HashMap::new(),
            next: 0,
            fixed: self.fixed.clone(),
        }
    }

    /// The name for inference variable `id`, allocating a fresh number the first
    /// time the id is seen.
    fn named(&mut self, id: u32) -> String {
        if let Some(name) = self.fixed.get(&id) {
            return name.clone();
        }
        let next = self.next;
        let n = *self.by_id.entry(id).or_insert_with(|| {
            // `next` was captured before the borrow; only commit it on insert.
            next
        });
        if n == next {
            self.next += 1;
        }
        format!("unknown_{n}")
    }

    /// A fresh `unknown_N` with no backing inference variable, for an
    /// unannotated parameter or return type that the front end never assigned an
    /// id (the signature tables only retain explicit annotations).
    fn fresh(&mut self) -> String {
        let n = self.next;
        self.next += 1;
        format!("unknown_{n}")
    }

    /// The `(inference variable id, N)` pairs assigned so far, in `N` order, so a
    /// caller can render an `unknown_N = <type>` binding for each variable using
    /// the same numbering the signature was rendered with.
    pub fn assignments(&self) -> Vec<(u32, usize)> {
        let mut pairs: Vec<(u32, usize)> = self.by_id.iter().map(|(&id, &n)| (id, n)).collect();
        pairs.sort_by_key(|&(_, n)| n);
        pairs
    }
}

/// Render a resolved type, mapping inference variables to `unknown_N`.
///
/// Delegates to the compiler's one type renderer (`Type::display_with`),
/// injecting the hover numbering, so hover and diagnostics can never disagree
/// on type syntax; only the inference-variable spelling differs.
pub fn render_type(ty: &Type, namer: &mut UnknownNamer) -> String {
    ty.display_with(&mut |id| namer.named(id))
}

/// Render a function or method signature as `fun name(p: T, ...) -> R`.
///
/// A parameter or return type with no annotation has no resolved type in the
/// signature tables, so it is rendered as a fresh `unknown_N` numbered by
/// position. An explicitly annotated slot is rendered from its resolved type.
pub fn render_signature(sig: &CallableSignature) -> String {
    render_signature_full(sig, &[], None)
}

/// Render a signature, filling unannotated slots from inference when available.
///
/// The signature tables hold only annotations, so an unannotated parameter or
/// return reads as absent there. `inferred_params[i]` (by position) and
/// `inferred_ret` supply the types inference recovered for them (see
/// `nav::inferred_param_type`/`nav::inferred_return`); a slot with neither an
/// annotation nor an inferred type falls back to a fresh `unknown_N`.
pub fn render_signature_full(
    sig: &CallableSignature,
    inferred_params: &[Option<Type>],
    inferred_ret: Option<&Type>,
) -> String {
    render_signature_into(
        sig,
        inferred_params,
        inferred_ret,
        None,
        &mut UnknownNamer::default(),
    )
}

/// Whether a type is shown without a `ref`/`mut` wrapper for an unannotated
/// parameter: a primitive (passed by value) or a function value (immutable, so a
/// reference/copy distinction is not meaningful). Every other (heap) type --
/// string, array, record, sum, tuple, or an unresolved variable -- is passed by
/// reference or copy and is shown wrapped.
fn is_value_display_type(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Bool | Type::Int(_) | Type::Float(_) | Type::Fun(..)
    )
}

/// The display form of an unannotated parameter's inferred passing mode: `self`
/// is a reference (`ref(mut(Self))` when it mutates itself, else `ref(Self)`); a
/// non-self heap parameter is a private `mut` copy when mutated, else a shared
/// `ref` borrow; a value parameter (a primitive) is shown bare. `inner` is the
/// already-rendered underlying type.
fn wrap_inferred_mode(inner: String, is_self: bool, is_value: bool, mutated: bool) -> String {
    if is_self {
        return if mutated {
            format!("ref(mut({inner}))")
        } else {
            format!("ref({inner})")
        };
    }
    if is_value {
        inner
    } else if mutated {
        format!("mut({inner})")
    } else {
        format!("ref({inner})")
    }
}

/// Like [`render_signature_full`], but numbering inference variables through the
/// caller's `namer`. After it returns, `namer.assignments()` gives the
/// `unknown_N` numbering used, so a binding section (`unknown_N = <type>`) can be
/// rendered with the same names.
pub fn render_signature_into(
    sig: &CallableSignature,
    inferred_params: &[Option<Type>],
    inferred_ret: Option<&Type>,
    mutated: Option<&[bool]>,
    namer: &mut UnknownNamer,
) -> String {
    let mut rendered = Vec::with_capacity(sig.params.len());
    for (i, p) in sig.params.iter().enumerate() {
        let is_mutated = mutated.and_then(|m| m.get(i).copied());
        // An unannotated `self` is a reference. Without mutation information it is
        // shown bare (`self`); with it, the inferred wrapper is shown explicitly
        // (`self: ref(Self)` or `self: ref(mut(Self))`), without consuming an
        // `unknown_N` slot.
        if p.name == "self" && p.resolved_ty.is_none() {
            match is_mutated {
                Some(m) => rendered.push(format!(
                    "self: {}",
                    wrap_inferred_mode("Self".into(), true, false, m)
                )),
                None => rendered.push("self".to_string()),
            }
            continue;
        }
        let inferred = inferred_params.get(i).and_then(|o| o.as_ref());
        // An annotated parameter renders from its type (which already shows any
        // `ref`/`mut`). An unannotated one renders its inferred type (or a fresh
        // `unknown_N`) and, when mutation information is available, shows the
        // inferred `ref`/`mut` passing mode explicitly.
        let ty = match (&p.resolved_ty, inferred) {
            (Some(t), _) => render_type(t, namer),
            (None, inf) => {
                let (inner, is_value) = match inf {
                    Some(t) => (render_type(t, namer), is_value_display_type(t)),
                    None => (namer.fresh(), false),
                };
                match is_mutated {
                    Some(m) => wrap_inferred_mode(inner, false, is_value, m),
                    None => inner,
                }
            }
        };
        rendered.push(format!("{}: {ty}", p.name));
    }
    let params = rendered.join(", ");
    // The annotation is the contract and normally wins. The exception is an
    // annotation that leaves part of the type open: a `T!` names only the OK
    // payload, and its Err side is inferred from the body's `error(..)` sites, so
    // rendering the annotation alone gives `Result<T, unknown_0>`. The caller only
    // ever passes an `inferred_ret` it has already found concrete.
    let ret = match (&sig.ret_ty, inferred_ret) {
        (Some(t), Some(inferred)) if !prepoly_hir::is_fully_known(t) => {
            render_type(inferred, namer)
        }
        (Some(t), _) => render_type(t, namer),
        (None, Some(t)) => render_type(t, namer),
        (None, None) => namer.fresh(),
    };
    format!("fun {}({params}) -> {ret}", sig.name)
}

/// Render a type definition: a record's slots, fields, and methods, or a sum
/// type's variants, taking each record field's type from `substitution` when it
/// carries one. An instance hover passes the value's substitution so a field
/// whose declared type is open shows the concrete type that instance pinned,
/// while a bare type-name hover passes an empty substitution and shows the
/// declaration.
///
/// Type slots (`slot: type` type parameters) are listed first: as the declared
/// `slot: type` marker when open, or as `slot: <concrete>` when the instance has
/// pinned them. A slot variable occurring in a field's or method's type renders
/// as `Self.<slot>`, as the declaration wrote it.
///
/// `resolved_methods` overrides a method's stored signature (annotations only)
/// with one whose types are already resolved -- against the scheme and the
/// instance (see `hover::typedef_method_signatures`); a method without an entry
/// falls back to its stored signature.
///
/// Members whose name begins with `_` are implementation details, not part of the
/// type's surface, and are omitted.
pub fn render_type_def_with(
    info: &TypeInfo,
    substitution: &Substitution,
    resolved_methods: &HashMap<String, CallableSignature>,
) -> String {
    let mut namer = UnknownNamer::default();
    match &info.kind {
        TypeKind::Record { fields, methods } => {
            for (name, var) in &info.slots {
                namer.fix(*var, format!("Self.{name}"));
            }
            // The substitution is keyed by field, with any slot pins embedded in
            // the field types; recover each slot's own type by matching the
            // declared field types -- which contain the slot variables -- against
            // the instance's structurally.
            let slot_vars: Vec<u32> = info.slots.iter().map(|(_, v)| *v).collect();
            let mut pins: BTreeMap<u32, Type> = BTreeMap::new();
            for f in fields {
                if let (Some(declared), Some(actual)) =
                    (f.resolved_ty.as_ref(), substitution.get(&f.name))
                {
                    match_type_vars(declared, actual, &slot_vars, &mut pins);
                }
            }
            let mut body = String::new();
            for (name, var) in info.slots.iter().filter(|(n, _)| is_public_member(n)) {
                let line = match pins.get(var) {
                    Some(t) if !t.is_unknown() => format!("{name}: {}", render_type(t, &mut namer)),
                    _ => format!("{name}: type"),
                };
                body.push_str(&format!("    {line}\n"));
            }
            for f in fields.iter().filter(|f| is_public_member(&f.name)) {
                let resolved = substitution.get(&f.name).or(f.resolved_ty.as_ref());
                let line = match resolved {
                    Some(t) => format!("{}: {}", f.name, render_type(t, &mut namer)),
                    None => f.name.clone(),
                };
                body.push_str(&format!("    {line}\n"));
            }
            let mut names: Vec<&String> = methods.keys().filter(|n| is_public_member(n)).collect();
            names.sort();
            for name in names {
                let sig = resolved_methods
                    .get(name.as_str())
                    .unwrap_or(&methods[name].signature);
                // A child namer keeps slot variables rendering as `Self.<slot>`
                // inside method types while each method numbers the variables
                // its scheme leaves open from `unknown_0`.
                let line = render_signature_into(sig, &[], None, None, &mut namer.fresh_child());
                body.push_str(&format!("    {line}\n"));
            }
            format!("type {} = {{\n{body}}}", info.name)
        }
        TypeKind::Sum { variants } => {
            let body = variants
                .iter()
                .filter(|v| is_public_member(&v.name))
                .map(|v| format!("    {}", render_variant(v, &mut namer)))
                .collect::<Vec<_>>()
                .join("\n");
            format!("type {} =\n{body}", info.name)
        }
    }
}

/// Whether a field/method/variant name is part of a type's public surface. A
/// leading underscore marks an implementation detail (e.g. `HashMap._find`),
/// which hover, the type view, and member completion omit.
pub(crate) fn is_public_member(name: &str) -> bool {
    !name.starts_with('_')
}

/// Record `var -> actual` where one of `vars` (an inference variable standing
/// for a type parameter) aligns with a concrete position in `actual`, recursing
/// through structurally matching shapes. The most informative pin wins: a
/// concrete match replaces an earlier still-unknown one, and an unknown never
/// replaces an entry (so several passes can layer, e.g. a declaration pass then
/// an instance pass).
pub(crate) fn match_type_vars(
    pattern: &Type,
    actual: &Type,
    vars: &[u32],
    map: &mut BTreeMap<u32, Type>,
) {
    match (pattern, actual) {
        (Type::Unknown(id), a) if vars.contains(id) => {
            let replace = match map.get(id) {
                None => true,
                Some(cur) => cur.is_unknown() && !a.is_unknown(),
            };
            if replace {
                map.insert(*id, a.clone());
            }
        }
        (Type::Slice(s), Type::Slice(a))
        | (Type::Slice(s), Type::Array(a, _))
        | (Type::Array(s, _), Type::Slice(a))
        | (Type::Array(s, _), Type::Array(a, _))
        | (Type::Nullable(s), Type::Nullable(a))
        | (Type::Ref(s), Type::Ref(a))
        | (Type::Mut(s), Type::Mut(a))
        | (Type::ConstOf(s), Type::ConstOf(a)) => match_type_vars(s, a, vars, map),
        (Type::Record(sn), Type::Record(an)) | (Type::Sum(sn), Type::Sum(an)) => {
            for (k, sv) in sn.substitution.iter() {
                if let Some(av) = an.substitution.get(k) {
                    match_type_vars(sv, av, vars, map);
                }
            }
        }
        (Type::Tuple(ss), Type::Tuple(aa)) => {
            for (s, a) in ss.iter().zip(aa) {
                match_type_vars(s, a, vars, map);
            }
        }
        (Type::Fun(sp, sr), Type::Fun(ap, ar)) => {
            for (s, a) in sp.iter().zip(ap) {
                match_type_vars(s, a, vars, map);
            }
            match_type_vars(sr, ar, vars, map);
        }
        _ => {}
    }
}

fn render_field(f: &FieldInfo, namer: &mut UnknownNamer) -> String {
    match &f.resolved_ty {
        Some(t) => format!("{}: {}", f.name, render_type(t, namer)),
        None => f.name.clone(),
    }
}

fn render_variant(v: &VariantInfo, namer: &mut UnknownNamer) -> String {
    if v.fields.is_empty() {
        return v.name.clone();
    }
    let fields = v
        .fields
        .iter()
        .map(|f| render_field(f, namer))
        .collect::<Vec<_>>()
        .join(", ");
    format!("{} {{ {fields} }}", v.name)
}

#[cfg(test)]
mod tests {
    use super::*;
    use prepoly_hir::{IntKind, Type};

    /// Distinct inference variables number by order of appearance and repeat
    /// consistently; a concrete type in between does not consume a number.
    #[test]
    fn unknowns_numbered_by_appearance() {
        let mut namer = UnknownNamer::default();
        let ty = Type::Fun(
            vec![Type::Unknown(7), Type::Int(IntKind::I32), Type::Unknown(3)],
            Box::new(Type::Unknown(7)),
        );
        assert_eq!(
            render_type(&ty, &mut namer),
            "(unknown_0, int32, unknown_1) -> unknown_0"
        );
    }
}
