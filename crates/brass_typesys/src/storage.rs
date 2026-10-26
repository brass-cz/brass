//! Representation identity at storage sites.
//!
//! Structural subtyping ([`crate::types_compatible`]) says a value is USABLE
//! where another type is required. That is only sound where the receiving
//! code is compiled for the value's own type -- a function or method
//! parameter, whose callee is instantiated per argument type. Every other
//! flow site stores the value into a slot that keeps its DECLARED type: an
//! annotated binding or return, an assignment, a record field, an array or
//! tuple element, a sum payload, a map entry, and the parameters and result
//! of a function-typed value (a closure or function value is compiled once).
//! The slot's readers read the declared layout with no conversion, so a
//! record or sum of another declaration -- or an anonymous record -- stored
//! there would be misread. This module decides that layout half of a storage
//! flow; assignability itself stays with [`crate::types_compatible`].

use brass_hir::{NominalType, STRUCTURAL_RECORD_ID, Type};

/// Whether a value of type `have`, stored in a slot declared `want`, keeps the
/// representation the slot's readers expect: at every position where both
/// types name a record or a sum, they name the SAME declaration (a structural
/// record: the same field-name set), recursively through arrays, slices,
/// tuples, nullables, function types and the substitution entries both
/// instances carry.
///
/// Only declaration identity is decided here. Everything else about the flow
/// -- numeric widths, nullability, invariance of element types, the
/// refinement a required instance demands -- is decided by the flow site's
/// other checks (numeric flow, [`crate::types_compatible`]), so positions
/// whose shapes differ in any other way (an `int32` against an `int64`, a `T`
/// against a `T?`) are left to them and answer `true`. A nullable
/// requirement over a non-nullable value compares the value against the
/// nullable's element, because the store wraps the value unchanged. Open
/// variables, `never` and the abstract `Self` match anything.
///
/// A record or sum against any non-nominal type is a representation change
/// (a protocol record type required of a primitive value, for one) and
/// answers `false`. The declared-sum-subtype rebuild a flow site may insert
/// for its TOP-LEVEL value is not modelled here either: the site records it
/// before consulting this relation, and nested positions have no rebuild.
pub fn same_representation(have: &Type, want: &Type) -> bool {
    match (peel(have), peel(want)) {
        (Type::Unknown(_) | Type::Never | Type::SelfType, _)
        | (_, Type::Unknown(_) | Type::Never | Type::SelfType) => true,
        (Type::Nullable(h), Type::Nullable(w)) => same_representation(h, w),
        (h, Type::Nullable(w)) => same_representation(h, w),
        (Type::Nullable(h), w) => same_representation(h, w),
        (Type::Array(h, _) | Type::Slice(h), Type::Array(w, _) | Type::Slice(w)) => {
            same_representation(h, w)
        }
        (Type::Tuple(hs), Type::Tuple(ws)) => {
            hs.len() != ws.len() || hs.iter().zip(ws).all(|(h, w)| same_representation(h, w))
        }
        (Type::Fun(hp, hr), Type::Fun(wp, wr)) => {
            hp.len() != wp.len()
                || (hp.iter().zip(wp).all(|(h, w)| same_representation(h, w))
                    && same_representation(hr, wr))
        }
        (Type::Record(h), Type::Record(w)) | (Type::Sum(h), Type::Sum(w)) => {
            same_declaration(h, w)
                && h.substitution.iter().all(|(key, ht)| {
                    w.substitution
                        .get(key)
                        .is_none_or(|wt| same_representation(ht, wt))
                })
        }
        (Type::Record(_) | Type::Sum(_), _) | (_, Type::Record(_) | Type::Sum(_)) => false,
        _ => true,
    }
}

/// Whether every function type `have` and `want` hold at corresponding
/// positions has the same representation ([`same_representation`]), while
/// records and sums outside function types may differ.
///
/// This is the representation rule of a PARAMETER flow: the callee is
/// instantiated at the argument's own type, so a structurally compatible
/// record argument (or an array of such records) is fine as it is. A
/// function value inside the argument, however, was compiled once for its
/// own signature and is called through the parameter's declared one, which
/// no instantiation can reconcile -- a `(Animal) -> string` value passed for
/// a `(Dog) -> string` parameter would receive `Dog` values laid out for
/// `Dog`.
pub fn function_values_keep_representation(have: &Type, want: &Type) -> bool {
    match (peel(have), peel(want)) {
        (h @ Type::Fun(..), w @ Type::Fun(..)) => same_representation(h, w),
        (Type::Nullable(h), Type::Nullable(w)) => function_values_keep_representation(h, w),
        (h, Type::Nullable(w)) => function_values_keep_representation(h, w),
        (Type::Array(h, _) | Type::Slice(h), Type::Array(w, _) | Type::Slice(w)) => {
            function_values_keep_representation(h, w)
        }
        (Type::Tuple(hs), Type::Tuple(ws)) => hs
            .iter()
            .zip(ws)
            .all(|(h, w)| function_values_keep_representation(h, w)),
        (Type::Record(h), Type::Record(w)) | (Type::Sum(h), Type::Sum(w)) => {
            h.substitution.iter().all(|(key, ht)| {
                w.substitution
                    .get(key)
                    .is_none_or(|wt| function_values_keep_representation(ht, wt))
            })
        }
        _ => true,
    }
}

/// Whether two nominal instances come from one declaration and therefore
/// share a layout: the same declared id, the same name for a synthetic
/// negative id, and for a structural record the same field names (its
/// layout is its field-name set).
fn same_declaration(a: &NominalType, b: &NominalType) -> bool {
    if a.id != b.id || (a.id < 0 && a.name() != b.name()) {
        return false;
    }
    a.id != STRUCTURAL_RECORD_ID
        || a.substitution
            .iter()
            .map(|(field, _)| field)
            .eq(b.substitution.iter().map(|(field, _)| field))
}

/// Reference, mutability and `const` wrappers describe how a slot is passed
/// or accessed, not the layout of the value it holds.
fn peel(ty: &Type) -> &Type {
    match ty {
        Type::Ref(inner) | Type::Mut(inner) | Type::ConstOf(inner) => peel(inner),
        other => other,
    }
}

#[cfg(test)]
mod tests {
    use brass_hir::{IntKind, Substitution, structural_record};

    use super::*;

    fn record(id: i32, name: &str, fields: &[(&str, Type)]) -> Type {
        let mut subst = Substitution::empty();
        for (field, ty) in fields {
            subst.insert(field.to_string(), ty.clone());
        }
        Type::Record(NominalType::with_substitution(id, name.to_string(), subst))
    }

    fn int() -> Type {
        Type::Int(IntKind::I32)
    }

    #[test]
    fn records_of_different_declarations_differ_at_every_depth() {
        let animal = record(1, "Animal", &[("name", Type::Str)]);
        let dog = record(2, "Dog", &[("name", Type::Str), ("age", int())]);
        assert!(!same_representation(&dog, &animal));
        assert!(!same_representation(
            &Type::Slice(Box::new(dog.clone())),
            &Type::Slice(Box::new(animal.clone()))
        ));
        assert!(!same_representation(
            &Type::Fun(vec![], Box::new(dog.clone())),
            &Type::Fun(vec![], Box::new(animal.clone()))
        ));
        // A nullable requirement compares against its element.
        assert!(!same_representation(
            &dog,
            &Type::Nullable(Box::new(animal.clone()))
        ));
        assert!(same_representation(
            &dog,
            &Type::Nullable(Box::new(dog.clone()))
        ));
    }

    #[test]
    fn instances_of_one_declaration_compare_their_shared_entries() {
        let boxed = |item: Type| record(3, "Box", &[("item", item)]);
        let bare = record(3, "Box", &[]);
        let animal = record(1, "Animal", &[("name", Type::Str)]);
        let dog = record(2, "Dog", &[("name", Type::Str), ("age", int())]);
        assert!(same_representation(&boxed(dog.clone()), &bare));
        assert!(same_representation(&bare, &boxed(dog.clone())));
        assert!(!same_representation(&boxed(dog), &boxed(animal)));
    }

    #[test]
    fn structural_records_match_by_field_names() {
        let narrow = structural_record(vec![("a".into(), int())]);
        let wide = structural_record(vec![("a".into(), int()), ("b".into(), Type::Str)]);
        let named = record(4, "Narrow", &[("a", int())]);
        assert!(same_representation(&narrow, &narrow));
        assert!(!same_representation(&wide, &narrow));
        assert!(!same_representation(&narrow, &named));
    }

    #[test]
    fn parameter_flows_keep_only_function_values_identical() {
        let animal = record(1, "Animal", &[("name", Type::Str)]);
        let dog = record(2, "Dog", &[("name", Type::Str), ("age", int())]);
        assert!(function_values_keep_representation(&dog, &animal));
        assert!(function_values_keep_representation(
            &Type::Slice(Box::new(dog.clone())),
            &Type::Slice(Box::new(animal.clone()))
        ));
        let takes = |param: &Type| Type::Fun(vec![param.clone()], Box::new(Type::Str));
        assert!(!function_values_keep_representation(
            &takes(&animal),
            &takes(&dog)
        ));
        assert!(!function_values_keep_representation(
            &Type::Nullable(Box::new(takes(&animal))),
            &Type::Nullable(Box::new(takes(&dog)))
        ));
    }

    #[test]
    fn a_nominal_against_a_primitive_is_a_representation_change() {
        let display = record(5, "Display", &[]);
        assert!(!same_representation(&int(), &display));
        // Shapes that differ outside nominals are not decided here.
        assert!(same_representation(&int(), &Type::Int(IntKind::I64)));
    }
}
