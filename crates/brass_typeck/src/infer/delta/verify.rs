//! Structural comparisons for the opt-in channel publication oracle.

use std::fmt::Debug;
use std::hash::Hash;
use std::sync::OnceLock;

use fxhash::{FxHashMap, FxHashSet};

use crate::stream::ChannelDelta;

/// Whether the process requests independent channel verification.
pub(super) fn enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var("BRASS_CHANNEL_CHECK").is_ok_and(|v| v == "1"))
}

fn map<K: Eq + Hash + Debug, V: PartialEq + Debug>(entries: &[(K, V)]) -> FxHashMap<&K, &V> {
    let values: FxHashMap<_, _> = entries.iter().map(|(key, value)| (key, value)).collect();
    assert_eq!(entries.len(), values.len(), "duplicate channel key");
    values
}

fn set<K: Eq + Hash + Debug>(entries: &[K]) -> FxHashSet<&K> {
    let values: FxHashSet<_> = entries.iter().collect();
    assert_eq!(entries.len(), values.len(), "duplicate channel removal");
    values
}

/// Compare every semantic field, retaining diagnostics and receiver-owner order.
pub(super) fn assert_delta(actual: &ChannelDelta, expected: &ChannelDelta) {
    assert_eq!(
        map(&actual.expr_types),
        map(&expected.expr_types),
        "expr_types"
    );
    assert_eq!(
        map(&actual.receiver_types),
        map(&expected.receiver_types),
        "receiver_types"
    );
    assert_eq!(
        map(&actual.receiver_owners),
        map(&expected.receiver_owners),
        "receiver_owners"
    );
    assert_eq!(
        map(&actual.field_calls),
        map(&expected.field_calls),
        "field_calls"
    );
    assert_eq!(
        map(&actual.fields_loops),
        map(&expected.fields_loops),
        "fields_loops"
    );
    assert_eq!(
        map(&actual.sum_views),
        map(&expected.sum_views),
        "sum_views"
    );
    assert_eq!(
        map(&actual.type_names),
        map(&expected.type_names),
        "type_names"
    );
    assert_eq!(
        map(&actual.typeof_types),
        map(&expected.typeof_types),
        "typeof_types"
    );
    assert_eq!(
        map(&actual.type_tests),
        map(&expected.type_tests),
        "type_tests"
    );
    assert_eq!(
        set(&actual.expr_types_removed),
        set(&expected.expr_types_removed),
        "expr_types_removed"
    );
    assert_eq!(
        set(&actual.receiver_types_removed),
        set(&expected.receiver_types_removed),
        "receiver_types_removed"
    );
    assert_eq!(
        set(&actual.view_args),
        set(&expected.view_args),
        "view_args"
    );
    assert_eq!(
        set(&actual.lift_errs),
        set(&expected.lift_errs),
        "lift_errs"
    );
    assert_eq!(
        set(&actual.null_props),
        set(&expected.null_props),
        "null_props"
    );
    assert_eq!(
        set(&actual.typeof_types_removed),
        set(&expected.typeof_types_removed),
        "typeof_types_removed"
    );
    assert_eq!(
        set(&actual.type_tests_removed),
        set(&expected.type_tests_removed),
        "type_tests_removed"
    );
    assert_eq!(actual.errors, expected.errors, "errors");
    assert_eq!(actual.warnings, expected.warnings, "warnings");
    let a: Vec<_> = actual
        .instance_seeds
        .iter()
        .map(|(s, entries)| (*s, map(entries)))
        .collect();
    let b: Vec<_> = expected
        .instance_seeds
        .iter()
        .map(|(s, entries)| (*s, map(entries)))
        .collect();
    assert_eq!(map(&a), map(&b), "instance_seeds");
    let a: Vec<_> = actual
        .instance_dispatch
        .iter()
        .map(|(s, entries)| (*s, map(entries)))
        .collect();
    let b: Vec<_> = expected
        .instance_dispatch
        .iter()
        .map(|(s, entries)| (*s, map(entries)))
        .collect();
    assert_eq!(map(&a), map(&b), "instance_dispatch");
    let a: Vec<_> = actual
        .instance_fields
        .iter()
        .map(|(s, entries)| (*s, map(entries)))
        .collect();
    let b: Vec<_> = expected
        .instance_fields
        .iter()
        .map(|(s, entries)| (*s, map(entries)))
        .collect();
    assert_eq!(map(&a), map(&b), "instance_fields");
    let a: Vec<_> = actual
        .instance_returns
        .iter()
        .map(|(s, args, ret)| ((s, args), ret))
        .collect();
    let b: Vec<_> = expected
        .instance_returns
        .iter()
        .map(|(s, args, ret)| ((s, args), ret))
        .collect();
    assert_eq!(map(&a), map(&b), "instance_returns");
    let a: Vec<_> = actual
        .keyed_calls
        .iter()
        .map(|(s, r, m, k)| (s, (r, m, k)))
        .collect();
    let b: Vec<_> = expected
        .keyed_calls
        .iter()
        .map(|(s, r, m, k)| (s, (r, m, k)))
        .collect();
    assert_eq!(map(&a), map(&b), "keyed_calls");
    assert_eq!(
        map(&actual.numeric_calls),
        map(&expected.numeric_calls),
        "numeric_calls"
    );
    assert_eq!(
        set(&actual.numeric_calls_removed),
        set(&expected.numeric_calls_removed),
        "numeric_calls_removed"
    );
}
