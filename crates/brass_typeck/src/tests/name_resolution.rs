use super::errs;

#[test]
fn alias_variant_typos_are_checker_errors() {
    // The checker rejects payload constructions through alias chains, and
    // recovery still checks the supplied field expressions.
    let errors = errs(
        "type Shape = Circle { r: int32 } | Empty\n\
         type Sh = Shape\n\
         type Alias = Sh\n\
         let value = Alias.Bogus { r: missing }\n",
    );
    assert!(
        errors.iter().any(|e| e == "`Alias` has no variant `Bogus`"),
        "{errors:?}"
    );
    assert!(
        errors.iter().any(|e| e.contains("unknown name `missing`")),
        "{errors:?}"
    );
}
