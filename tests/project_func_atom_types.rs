use circuitgame2_core::project::{
    CircuitLiteralWidthError, FuncAtomTypeError, FuncLiteralError, FuncWiringResult, ResolvedPortType,
    SourceSnapshot, check_use_aliases, index_use_targets, parse_circuit_project,
};

fn source(text: &str) -> SourceSnapshot<'_> {
    SourceSnapshot { path: "./lib/../main.ncg2", revision: 21, text }
}

#[test]
fn propagates_the_original_type_and_site_through_a_chain_of_definitions() {
    let text = concat!(
        "; 日本語\n",
        "(func unrelated (in a) (out y) (def y a)) ",
        "(func f (in (a (bits 8))) (out (x (bits 8)) (y (bits 8))) ",
        "  (def seed #x01) (def alias seed) (def y alias) (def x a))",
    );
    let project = parse_circuit_project(&[source(text)]).unwrap();
    let table = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&table).unwrap();
    let result = aliases.check_func_atom_types(0, 1, 8).unwrap();
    assert_eq!(result.types.len(), 4);
    for (item, origin) in result.types.iter().zip(["#x01", "#x01", "#x01", "8"]) {
        let typed = item.as_ref().unwrap();
        assert!(matches!(typed.ty, ResolvedPortType::Bits(8)));
        assert_eq!(&text[typed.origin.span.clone()], origin);
        assert_eq!(typed.origin.source.revision, 21);
        assert_eq!(typed.origin.source.id.components(), ["main.ncg2"]);
    }
}

#[test]
fn compares_declared_types_without_resizing_the_earlier_signal() {
    let text = concat!(
        "(struct Word (width 8)) (struct Other (width 8)) (use ::Word Alias) ",
        "(func same (in (a Word)) (out (y Alias)) (def y a)) ",
        "(func distinct (in (a Word)) (out (y Other)) (def y a)) ",
        "(func narrow (in) (out y) (def local #x01) (def y local)) ",
        "(func pending (in a) (out (y (bits 4))) (def local (bit a 0)) (def y local)) ",
        "(func independent (in (a (bits 8))) (out (y (bits 4)) z) ",
        "  (def local (bit a 0)) (def y local) (def z a))",
    );
    let project = parse_circuit_project(&[source(text)]).unwrap();
    let table = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&table).unwrap();
    let same = aliases.check_func_atom_types(0, 3, 8).unwrap();
    assert!(matches!(
        same.types[0].as_ref().unwrap().ty,
        ResolvedPortType::Struct { form, .. } if form.name.word == "Word"
    ));
    for (entry, name, expected_text, actual_text) in [(4, "a", "Other", "Word"), (5, "local", "y", "#x01")] {
        let error = aliases.check_func_atom_types(0, entry, 8).unwrap_err();
        let FuncAtomTypeError::OutputType { reference, expected, actual } = error else {
            panic!("expected output type mismatch: {error:?}");
        };
        assert_eq!(&text[reference.span], name);
        assert_eq!(&text[expected.origin.span], expected_text);
        assert_eq!(&text[actual.origin.span], actual_text);
        assert_eq!(reference.source.revision, 21);
    }
    let pending = aliases.check_func_atom_types(0, 6, 8).unwrap();
    assert!(pending.types.iter().all(Option::is_none));
    let later = aliases.check_func_atom_types(0, 7, 8).unwrap_err();
    let FuncAtomTypeError::OutputType { reference, expected, actual } = later else {
        panic!("expected the independent type mismatch: {later:?}");
    };
    assert_eq!(&text[reference.span], "a");
    assert_eq!(&text[expected.origin.span], "z");
    assert!(matches!(actual.ty, ResolvedPortType::Bits(8)));
}

#[test]
fn keeps_prior_literal_diagnostics_and_expansion_states() {
    let text = concat!(
        "(func invalid (in (a (bits 8))) (out y z) (def y a) (def z #x02)) ",
        "(func waiting (in) (out y) (expand gen))",
    );
    let project = parse_circuit_project(&[source(text)]).unwrap();
    let table = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&table).unwrap();
    assert!(matches!(
        aliases.check_func_atom_types(0, 0, 8),
        Err(FuncAtomTypeError::Literal(FuncLiteralError::Width {
            reason: CircuitLiteralWidthError::DoesNotFit { expected: 1, required: 2 }, ..
        }))
    ));
    let waiting = aliases.check_func_atom_types(0, 1, 8).unwrap();
    assert!(waiting.types.is_empty());
    assert!(matches!(waiting.literals.wiring, FuncWiringResult::NeedsExpansion(_)));
}
