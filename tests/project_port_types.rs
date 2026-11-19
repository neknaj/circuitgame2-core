use circuitgame2_core::project::{
    DefinitionReferenceReason, PortDirection, ResolvedPortType, SourceSnapshot,
    TypedSignatureError, check_use_aliases, index_use_targets, parse_circuit_project,
};
use circuitgame2_core::syntax::circuit::Head;

fn snapshot<'a>(path: &'a str, revision: u64, text: &'a str) -> SourceSnapshot<'a> {
    SourceSnapshot {
        path,
        revision,
        text,
    }
}

#[test]
fn aliases_and_qualified_names_can_identify_the_same_structure() {
    let source = concat!(
        "(namespace app (use ::lib::Word T) (use ::lib ns) ",
        "(func first (in (x T)) (out (x ns::Word))) ",
        "(func second (in (x T)) (out (x ::lib::Word))))",
    );
    let library = concat!(
        "(namespace lib (export Word) (struct Word (width 8)) (struct Private (width 8)) ",
        "(func internal (in (x Private)) (out (x Private))))",
    );
    let project = parse_circuit_project(&[
        snapshot("app.ncg2", 4, source),
        snapshot("lib.ncg2", 7, library),
    ])
    .unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();

    for (entry, form) in project.circuits()[0].syntax.entries.iter().enumerate() {
        if form.head != Head::Func {
            continue;
        }
        let typed = aliases
            .resolve_routine_signature(0, entry, 128)
            .unwrap()
            .unwrap();
        assert_eq!(typed.output_inputs, [Some(0)]);
        assert!(typed.inputs[0].ty.is_same_type(&typed.outputs[0].ty));
        assert!(
            matches!(typed.outputs[0].ty, ResolvedPortType::Struct { source, form }
            if source.revision == 7 && form.name.word == "Word")
        );
    }
    assert!(
        aliases
            .resolve_routine_signature(0, usize::MAX, 128)
            .unwrap()
            .is_none()
    );
    let internal_entry = project.circuits()[1].syntax.entries.len() - 1;
    let internal = aliases
        .resolve_routine_signature(1, internal_entry, 128)
        .unwrap()
        .unwrap();
    assert_eq!(internal.output_inputs, [Some(0)]);
    assert!(
        matches!(internal.inputs[0].ty, ResolvedPortType::Struct { form, .. }
        if form.name.word == "Private")
    );
}

#[test]
fn same_width_does_not_make_distinct_port_types_identical() {
    for output_type in ["Other", "(bits 8)"] {
        let text = format!(
            concat!(
                "; 型の照合\n(struct Word (width 8)) (struct Other (width 8)) ",
                "(func f (in (x Word)) (out (x {})))",
            ),
            output_type,
        );
        let project = parse_circuit_project(&[snapshot("main.ncg2", 6, &text)]).unwrap();
        let targets = index_use_targets(&project).unwrap();
        let aliases = check_use_aliases(&targets).unwrap();
        let error = aliases.resolve_routine_signature(0, 2, 128).unwrap_err();
        let TypedSignatureError::SharedTypeMismatch { input, output } = error else {
            panic!("expected distinct port types: {error:?}");
        };
        assert_eq!(&text[input.annotation.span], "Word");
        assert_eq!(
            &text[output.annotation.span],
            if output_type == "Other" { "Other" } else { "8" }
        );
    }
}

#[test]
fn keeps_the_scope_and_related_location_of_the_reference() {
    let library = "(namespace lib (export Word) (struct Word (width 8)) (struct Hidden (width 8)))";
    for (path, expected) in [
        ("::lib::Hidden", "private"),
        ("::lib", "namespace"),
        ("wrong", "kind"),
        ("nor", "missing"),
        ("T", "missing"),
    ] {
        let text = format!(
            concat!(
                "; 型名\n(namespace app (use ::lib::Word T)) ",
                "(namespace app (func wrong (in) (out x)) (func f (in (x {})) (out x)))",
            ),
            path,
        );
        let project = parse_circuit_project(&[
            snapshot("./tmp/../main.ncg2", 6, &text),
            snapshot("lib.ncg2", 9, library),
        ])
        .unwrap();
        let targets = index_use_targets(&project).unwrap();
        let aliases = check_use_aliases(&targets).unwrap();
        let entry = project.circuits()[0].syntax.entries.len() - 1;
        let error = aliases
            .resolve_routine_signature(0, entry, 128)
            .unwrap_err();
        let TypedSignatureError::TypeReference {
            direction,
            reference,
            reason,
        } = error
        else {
            panic!("expected a port type reference error: {error:?}");
        };
        assert_eq!(direction, PortDirection::Input);
        assert_eq!(reference.source.id.components(), ["main.ncg2"]);
        assert_eq!(reference.source.revision, 6);
        assert_eq!(&text[reference.span], path);
        match (expected, reason) {
            ("private", DefinitionReferenceReason::Private(location)) => {
                assert_eq!(location.source.revision, 9);
                assert_eq!(&library[location.span], "Hidden");
            }
            ("namespace", DefinitionReferenceReason::Namespace(location)) => {
                assert_eq!(&library[location.span], "lib");
            }
            ("kind", DefinitionReferenceReason::WrongDeclaration { source, form }) => {
                assert_eq!(source.revision, 6);
                assert_eq!(&text[form.name.span.clone()], "wrong");
            }
            ("missing", DefinitionReferenceReason::Missing) => {}
            (_, reason) => panic!("unexpected error for {path}: {reason:?}"),
        }
    }
}
