use circuitgame2_core::project::{
    AbsoluteResolutionError, AbsoluteTarget, NameKey, SourceSnapshot, index_exports,
    parse_circuit_project,
};
use circuitgame2_core::syntax::split_absolute_path;

#[test]
fn splits_only_absolute_paths_and_keeps_the_parent_spelling() {
    for (path, expected) in [
        ("::root", (None, "root")),
        (
            "::Area_2::cell-4::Output",
            (Some("Area_2::cell-4"), "Output"),
        ),
        ("::logic::nor", (Some("logic"), "nor")),
    ] {
        assert_eq!(split_absolute_path(path), Some(expected));
    }
    for path in [
        "", "::", "root", "a::b", "::a:", "::a::", ":::a", "::a::::b", "::回路",
    ] {
        assert_eq!(split_absolute_path(path), None, "{path}");
    }
}

#[test]
fn applies_visibility_to_declarations_and_preserves_declaration_identity() {
    let text = concat!(
        "; 範囲は元ソースのバイト位置\n",
        "(struct Root (width 1)) ",
        "(namespace app::logic (struct Shared (width 1)) (struct Hidden (width 1)))",
    );
    let project = parse_circuit_project(&[
        SourceSnapshot {
            path: "definitions.ncg2",
            revision: 18,
            text,
        },
        SourceSnapshot {
            path: "exports.ncg2",
            revision: 2,
            text: "(namespace app::logic (export Shared))",
        },
    ])
    .unwrap();
    let table = index_exports(&project).unwrap();
    let AbsoluteTarget::Declaration { source, form } = table
        .resolve_absolute("::app::logic::Shared", Some("another"))
        .unwrap()
    else {
        panic!("expected a declaration");
    };
    let direct = table
        .declarations()
        .declaration(NameKey {
            parent: Some("app::logic"),
            name: "Shared",
        })
        .unwrap();
    assert!(core::ptr::eq(source, direct.0) && core::ptr::eq(form, direct.1));
    assert!(table.resolve_absolute("::Root", None).is_ok());
    assert!(
        table
            .resolve_absolute("::app::logic::Hidden", Some("app::logic"))
            .is_ok()
    );

    for (path, caller, name) in [
        ("::Root", Some("app"), "Root"),
        ("::app::logic::Hidden", None, "Hidden"),
        ("::app::logic::Hidden", Some("app"), "Hidden"),
    ] {
        let error = table.resolve_absolute(path, caller).unwrap_err();
        let AbsoluteResolutionError::Private(location) = error else {
            panic!("expected a private declaration: {error:?}");
        };
        assert_eq!(location.source.id.components(), ["definitions.ncg2"]);
        assert_eq!(location.source.revision, 18);
        assert_eq!(&text[location.span], name);
    }
}

#[test]
fn resolves_implicit_namespaces_and_distinguishes_missing_and_malformed_paths() {
    let text = "(namespace app::logic::inner)";
    let project = parse_circuit_project(&[SourceSnapshot {
        path: "namespaces.ncg2",
        revision: 3,
        text,
    }])
    .unwrap();
    let table = index_exports(&project).unwrap();
    for (path, parent, name) in [
        ("::app", None, "app"),
        ("::app::logic", Some("app"), "logic"),
        ("::app::logic::inner", Some("app::logic"), "inner"),
    ] {
        let AbsoluteTarget::Namespace { key, introduced_at } =
            table.resolve_absolute(path, Some("outside")).unwrap()
        else {
            panic!("expected a namespace");
        };
        assert_eq!(key, NameKey { parent, name });
        assert_eq!(introduced_at.source.revision, 3);
        assert_eq!(&text[introduced_at.span], name);
    }
    assert!(matches!(
        table.resolve_absolute("::app::log", None),
        Err(AbsoluteResolutionError::Missing)
    ));
    assert!(matches!(
        table.resolve_absolute("app::logic", None),
        Err(AbsoluteResolutionError::InvalidPath)
    ));
}
