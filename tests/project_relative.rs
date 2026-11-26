use circuitgame2_core::project::{
    AbsoluteTarget, LookupTarget, OwnedUnqualifiedLookup, ReferenceScopeError, RelativeResolutionError, RelativeTarget, SourceSnapshot,
    check_use_aliases, index_use_targets, parse_circuit_project,
};
use circuitgame2_core::syntax::{circuit::Head, split_relative_path};

#[test]
fn splits_relative_paths_into_original_components() {
    assert_eq!(split_relative_path("A::b"), Some(("A", None, "b")));
    assert_eq!(
        split_relative_path("Area_2::cell-4::inner::Output"),
        Some(("Area_2", Some("cell-4::inner"), "Output"))
    );
    for invalid in [
        "",
        "::",
        "::x::y",
        "x",
        "x:",
        "x::",
        "x:::y",
        "x::::y",
        "x::2",
        "x::回路",
    ] {
        assert_eq!(split_relative_path(invalid), None, "{invalid}");
    }
}

#[test]
fn follows_namespace_aliases_and_checks_visibility_from_the_caller() {
    let text = concat!(
        "; 非公開宣言の範囲を確認する\n",
        "(namespace app (use ::logic gates) (use ::logic::inner cells) ",
        "  (use ::logic::inner::Open leaf)) ",
        "(namespace app) ",
        "(namespace logic (use ::logic::inner shortcut)) ",
        "(namespace logic::inner ",
        "  (export Open) (struct Open (width 1)) (struct Hidden (width 1)) ",
        "  (use ::logic gates))",
    );
    let project = parse_circuit_project(&[SourceSnapshot {
        path: "project.ncg2",
        revision: 12,
        text,
    }])
    .unwrap();
    let blocks: Vec<_> = project.circuits()[0]
        .names
        .iter()
        .filter(|form| form.head == Head::Namespace)
        .map(|form| form.form)
        .collect();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let app = Some(blocks[0]);
    for (block, path) in [
        (app, "gates::inner::Open"),
        (app, "cells::Open"),
        (Some(blocks[2]), "inner::Open"),
    ] {
        let RelativeTarget::Declaration { source, form } =
            aliases.resolve_relative(0, block, path).unwrap()
        else {
            panic!("expected a declaration");
        };
        let AbsoluteTarget::Declaration {
            source: original_source,
            form: original_form,
        } = targets
            .exports()
            .resolve_absolute("::logic::inner::Open", Some("app"))
            .unwrap()
        else {
            panic!("expected the corresponding absolute declaration");
        };
        assert!(core::ptr::eq(source, original_source));
        assert!(core::ptr::eq(form, original_form));
    }
    let RelativeResolutionError::Private(location) = aliases
        .resolve_relative(0, app, "gates::inner::Hidden")
        .unwrap_err()
    else {
        panic!("expected a private declaration");
    };
    assert_eq!(location.source.revision, 12);
    assert_eq!(&text[location.span], "Hidden");
    assert!(matches!(
        aliases.resolve_relative(0, Some(blocks[3]), "gates::inner::Hidden"),
        Ok(RelativeTarget::Declaration { form, .. }) if form.name.word == "Hidden"
    ));
    assert!(matches!(
        aliases.resolve_relative(0, app, "gates::shortcut::Open"),
        Err(RelativeResolutionError::Missing)
    ));
    assert!(matches!(
        aliases.resolve_relative(0, Some(blocks[1]), "gates::inner::Open"),
        Err(RelativeResolutionError::MissingHead)
    ));
    assert!(matches!(
        aliases.resolve_relative(0, app, "leaf::child"),
        Err(RelativeResolutionError::DeclarationHead { form, .. }) if form.name.word == "Open"
    ));
    assert!(matches!(
        aliases.resolve_relative(0, app, "::logic::inner::Open"),
        Err(RelativeResolutionError::InvalidPath)
    ));
    assert!(matches!(
        aliases.resolve_relative(0, Some(usize::MAX), "::logic::inner::Open"),
        Err(RelativeResolutionError::Scope(
            ReferenceScopeError::UnknownBlock
        ))
    ));
    let RelativeTarget::Namespace {
        parent,
        name,
        introduced_at,
    } = aliases.resolve_relative(0, app, "gates::inner").unwrap()
    else {
        panic!("expected a namespace");
    };
    assert_eq!(parent, "logic");
    assert_eq!(name, "inner");
    assert_eq!(&text[introduced_at.span], "inner");
}

#[test]
fn observes_a_missing_relative_head_and_the_alias_that_replaces_it() {
    fn observe(text: &str, revision: u64) -> OwnedUnqualifiedLookup {
        let project = parse_circuit_project(&[SourceSnapshot { path: "area/main.ncg2", revision, text }]).unwrap();
        let targets = index_use_targets(&project).unwrap();
        let aliases = check_use_aliases(&targets).unwrap();
        aliases.observe_unqualified(0, None, "gates").unwrap()
    }

    let declarations = "(namespace logic (struct Open (width 1)) (export Open))";
    let missing = observe(declarations, 1);
    assert_eq!(missing, OwnedUnqualifiedLookup::Missing);

    let text = format!("{declarations} (use ::logic gates)");
    let alias = observe(&text, 2);
    let OwnedUnqualifiedLookup::Alias {
        directive,
        target: LookupTarget::Namespace { parent, name, introduced_at },
    } = alias else {
        panic!("相対名の先頭で別名が選ばれるはず");
    };
    assert_eq!(directive.file, [b"area".to_vec(), b"main.ncg2".to_vec()]);
    assert_eq!(&text[directive.span], "gates");
    assert_eq!(parent, None);
    assert_eq!(name, b"logic");
    assert_eq!(&text[introduced_at.span], "logic");
}
