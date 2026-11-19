use circuitgame2_core::project::{
    AbsoluteTarget, AliasDisposition, ReferenceScopeError, SourceSnapshot, UnqualifiedTarget,
    UseAliasConflict, check_use_aliases, index_use_targets, parse_circuit_project,
};
use circuitgame2_core::syntax::circuit::Head;

#[test]
fn warns_on_every_repeat_and_keeps_scopes_and_distinct_aliases_separate() {
    let text = concat!(
        "; 範囲を UTF-8 のバイト位置で確認する\n",
        "(struct Top (width 1)) ",
        "(use ::Top Top) (use ::Top Top) (use ::Top Top) (use ::Top other) ",
        "(namespace app (use ::logic helper) (use ::logic helper)) ",
        "(namespace app (use ::logic helper)) ",
        "(namespace logic::core)",
    );
    let project = parse_circuit_project(&[
        SourceSnapshot {
            path: "a.ncg2",
            revision: 1,
            text,
        },
        SourceSnapshot {
            path: "b.ncg2",
            revision: 2,
            text: "(use ::logic Top) (namespace app (use ::logic helper))",
        },
    ]);
    // 同名の直接宣言は別ファイルにも及ぶので、b のルートの指定だけは衝突する。
    let project = project.unwrap();
    let targets = index_use_targets(&project).unwrap();
    let UseAliasConflict::Direct { directive, .. } = check_use_aliases(&targets).unwrap_err()
    else {
        panic!("expected a project-wide direct conflict");
    };
    assert_eq!(directive.site.source.revision, 2);
    assert_eq!(directive.site.alias.word, "Top");

    let project = parse_circuit_project(&[
        SourceSnapshot {
            path: "a.ncg2",
            revision: 1,
            text,
        },
        SourceSnapshot {
            path: "b.ncg2",
            revision: 2,
            text: "(use ::logic other) (namespace app (use ::logic helper))",
        },
    ])
    .unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    use AliasDisposition::{Binding, Duplicate};
    assert_eq!(
        aliases.dispositions(),
        [
            Binding,
            Duplicate { first: 0 },
            Duplicate { first: 0 },
            Binding,
            Binding,
            Duplicate { first: 4 },
            Binding,
            Binding,
            Binding,
        ]
    );
    let sites = aliases.directives();
    assert_eq!(sites[2].site.alias.word, "Top");
    assert_eq!(&text[sites[0].site.reference.span.clone()], "::Top");
    assert!(sites[0].site.alias.span.start < sites[2].site.alias.span.start);
}

#[test]
fn reports_the_first_conflicting_use_with_both_targets_and_source_ranges() {
    let text = "(namespace app (use ::left x) (use ::left x) (use ::right x))";
    let project = parse_circuit_project(&[
        SourceSnapshot {
            path: "app.ncg2",
            revision: 7,
            text,
        },
        SourceSnapshot {
            path: "library.ncg2",
            revision: 2,
            text: "(namespace left::inside) (namespace right::inside)",
        },
    ])
    .unwrap();
    let targets = index_use_targets(&project).unwrap();
    let UseAliasConflict::BetweenUses { first, later } = check_use_aliases(&targets).unwrap_err()
    else {
        panic!("expected two conflicting use directives");
    };
    assert_eq!(first.site.source.revision, 7);
    assert_eq!(later.site.source.revision, 7);
    assert_eq!(first.site.alias.span.start, text.find("x)").unwrap());
    assert_eq!(later.site.alias.span.start, text.rfind("x)").unwrap());
    assert_eq!(&text[first.site.reference.span.clone()], "::left");
    assert_eq!(&text[later.site.reference.span.clone()], "::right");
    assert!(!first.target.is_same_target(&later.target));
}

#[test]
fn checks_implicit_child_namespaces_from_other_blocks() {
    let text = "(namespace app::gate::inside)";
    for alias in [
        "(namespace app (use ::app::gate gate))",
        "(namespace app (use ::logic gate))",
    ] {
        let project = parse_circuit_project(&[
            SourceSnapshot {
                path: "app.ncg2",
                revision: 3,
                text: alias,
            },
            SourceSnapshot {
                path: "child.ncg2",
                revision: 8,
                text,
            },
            SourceSnapshot {
                path: "logic.ncg2",
                revision: 4,
                text: "(namespace logic)",
            },
        ])
        .unwrap();
        let targets = index_use_targets(&project).unwrap();
        if alias.contains("::app::gate") {
            assert_eq!(
                check_use_aliases(&targets).unwrap().dispositions(),
                [AliasDisposition::Binding]
            );
        } else {
            let UseAliasConflict::Direct {
                directive,
                existing,
            } = check_use_aliases(&targets).unwrap_err()
            else {
                panic!("expected a direct namespace conflict");
            };
            assert_eq!(directive.site.reference.word, "::logic");
            let AbsoluteTarget::Namespace { key, introduced_at } = existing else {
                panic!("expected an implicit child namespace");
            };
            assert_eq!(key.parent, Some("app"));
            assert_eq!(key.name, "gate");
            assert_eq!(introduced_at.source.revision, 8);
            assert_eq!(&text[introduced_at.span], "gate");
        }
    }
}

#[test]
fn resolves_names_from_the_indexed_file_and_block() {
    let project = parse_circuit_project(&[
        SourceSnapshot {
            path: "app.ncg2",
            revision: 2,
            text: concat!(
                "(use ::logic gates) ",
                "(namespace app ",
                "  (module main (in x) (out y) (def y (alias x))) ",
                "  (use ::app::cell alias) (use ::app::cell alias) (use ::app::cell cell)) ",
                "(namespace app (func cell (in x) (out x))) ",
            ),
        },
        SourceSnapshot {
            path: "lib.ncg2",
            revision: 3,
            text: "(namespace app) (namespace logic::inner)",
        },
    ])
    .unwrap();
    let first = &project.circuits()[0];
    let mut blocks = first
        .names
        .iter()
        .filter(|entry| entry.head == Head::Namespace);
    let active = blocks.next().unwrap().form;
    let adjacent = blocks.next().unwrap().form;
    let foreign = project.circuits()[1].names[0].form;
    let module = first
        .names
        .iter()
        .find(|entry| entry.head == Head::Module)
        .unwrap();
    let targets = index_use_targets(&project).unwrap();
    let names = check_use_aliases(&targets).unwrap();

    let Some(UnqualifiedTarget::Alias(alias)) =
        names.resolve_unqualified(0, Some(active), "alias").unwrap()
    else {
        panic!("expected an alias from the whole namespace block");
    };
    assert!(alias.site.alias.span.start < names.directives()[2].site.alias.span.start);
    let Some(UnqualifiedTarget::Alias(coalesced)) =
        names.resolve_unqualified(0, Some(active), "cell").unwrap()
    else {
        panic!("expected a reference with alias provenance");
    };
    let Some(UnqualifiedTarget::Direct(direct)) =
        names.resolve_unqualified(1, Some(foreign), "cell").unwrap()
    else {
        panic!("expected a shared declaration in a different file");
    };
    assert!(alias.target.is_same_target(&direct));
    assert!(coalesced.target.is_same_target(&direct));
    assert!(
        names
            .resolve_unqualified(0, Some(adjacent), "alias")
            .unwrap()
            .is_none()
    );
    assert!(
        names
            .resolve_unqualified(1, Some(foreign), "alias")
            .unwrap()
            .is_none()
    );
    assert!(
        names
            .resolve_unqualified(0, Some(active), "gates")
            .unwrap()
            .is_none()
    );
    assert!(
        names
            .resolve_unqualified(1, None, "gates")
            .unwrap()
            .is_none()
    );
    let Some(UnqualifiedTarget::Alias(namespace)) =
        names.resolve_unqualified(0, None, "gates").unwrap()
    else {
        panic!("expected the file-level namespace alias");
    };
    assert!(
        matches!(namespace.target, AbsoluteTarget::Namespace { key, .. } if key.name == "logic")
    );
    assert!(matches!(
        names.resolve_unqualified(0, Some(module.form), "alias"),
        Err(ReferenceScopeError::UnknownBlock)
    ));
    assert!(matches!(
        names.resolve_unqualified(usize::MAX, None, "alias"),
        Err(ReferenceScopeError::UnknownFile)
    ));
}
