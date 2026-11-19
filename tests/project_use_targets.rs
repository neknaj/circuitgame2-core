use circuitgame2_core::project::{
    AbsoluteTarget, ExportError, SourceSnapshot, UseTargetError, index_use_targets,
    parse_circuit_project,
};

fn snapshot<'a>(path: &'a str, revision: u64, text: &'a str) -> SourceSnapshot<'a> {
    SourceSnapshot {
        path,
        revision,
        text,
    }
}

#[test]
fn resolves_all_use_targets_and_preserves_their_distinct_scopes() {
    let first = concat!(
        "; 別名の位置を確認する\n",
        "(use ::logic::public rootAlias) ",
        "(namespace app (use ::app::same inv) (use ::app::same inv)) ",
        "(namespace app (use ::logic logicAlias))",
    );
    let second = "(use ::logic::public rootAlias) ";
    let definitions = "(namespace logic (struct public (width 1)) (export public)) (namespace app (struct same (width 1)))";
    let project = parse_circuit_project(&[
        snapshot("./client.ncg2", 12, first),
        snapshot("second.ncg2", 3, second),
        snapshot("definitions.ncg2", 1, definitions),
    ])
    .unwrap();
    let result = index_use_targets(&project).unwrap();
    let directives = result.directives();
    assert_eq!(directives.len(), 5);
    assert_eq!(
        directives
            .iter()
            .map(|item| item.site.alias.word)
            .collect::<Vec<_>>(),
        ["rootAlias", "inv", "inv", "logicAlias", "rootAlias"]
    );
    for (index, directive) in directives.iter().enumerate() {
        let site = &directive.site;
        let source = if index == 4 { second } else { first };
        assert_eq!(site.source.text, source);
        assert_eq!(&source[site.alias.span.clone()], site.alias.word);
        assert_eq!(&source[site.reference.span.clone()], site.reference.word);
    }
    assert!(directives[0].site.block.is_none() && directives[4].site.block.is_none());
    assert!(
        !directives[0]
            .site
            .source
            .id
            .same_file(&directives[4].site.source.id)
    );
    assert_eq!(directives[1].site.block, directives[2].site.block);
    assert_ne!(directives[1].site.block, directives[3].site.block);
    assert_eq!(directives[1].site.namespace, Some("app"));
    assert_eq!(directives[1].site.namespace, directives[3].site.namespace);
    assert!(
        matches!(directives[1].target, AbsoluteTarget::Declaration { form, .. } if form.name.word == "same")
    );
    assert!(
        matches!(directives[3].target, AbsoluteTarget::Namespace { key, .. } if key.name == "logic")
    );
}

#[test]
fn reports_the_first_unresolved_reference_and_its_private_declaration() {
    let use_text = "; 参照先の位置\n(use ::inner::hidden alias) (use ::missing later)";
    let definitions = "(namespace inner (struct hidden (width 1)))";
    let project = parse_circuit_project(&[
        snapshot("client.ncg2", 14, use_text),
        snapshot("lib/./defs.ncg2", 8, definitions),
    ])
    .unwrap();
    let error = index_use_targets(&project).unwrap_err();
    let UseTargetError::Private { site, declaration } = error else {
        panic!("expected a private declaration: {error:?}");
    };
    assert_eq!(site.source.id.components(), ["client.ncg2"]);
    assert_eq!(site.source.revision, 14);
    assert_eq!(&use_text[site.reference.span], "::inner::hidden");
    assert_eq!(&use_text[site.alias.span], "alias");
    assert_eq!(declaration.source.id.components(), ["lib", "defs.ncg2"]);
    assert_eq!(declaration.source.revision, 8);
    assert_eq!(&definitions[declaration.span], "hidden");
}

#[test]
fn resolves_fully_qualified_references_without_using_other_aliases() {
    let text = "(struct declared (width 1)) (use ::declared alias) (use ::alias chained)";
    let project = parse_circuit_project(&[snapshot("main.ncg2", 2, text)]).unwrap();
    let error = index_use_targets(&project).unwrap_err();
    let UseTargetError::Missing(site) = error else {
        panic!("expected an unresolved declaration: {error:?}");
    };
    assert_eq!(&text[site.reference.span], "::alias");
    assert_eq!(site.alias.word, "chained");
}

#[test]
fn checks_exports_before_resolving_use_targets() {
    let text = "(use ::unknown alias) (export missing)";
    let project = parse_circuit_project(&[snapshot("main.ncg2", 2, text)]).unwrap();
    assert!(matches!(
        index_use_targets(&project),
        Err(UseTargetError::Export(ExportError::MissingDeclaration(_)))
    ));
}
