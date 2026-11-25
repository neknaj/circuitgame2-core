use circuitgame2_core::project::{
    ModuleBodyPosition, SignalOccurrence, SignalOccurrenceKind, SignalRole, SourceSnapshot,
    check_use_aliases, index_use_targets, parse_circuit_project,
};

fn spelling<'s>(row: &'s SignalOccurrence<'_, '_>) -> &'s str {
    &row.site.source.text[row.site.span.clone()]
}

#[test]
fn observes_function_ports_definitions_and_their_references() {
    let source =
        "(using nor) (func gate (in a b) (out a q) (def tmp (nor a b)) (def q (nor tmp a)))";
    let snapshots = [SourceSnapshot {
        path: "gate.ncg2",
        revision: 7,
        text: source,
    }];
    let project = parse_circuit_project(&snapshots).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let rows = aliases.observe_func_signals(0, 1, 8).unwrap().unwrap();
    let names: Vec<_> = rows.iter().map(spelling).collect();
    assert_eq!(
        names,
        ["a", "b", "a", "q", "tmp", "q", "a", "b", "tmp", "a"]
    );
    use SignalRole::{Input, Local, Output};
    assert_eq!(
        rows.iter().map(|row| row.role).collect::<Vec<_>>(),
        [
            Input, Input, Output, Output, Local, Output, Input, Input, Local, Input
        ]
    );
    assert!(
        rows.iter()
            .all(|row| row.site.source.revision == 7 && row.width == Some(1))
    );
    assert_eq!(rows[2].binding.span, rows[0].site.span);
    assert_eq!(rows[3].binding.span, rows[5].site.span);
    assert_eq!(rows[8].binding.span, rows[4].site.span);
    assert_eq!(rows[2].occurrence, SignalOccurrenceKind::PortDeclaration);
    assert_eq!(rows[5].occurrence, SignalOccurrenceKind::Definition);
    assert_eq!(rows[8].occurrence, SignalOccurrenceKind::Reference);
}

#[test]
fn keeps_module_occurrences_in_the_selected_file_and_bindings_across_files() {
    let root =
        ";; 🌙\n(using nor) (module main (in (a (bits 2))) (out (q (bits 2))) (def q bridge))
        (module-part main (def spare (bit q 0)))";
    let part = ";; 別の文書\n(module-part main (def bridge a))";
    let snapshots = [
        SourceSnapshot {
            path: "root.ncg2",
            revision: 17,
            text: root,
        },
        SourceSnapshot {
            path: "part.ncg2",
            revision: 18,
            text: part,
        },
    ];
    let project = parse_circuit_project(&snapshots).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let owner = ModuleBodyPosition { file: 0, entry: 1 };
    let root_rows = aliases
        .observe_module_signals(owner, 0, 8)
        .unwrap()
        .unwrap();
    let part_rows = aliases
        .observe_module_signals(owner, 1, 8)
        .unwrap()
        .unwrap();
    assert!(root_rows.iter().all(|row| row.site.source.revision == 17));
    assert!(part_rows.iter().all(|row| row.site.source.revision == 18));
    assert_eq!(
        root_rows.iter().map(spelling).collect::<Vec<_>>(),
        ["a", "q", "q", "spare", "bridge", "q"]
    );
    assert_eq!(
        part_rows.iter().map(spelling).collect::<Vec<_>>(),
        ["bridge", "a"]
    );
    assert_eq!(root_rows[4].width, Some(2));
    assert_eq!(root_rows[4].binding.source.revision, 18);
    assert_eq!(root_rows[4].binding.span, part_rows[0].site.span);
    assert_eq!(part_rows[1].binding.source.revision, 17);
    assert_eq!(part_rows[1].binding.span, root_rows[0].site.span);
    assert_eq!(root_rows[3].width, Some(1));
    assert!(
        aliases
            .observe_module_signals(owner, 2, 8)
            .unwrap()
            .is_none()
    );
}
