use circuitgame2_core::project::{
    DefinitionBinding, ModulePartError, SourceSnapshot, check_use_aliases, index_use_targets, parse_circuit_project,
};
use circuitgame2_core::syntax::circuit::Head;

#[test]
fn resolves_the_owner_across_files_and_preserves_the_part_location() {
    let input = [
        SourceSnapshot {
            path: "owner.ncg2", revision: 13,
            text: "(using nor)
                  (namespace lib (export invert pass)
                    (func invert (in a) (out b) (def b (nor a a)))
                    (func pass (in a) (out a)))
                  (namespace app (use ::lib::invert select)
                    (module main (in a) (out y) (def mid (select a))))",
        },
        SourceSnapshot {
            path: "part.ncg2", revision: 15,
            text: "(namespace app (use ::lib::pass select)
                    (module-part main (def y (select mid))))",
        },
    ];
    let project = parse_circuit_project(&input).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let bindings = targets.collect_module_parts().unwrap();
    assert_eq!(bindings.len(), 1);
    let binding = &bindings[0];
    assert_eq!(binding.part_source.revision, 15);
    assert_eq!(binding.part.block, Some(project.circuits()[1].names[0].form));
    assert_eq!(binding.module_source.revision, 13);
    assert_eq!(binding.module.head, Head::Module);
    let entry = binding.part_position;
    assert_eq!(project.circuits()[entry.file].syntax.entries[entry.entry].form, binding.part.form);
    let aliases = check_use_aliases(&targets).unwrap();
    for (position, expected) in [(binding.module_position, "invert"), (binding.part_position, "pass")] {
        let resolved = aliases.resolve_definition_reference(position.file, position.entry, 0, 0).unwrap();
        let DefinitionBinding::Declaration { form, .. } = resolved.binding else {
            panic!("the call must resolve in its own file and namespace block");
        };
        assert_eq!(form.name.word, expected);
    }
}

#[test]
fn module_part_owner_ignores_aliases_and_reports_other_declaration_kinds() {
    let input = [SourceSnapshot {
        path: "wrong.ncg2", revision: 1,
        text: "(using nor)
              (namespace lib (export other) (module other (in a) (out a)))
              (namespace app (use ::lib::other local)
                (func helper (in a) (out a))
                (module-part local)
                (module-part helper))",
    }];
    let project = parse_circuit_project(&input).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let parts = project.circuits()[0].names.iter().enumerate()
        .filter(|(_, form)| form.head == Head::ModulePart).map(|(index, _)| index).collect::<Vec<_>>();
    let first = targets.collect_module_parts().unwrap_err();
    assert_eq!((first.file, first.name), (0, parts[0]));
    let Err(ModulePartError::MissingModule(part)) = targets.resolve_module_part(0, parts[0]) else {
        panic!("an alias must not bind a module part");
    };
    assert_eq!(&part.source.text[part.span], "local");
    let Err(ModulePartError::WrongTarget { part, target, head: Head::Func }) =
        targets.resolve_module_part(0, parts[1]) else {
        panic!("the target must be a module");
    };
    assert_eq!(&part.source.text[part.span.clone()], "helper");
    assert_eq!(&target.source.text[target.span.clone()], "helper");
    assert!(target.span.start < part.span.start);
}
