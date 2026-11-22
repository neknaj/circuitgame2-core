use circuitgame2_core::project::{
    CallInputReason, DefinitionPosition, FuncDriverError, ModuleAliasTypesError, ModuleCallInputsError, ModuleCallPortsError,
    ModuleCallSignatureError, ModuleCallTarget, ModuleDriverError, ModulePartError, ModuleRootTypesError,
    ModuleSelectionsError, ModuleWiringError, OutputDriver, PortDirection, ResolvedPortType, SelectionArgument, SelectionArgumentError,
    SignalType, SourceSnapshot,
    check_use_aliases, index_use_targets, parse_circuit_project,
};
use circuitgame2_core::syntax::circuit::Head;
use circuitgame2_core::syntax::Form;

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
                    (module main (in a) (out y) (def y (select mid))))",
        },
        SourceSnapshot {
            path: "part.ncg2", revision: 15,
            text: "(namespace app (use ::lib::pass select)
                    (module-part main (def mid (select a))))",
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
    let wiring = aliases.check_module_wiring(binding.module_position, 16).unwrap().unwrap();
    let assembly = &wiring.drivers;
    assert_eq!(assembly.body.members, [binding.module_position, binding.part_position]);
    assert_eq!(assembly.origins, assembly.body.members);
    assert_eq!(assembly.outputs, [OutputDriver::Definition(0)]);
    let forward = &wiring.signals[0][0];
    assert_eq!(forward.driver, OutputDriver::Definition(1));
    assert_eq!(forward.definition.body, binding.module_position);
    assert_eq!(&forward.site.source.text[forward.site.span.clone()], "mid");
    assert_eq!(wiring.signals[1][0].driver, OutputDriver::Input(0));
    for (position, expected) in [(binding.module_position, "invert"), (binding.part_position, "pass")] {
        let call = aliases.resolve_module_call_signature(DefinitionPosition {
            file: position.file, entry: position.entry, definition: 0, reference: 0,
        }, 16).unwrap().unwrap();
        assert_eq!(call.source.revision, project.sources()[position.file].revision);
        let ModuleCallTarget::Routine { declaration, signature, .. } = call.target else {
            panic!("the call must resolve in its own file and namespace block");
        };
        assert_eq!(&declaration.source.text[declaration.span], expected);
        assert_eq!(signature.inputs.len(), 1);
    }
}

#[test]
fn reported_signature_violation_keeps_both_call_and_declaration_locations() {
    let input = [
        SourceSnapshot { path: "owner.ncg2", revision: 3,
            text: "(using nor) (module root (in a) (out y))" },
        SourceSnapshot { path: "part.ncg2", revision: 7,
            text: "(module-part root (def y (child a)))" },
        SourceSnapshot { path: "target.ncg2", revision: 11,
            text: "(module child (in (a (bits 2))) (out (a (bits 2))))" },
    ];
    let project = parse_circuit_project(&input).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let part = targets.collect_module_parts().unwrap()[0].part_position;
    let aliases = check_use_aliases(&targets).unwrap();
    let at = DefinitionPosition { file: part.file, entry: part.entry, definition: 0, reference: 0 };
    let call = aliases.resolve_module_call_signature(at, 16).unwrap().unwrap();
    let ModuleCallTarget::Routine { position, signature, .. } = call.target else {
        panic!("the part must resolve a module as its callee");
    };
    assert_eq!(project.circuits()[position.file].syntax.entries[position.entry].head, Head::Module);
    assert!(matches!(signature.inputs[0].ty, ResolvedPortType::Bits(2)));
    let Err(ModuleCallSignatureError::Signature { reference, declaration, .. }) =
        aliases.resolve_module_call_signature(at, 1) else {
        panic!("an invalid target signature must report the call and declaration sites");
    };
    assert_eq!((reference.source.revision, declaration.source.revision), (7, 11));
    assert_eq!(&reference.source.text[reference.span], "child");
    assert_eq!(&declaration.source.text[declaration.span], "child");
}

#[test]
fn matches_direct_arguments_and_distinguishes_root_from_nested_outputs() {
    let input = [
        SourceSnapshot { path: "owner.ncg2", revision: 3,
            text: "(using nor) (module root (in a) (out y z))" },
        SourceSnapshot { path: "part.ncg2", revision: 7,
            text: "(module-part root (def (y z) (pair (nor a a) a))
                  (def nested (nor (pair a a) a)) (def wrong (pair a)) (def single (pair a a))
                  (def (literal-a literal-b) (pair a #b1)))" },
        SourceSnapshot { path: "target.ncg2", revision: 11,
            text: "(func pair (in a (b (bits 2))) (out a (b (bits 2))))" },
    ];
    let project = parse_circuit_project(&input).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let bindings = targets.collect_module_parts().unwrap();
    let part = bindings[0].part_position;
    let owner = bindings[0].module_position;
    let aliases = check_use_aliases(&targets).unwrap();
    let at = |definition, reference| DefinitionPosition { file: part.file, entry: part.entry, definition, reference };
    let ports = aliases.check_module_call_ports(at(0, 0), 16).unwrap().unwrap();
    let forms = &project.circuits()[part.file].syntax.forms;
    let [left, right] = ports.arguments[..] else { panic!("there are two direct arguments"); };
    let Form::List { end, .. } = forms[left] else { panic!("the first argument is a nested call"); };
    assert_eq!(right, end);
    let required = ports.signature.target.port(PortDirection::Input, 1).unwrap();
    assert!(matches!(required.ty, ResolvedPortType::Bits(2)));
    assert_eq!(required.annotation.unwrap().source.revision, 11);
    let signature = aliases.resolve_routine_signature(owner.file, owner.entry, 16).unwrap().unwrap();
    let input = signature.inputs.into_iter().next().unwrap();
    let known = [None, Some(SignalType { ty: input.ty, origin: input.annotation })];
    let Err(ModuleCallInputsError::Argument { index: 1, argument, expected: ResolvedPortType::Bits(2),
        required_at: Some(required), reason: CallInputReason::SignalType(actual) }) =
        aliases.check_module_call_inputs(at(0, 0), 16, &known) else {
        panic!("the known width of a must be checked against the second input port");
    };
    assert_eq!((argument.source.revision, required.source.revision, actual.origin.source.revision), (7, 11, 3));
    assert_eq!(&argument.source.text[argument.span], "a");
    let typed = aliases.check_module_call_inputs(at(4, 0), 16, &[None, None]).unwrap().unwrap();
    let [None, Some(literal)] = typed.types.as_slice() else { panic!("the literal gets its contextual width"); };
    assert!(matches!(literal.ty, ResolvedPortType::Bits(2)));
    assert_eq!(&literal.origin.source.text[literal.origin.span.clone()], "#b1");
    let Err(ModuleCallPortsError::OutputCount { call, left: None, expected: 1, actual: 2, .. }) =
        aliases.check_module_call_ports(at(1, 1), 16) else { panic!("a nested call must return one value"); };
    assert_eq!(&call.source.text[call.span], "(pair a a)");
    let Err(ModuleCallPortsError::InputCount { call, declaration: Some(target), expected: 2, actual: 1 }) =
        aliases.check_module_call_ports(at(2, 0), 16) else { panic!("input count takes precedence"); };
    assert_eq!((call.source.revision, target.source.revision), (7, 11));
    let Err(ModuleCallPortsError::OutputCount { left: Some(left), expected: 1, actual: 2, .. }) =
        aliases.check_module_call_ports(at(3, 0), 16) else { panic!("the root call reports its left-hand side"); };
    assert_eq!(&left.source.text[left.span], "single");
}

#[test]
fn seeds_call_outputs_for_all_fragments_before_checking_forward_inputs() {
    let input = [
        SourceSnapshot { path: "owner.ncg2", revision: 2,
            text: "(using nor) (func pair (in a (b (bits 2))) (out a (b (bits 2))))
                  (module root (in (wide (bits 2))) (out y (z (bits 2)))
                    (def (y z) (pair bridge wide)) (def bridge mid))" },
        SourceSnapshot { path: "part.ncg2", revision: 6,
            text: "(module-part root (def mid (nor (bit z 0) 0)) (def part-copy wide)
                    (def sampled (slice later 0 1 18446744073709551615)) (def later wide)
                    (def selected (bit (slice later 0 2) 1)))" },
    ];
    let project = parse_circuit_project(&input).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let owner = targets.collect_module_parts().unwrap()[0].module_position;
    let aliases = check_use_aliases(&targets).unwrap();
    let selections = aliases.check_module_selections(owner, 16).unwrap().unwrap();
    let resolved = &selections.typed;
    let checked = &resolved.sources;
    let [Some(y), Some(z), None, Some(mid), None, Some(sampled), None, Some(_)] = checked.roots.types.as_slice() else {
        panic!("both calls must seed all their output types");
    };
    assert!(matches!(y.ty, ResolvedPortType::Bits(1)));
    assert!(matches!(z.ty, ResolvedPortType::Bits(2)));
    assert!(matches!(mid.ty, ResolvedPortType::Bits(1)));
    assert_eq!(&z.origin.source.text[z.origin.span.clone()], "2");
    assert_eq!(mid.origin.source.revision, 6);
    assert_eq!(&mid.origin.source.text[mid.origin.span.clone()], "(nor (bit z 0) 0)");
    assert!(matches!(sampled.ty, ResolvedPortType::Bits(1)));
    assert_eq!(&sampled.origin.source.text[sampled.origin.span.clone()], "(slice later 0 1 18446744073709551615)");
    let [None, None, Some(bridge), None, Some(copy), None, Some(_), None] = checked.aliases.as_slice() else {
        panic!("only bare signal references carry alias dependencies");
    };
    assert_eq!(bridge.driver, OutputDriver::Definition(3));
    assert_eq!(&bridge.reference.source.text[bridge.reference.span.clone()], "mid");
    assert_eq!(copy.driver, OutputDriver::Input(0));
    assert_eq!(copy.reference.source.revision, 6);
    let [_, _, Some(bridge), _, Some(copy), _, Some(_), _] = resolved.types.as_slice() else {
        panic!("the aliases must inherit their types from the bound driver");
    };
    assert!(matches!(bridge.ty, ResolvedPortType::Bits(1)));
    assert_eq!((bridge.origin.source.revision, bridge.origin.span.clone()), (6, mid.origin.span.clone()));
    assert!(matches!(copy.ty, ResolvedPortType::Bits(2)));
    assert_eq!(copy.origin.source.revision, 2);
    assert_eq!(selections.selections[5].as_ref().unwrap().projection.stride, u64::MAX);
    let combined = selections.selections[7].as_ref().unwrap();
    assert_eq!(combined.driver, OutputDriver::Definition(6));
    assert_eq!((combined.projection.start, combined.projection.count, combined.projection.last), (1, 1, 1));
}

#[test]
fn reports_the_input_width_origin_of_a_failed_module_selection() {
    let input = [
        SourceSnapshot { path: "owner.ncg2", revision: 2,
            text: "(using nor) (module root (in (wide (bits 2))) (out y))" },
        SourceSnapshot { path: "part.ncg2", revision: 6,
            text: "(module-part root (def y (bit later 2)) (def later wide))" },
    ];
    let project = parse_circuit_project(&input).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let owner = targets.collect_module_parts().unwrap()[0].module_position;
    let aliases = check_use_aliases(&targets).unwrap();
    let Err(ModuleSelectionsError::Argument(SelectionArgumentError::Outside { site, width_origin, input_width: 2, .. })) =
        aliases.check_module_selections(owner, 16) else {
        panic!("the selected bit is outside the width of the forward reference");
    };
    assert_eq!((site.source.revision, width_origin.source.revision), (6, 2));
    assert_eq!(&site.source.text[site.span], "2");
    assert_eq!(&width_origin.source.text[width_origin.span], "2");
}

#[test]
fn reports_selection_numeric_overflow_before_a_zero_count() {
    let input = [
        SourceSnapshot { path: "owner.ncg2", revision: 2,
            text: "(using nor) (module root (in a) (out y))" },
        SourceSnapshot { path: "part.ncg2", revision: 6,
            text: "(module-part root (def y (slice a 0 0 18446744073709551616)))" },
    ];
    let project = parse_circuit_project(&input).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let owner = targets.collect_module_parts().unwrap()[0].module_position;
    let aliases = check_use_aliases(&targets).unwrap();
    let Err(ModuleRootTypesError::SelectionArgument(SelectionArgumentError::NaturalOverflow {
        argument: SelectionArgument::Stride, site,
    })) = aliases.check_module_root_types(owner, 16) else {
        panic!("all explicit arguments must be converted before requiring a positive count");
    };
    assert_eq!(site.source.revision, 6);
    assert_eq!(&site.source.text[site.span], "18446744073709551616");
}

#[test]
fn reports_every_reference_in_a_bare_wire_cycle_across_files() {
    let input = [
        SourceSnapshot { path: "owner.ncg2", revision: 4,
            text: "(using nor) (module ring (in) (out x) (def x y))" },
        SourceSnapshot { path: "part.ncg2", revision: 9,
            text: "(module-part ring (def y x))" },
    ];
    let project = parse_circuit_project(&input).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let owner = targets.collect_module_parts().unwrap()[0].module_position;
    let aliases = check_use_aliases(&targets).unwrap();
    let Err(ModuleAliasTypesError::Cycle(steps)) = aliases.resolve_module_alias_types(owner, 16) else {
        panic!("a cycle of wire aliases has no gate to advance a tick");
    };
    let mut sites: Vec<_> = steps.iter().map(|step| (
        step.definition, step.reference.source.revision, &step.reference.source.text[step.reference.span.clone()],
    )).collect();
    sites.sort_unstable();
    assert_eq!(sites, [(0, 4, "y"), (1, 9, "x")]);
}

#[test]
fn reports_the_first_undefined_signal_at_its_fragment_location() {
    let input = [
        SourceSnapshot { path: "owner.ncg2", revision: 4,
            text: "(using nor) (module main (in a) (out y) (def mid a))" },
        SourceSnapshot { path: "part.ncg2", revision: 9,
            text: "(module-part main (def y (nor missing another)))" },
    ];
    let project = parse_circuit_project(&input).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let owner = targets.resolve_module_part(1, 0).unwrap().module_position;
    let aliases = check_use_aliases(&targets).unwrap();
    let Err(ModuleWiringError::Undefined(site)) = aliases.check_module_wiring(owner, 16) else {
        panic!("an undefined right-hand signal must prevent module assembly");
    };
    assert_eq!(site.source.revision, 9);
    assert_eq!(&site.source.text[site.span], "missing");
}

#[test]
fn reports_conflicting_drivers_at_both_source_revisions() {
    let input = [
        SourceSnapshot { path: "owner.ncg2", revision: 4,
            text: "(using nor) (module main (in a) (out y) (def y a))" },
        SourceSnapshot { path: "part.ncg2", revision: 9,
            text: "(module-part main (def y (nor a a)))" },
    ];
    let project = parse_circuit_project(&input).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let owner = targets.resolve_module_part(1, 0).unwrap().module_position;
    let aliases = check_use_aliases(&targets).unwrap();
    let Err(ModuleDriverError::Signals(FuncDriverError::MultipleDrivers { later, first })) =
        aliases.check_module_drivers(owner, 16) else {
        panic!("the two bodies must share the same signal namespace");
    };
    assert_eq!(first.source.revision, 4);
    assert_eq!(later.source.revision, 9);
    assert_eq!(&first.source.text[first.span], "y");
    assert_eq!(&later.source.text[later.span], "y");
}

#[test]
fn reports_an_unexpanded_macro_in_a_fragment() {
    let input = [
        SourceSnapshot { path: "owner.ncg2", revision: 1,
            text: "(using nor) (module main (in a) (out y))" },
        SourceSnapshot { path: "part.ncg2", revision: 2,
            text: "(module-part main (def other a) (expand make y a))" },
    ];
    let project = parse_circuit_project(&input).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let owner = targets.resolve_module_part(1, 0).unwrap().module_position;
    let aliases = check_use_aliases(&targets).unwrap();
    let Err(ModuleDriverError::NeedsExpansion(site)) = aliases.check_module_drivers(owner, 16) else {
        panic!("module-part expansion must be detected before searching for undriven outputs");
    };
    assert_eq!(site.source.revision, 2);
    assert_eq!(&site.source.text[site.span], "(expand make y a)");
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
