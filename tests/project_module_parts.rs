use circuitgame2_core::project::{
    CallInputReason, DefinitionPosition, FuncDriverError, ModuleAliasTypesError, ModuleCallInputsError, ModuleCallPortsError,
    ConcatResultWidthError, ModuleCallSignatureError, ModuleCallTarget, ModuleConcatsError,
    ModuleCallsError, ModuleDriverError, ModuleInferredCallError, ModuleOutputTypesError, ModulePartError, ModuleRootTypesError,
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
fn checks_concat_width_and_operand_order_across_module_parts() {
    let input = [
        SourceSnapshot { path: "owner.ncg2", revision: 2,
            text: "(using nor) (module root (in (wide (bits 2))) (out (wide (bits 2)) picked))" },
        SourceSnapshot { path: "part.ncg2", revision: 6,
            text: "(module-part root (def first (concat relay #b1)) (def relay joined)
                    (def joined (concat later #b01)) (def later wide)
                    (def immediate (concat wide #b111)) (def picked (bit relay 3)))" },
    ];
    let project = parse_circuit_project(&input).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let owner = targets.collect_module_parts().unwrap()[0].module_position;
    let aliases = check_use_aliases(&targets).unwrap();
    let checked = aliases.check_module_concats(owner, 16).unwrap().unwrap();
    let first = checked.concats[0].as_ref().unwrap();
    assert!(matches!(first.result.ty, ResolvedPortType::Bits(5)));
    let relay = checked.types[1].as_ref().unwrap();
    assert!(matches!(relay.ty, ResolvedPortType::Bits(4)));
    assert_eq!(&relay.origin.source.text[relay.origin.span.clone()], "(concat later #b01)");
    let concat = checked.concats[2].as_ref().unwrap();
    assert!(matches!(concat.result.ty, ResolvedPortType::Bits(4)));
    assert_eq!(&concat.result.origin.source.text[concat.result.origin.span.clone()], "(concat later #b01)");
    let [low, high] = concat.operands.as_slice() else { panic!("there must be two operands"); };
    assert_eq!((low.driver, low.width, high.driver, high.width), (Some(OutputDriver::Definition(3)), 2, None, 2));
    let outputs = aliases.check_module_output_types(owner, 16).unwrap().unwrap();
    let picked = outputs.expressions.selections[5].as_ref().unwrap();
    assert_eq!((picked.driver, picked.projection.last), (OutputDriver::Definition(1), 3));
    let [Some(direct), Some(selected)] = outputs.outputs.as_slice() else { panic!("both output types should agree"); };
    assert_eq!((direct.origin.source.revision, selected.origin.source.revision), (2, 6));
    let Err(ModuleConcatsError::Width { concat, reason: ConcatResultWidthError::ConfiguredLimit { limit: 3, actual: 4 } }) =
        aliases.check_module_concats(owner, 3) else { panic!("the result exceeds the configured width limit"); };
    assert_eq!((concat.source.revision, &concat.source.text[concat.span]), (6, "(concat later #b01)"));
    let Err(ModuleConcatsError::Width { concat, reason: ConcatResultWidthError::ConfiguredLimit { limit: 4, actual: 5 } }) =
        aliases.check_module_concats(owner, 4) else { panic!("the later seed lets the earlier failure become visible"); };
    assert_eq!(&concat.source.text[concat.span], "(concat relay #b1)");
}

#[test]
fn module_output_type_check_reports_distinct_layout_names_after_a_pending_port() {
    let input = [
        SourceSnapshot { path: "owner.ncg2", revision: 2,
            text: "(using nor) (struct Left (width 2)) (struct Right (width 2))
                   (module root (in (a Left)) (out pending (y Right)))" },
        SourceSnapshot { path: "part.ncg2", revision: 6,
            text: "(module-part root (def pending 0) (def y a))" },
    ];
    let project = parse_circuit_project(&input).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let owner = targets.collect_module_parts().unwrap()[0].module_position;
    let aliases = check_use_aliases(&targets).unwrap();
    let Err(ModuleOutputTypesError::Mismatch { index: 1, expected, actual }) = aliases.check_module_output_types(owner, 16) else {
        panic!("distinct structures of the same bit width must not agree");
    };
    assert_eq!(&expected.origin.source.text[expected.origin.span], "Right");
    assert_eq!(&actual.origin.source.text[actual.origin.span], "Left");
}

#[test]
fn module_call_checks_the_type_of_a_bound_forward_signal() {
    let input = [
        SourceSnapshot { path: "owner.ncg2", revision: 2,
            text: "(using nor) (module root (in a) (out y))" },
        SourceSnapshot { path: "part.ncg2", revision: 6,
            text: "(module-part root (def y (nor bus 0)) (def correct (nor a 0)))" },
        SourceSnapshot { path: "signals.ncg2", revision: 9,
            text: "(module-part root (def bus (concat a a)))" },
    ];
    let project = parse_circuit_project(&input).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let bindings = targets.collect_module_parts().unwrap();
    let owner = bindings[0].module_position;
    let part = bindings[0].part_position;
    let aliases = check_use_aliases(&targets).unwrap();
    let at = |definition| DefinitionPosition { file: part.file, entry: part.entry, definition, reference: 0 };
    let Err(ModuleInferredCallError::Call(ModuleCallInputsError::Argument {
        index: 0, argument, expected: ResolvedPortType::Bits(1), required_at: None, reason: CallInputReason::SignalType(actual),
    })) = aliases.check_module_call_with_inferred_types(owner, at(0), 16) else {
        panic!("the forward reference to bus supplies two bits");
    };
    assert!(matches!(actual.ty, ResolvedPortType::Bits(2)));
    assert_eq!((argument.source.revision, actual.origin.source.revision), (6, 9));
    assert_eq!(&argument.source.text[argument.span], "bus");
    assert_eq!(&actual.origin.source.text[actual.origin.span], "(concat a a)");
    let call = aliases.check_module_call_with_inferred_types(owner, at(1), 16).unwrap().unwrap();
    let [Some(signal), Some(literal)] = call.types.as_slice() else { panic!("both input types should agree"); };
    assert_eq!((signal.origin.source.revision, literal.origin.source.revision), (2, 6));
}

#[test]
fn module_call_batch_checks_nested_calls_in_fragment_order() {
    for (argument, expect_error) in [("wide", true), ("a", false)] {
        let fragment = format!("(module-part root (def y (bit (nor a {argument}) 0)) (def z (nor a 0)))");
        let input = [
            SourceSnapshot { path: "owner.ncg2", revision: 2,
                text: "(using nor) (module root (in a) (out y) (def wide (concat a a)) (def w (nor a 1)))" },
            SourceSnapshot { path: "part.ncg2", revision: 6, text: &fragment },
        ];
        let project = parse_circuit_project(&input).unwrap();
        let targets = index_use_targets(&project).unwrap();
        let bindings = targets.collect_module_parts().unwrap();
        let owner = bindings[0].module_position;
        let part = bindings[0].part_position;
        let aliases = check_use_aliases(&targets).unwrap();
        let at = |position: circuitgame2_core::project::ModuleBodyPosition, definition| DefinitionPosition {
            file: position.file, entry: position.entry, definition, reference: 0,
        };
        let result = aliases.check_module_calls(owner, 16);
        if expect_error {
            let Err(ModuleCallsError::Call { at: location, reason: ModuleCallInputsError::Argument {
                index: 1, argument, reason: CallInputReason::SignalType(origin), ..
            } }) = result else { panic!("the nested NOR must reject the wide input"); };
            assert_eq!(location, at(part, 0));
            assert_eq!(&argument.source.text[argument.span], "wide");
            assert_eq!(&origin.origin.source.text[origin.origin.span], "(concat a a)");
        } else {
            let checked = result.unwrap().unwrap();
            let actual: Vec<_> = checked.calls.iter().map(|call| call.at).collect();
            assert_eq!(actual, [at(owner, 1), at(part, 0), at(part, 1)]);
        }
    }
}

#[test]
fn module_call_checks_child_output_type_without_reordering_child_diagnostics() {
    for (arguments, reference, bad_argument, child_output) in [
        ("(wide-pass wide) bit1", 0, "(wide-pass wide)", true),
        ("(wide-pass) wide", 0, "wide", false),
        ("(wide-pass) bit1", 1, "(wide-pass)", false),
    ] {
        let fragment = format!("(module-part root (def y (nor {arguments})))");
        let input = [
            SourceSnapshot { path: "owner.ncg2", revision: 2,
                text: "(using nor) (func wide-pass (in (x (bits 2))) (out (x (bits 2))))
                       (module root (in bit1 (wide (bits 2))) (out y))" },
            SourceSnapshot { path: "fragment.ncg2", revision: 6, text: &fragment },
        ];
        let project = parse_circuit_project(&input).unwrap();
        let targets = index_use_targets(&project).unwrap();
        let bindings = targets.collect_module_parts().unwrap();
        let owner = bindings[0].module_position;
        let part = bindings[0].part_position;
        let aliases = check_use_aliases(&targets).unwrap();
        let Err(ModuleCallsError::Call { at, reason }) = aliases.check_module_calls(owner, 16) else {
            panic!("the parent or child must report a call error");
        };
        assert_eq!(at, DefinitionPosition { file: part.file, entry: part.entry, definition: 0, reference });
        match reason {
            ModuleCallInputsError::Argument { index, argument, reason: CallInputReason::SignalType(actual), .. } => {
                assert_eq!(reference, 0);
                assert_eq!(index, if child_output { 0 } else { 1 });
                assert_eq!(&argument.source.text[argument.span], bad_argument);
                assert!(matches!(actual.ty, ResolvedPortType::Bits(2)));
                if child_output {
                    assert_eq!(actual.origin.source.revision, 2);
                    let output = "(out (x (bits ";
                    let width = actual.origin.source.text.find(output).unwrap() + output.len();
                    assert_eq!(actual.origin.span, width..width + 1);
                }
            },
            ModuleCallInputsError::Ports(ModuleCallPortsError::InputCount { call, expected: 1, actual: 0, .. }) => {
                assert_eq!(reference, 1);
                assert_eq!(&call.source.text[call.span], bad_argument);
            },
            error => panic!("unexpected error: {error:?}"),
        }
    }
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

    use circuitgame2_core::project::{ClockedEndpointError, ClockedModuleVmError, ClockedModuleVmLimits,
        ModuleCallsError, ModuleOutputTypesError};
    let limits = ClockedModuleVmLimits { width: 16, wiring_bits: 2, gates: 0, state_bits: 0 };
    let Err(ClockedModuleVmError::Endpoints(ClockedEndpointError::Calls(ModuleCallsError::Module(
        ModuleOutputTypesError::Expressions(ModuleSelectionsError::Types(ModuleAliasTypesError::Cycle(compiled_steps))),
    )))) = aliases.lower_clocked_vm(owner, limits) else {
        panic!("the checked circuit must report the source alias cycle");
    };
    assert_eq!(compiled_steps.len(), steps.len());
    for (actual, expected) in compiled_steps.iter().zip(&steps) {
        assert_eq!(actual.definition, expected.definition);
        assert_eq!(actual.reference.source.revision, expected.reference.source.revision);
        assert_eq!(actual.reference.span, expected.reference.span);
    }
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


#[test]
fn checks_storage_calls_with_types_from_their_declaration_scope() {
    let project = parse_circuit_project(&[
        SourceSnapshot { path: "app.ncg2", revision: 17,
            text: "(using nor)
                (namespace app
                  (struct Word (width 8))
                  (module root (in (address (bits 2)) (payload ::lib::Word) enable)
                    (out (observed ::lib::Word) (held (bits 2)))
                    (def observed (::lib::ram address payload enable))
                    (def held (::lib::hold address enable))))" },
        SourceSnapshot { path: "lib.ncg2", revision: 21,
            text: "(namespace lib
                    (struct Word (width 8))
                    (memory ram (address 2) (data Word))
                    (latch hold (width 2))
                    (export Word ram hold))" },
    ]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let entry = project.circuits()[0].syntax.entries.iter().position(|item| item.head == Head::Module).unwrap();
    let owner = circuitgame2_core::project::ModuleBodyPosition { file: 0, entry };
    let checked = aliases.check_module_calls(owner, 16).unwrap().unwrap();
    let [ram, latch] = checked.calls.as_slice() else { panic!("expected the RAM and latch calls"); };
    let target = &ram.inputs.ports.signature.target;
    let data = target.port(PortDirection::Input, 1).unwrap();
    let output = target.port(PortDirection::Output, 0).unwrap();
    assert!(data.ty.is_same_type(&output.ty));
    assert!(matches!(data.ty, ResolvedPortType::Struct { source, .. } if source.revision == 21));
    let annotation = data.annotation.unwrap();
    assert_eq!(&annotation.source.text[annotation.span.clone()], "Word");
    let enable = target.port(PortDirection::Input, 2).unwrap();
    assert!(matches!(enable.ty, ResolvedPortType::Bits(1)) && enable.annotation.is_none());
    let output = latch.inputs.ports.signature.target.port(PortDirection::Output, 0).unwrap();
    assert!(matches!(output.ty, ResolvedPortType::Bits(2)));
}


#[test]
fn places_struct_ram_outputs_in_call_order_across_module_parts() {
    use circuitgame2_core::netlist::{ClockedVmError, PortBitLayoutError, Wire};
    use circuitgame2_core::project::{
        ClockedDefinitionLayoutError, ClockedModuleVmError, ClockedModuleVmLimits, ClockedStorageLayoutError,
        ClockedWireDriver, ModuleBodyPosition,
    };

    let input = [
        SourceSnapshot { path: "main.ncg2", revision: 5,
            text: "(using nor)
                (struct Word (width 8))
                (memory bank (address 2) (data Word))
                (module root (in (a (bits 2)) (d Word) we) (out (a (bits 2)) (first Word) (second Word))
                  (def first (bank a d we)))" },
        SourceSnapshot { path: "part.ncg2", revision: 7, text: "(module-part root (def second (bank #b1 d we)))" },
    ];
    let project = parse_circuit_project(&input).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let entry = project.circuits()[0].syntax.entries.iter().position(|entry| entry.head == Head::Module).unwrap();
    let owner = ModuleBodyPosition { file: 0, entry };
    let definitions = aliases.plan_clocked_definitions(owner, 16, 16).unwrap().unwrap();
    assert_eq!(definitions.ranges(), [0..8, 8..16]);
    let Err(ClockedDefinitionLayoutError::Capacity {
        definition,
        layout: PortBitLayoutError::CapacityExceeded { port: 1, used: 8, width: 8, capacity: 15 },
    }) = aliases.plan_clocked_definitions(owner, 16, 15) else { panic!("the second definition exceeds the limit"); };
    assert_eq!(definition.source.revision, 7);
    assert_eq!(&definition.source.text[definition.span], "second");

    let output_plan = aliases.plan_clocked_outputs(owner, 16, 18).unwrap().unwrap();
    assert_eq!(output_plan.inputs.ranges(), [0..2, 2..10, 10..11]);
    assert_eq!(output_plan.outputs.ranges(), [0..2, 2..10, 10..18]);
    assert_eq!(output_plan.drivers[0], [0, 1].map(|i| ClockedWireDriver::Terminal(Wire::Input(i))));
    assert_eq!(output_plan.drivers[1], core::array::from_fn::<_, 8, _>(ClockedWireDriver::Alias));
    assert_eq!(output_plan.drivers[2], core::array::from_fn::<_, 8, _>(|i| ClockedWireDriver::Alias(8 + i)));

    let plan = aliases.plan_clocked_storage(owner, 16, 11, 27).unwrap().unwrap();
    let [first, second] = plan.instances.as_slice() else { panic!("expected two calls"); };
    assert_eq!((first.call.source.revision, second.call.source.revision), (5, 7));
    assert_eq!((first.outputs.clone(), second.outputs.clone()), (11..19, 19..27));
    let Err(ClockedStorageLayoutError::Capacity { call, annotation, used: 19, width: 8 }) =
        aliases.plan_clocked_storage(owner, 16, 11, 26) else { panic!("the second call exceeds the limit"); };
    assert_eq!((call.source.revision, annotation.source.revision), (7, 5));
    assert_eq!(&annotation.source.text[annotation.span], "Word");

    let limits = ClockedModuleVmLimits { width: 16, wiring_bits: 27, gates: 0, state_bits: 80 };
    let Err(ClockedModuleVmError::Vm(ClockedVmError::Storage { instance: 1, .. }, Some(site))) =
        aliases.lower_clocked_vm(owner, ClockedModuleVmLimits { state_bits: 40, ..limits })
    else { panic!("the second RAM exceeds the state budget"); };
    assert_eq!(site.source.revision, 7);
    assert_eq!(&site.source.text[site.span], "(bank #b1 d we)");

    let mut compiled = aliases.lower_clocked_vm(owner, limits).unwrap().unwrap();
    assert_eq!(compiled.outputs.ranges(), [0..2, 2..10, 10..18]);
    assert_eq!(compiled.vm.reset(), [false; 18]);
    let mut frame = [false; 11];
    frame[2] = true;
    frame[10] = true;
    assert_eq!(compiled.vm.step(&frame).unwrap(), [false; 18]);
    frame[10] = false;
    let mut expected = [false; 18];
    expected[2] = true;
    expected[10] = true;
    assert_eq!(compiled.vm.step(&frame).unwrap(), expected);
}

#[test]
fn lowers_nor_and_latch_to_one_tick_machine() {
    use circuitgame2_core::project::{ClockedModuleVmLimits, ModuleBodyPosition};

    let input = [SourceSnapshot { path: "main.ncg2", revision: 5,
        text: "(using nor)
            (latch hold (width 1))
            (module root (in (d (bits 4)) we) (out q mixed)
              (def q (hold (bit (slice d 1 2 2) 1) we))
              (def mixed (nor q 0)))" }];
    let project = parse_circuit_project(&input).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let entry = project.circuits()[0].syntax.entries.iter().position(|entry| entry.head == Head::Module).unwrap();
    let owner = ModuleBodyPosition { file: 0, entry };
    let limits = ClockedModuleVmLimits { width: 8, wiring_bits: 8, gates: 1, state_bits: 1 };
    let mut compiled = aliases.lower_clocked_vm(owner, limits).unwrap().unwrap();
    assert_eq!(compiled.vm.reset(), [false, false]);
    assert_eq!(compiled.vm.step(&[false, false, false, true, true]).unwrap(), [true, true]);
    assert_eq!(compiled.vm.step(&[false, false, false, false, false]).unwrap(), [true, false]);
}

#[test]
fn lowers_forward_aliases_across_parts_without_consuming_calls() {
    use circuitgame2_core::project::ClockedModuleVmLimits;

    let input = [
        SourceSnapshot { path: "root.ncg2", revision: 3, text:
            "(using nor) (latch hold (width 2))
             (module root (in (data (bits 2)) enable) (out (q-copy (bits 2)) n)
               (def q-copy q) (def d data))" },
        SourceSnapshot { path: "part.ncg2", revision: 9, text:
            "(module-part root
               (def q (hold d enable))
               (def n (nor (bit q-copy 1) 0)))" },
    ];
    let project = parse_circuit_project(&input).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let owner = targets.collect_module_parts().unwrap()[0].module_position;
    let aliases = check_use_aliases(&targets).unwrap();
    let limits = ClockedModuleVmLimits { width: 2, wiring_bits: 8, gates: 1, state_bits: 2 };
    let mut compiled = aliases.lower_clocked_vm(owner, limits).unwrap().unwrap();
    assert_eq!(compiled.vm.reset(), [false, false, false]);
    assert_eq!(compiled.vm.step(&[false, true, true]).unwrap(), [false, true, true]);
    assert_eq!(compiled.vm.step(&[true, false, false]).unwrap(), [false, true, false]);
}

#[test]
fn reports_selection_in_a_call_at_the_argument_and_input_declaration() {
    use circuitgame2_core::project::{ClockedArgumentWiringError, ClockedModuleVmError, ClockedModuleVmLimits};

    let limits = ClockedModuleVmLimits { width: 8, wiring_bits: 8, gates: 1, state_bits: 1 };
    for argument in ["(bit d 4)", "(slice d 0 2)"] {
        let body = format!("(module-part root (def q (hold {argument} we)))");
        let input = [
            SourceSnapshot { path: "root.ncg2", revision: 3, text:
                "(using nor) (latch hold (width 1)) (module root (in (d (bits 4)) we) (out q))" },
            SourceSnapshot { path: "part.ncg2", revision: 9, text: &body },
        ];
        let project = parse_circuit_project(&input).unwrap();
        let targets = index_use_targets(&project).unwrap();
        let owner = targets.collect_module_parts().unwrap()[0].module_position;
        let aliases = check_use_aliases(&targets).unwrap();
        match aliases.lower_clocked_vm(owner, limits) {
            Err(ClockedModuleVmError::Arguments(ClockedArgumentWiringError::Selection(
                ModuleSelectionsError::Argument(SelectionArgumentError::Outside {
                    site, width_origin, start: 4, last: 4, input_width: 4,
                }),
            ))) if argument == "(bit d 4)" => {
                assert_eq!((site.source.revision, width_origin.source.revision), (9, 3));
                assert_eq!(&site.source.text[site.span], "4");
                assert_eq!(&width_origin.source.text[width_origin.span], "4");
            },
            Err(ClockedModuleVmError::Arguments(ClockedArgumentWiringError::SelectionPort {
                argument: site, expected: ResolvedPortType::Bits(1), required_at: Some(required), width: 2,
            })) if argument == "(slice d 0 2)" => {
                assert_eq!((site.source.revision, required.source.revision), (9, 3));
                assert_eq!(&site.source.text[site.span], argument);
                assert_eq!(&required.source.text[required.span], "1");
            },
            _ => panic!("expected a selection diagnostic for {argument}"),
        }
    }
}
