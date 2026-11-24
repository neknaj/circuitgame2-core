use circuitgame2_core::netlist::{ClockedNor, NorGate, NorNetlist, Wire};
use circuitgame2_core::project::{ClockedModuleError, ClockedPlanError, ClockedWireDriver, ModuleBodyPosition, SourceSnapshot,
    check_use_aliases, index_use_targets, parse_circuit_project, plan_clocked_links};

#[test]
fn settling_bound_covers_reversed_dependencies_and_unobserved_gates() {
    use circuitgame2_core::project::clocked_nor_settling_bound;

    let empty = ClockedNor::check(NorNetlist {
        input_count: 1, gates: Vec::new(), outputs: vec![Wire::Input(0)],
    }).unwrap();
    assert_eq!(clocked_nor_settling_bound(&empty), Some(0));

    let chain = ClockedNor::check(NorNetlist {
        input_count: 1,
        gates: vec![
            NorGate { left: Wire::Gate(1), right: Wire::Constant(false) },
            NorGate { left: Wire::Input(0), right: Wire::Input(0) },
        ],
        outputs: vec![Wire::Input(0)],
    }).unwrap();
    assert_eq!(clocked_nor_settling_bound(&chain), Some(2));

    let hidden_oscillator = ClockedNor::check(NorNetlist {
        input_count: 1,
        gates: vec![NorGate { left: Wire::Gate(0), right: Wire::Constant(false) }],
        outputs: vec![Wire::Input(0)],
    }).unwrap();
    assert_eq!(clocked_nor_settling_bound(&hidden_oscillator), None);
}

#[test]
fn oscillator_and_constant_are_observed_from_reset() {
    let circuit = ClockedNor::check(NorNetlist {
        input_count: 0,
        gates: vec![NorGate { left: Wire::Gate(0), right: Wire::Gate(0) }],
        outputs: vec![Wire::Gate(0), Wire::Constant(true)],
    }).unwrap();
    let mut frame = circuit.reset();
    for bit in [false, true, false, true] {
        assert_eq!(frame.outputs, [bit, true]);
        frame = circuit.step(&frame.gates, &[]).unwrap();
    }
}

#[test]
fn cross_coupled_nor_updates_from_the_same_old_state() {
    let circuit = ClockedNor::check(NorNetlist {
        input_count: 2,
        gates: vec![
            NorGate { left: Wire::Input(1), right: Wire::Gate(1) },
            NorGate { left: Wire::Input(0), right: Wire::Gate(0) },
        ],
        outputs: vec![Wire::Gate(0), Wire::Gate(1)],
    }).unwrap();
    let mut frame = circuit.reset();
    assert_eq!(frame.outputs, [false, false]);
    for (input, expected) in [
        ([true, false], [true, false]),
        ([false, false], [true, false]),
        ([false, true], [false, false]),
        ([false, true], [false, true]),
        ([false, false], [false, true]),
    ] {
        frame = circuit.step(&frame.gates, &input).unwrap();
        assert_eq!(frame.outputs, expected);
    }
}

#[test]
fn lowers_a_source_oscillator_with_a_direct_output() {
    let project = parse_circuit_project(&[SourceSnapshot { path: "oscillator.ncg2", revision: 1,
        text: "(using nor) (module oscillator (in pin) (out q pin) (def q (nor q 0)))" }]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let circuit = aliases.lower_clocked_module(ModuleBodyPosition { file: 0, entry: 1 }, 16, 1).unwrap().unwrap();
    let mut frame = circuit.reset();
    assert_eq!(frame.outputs, [false, false]);
    for (pin, q) in [(true, true), (false, false), (true, true)] {
        frame = circuit.step(&frame.gates, &[pin]).unwrap();
        assert_eq!(frame.outputs, [q, pin]);
    }
}

#[test]
fn lowers_a_source_sr_latch_across_module_parts() {
    let project = parse_circuit_project(&[
        SourceSnapshot { path: "latch.ncg2", revision: 2,
            text: "(using nor) (module sr-latch (in set reset) (out q nq) (def q (nor reset nq)))" },
        SourceSnapshot { path: "other.ncg2", revision: 3,
            text: "(module-part sr-latch (def nq (nor set q)))" },
    ]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let parts = targets.collect_module_parts().unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let circuit = aliases.lower_clocked_module(parts[0].module_position, 16, 2).unwrap().unwrap();
    let mut frame = circuit.reset();
    assert_eq!(frame.outputs, [false, false]);
    for (input, expected) in [
        ([true, false], [true, false]),
        ([false, false], [true, false]),
        ([false, true], [false, false]),
        ([false, true], [false, true]),
        ([false, false], [false, true]),
    ] {
        frame = circuit.step(&frame.gates, &input).unwrap();
        assert_eq!(frame.outputs, expected);
    }
}

#[test]
fn an_expanded_func_keeps_gate_delays_and_direct_output_connections() {
    let project = parse_circuit_project(&[SourceSnapshot { path: "buffer.ncg2", revision: 1,
        text: "(using nor) (func buffer (in a) (out y a) (def n (nor a a)) (def y (nor n n)))" }]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let functions = aliases.expand_functions(8, 16, 3).unwrap();
    let buffer = functions.get(0, 1).unwrap().netlist();
    let child = ClockedNor::check(NorNetlist { input_count: buffer.input_count,
        gates: buffer.gates.clone(), outputs: buffer.outputs.clone() }).unwrap();
    let mut gates = Vec::new();
    let outputs = child.append_instance(&mut gates, &[Wire::Gate(2)], 1, 3).unwrap();
    gates.push(NorGate { left: Wire::Input(0), right: Wire::Input(0) });
    let parent = ClockedNor::check(NorNetlist { input_count: 1, gates, outputs }).unwrap();

    let mut frame = parent.reset();
    assert_eq!(frame.outputs, [false, false]);
    for (input, expected) in [
        (true, [true, false]),
        (true, [false, false]),
        (false, [false, true]),
        (false, [false, true]),
        (false, [true, true]),
    ] {
        frame = parent.step(&frame.gates, &[input]).unwrap();
        assert_eq!(frame.outputs, expected);
    }
}

#[test]
fn two_expanded_module_instances_keep_separate_feedback_states() {
    let project = parse_circuit_project(&[SourceSnapshot { path: "branch.ncg2", revision: 1,
        text: "(using nor) (module branch (in hold) (out q) (def q (nor hold q)))" }]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let child = aliases.lower_primitive_module(ModuleBodyPosition { file: 0, entry: 1 }, 8).unwrap().unwrap();
    let mut gates = Vec::new();
    let mut outputs = child.append_instance(&mut gates, &[Wire::Input(0)], 2, 2).unwrap();
    outputs.extend(child.append_instance(&mut gates, &[Wire::Input(1)], 2, 2).unwrap());
    let parent = ClockedNor::check(NorNetlist { input_count: 2, gates, outputs }).unwrap();

    let mut frame = parent.reset();
    assert_eq!(frame.outputs, [false, false]);
    for (input, expected) in [
        ([true, false], [false, true]),
        ([false, false], [true, false]),
        ([false, false], [false, true]),
    ] {
        frame = parent.step(&frame.gates, &input).unwrap();
        assert_eq!(frame.outputs, expected);
    }
}

#[test]
fn resolves_a_forward_output_alias_before_appending_clocked_instances() {
    use ClockedWireDriver::{Alias, Terminal};

    let project = parse_circuit_project(&[SourceSnapshot { path: "branch.ncg2", revision: 1,
        text: "(using nor) (module branch (in a) (out a q) (def q (nor a a)))" }]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let child = aliases.lower_primitive_module(ModuleBodyPosition { file: 0, entry: 1 }, 8).unwrap().unwrap();
    let plan = plan_clocked_links(&[1, 1],
        &[Alias(3), Terminal(Wire::Gate(0)), Terminal(Wire::Input(0)), Terminal(Wire::Gate(1))], 1, 2).unwrap();

    let mut gates = Vec::new();
    let outputs = child.append_instance(&mut gates, &plan.wires[0..1], 1, plan.gate_count).unwrap();
    child.append_instance(&mut gates, &plan.wires[2..3], 1, plan.gate_count).unwrap();
    let parent = ClockedNor::check(NorNetlist { input_count: 1, gates, outputs }).unwrap();
    let mut frame = parent.reset();
    for (input, expected) in [(false, [true, true]), (true, [false, false]), (true, [false, true])] {
        frame = parent.step(&frame.gates, &[input]).unwrap();
        assert_eq!(frame.outputs, expected);
    }
    let cycle = plan_clocked_links(&[0], &[Alias(0)], 0, 0).unwrap_err();
    assert_eq!(cycle, ClockedPlanError::AliasCycle(vec![0]));
}

#[test]
fn lowers_a_parent_and_its_child_calls_from_source() {
    let project = parse_circuit_project(&[
        SourceSnapshot { path: "parent.ncg2", revision: 2,
            text: "(using nor) (module root (in i) (out passed x y) (def (passed x) (child y)))" },
        SourceSnapshot { path: "part.ncg2", revision: 3,
            text: "(module child (in a) (out a q) (def q (leaf a)))
                   (module leaf (in a) (out q) (def q (nor a #x0)))
                   (module unused (in a) (out q) (def q (unused a)))
                   (module-part root (def (echo y) (child i)))" },
    ]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let parts = targets.collect_module_parts().unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let circuit = aliases.lower_clocked_module(parts[0].module_position, 8, 2).unwrap().unwrap();
    let mut frame = circuit.reset();
    for (input, expected) in [(false, [true, true, true]), (true, [false, false, false]), (true, [false, true, false])] {
        frame = circuit.step(&frame.gates, &[input]).unwrap();
        assert_eq!(frame.outputs, expected);
    }
}

#[test]
fn a_module_observes_delayed_function_gates_and_immediate_wires() {
    let project = parse_circuit_project(&[SourceSnapshot {
        path: "root.ncg2", revision: 4,
        text: "(using nor)
               (module root (in a) (out q echo other)
                 (def q (buffer a))
                 (def echo (direct a))
                 (def other (buffer 0)))
               (func invert (in a) (out y) (def y (nor a a)))
               (func buffer (in a) (out y) (def n (invert a)) (def passthrough n) (def y (invert passthrough)) (def copy a))
               (func direct (in a) (out a))",
    }]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let owner = ModuleBodyPosition { file: 0, entry: 1 };
    let Err(ClockedModuleError::PortLayout { direction, site, layout }) =
        aliases.lower_clocked_module_with_limits(owner, 8, 2, 4)
    else { panic!("module output bits must respect the configured limit"); };
    assert!(matches!(direction, circuitgame2_core::project::PortDirection::Output));
    assert!(matches!(layout, circuitgame2_core::netlist::PortBitLayoutError::CapacityExceeded {
        port: 2, width: 1, used: 2, capacity: 2,
    }));
    assert_eq!(&site.source.text[site.span], "other");

    let Err(ClockedModuleError::Function { call, expansion }) =
        aliases.lower_clocked_module_with_limits(owner, 8, 3, 4)
    else { panic!("function definition bits must respect the configured limit"); };
    assert_eq!((call.source.revision, &call.source.text[call.span]), (4, "(buffer a)"));
    assert!(matches!(expansion, circuitgame2_core::project::ExpandFunctionsError::Function { position: (0, 3), .. }));

    let circuit = aliases.lower_clocked_module_with_limits(owner, 8, 4, 4).unwrap().unwrap();
    let mut frame = circuit.reset();
    assert_eq!(frame.gates.len(), 4);
    assert_eq!(frame.outputs, [false, false, false]);
    for (input, expected) in [
        (true, [true, true, true]),
        (true, [true, true, false]),
        (false, [true, false, false]),
        (false, [false, false, false]),
    ] {
        frame = circuit.step(&frame.gates, &[input]).unwrap();
        assert_eq!(frame.outputs, expected);
    }
}

#[test]
fn rejects_reachable_module_recursion_at_the_original_calls() {
    let project = parse_circuit_project(&[
        SourceSnapshot { path: "parent.ncg2", revision: 2,
            text: "(using nor) (module root (in a) (out y))" },
        SourceSnapshot { path: "part.ncg2", revision: 3,
            text: "(module-part root (def y (child a)))" },
        SourceSnapshot { path: "child.ncg2", revision: 4,
            text: "(module child (in a) (out y) (def y (root a)))" },
    ]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let parts = targets.collect_module_parts().unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let Err(ClockedModuleError::Recursion(calls)) =
        aliases.lower_clocked_module(parts[0].module_position, 8, 4)
    else { panic!("reachable recursion must be rejected"); };
    assert_eq!(calls.len(), 2);
    assert_eq!((calls[0].source.revision, &calls[0].source.text[calls[0].span.clone()]), (3, "(child a)"));
    assert_eq!((calls[1].source.revision, &calls[1].source.text[calls[1].span.clone()]), (4, "(root a)"));
}

#[test]
fn identifies_the_source_output_in_a_child_passthrough_cycle() {
    let project = parse_circuit_project(&[SourceSnapshot {
        path: "loop.ncg2", revision: 7,
        text: "(using nor) (module root (in) (out z) (def (z n) (child z)))
               (module child (in a) (out a q) (def q (nor a a)))",
    }]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let Err(ClockedModuleError::AliasCycle(sites)) =
        aliases.lower_clocked_module(ModuleBodyPosition { file: 0, entry: 1 }, 8, 2)
    else { panic!("the direct output is a zero-delay cycle"); };
    let [output] = sites.as_slice() else { panic!("the cycle should contain the direct output only"); };
    assert_eq!(output.source.revision, 7);
    let start = output.source.text.find("(def (z n)").unwrap() + "(def (".len();
    assert_eq!(output.span, start..start + 1);
}


#[test]
fn latch_and_nor_read_the_same_previous_tick() {
    use circuitgame2_core::netlist::{ClockedStorageInputs, ClockedVm};

    let nor = ClockedNor::check(NorNetlist {
        input_count: 1,
        gates: vec![NorGate { left: Wire::Input(0), right: Wire::Constant(false) }],
        outputs: vec![Wire::Gate(0), Wire::Input(0), Wire::Constant(true)],
    }).unwrap();
    let mut vm = ClockedVm::new(nor, 0, vec![ClockedStorageInputs {
        address: None, data: vec![Wire::Gate(0)], enable: Wire::Constant(true),
    }], 1).unwrap();
    assert_eq!(vm.reset(), [false, false, true]);
    for (gate, held) in [(true, false), (true, true), (false, true), (false, false)] {
        assert_eq!(vm.step(&[]).unwrap(), [gate, held, true]);
    }
}

#[test]
fn mixed_vm_observes_read_first_and_keeps_two_ram_instances_separate() {
    use circuitgame2_core::netlist::{
        ClockedStorageError, ClockedStorageInputs, ClockedVm, ClockedVmError, StateAllocationError, TickInputError,
    };

    let circuit = || ClockedNor::check(NorNetlist {
        input_count: 6, gates: vec![], outputs: vec![Wire::Input(4), Wire::Input(5)],
    }).unwrap();
    let wiring = || [Wire::Input(3), Wire::Constant(false)].into_iter().map(|enable| ClockedStorageInputs {
        address: Some(vec![Wire::Input(0), Wire::Input(1)]),
        data: vec![Wire::Input(2)],
        enable,
    }).collect();
    assert!(matches!(ClockedVm::new(circuit(), 4, wiring(), 9),
        Err(ClockedVmError::Storage { instance: 1, error: ClockedStorageError::State(StateAllocationError::Capacity) })));

    let mut vm = ClockedVm::new(circuit(), 4, wiring(), 10).unwrap();
    assert_eq!(vm.reset(), [false, false]);
    assert_eq!(vm.step(&[true, false, true, true]).unwrap(), [false, false]);
    assert_eq!(vm.step(&[true]), Err(TickInputError::InputCount));
    assert_eq!(vm.step(&[true, false, false, false]).unwrap(), [true, false]);
    assert_eq!(vm.step(&[false, true, false, false]).unwrap(), [false, false]);
    assert_eq!(vm.reset(), [false, false]);
    assert_eq!(vm.step(&[true, false, false, false]).unwrap(), [false, false]);
}

#[test]
fn selects_clocked_driver_bits_in_the_signal_port() {
    use circuitgame2_core::netlist::PortBitLayout;
    use circuitgame2_core::project::{CheckedBitSelection, ClockedDriverBitsError, OutputDriver, clocked_driver_bits};

    let inputs = PortBitLayout::from_widths(&[2, 4], 6).unwrap();
    let definitions = PortBitLayout::from_widths(&[5, 4], 9).unwrap();
    let selection = CheckedBitSelection { start: 1, count: 2, stride: 2, last: 3 };
    assert_eq!(clocked_driver_bits(&inputs, &definitions, OutputDriver::Input(1), None).unwrap(),
        [2, 3, 4, 5].map(|bit| ClockedWireDriver::Terminal(Wire::Input(bit))));
    assert_eq!(clocked_driver_bits(&inputs, &definitions, OutputDriver::Input(1), Some(selection)).unwrap(),
        [ClockedWireDriver::Terminal(Wire::Input(3)), ClockedWireDriver::Terminal(Wire::Input(5))]);
    assert_eq!(clocked_driver_bits(&inputs, &definitions, OutputDriver::Definition(1), Some(selection)).unwrap(),
        [ClockedWireDriver::Alias(6), ClockedWireDriver::Alias(8)]);

    let incorrect_last = CheckedBitSelection { last: 2, ..selection };
    assert_eq!(clocked_driver_bits(&inputs, &definitions, OutputDriver::Definition(1), Some(incorrect_last)),
        Err(ClockedDriverBitsError::Last { expected: 3, actual: 2 }));

    let oversized = PortBitLayout::from_widths(&[usize::MAX as u64 - 2, 2], usize::MAX).unwrap();
    let result = clocked_driver_bits(&oversized, &definitions, OutputDriver::Input(0), None);
    assert_eq!(result, Err(ClockedDriverBitsError::Capacity {
        count: usize::MAX as u64 - 2,
        limit: isize::MAX as usize / core::mem::size_of::<ClockedWireDriver>(),
    }));
    assert_eq!(clocked_driver_bits(&oversized, &definitions, OutputDriver::Input(1), None).unwrap(),
        [usize::MAX - 2, usize::MAX - 1].map(|bit| ClockedWireDriver::Terminal(Wire::Input(bit))));
}

#[test]
fn two_instances_of_a_clocked_ram_child_have_separate_state() {
    use circuitgame2_core::netlist::{ClockedStorageInputs, ClockedVm};

    let child = ClockedNor::check(NorNetlist {
        input_count: 4,
        gates: vec![NorGate { left: Wire::Input(1), right: Wire::Constant(false) }],
        outputs: vec![Wire::Input(3), Wire::Gate(0)],
    }).unwrap();
    let storage = [ClockedStorageInputs {
        address: Some(vec![Wire::Input(0)]), data: vec![Wire::Input(1)], enable: Wire::Input(2),
    }];
    let mut gates = Vec::new();
    let mut next_state_input = 6;
    let first = child.append_stateful_instance(&mut gates, &storage,
        &[Wire::Input(0), Wire::Input(1), Wire::Input(2)], &mut next_state_input, 8, 2).unwrap();
    assert_eq!(next_state_input, 7);
    let second = child.append_stateful_instance(&mut gates, &storage,
        &[Wire::Input(3), Wire::Input(4), Wire::Input(5)], &mut next_state_input, 8, 2).unwrap();
    assert_eq!(next_state_input, 8);
    assert_eq!(first.outputs, [Wire::Input(6), Wire::Gate(0)]);
    assert_eq!(second.outputs, [Wire::Input(7), Wire::Gate(1)]);
    let parent = ClockedNor::check(NorNetlist {
        input_count: 8, gates, outputs: first.outputs.into_iter().chain(second.outputs).collect(),
    }).unwrap();
    let mut vm = ClockedVm::new(parent, 6, first.storage.into_iter().chain(second.storage).collect(), 6).unwrap();

    assert_eq!(vm.reset(), [false, false, false, false]);
    assert_eq!(vm.step(&[false, true, true, false, false, false]).unwrap(), [false, false, false, true]);
    assert_eq!(vm.step(&[false, false, false, false, false, false]).unwrap(), [true, true, false, true]);
    assert_eq!(vm.step(&[false, false, false, false, true, true]).unwrap(), [true, true, false, false]);
    assert_eq!(vm.step(&[false, false, false, false, false, false]).unwrap(), [true, true, true, true]);
    assert_eq!(vm.reset(), [false, false, false, false]);
}

#[test]
fn rejects_invalid_child_storage_before_adding_any_gates() {
    use circuitgame2_core::netlist::{ClockedStatefulInstanceError, ClockedStorageInputs};

    let child = ClockedNor::check(NorNetlist {
        input_count: 1,
        gates: vec![NorGate { left: Wire::Input(0), right: Wire::Constant(false) }],
        outputs: vec![Wire::Gate(0)],
    }).unwrap();
    let bad = ClockedStorageInputs { address: None, data: vec![Wire::Input(1)], enable: Wire::Constant(true) };
    let mut next_state_input = 1;
    let mut gates = vec![NorGate { left: Wire::Constant(true), right: Wire::Constant(false) }];
    let prior = gates.clone();
    assert!(matches!(
        child.append_stateful_instance(&mut gates, core::slice::from_ref(&bad), &[Wire::Input(0)],
            &mut next_state_input, 2, 2),
        Err(ClockedStatefulInstanceError::InputLayout)
    ));
    assert!(matches!(
        child.append_stateful_instance(&mut gates, core::slice::from_ref(&bad), &[],
            &mut next_state_input, 1, 2),
        Err(ClockedStatefulInstanceError::StorageCapacity)
    ));
    assert!(matches!(
        child.append_stateful_instance(&mut gates, &[bad], &[], &mut next_state_input, 2, 2),
        Err(ClockedStatefulInstanceError::StoragePins(0))
    ));
    assert_eq!(gates, prior);
    assert_eq!(next_state_input, 1);
}
