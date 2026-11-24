//! 直接の実引数からビット選択をたどり、元の信号と射影を求める。

use super::{ClockedArgumentWiringError, ClockedModuleOutputs, ClockedWireDriver, ModuleCalls, UseAliases};
use super::super::{concats::find_signal, selections::read_bound_type};
use crate::project::{CallPortType, CheckedBitSelection, ModuleBodyPosition, ModuleSelectionsError,
    OutputDriver, ResolvedPortType, circuits::form_location, clocked_driver_bits};
use crate::project::use_aliases::{function_atoms::copy_location, selection_arguments::check_selection_chain};
use crate::syntax::{AtomKind, Form, circuit::bit_selection_chain};
#[cfg(verus_only)]
use super::super::{clocked_driver_bits_result, driver_bits::{checked_selection_wiring_error, clocked_selected_port_bits, clocked_selected_port_ready}, selections::bound_type};
#[cfg(verus_only)]
use crate::project::{PortDirection, circuits::{is_form_location, parsed_index_evidence}};
#[cfg(verus_only)]
use crate::project::use_aliases::selection_arguments::selection_chain_arguments_match;
#[cfg(verus_only)]
use crate::syntax::circuit::{BitSelectionShape, bit_selection_path, bit_selection_shape_matches, bit_selection_shape_positions,
    bit_selection_step_root, build_definition_scope_evidence, build_entry_ranges_evidence, call_argument_position_bounds,
    call_argument_position_is_direct, definition_signal_positions_in_order, indexed_call_selection_leaf};
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

struct SelectedPort {
    driver: OutputDriver,
    projection: CheckedBitSelection,
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    #[verifier::opaque]
    spec fn selection_at_argument(
        &self, checked: &ModuleCalls, limit: u64, index: usize, arg: usize,
        result: Result<Option<SelectedPort>, ClockedArgumentWiringError>,
    ) -> bool {
        let call = checked.calls@[index as int];
        let source = call.inputs.ports.signature.source;
        let parsed = self.targets.project_model().circuits_model()[call.at.file as int];
        let frame = parsed.entry_ranges@[call.at.entry as int];
        let row = parsed.definitions@[frame.definitions.start + call.at.definition];
        let forms = parsed.syntax.forms@;
        let root = call.inputs.ports.arguments@[arg as int];
        let wiring = &checked.module.expressions.typed.sources.roots.wiring;
        exists|steps: Seq<BitSelectionShape>, leaf: usize|
            #[trigger] bit_selection_path(source.text, forms, root, steps, leaf)
            && !(exists|shape: BitSelectionShape| #[trigger] bit_selection_shape_matches(source.text, forms, leaf as int, shape))
            && if steps.len() == 0 || !(forms[leaf as int] is Atom && forms[leaf as int]->Atom_kind is Name) {
                result == Ok(None)
            } else {
                let signals = parsed.signals@;
                exists|position: int| row.signals.start <= position < row.signals.end
                        && #[trigger] signals[position] == leaf && {
                            let bound = wiring.signals@[call.member as int]@[position - frame.signals.start];
                            let ty = bound_type(&checked.module.expressions.typed, checked.module.expressions.types@, bound.driver);
                            &&& bound.form == leaf
                            &&& match ty {
                                None => false,
                                Some(actual) => match actual.ty {
                                    ResolvedPortType::Struct { .. } =>
                                        result matches Err(ClockedArgumentWiringError::Selection(ModuleSelectionsError::InputType { input, actual: found }))
                                            && found == actual && is_form_location(source, forms[leaf as int], input),
                                    ResolvedPortType::Bits(width) => match result {
                                        Ok(Some(selected)) => selected.driver == bound.driver && selected.projection.count <= limit
                                            && selection_chain_arguments_match(source, forms, steps, width, actual.origin, Ok(selected.projection)),
                                        Err(ClockedArgumentWiringError::Selection(ModuleSelectionsError::Argument(error))) =>
                                            selection_chain_arguments_match(source, forms, steps, width, actual.origin, Err(error)),
                                        Err(ClockedArgumentWiringError::Selection(ModuleSelectionsError::Width { expression, width: count, limit: cap })) =>
                                            is_form_location(source, forms[root as int], expression) && cap == limit && count > limit
                                            && exists|projection: CheckedBitSelection| #[trigger]
                                                selection_chain_arguments_match(source, forms, steps, width, actual.origin, Ok(projection))
                                                    && projection.count == count,
                                        _ => false,
                                    },
                                },
                            }
                        }
            }
    }

    fn check_argument_selection(
        &self, _owner: ModuleBodyPosition, limit: u64, _capacity: usize, _plan: &ClockedModuleOutputs, checked: &ModuleCalls<'p, 'a>, index: usize, arg: usize,
    ) -> (result: Result<Option<SelectedPort>, ClockedArgumentWiringError<'p, 'a>>)
        requires
            self.can_resolve(), self.module_calls_result(_owner, limit, Ok(Some(*checked))),
            index < checked.calls@.len(), arg < checked.calls@[index as int].inputs.ports.arguments@.len(),
            self.outputs_on_checked(&checked.module, limit, _capacity, Ok(*_plan)),
        ensures self.selection_at_argument(checked, limit, index, arg, result),
            result matches Ok(Some(selected)) ==>
                clocked_selected_port_ready(&_plan.inputs, &_plan.definitions, selected.driver, selected.projection),
            result.is_err() ==> result matches Err(ClockedArgumentWiringError::Selection(_)),
    {
        reveal(UseAliases::selection_at_argument);
        let call = &checked.calls[index];
        let expressions = &checked.module.expressions;
        let wiring = &expressions.typed.sources.roots.wiring;
        let ports = &call.inputs.ports;
        proof {
            self.module_calls_item_evidence(_owner, limit, checked, index as int);
            self.module_call_ports_evidence(call.at, limit, *ports);
            self.module_call_site_evidence(call.at, limit, ports.signature);
        }
        let source = ports.signature.source;
        let parsed = &self.targets.project().circuits()[call.at.file];
        let forms = parsed.syntax.forms.as_slice();
        let root = ports.arguments[arg];
        proof {
            parsed_index_evidence(*source, *parsed);
            call_argument_position_bounds(forms@, ports.signature.call, ports.arguments@, arg as int);
        }
        let (steps, leaf) = bit_selection_chain(source.text, forms, root);
        if steps.is_empty() { return Ok(None); }
        proof {
            let last = steps@.len() - 1;
            let at = bit_selection_step_root(root, steps@, last);
            assert(bit_selection_shape_matches(source.text, forms@, at, steps@[last]));
            bit_selection_shape_positions(source.text, forms@, at, steps@[last]);
        }
        if !matches!(forms[leaf], Form::Atom { kind: AtomKind::Name, .. }) { return Ok(None); }
        let frame = &parsed.entry_ranges[call.at.entry];
        let definition = frame.definitions.start + call.at.definition;
        let row = &parsed.definitions[definition];
        proof {
            let model = parsed.build_model();
            build_entry_ranges_evidence(source.text, &model, call.at.entry as int);
            build_definition_scope_evidence(source.text, &model, call.at.entry as int, definition as int);
            definition_signal_positions_in_order(source.text, &model, call.at.entry as int, definition as int);
            call_argument_position_is_direct(forms@, ports.signature.call, ports.arguments@, arg as int);
            let reference = row.references.start + call.at.reference;
            indexed_call_selection_leaf(source.text, forms@, row, parsed.references@, reference as usize,
                &ports.signature.call, parsed.signals@, root, steps@, leaf);
        }
        let Some(position) = find_signal(parsed.signals.as_slice(), row.signals.start, row.signals.end, leaf) else { unreachable!() };
        proof {
            self.module_calls_type_evidence(_owner, limit, checked);
            self.module_output_types_evidence(_owner, limit, checked.module);
            self.module_selections_evidence(_owner, limit, *expressions);
            self.module_input_sites(_owner, limit, wiring.drivers);
            self.module_signal_index_item(_owner, limit, *wiring, call.member as int, position as int);
        }
        let driver = wiring.signals[call.member][position - frame.signals.start].driver;
        proof {
            if let OutputDriver::Definition(slot) = driver {
                self.clocked_output_layouts(&checked.module, limit, _capacity, _plan);
                self.clocked_definition_layout_evidence(expressions, limit, _capacity, &_plan.definitions, slot);
            }
        }
        let Some(actual) = read_bound_type(&expressions.typed, expressions.types.as_slice(), driver) else { unreachable!() };
        let ResolvedPortType::Bits(width) = actual.ty else {
            return Err(ClockedArgumentWiringError::Selection(ModuleSelectionsError::InputType {
                input: form_location(source, forms, leaf), actual,
            }));
        };
        let projection = match check_selection_chain(source, forms, root, steps.as_slice(), leaf, width, &actual.origin) {
            Ok(projection) => projection,
            Err(error) => return Err(ClockedArgumentWiringError::Selection(ModuleSelectionsError::Argument(error))),
        };
        if projection.count > limit {
            return Err(ClockedArgumentWiringError::Selection(ModuleSelectionsError::Width {
                expression: form_location(source, forms, root), width: projection.count, limit,
            }));
        }
        proof {
            self.clocked_output_layouts(&checked.module, limit, _capacity, _plan);
            self.module_output_driver(_owner, limit, wiring.drivers, 0);
            match driver {
                OutputDriver::Input(input) => self.routine_bit_layout_port(wiring.drivers.signature, limit, _capacity,
                    &_plan.inputs, &_plan.outputs, PortDirection::Input, input),
                OutputDriver::Definition(slot) => self.clocked_definition_layout_evidence(expressions, limit, _capacity, &_plan.definitions, slot),
            }
            assert(clocked_selected_port_ready(&_plan.inputs, &_plan.definitions, driver, projection));
        }
        Ok(Some(SelectedPort { driver, projection }))
    }

    pub(super) closed spec fn selected_argument_wires(
        &self, checked: &ModuleCalls, limit: u64, plan: &ClockedModuleOutputs, index: usize, arg: usize, port: CallPortType,
        result: Result<Vec<ClockedWireDriver>, ClockedArgumentWiringError>,
    ) -> bool {
        let call = checked.calls@[index as int];
        let parsed = self.targets.project_model().circuits_model()[call.at.file as int];
        let form = parsed.syntax.forms@[call.inputs.ports.arguments@[arg as int] as int];
        let source = call.inputs.ports.signature.source;
        exists|selected: Result<Option<SelectedPort>, ClockedArgumentWiringError>|
            #[trigger] self.selection_at_argument(checked, limit, index, arg, selected)
            && match selected {
                Ok(None) => result matches Err(ClockedArgumentWiringError::Unsupported(argument))
                    && is_form_location(source, form, argument),
                Err(error) => result == Err(error),
                Ok(Some(selected)) => {
                    let count = selected.projection.count;
                    if port.ty == ResolvedPortType::Bits(count) {
                        match result {
                            Ok(wires) => clocked_driver_bits_result(&plan.inputs, &plan.definitions, selected.driver, Some(selected.projection), Ok(wires)),
                            Err(ClockedArgumentWiringError::Wiring { argument, reason }) =>
                                is_form_location(source, form, argument) && (reason is Capacity || reason is Allocation)
                                    && clocked_driver_bits_result(&plan.inputs, &plan.definitions, selected.driver, Some(selected.projection), Err(reason)),
                            _ => false,
                        }
                    } else {
                        result matches Err(ClockedArgumentWiringError::SelectionPort { argument, expected, required_at, width })
                            && is_form_location(source, form, argument) && width == count && expected == port.ty
                            && required_at == match port.annotation { Some(annotation) => Some(*annotation), None => None }
                    }
                },
            }
    }

    pub(super) proof fn selected_argument_width(
        &self, checked: &ModuleCalls, limit: u64, plan: &ClockedModuleOutputs, index: usize, arg: usize, port: CallPortType,
        wires: Vec<ClockedWireDriver>,
    )
        requires self.selected_argument_wires(checked, limit, plan, index, arg, port, Ok(wires)),
        ensures port.ty == ResolvedPortType::Bits(wires@.len() as u64), wires@.len() <= u64::MAX,
    {
        let (driver, projection) = self.selected_argument_projection(checked, limit, plan, index, arg, port, wires);
        clocked_selected_port_bits(&plan.inputs, &plan.definitions, driver, projection, wires);
    }

    /// 選択の配線に使った型検査済みの駆動元と射影を取り出す。
    pub(super) proof fn selected_argument_projection(
        &self, checked: &ModuleCalls, limit: u64, plan: &ClockedModuleOutputs, index: usize, arg: usize,
        port: CallPortType, wires: Vec<ClockedWireDriver>,
    ) -> (result: (OutputDriver, CheckedBitSelection))
        requires self.selected_argument_wires(checked, limit, plan, index, arg, port, Ok(wires)),
        ensures port.ty == ResolvedPortType::Bits(result.1.count),
            clocked_driver_bits_result(&plan.inputs, &plan.definitions, result.0, Some(result.1), Ok(wires)),
    {
        let selection = choose|selection: SelectedPort|
            #[trigger] self.selection_at_argument(checked, limit, index, arg, Ok(Some(selection)))
            && port.ty == ResolvedPortType::Bits(selection.projection.count)
            && clocked_driver_bits_result(&plan.inputs, &plan.definitions, selection.driver, Some(selection.projection), Ok(wires));
        (selection.driver, selection.projection)
    }

    /// 型検査が保留した選択式を検査して、要求した幅の配線に変換する。
    pub(super) fn wire_selected_argument(
        &self, owner: ModuleBodyPosition, limit: u64, _capacity: usize, checked: &ModuleCalls<'p, 'a>, plan: &ClockedModuleOutputs,
        index: usize, arg: usize, port: CallPortType<'_, 'p, 'a>,
    ) -> (result: Result<Vec<ClockedWireDriver>, ClockedArgumentWiringError<'p, 'a>>)
        requires
            self.can_resolve(), self.module_calls_result(owner, limit, Ok(Some(*checked))),
            index < checked.calls@.len(), arg < checked.calls@[index as int].inputs.ports.arguments@.len(),
            self.outputs_on_checked(&checked.module, limit, _capacity, Ok(*plan)),
            checked.calls@[index as int].inputs.ports.signature.target.port_matches(PortDirection::Input, arg, Some(port)),
        ensures self.selected_argument_wires(checked, limit, plan, index, arg, port, result),
            !(result matches Err(ClockedArgumentWiringError::Layout(_))),
    {
        let checked_projection = self.check_argument_selection(owner, limit, _capacity, plan, checked, index, arg);
        let argument = self.module_argument(owner, limit, checked, index, arg);
        let selected = match checked_projection {
            Ok(Some(selected)) => selected,
            Err(error) => return Err(error),
            Ok(None) => return Err(ClockedArgumentWiringError::Unsupported(form_location(argument.source, argument.forms, argument.root))),
        };
        let width = selected.projection.count;
        if !matches!(port.ty, ResolvedPortType::Bits(bits) if bits == width) {
            return Err(ClockedArgumentWiringError::SelectionPort {
                argument: form_location(argument.source, argument.forms, argument.root),
                expected: port.ty,
                required_at: match port.annotation { Some(annotation) => Some(copy_location(annotation)), None => None },
                width,
            });
        }
        match clocked_driver_bits(&plan.inputs, &plan.definitions, selected.driver, Some(selected.projection)) {
            Ok(wires) => Ok(wires),
            Err(reason) => {
                proof { checked_selection_wiring_error(&plan.inputs, &plan.definitions, selected.driver, selected.projection, reason); }
                Err(ClockedArgumentWiringError::Wiring {
                    argument: form_location(argument.source, argument.forms, argument.root), reason,
                })
            },
        }
    }
}

} // verus!
