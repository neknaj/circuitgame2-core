//! モジュールの呼び出しにおける実引数と、検査済みの駆動元を対応付ける。

use super::{ModuleCalls, UseAliases};
use crate::project::{ModuleBodyPosition, OutputDriver, ProjectSource};
use crate::syntax::{AtomKind, Form, circuit::indexed_call_signal};
use vstd::prelude::*;
#[cfg(verus_only)]
use crate::project::circuits::parsed_index_evidence;
#[cfg(verus_only)]
use crate::syntax::{form_spans_valid, circuit::{
    build_definition_scope_evidence, build_entry_ranges_evidence,
    call_argument_position_bounds, call_argument_position_is_direct, definition_signal_positions_in_order,
}};
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 検査済みの呼び出しに含まれる実引数と、裸の信号名に対応する駆動元。
pub(super) struct ModuleArgument<'s, 'p, 'a> {
    /// 実引数が現れたファイル。
    pub(super) source: &'p ProjectSource<'a>,
    /// 元のファイルの構文フォーム列。
    pub(super) forms: &'s [Form],
    /// フォーム列における実引数の根の添字。
    pub(super) root: usize,
    /// 裸の信号名に対応する入力または定義。ほかの式では `None`。
    pub(super) driver: Option<OutputDriver>,
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    pub(super) open spec fn module_argument_binding_at(&self, checked: &ModuleCalls, index: int, arg: int,
        position: int, driver: OutputDriver,
    ) -> bool {
        let call = checked.calls@[index];
        let root = call.inputs.ports.arguments@[arg];
        let wiring = &checked.module.expressions.typed.sources.roots.wiring;
        let parsed = self.targets.project_model().circuits_model()[call.at.file as int];
        let frame = parsed.entry_ranges@[call.at.entry as int];
        let definition = parsed.definitions@[frame.definitions.start + call.at.definition];
        let bound = wiring.signals@[call.member as int]@[position - frame.signals.start];
        &&& 0 <= arg < call.inputs.ports.arguments@.len()
        &&& root < parsed.syntax.forms@.len()
        &&& parsed.syntax.forms@[root as int] is Atom
        &&& parsed.syntax.forms@[root as int]->Atom_kind is Name
        &&& definition.signals.start <= position < definition.signals.end
        &&& parsed.signals@[position] == root
        &&& bound.form == root
        &&& driver == bound.driver
    }

    /// 裸の信号名が、同じ実引数の元の位置で指定された端子または定義を参照する。
    pub(super) open spec fn module_argument_binding(
        &self, checked: &ModuleCalls, index: int, arg: int, driver: OutputDriver,
    ) -> bool {
        exists|position: int| #[trigger] self.module_argument_binding_at(checked, index, arg, position, driver)
    }

    /// 同じ実引数の裸の信号名に対応する駆動元は一つに決まる。
    pub(super) proof fn module_argument_bindings_agree(
        &self, owner: ModuleBodyPosition, limit: u64, checked: &ModuleCalls, index: int, arg: int,
        left: OutputDriver, right: OutputDriver,
    )
        requires
            self.can_resolve(),
            self.module_calls_result(owner, limit, Ok(Some(*checked))),
            0 <= index < checked.calls@.len(),
            self.module_argument_binding(checked, index, arg, left),
            self.module_argument_binding(checked, index, arg, right),
        ensures left == right,
    {
        let call = checked.calls@[index];
        self.module_calls_item_evidence(owner, limit, checked, index);
        self.module_call_ports_evidence(call.at, limit, call.inputs.ports);
        self.module_call_site_evidence(call.at, limit, call.inputs.ports.signature);
        self.targets.parsed_project_model();
        let parsed = self.targets.project_model().circuits_model()[call.at.file as int];
        let source = call.inputs.ports.signature.source;
        let frame = parsed.entry_ranges@[call.at.entry as int];
        let definition = frame.definitions.start + call.at.definition;
        parsed_index_evidence(*source, parsed);
        let model = parsed.build_model();
        build_entry_ranges_evidence(source.text, &model, call.at.entry as int);
        build_definition_scope_evidence(source.text, &model, call.at.entry as int, definition);
        definition_signal_positions_in_order(source.text, &model, call.at.entry as int, definition);
        let a = choose|at: int| #[trigger] self.module_argument_binding_at(checked, index, arg, at, left);
        let b = choose|at: int| #[trigger] self.module_argument_binding_at(checked, index, arg, at, right);
        assert(parsed.signals@[a] == parsed.signals@[b]);
        if a < b {
            assert(parsed.signals@[a] < parsed.signals@[b]);
        } else if b < a {
            assert(parsed.signals@[b] < parsed.signals@[a]);
        }
    }

    /// 元のファイルと式の位置を取り出し、裸の信号名を検査済みの配線表で引く。
    pub(super) fn module_argument<'s>(
        &'s self, _owner: ModuleBodyPosition, _limit: u64, checked: &ModuleCalls<'p, 'a>,
        index: usize, arg: usize,
    ) -> (argument: ModuleArgument<'s, 'p, 'a>)
        requires
            self.can_resolve(), self.module_calls_result(_owner, _limit, Ok(Some(*checked))),
            index < checked.calls@.len(), arg < checked.calls@[index as int].inputs.ports.arguments@.len(),
        ensures
            checked.calls@[index as int].at.file < self.targets.project_model().circuits_model().len(),
            argument.source == checked.calls@[index as int].inputs.ports.signature.source,
            argument.forms@ == self.targets.project_model().circuits_model()[checked.calls@[index as int].at.file as int].syntax.forms@,
            argument.root == checked.calls@[index as int].inputs.ports.arguments@[arg as int],
            argument.root < argument.forms@.len(),
            form_spans_valid(argument.source.text, argument.forms@, argument.source.text.spec_bytes().len() as int),
            argument.driver.is_some() <==> ({
                let form = argument.forms@[argument.root as int];
                form is Atom && form->Atom_kind is Name
            }),
            argument.driver matches Some(driver) ==>
                self.module_argument_binding(checked, index as int, arg as int, driver)
                && ({
                    let drivers = checked.module.expressions.typed.sources.roots.wiring.drivers;
                    match driver {
                        OutputDriver::Input(port) => port < drivers.signature.inputs@.len(),
                        OutputDriver::Definition(slot) => slot < drivers.definitions@.len(),
                    }
                }),
    {
        let call = &checked.calls[index];
        let ghost at = call.at;
        let ports = &call.inputs.ports;
        let wiring = &checked.module.expressions.typed.sources.roots.wiring;
        proof {
            self.module_calls_type_evidence(_owner, _limit, checked);
            self.module_output_types_evidence(_owner, _limit, checked.module);
            self.module_selections_evidence(_owner, _limit, checked.module.expressions);
            self.module_calls_item_evidence(_owner, _limit, checked, index as int);
            self.module_call_ports_evidence(at, _limit, *ports);
            self.module_call_site_evidence(at, _limit, ports.signature);
        }
        let project = self.targets.project();
        let source = ports.signature.source;
        let parsed = &project.circuits()[call.at.file];
        let ghost model = parsed.build_model();
        proof {
            parsed_index_evidence(*source, *parsed);
            build_entry_ranges_evidence(source.text, &model, at.entry as int);
        }
        let frame = &parsed.entry_ranges[call.at.entry];
        let definition = frame.definitions.start + call.at.definition;
        let row = &parsed.definitions[definition];
        let forms = parsed.syntax.forms.as_slice();
        let root = ports.arguments[arg];
        proof {
            build_definition_scope_evidence(source.text, &model, at.entry as int, definition as int);
            call_argument_position_bounds(forms@, ports.signature.call, ports.arguments@, arg as int);
        }
        let driver = if matches!(forms[root], Form::Atom { kind: AtomKind::Name, .. }) {
            proof { call_argument_position_is_direct(forms@, ports.signature.call, ports.arguments@, arg as int); }
            let reference = row.references.start + call.at.reference;
            let position = indexed_call_signal(source.text, forms, row, parsed.references.as_slice(), reference,
                &ports.signature.call, parsed.signals.as_slice(), root);
            proof { self.module_signal_index_item(_owner, _limit, *wiring, call.member as int, position as int); }
            let driver = wiring.signals[call.member][position - frame.signals.start].driver;
            assert(self.module_argument_binding_at(checked, index as int, arg as int, position as int, driver));
            Some(driver)
        } else {
            None
        };
        ModuleArgument { source, forms, root, driver }
    }
}

} // verus!
