//! 型と位置を照合した実引数から、入力ポートごとの配線を取り出す。

mod selection;

use super::{ClockedDriverBitsError, ClockedModuleOutputs, ClockedModuleOutputsError, ClockedWireDriver,
    ModuleCalls, ModuleSelectionsError, UseAliases, clocked_driver_bits, driver_bits::reserve_clocked_bits};
use crate::netlist::Wire;
use crate::project::{LocatedName, ModuleBodyPosition, PortDirection, ResolvedPortType,
    circuits::{form_location, read_indexed_atom}};
use crate::syntax::{AtomKind, Form, read_bit_literal};
use alloc::vec::Vec;
use vstd::prelude::*;
#[cfg(verus_only)]
use super::{clocked_driver_bits_result, driver_bits::{clocked_whole_port_bits, driver_bits_capacity}, selections::bound_type};
#[cfg(verus_only)]
use crate::project::{CallPortType, OutputDriver, SignalType, StructureLayouts, circuit_literal_width_matches, port_types_equal,
    circuits::is_form_location, use_aliases::call_arity::{checked_literal_leaf_width, leaf_result}};
#[cfg(verus_only)]
use crate::syntax::{bit_literal_value_at, form_span};
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 呼び出しの実引数をビット配線へ変換できなかった理由。
#[derive(Debug)]
pub enum ClockedArgumentWiringError<'p, 'a> {
    /// 呼び出しの型検査または入出力・定義の配置に失敗した。
    Layout(ClockedModuleOutputsError<'p, 'a>),
    /// 入力ポートの一覧に必要なメモリを確保できなかった。
    Allocation,
    /// 変換が未対応の実引数。範囲は引数式全体を指す。
    Unsupported(LocatedName<'p, 'a>),
    /// 選択対象の型、選択の数値引数、または選択範囲に違反がある。
    Selection(ModuleSelectionsError<'p, 'a>),
    /// 選択したビット列と呼び出し先の入力型が一致しない。
    SelectionPort {
        /// 選択式全体の範囲。
        argument: LocatedName<'p, 'a>,
        /// 入力ポートの要求型。
        expected: ResolvedPortType<'p, 'a>,
        /// 入力ポートの型注釈。注釈のない入力では `None`。
        required_at: Option<LocatedName<'p, 'a>>,
        /// 選択したビット列の幅。
        width: u64,
    },
    /// 配線列の容量または確保に失敗した。
    Wiring {
        /// 元の引数式の範囲。
        argument: LocatedName<'p, 'a>,
        /// 配線列を作れなかった理由。
        reason: ClockedDriverBitsError,
    },
}

spec fn literal_atom(form: Form) -> bool {
    form is Atom && (form->Atom_kind is Binary || form->Atom_kind is Hexadecimal || form->Atom_kind is Natural)
}

pub(super) open spec fn literal_wires(bytes: Seq<u8>, width: u64, result: Result<Vec<ClockedWireDriver>, ClockedDriverBitsError>) -> bool {
    match result {
        Ok(wires) => wires@.len() == width <= driver_bits_capacity()
            && (forall|i: int| 0 <= i < width ==> (#[trigger] wires@[i]) ==
                ClockedWireDriver::Terminal(Wire::Constant(
                    if bytes.len() == 1 { bytes[0] == b'1' } else { bit_literal_value_at(bytes, i as nat) }))),
        Err(ClockedDriverBitsError::Capacity { count, limit }) =>
            count == width && limit == driver_bits_capacity() && count > limit,
        Err(ClockedDriverBitsError::Allocation) => width <= driver_bits_capacity(),
        _ => false,
    }
}

pub(super) fn wire_literal(word: &str, width: u64, _limit: u64)
    -> (result: Result<Vec<ClockedWireDriver>, ClockedDriverBitsError>)
    requires circuit_literal_width_matches(word.spec_bytes(), Some(width), _limit, Ok(width)),
    ensures literal_wires(word.spec_bytes(), width, result),
{
    proof { crate::project::literal_width::checked_literal_for_port(word.spec_bytes(), width, _limit, width); }
    let mut wires = reserve_clocked_bits(width)?;
    let bytes = word.as_bytes();
    if bytes.len() == 1 {
        proof {
            let kind = crate::syntax::bare_atom_kind(word.spec_bytes());
            if kind == Some(AtomKind::Binary) || kind == Some(AtomKind::Hexadecimal) {
                crate::syntax::bit_literal_kind_has_digits(word.spec_bytes());
            }
            assert(width == 1);
        }
        let bit = bytes[0] == b'1';
        wires.push(ClockedWireDriver::Terminal(Wire::Constant(bit)));
        assert forall|i: int| 0 <= i < width implies (#[trigger] wires@[i]) ==
            ClockedWireDriver::Terminal(Wire::Constant(word.spec_bytes()[0] == b'1')) by {
            assert(i == 0);
        };
        return Ok(wires);
    }
    proof { crate::syntax::bit_literal_kind_has_digits(word.spec_bytes()); }
    let Some(literal) = read_bit_literal(word) else { unreachable!() };
    let mut i = 0u64;
    while i < width
        invariant
            i == wires@.len() <= width <= driver_bits_capacity(),
            word.spec_bytes().len() != 1,
            literal.word_model().spec_bytes() == word.spec_bytes(),
            forall|j: int| 0 <= j < i ==> (#[trigger] wires@[j]) ==
                ClockedWireDriver::Terminal(Wire::Constant(bit_literal_value_at(word.spec_bytes(), j as nat))),
        decreases width - i,
    {
        let bit = literal.bit(i);
        let ghost before = wires@;
        wires.push(ClockedWireDriver::Terminal(Wire::Constant(bit)));
        assert forall|j: int| 0 <= j <= i implies (#[trigger] wires@[j]) ==
            ClockedWireDriver::Terminal(Wire::Constant(bit_literal_value_at(word.spec_bytes(), j as nat))) by {
            if j < i { assert(wires@[j] == before[j]); }
        };
        i += 1;
    }
    Ok(wires)
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn argument_wires(
        &self, checked: &ModuleCalls, limit: u64, plan: &ClockedModuleOutputs,
        index: usize, arg: usize, result: Result<Vec<ClockedWireDriver>, ClockedArgumentWiringError>,
    ) -> bool {
        let row = checked.calls@[index as int];
        let ports = row.inputs.ports;
        let parsed = self.targets.project_model().circuits_model()[row.at.file as int];
        let form = parsed.syntax.forms@[ports.arguments@[arg as int] as int];
        let site = |label: LocatedName| is_form_location(ports.signature.source, form, label);
        if form is Atom && form->Atom_kind is Name {
            let expressions = &checked.module.expressions;
            exists|driver: OutputDriver, port: CallPortType|
                #[trigger] self.module_argument_binding(checked, index as int, arg as int, driver)
                && #[trigger] ports.signature.target.port_matches(PortDirection::Input, arg, Some(port))
                && row.inputs.types@[arg as int] == bound_type(&expressions.typed, expressions.types@, driver)
                && (row.inputs.types@[arg as int] matches Some(ty) ==> port_types_equal(ty.ty, port.ty))
                && match result {
                    Ok(wires) => clocked_driver_bits_result(&plan.inputs, &plan.definitions, driver, None, Ok(wires)),
                    Err(ClockedArgumentWiringError::Wiring { argument, reason }) =>
                        site(argument) && clocked_driver_bits_result(&plan.inputs, &plan.definitions, driver, None, Err(reason)),
                    _ => false,
                }
        } else if literal_atom(form) {
            let span = form_span(form);
            let bytes = ports.signature.source.text.spec_bytes()[span.start as int..span.end as int];
            exists|port: CallPortType| #[trigger] ports.signature.target.port_matches(PortDirection::Input, arg, Some(port))
                && port.ty is Bits
                && circuit_literal_width_matches(bytes, Some(port.ty->Bits_0), limit, Ok(port.ty->Bits_0))
                && match result {
                    Ok(wires) => literal_wires(bytes, port.ty->Bits_0, Ok(wires)),
                    Err(ClockedArgumentWiringError::Wiring { argument, reason }) =>
                        site(argument) && literal_wires(bytes, port.ty->Bits_0, Err(reason)),
                    _ => false,
                }
        } else if form is List {
            exists|port: CallPortType| #[trigger] ports.signature.target.port_matches(PortDirection::Input, arg, Some(port))
                && self.selected_argument_wires(checked, limit, plan, index, arg, port, result)
        } else {
            result matches Err(ClockedArgumentWiringError::Unsupported(argument)) && site(argument)
        }
    }

    fn wire_call_argument(
        &self, owner: ModuleBodyPosition, limit: u64, _capacity: usize, checked: &ModuleCalls<'p, 'a>,
        plan: &ClockedModuleOutputs, index: usize, arg: usize,
    ) -> (result: Result<Vec<ClockedWireDriver>, ClockedArgumentWiringError<'p, 'a>>)
        requires
            self.can_resolve(), self.module_calls_result(owner, limit, Ok(Some(*checked))),
            index < checked.calls@.len(), arg < checked.calls@[index as int].inputs.ports.arguments@.len(),
            self.outputs_on_checked(&checked.module, limit, _capacity, Ok(*plan)),
        ensures self.argument_wires(checked, limit, plan, index, arg, result),
            !(result matches Err(ClockedArgumentWiringError::Layout(_))),
    {
        let row = &checked.calls[index];
        let argument = self.module_argument(owner, limit, checked, index, arg);
        proof {
            self.module_calls_item_evidence(owner, limit, checked, index as int);
            self.module_call_ports_evidence(row.at, limit, row.inputs.ports);
        }
        let Some(port) = row.inputs.ports.signature.target.port(PortDirection::Input, arg) else { unreachable!() };
        proof { self.module_call_leaf(owner, limit, checked, index, arg, port, argument.driver); }
        let source = argument.source;
        let forms = argument.forms;
        let root = argument.root;
        let result = if let Some(driver) = argument.driver {
            clocked_driver_bits(&plan.inputs, &plan.definitions, driver, None)
        } else if matches!(forms[root], Form::Atom { kind: AtomKind::Binary | AtomKind::Hexadecimal | AtomKind::Natural, .. }) {
            let (word, _) = read_indexed_atom(source.text, forms, root);
            proof {
                let form = forms@[root as int];
                let typed = row.inputs.types@[arg as int];
                let known = choose|known: Option<SignalType>| #[trigger] leaf_result(source, form, &port, known, limit, Ok(typed));
                checked_literal_leaf_width(source, form, &port, known, limit, typed);
                crate::project::literal_width::checked_literal_for_port(word.spec_bytes(), port.ty->Bits_0, limit, typed->Some_0.ty->Bits_0);
            }
            let ResolvedPortType::Bits(width) = port.ty else { unreachable!() };
            wire_literal(word, width, limit)
        } else if matches!(forms[root], Form::List { .. }) {
            return self.wire_selected_argument(owner, limit, _capacity, checked, plan, index, arg, port);
        } else {
            return Err(ClockedArgumentWiringError::Unsupported(form_location(source, forms, root)));
        };
        match result {
            Ok(wires) => Ok(wires),
            Err(reason) => Err(ClockedArgumentWiringError::Wiring { argument: form_location(source, forms, root), reason }),
        }
    }

    #[verifier::opaque]
    spec fn call_wires_prefix(
        &self, checked: &ModuleCalls, limit: u64, plan: &ClockedModuleOutputs,
        index: usize, wires: Seq<Vec<ClockedWireDriver>>,
    ) -> bool {
        &&& wires.len() <= checked.calls@[index as int].inputs.ports.arguments@.len()
        &&& forall|i: int| 0 <= i < wires.len() ==>
            self.argument_wires(checked, limit, plan, index, i as usize, Ok(#[trigger] wires[i]))
    }

    /// 指定した呼び出しに対する実引数の配線列と、最初の診断を表す。
    pub(super) closed spec fn call_wires_result(
        &self, checked: &ModuleCalls, limit: u64, plan: &ClockedModuleOutputs, index: usize,
        result: Result<Vec<Vec<ClockedWireDriver>>, ClockedArgumentWiringError>,
    ) -> bool {
        match result {
            Ok(wires) => self.call_wires_prefix(checked, limit, plan, index, wires@)
                && wires@.len() == checked.calls@[index as int].inputs.ports.arguments@.len(),
            Err(ClockedArgumentWiringError::Allocation) => checked.calls@[index as int].inputs.ports.arguments@.len() > 0,
            Err(error) => exists|before: Seq<Vec<ClockedWireDriver>>|
                #[trigger] self.call_wires_prefix(checked, limit, plan, index, before)
                && before.len() < checked.calls@[index as int].inputs.ports.arguments@.len()
                && self.argument_wires(checked, limit, plan, index, before.len() as usize, Err(error)),
        }
    }

    /// 解決した配線の行数が、ソースに書かれた実引数の数に等しいことを示す。
    pub(super) proof fn call_wires_count(
        &self, checked: &ModuleCalls, limit: u64, plan: &ClockedModuleOutputs, index: usize, wires: Vec<Vec<ClockedWireDriver>>,
    )
        requires self.call_wires_result(checked, limit, plan, index, Ok(wires)),
        ensures wires@.len() == checked.calls@[index as int].inputs.ports.arguments@.len(),
    {
    }

    /// 実引数の配線数が呼び出し先の入力ポートの表現幅に一致することを示す。
    pub(super) proof fn clocked_call_argument_port(
        &self, owner: ModuleBodyPosition, limit: u64, capacity: usize, checked: &ModuleCalls, plan: &ClockedModuleOutputs,
        index: usize, arg: usize, port: CallPortType, wires: Vec<Vec<ClockedWireDriver>>,
    )
        requires
            self.can_resolve(), self.module_calls_result(owner, limit, Ok(Some(*checked))),
            index < checked.calls@.len(), arg < checked.calls@[index as int].inputs.ports.arguments@.len(),
            self.outputs_on_checked(&checked.module, limit, capacity, Ok(*plan)),
            self.call_wires_result(checked, limit, plan, index, Ok(wires)),
            checked.calls@[index as int].inputs.ports.signature.target.port_matches(PortDirection::Input, arg, Some(port)),
        ensures
            arg < wires@.len(),
            match port.ty {
                ResolvedPortType::Bits(width) => wires@[arg as int]@.len() == width,
                ty @ ResolvedPortType::Struct { .. } => exists|table: StructureLayouts|
                    self.structure_types_match(limit, Ok(table))
                    && #[trigger] self.layout_port_width_matches(&table, ty, wires@[arg as int]@.len() as int),
            },
    {
        reveal(UseAliases::call_wires_prefix);
        let row = checked.calls@[index as int];
        let ports = row.inputs.ports;
        let parsed = self.targets.project_model().circuits_model()[row.at.file as int];
        let root = ports.arguments@[arg as int];
        let form = parsed.syntax.forms@[root as int];
        let bits = wires@[arg as int];
        assert(self.argument_wires(checked, limit, plan, index, arg, Ok(bits)));
        if form is Atom && form->Atom_kind is Name {
            let (driver, declared) = choose|driver: OutputDriver, declared: CallPortType|
                #[trigger] self.module_argument_binding(checked, index as int, arg as int, driver)
                && #[trigger] ports.signature.target.port_matches(PortDirection::Input, arg, Some(declared))
                && row.inputs.types@[arg as int] == bound_type(&checked.module.expressions.typed, checked.module.expressions.types@, driver)
                && (row.inputs.types@[arg as int] matches Some(ty) ==> port_types_equal(ty.ty, declared.ty))
                && clocked_driver_bits_result(&plan.inputs, &plan.definitions, driver, None, Ok(bits));
            ports.signature.target.port_results_agree(PortDirection::Input, arg, Some(port), Some(declared));
            self.clocked_output_layouts(&checked.module, limit, capacity, plan);
            self.module_calls_type_evidence(owner, limit, checked);
            self.module_output_types_evidence(owner, limit, checked.module);
            self.module_selections_evidence(owner, limit, checked.module.expressions);
            self.module_selection_type_declarations(owner, limit, checked.module.expressions);
            let drivers = checked.module.expressions.typed.sources.roots.wiring.drivers;
            self.module_output_driver(owner, limit, drivers, 0);
            self.typed_signature_types_declared(owner.file, owner.entry, limit, drivers.signature);
            clocked_whole_port_bits(&plan.inputs, &plan.definitions, driver, bits);
            self.clocked_definition_layout_evidence(&checked.module.expressions, limit, capacity, &plan.definitions, 0);
            match driver {
                OutputDriver::Input(input) =>
                    self.routine_bit_layout_port(drivers.signature, limit, capacity, &plan.inputs, &plan.outputs, PortDirection::Input, input),
                OutputDriver::Definition(slot) =>
                    self.clocked_definition_layout_evidence(&checked.module.expressions, limit, capacity, &plan.definitions, slot),
            }
            let actual = row.inputs.types@[arg as int]->Some_0.ty;
            self.module_calls_item_evidence(owner, limit, checked, index as int);
            self.module_call_ports_evidence(row.at, limit, ports);
            self.module_call_port_type_declared(row.at, limit, ports.signature, PortDirection::Input, arg, port);
            self.equivalent_declared_port_types(actual, port.ty);
        } else if form is List {
            let declared = choose|declared: CallPortType| #[trigger] ports.signature.target.port_matches(PortDirection::Input, arg, Some(declared))
                && self.selected_argument_wires(checked, limit, plan, index, arg, declared, Ok(bits));
            ports.signature.target.port_results_agree(PortDirection::Input, arg, Some(port), Some(declared));
            self.selected_argument_width(checked, limit, plan, index, arg, port, bits);
        } else {
            assert(literal_atom(form));
            let span = form_span(form);
            let bytes = ports.signature.source.text.spec_bytes()[span.start as int..span.end as int];
            let declared = choose|declared: CallPortType| #[trigger] ports.signature.target.port_matches(PortDirection::Input, arg, Some(declared))
                && declared.ty is Bits
                && circuit_literal_width_matches(bytes, Some(declared.ty->Bits_0), limit, Ok(declared.ty->Bits_0))
                && literal_wires(bytes, declared.ty->Bits_0, Ok(bits));
            ports.signature.target.port_results_agree(PortDirection::Input, arg, Some(port), Some(declared));
        }
    }

    /// 型検査済みの呼び出しの実引数を、同じモジュールのビット配置へ結び付ける。
    pub(super) fn wire_call_arguments(
        &self, owner: ModuleBodyPosition, limit: u64, _capacity: usize, checked: &ModuleCalls<'p, 'a>, plan: &ClockedModuleOutputs, index: usize,
    ) -> (result: Result<Vec<Vec<ClockedWireDriver>>, ClockedArgumentWiringError<'p, 'a>>)
        requires
            self.can_resolve(), self.module_calls_result(owner, limit, Ok(Some(*checked))), index < checked.calls@.len(),
            self.outputs_on_checked(&checked.module, limit, _capacity, Ok(*plan)),
        ensures self.call_wires_result(checked, limit, plan, index, result),
            !(result matches Err(ClockedArgumentWiringError::Layout(_))),
    {
        let count = checked.calls[index].inputs.ports.arguments.len();
        let mut wires = Vec::new();
        if count != 0 && wires.try_reserve_exact(count).is_err() { return Err(ClockedArgumentWiringError::Allocation); }
        assert(self.call_wires_prefix(checked, limit, plan, index, wires@)) by { reveal(UseAliases::call_wires_prefix); };
        let mut arg = 0;
        while arg < count
            invariant
                self.can_resolve(), self.module_calls_result(owner, limit, Ok(Some(*checked))), index < checked.calls@.len(),
                arg == wires@.len() <= count == checked.calls@[index as int].inputs.ports.arguments@.len(),
                self.outputs_on_checked(&checked.module, limit, _capacity, Ok(*plan)),
                self.call_wires_prefix(checked, limit, plan, index, wires@),
            decreases count - arg,
        {
            let bits = self.wire_call_argument(owner, limit, _capacity, checked, plan, index, arg)?;
            let ghost before = wires@;
            wires.push(bits);
            assert(self.call_wires_prefix(checked, limit, plan, index, wires@)) by {
                reveal(UseAliases::call_wires_prefix);
                assert forall|i: int| 0 <= i < wires@.len() implies
                    self.argument_wires(checked, limit, plan, index, i as usize, Ok(#[trigger] wires@[i])) by {
                    if i < arg { assert(wires@[i] == before[i]); }
                };
            };
            arg += 1;
        }
        Ok(wires)
    }

    /// 配置と実引数の配線が、同じモジュールと呼び出し順に対応することを表す。
    pub closed spec fn clocked_call_arguments_result(
        &self, owner: ModuleBodyPosition, limit: u64, capacity: usize, index: usize,
        result: Result<Option<(ClockedModuleOutputs, Vec<Vec<ClockedWireDriver>>)>, ClockedArgumentWiringError>,
    ) -> bool {
        match result {
            Err(ClockedArgumentWiringError::Layout(ClockedModuleOutputsError::Calls(error))) =>
                self.module_calls_result(owner, limit, Err(error)),
            Err(ClockedArgumentWiringError::Layout(error)) =>
                exists|checked: ModuleCalls| #[trigger] self.module_calls_result(owner, limit, Ok(Some(checked)))
                    && index < checked.calls@.len() && self.outputs_on_checked(&checked.module, limit, capacity, Err(error)),
            _ => self.module_calls_result(owner, limit, Ok(None)) && result == Ok(None)
                || exists|checked: ModuleCalls| #[trigger] self.module_calls_result(owner, limit, Ok(Some(checked)))
                    && match result {
                        Ok(None) => index >= checked.calls@.len(),
                        Ok(Some((plan, wires))) => index < checked.calls@.len()
                            && self.outputs_on_checked(&checked.module, limit, capacity, Ok(plan))
                            && self.call_wires_result(&checked, limit, &plan, index, Ok(wires)),
                        Err(error) => index < checked.calls@.len() && exists|plan: ClockedModuleOutputs|
                            #[trigger] self.outputs_on_checked(&checked.module, limit, capacity, Ok(plan))
                                && self.call_wires_result(&checked, limit, &plan, index, Err(error)),
                    },
        }
    }

    /// 型検査の呼び出し一覧で指定した1件の実引数を、入力ポート順に配線へ変換する。
    ///
    /// 入力、定義、公開出力の配置も返す。モジュールや指定した呼び出しがなければ `Ok(None)` を返す。
    ///
    /// # Errors
    ///
    /// 型検査と入出力・定義の配置を確認した後、入力ポートの一覧を確保する。
    /// 型検査で保留した選択式は、配線を作る段階で調べる。実引数は裸の信号名、ビットリテラル、
    /// 信号名からのビット選択を扱う。配線を作る段階では、入力ポート順で最初に失敗した引数の範囲を返す。
    pub fn plan_clocked_call_arguments(&self, owner: ModuleBodyPosition, limit: u64, capacity: usize, index: usize)
        -> (result: Result<Option<(ClockedModuleOutputs, Vec<Vec<ClockedWireDriver>>)>, ClockedArgumentWiringError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.clocked_call_arguments_result(owner, limit, capacity, index, result),
    {
        let checked = match self.check_module_calls(owner, limit) {
            Ok(Some(checked)) => checked,
            Ok(None) => return Ok(None),
            Err(error) => return Err(ClockedArgumentWiringError::Layout(ClockedModuleOutputsError::Calls(error))),
        };
        if index >= checked.calls.len() { return Ok(None); }
        proof { self.module_calls_type_evidence(owner, limit, &checked); }
        let plan = match self.wire_clocked_outputs(owner, limit, capacity, &checked.module) {
            Ok(plan) => plan,
            Err(error) => {
                proof { self.clocked_outputs_error_is_not_call_error(&checked.module, limit, capacity, error); }
                return Err(ClockedArgumentWiringError::Layout(error));
            },
        };
        match self.wire_call_arguments(owner, limit, capacity, &checked, &plan, index) {
            Ok(wires) => Ok(Some((plan, wires))),
            Err(error) => {
                assert(self.clocked_call_arguments_result(owner, limit, capacity, index, Err(error)));
                Err(error)
            },
        }
    }
}

} // verus!
