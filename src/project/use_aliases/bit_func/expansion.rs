//! 型検査済みの通常呼び出しを、展開順と出力の左辺に結び付ける。

use super::frontend::BitFuncError;
use super::super::{FuncSignalTypes, FuncWiring, FuncWiringResult, FunctionExpansionOrder, TypedFuncCall, UseAliases};
use super::super::call_arity::{CallArgumentProjections, RootFunctionCall};
#[cfg(verus_only)]
use super::super::call_arity::CallArgumentSource;
use super::super::function_atoms::FuncProjections;
#[cfg(verus_only)]
use super::super::function_atoms::{SignalType, concat_projections_match, signal_type_at, structure_projection_matches,
    structure_projections_in_order};
use crate::project::LocatedName;
#[cfg(verus_only)]
use crate::project::location_in_source;
use crate::project::circuits::form_location;
#[cfg(verus_only)]
use crate::project::circuits::{is_form_location, parsed_circuit_matches, parsed_index_evidence};
#[cfg(verus_only)]
use crate::syntax::circuit::{build_definition_scope_evidence, build_entry_ranges_evidence};
use alloc::vec::Vec;
use core::ops::Range;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 一回の呼び出しで割り当てる左辺、引数範囲、展開済みの呼び出し先。
pub(super) struct CheckedExpansionCall<'p, 'a> {
    /// 呼び出し全体の元ソース範囲。
    pub(super) expression: LocatedName<'p, 'a>,
    /// 左辺の駆動元一覧で、出力ポートと同じ順の連続区間。
    pub(super) outputs: Range<usize>,
    /// 関数の平坦な実引数列における区間。
    pub(super) arguments: Range<usize>,
    /// 展開済み回路を保持する配列における呼び出し先の番号。
    pub(super) vertex: usize,
    pub(super) _signature: Ghost<TypedFuncCall<'p, 'a>>,
    pub(super) _order: Ghost<(int, int)>,
}

/// 通常呼び出しを展開する前の関数本体と、型検査から得た各呼び出しの位置。
pub(super) struct PreparedExpansionBody<'p, 'a> {
    pub(super) typed: FuncSignalTypes<'p, 'a>,
    pub(super) projections: FuncProjections<'p, 'a>,
    pub(super) calls: Vec<CheckedExpansionCall<'p, 'a>>,
}

/// 元の字句を低位ビットから読む。自然定数の 0 と 1 は一ビットで表す。
pub(super) open spec fn call_literal_bit(bytes: Seq<u8>, bit: nat) -> bool {
    if bytes.len() == 1 { bytes[0] == b'1' } else { crate::syntax::bit_literal_value_at(bytes, bit) }
}

pub(super) open spec fn source_argument_bytes(source: &crate::project::ProjectSource, forms: Seq<crate::syntax::Form>, form: usize)
    -> Seq<u8> {
    let span = crate::syntax::form_span(forms[form as int]);
    source.text.spec_bytes()[span.start as int..span.end as int]
}

/// 引数フォームの値を、呼び出し直前の信号値または元の字句から定める。
#[verifier::opaque]
pub(super) open spec fn source_call_argument_value(
    source: &crate::project::ProjectSource, parsed: &crate::syntax::circuit::NamedBuildCircuit,
    wiring: &FuncWiring, entry: usize, definition: usize, form: usize, limit: u64,
    inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>, width: u64, value: Seq<bool>,
) -> bool {
    let forms = parsed.syntax.forms@;
    let frame = parsed.entry_ranges@[entry as int];
    let row = parsed.definitions@[definition as int];
    let span = crate::syntax::form_span(forms[form as int]);
    let bytes = source_argument_bytes(source, forms, form);
    &&& entry < parsed.entry_ranges@.len()
    &&& frame.definitions.start <= definition < frame.definitions.end <= parsed.definitions@.len()
    &&& form < forms.len() && forms[form as int] is Atom
    &&& value.len() == width
    &&& if forms[form as int]->Atom_kind is Name {
        exists|position: int| row.signals.start <= position < row.signals.end <= parsed.signals@.len()
            && (#[trigger] parsed.signals@[position]) == form
            && 0 <= position - frame.signals.start < wiring.signals@.len()
            && {
                let driver = wiring.signals@[position - frame.signals.start].driver;
                &&& (match driver {
                    super::super::OutputDriver::Input(port) => port < inputs.len(),
                    super::super::OutputDriver::Definition(slot) => slot < prior.len(),
                })
                &&& value == super::semantics::driver_values(inputs, prior, driver)
            }
    } else {
        &&& span.start < span.end <= source.text.spec_bytes().len()
        &&& crate::project::circuit_literal_width_matches(bytes, Some(width), limit, Ok(width))
        &&& ((width == 1 && bytes.len() == 1 && (bytes[0] == b'0' || bytes[0] == b'1'))
            || crate::syntax::bare_atom_kind(bytes) == Some(crate::syntax::AtomKind::Binary)
            || crate::syntax::bare_atom_kind(bytes) == Some(crate::syntax::AtomKind::Hexadecimal))
        &&& value == Seq::new(width as nat, |bit: int| call_literal_bit(bytes, bit as nat))
    }
}

/// 同じ引数フォームを同じ幅で評価すると、信号名でもリテラルでも同じ値になる。
proof fn source_call_argument_values_agree(
    source: &crate::project::ProjectSource, parsed: &crate::syntax::circuit::NamedBuildCircuit,
    left_wiring: &FuncWiring, right_wiring: &FuncWiring, entry: usize, definition: usize, form: usize, limit: u64,
    inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>, width: u64, left: Seq<bool>, right: Seq<bool>,
)
    requires
        parsed_circuit_matches(*source, *parsed),
        entry < parsed.syntax.entries@.len(),
        left_wiring.signals@ == right_wiring.signals@,
        source_call_argument_value(source, parsed, left_wiring, entry, definition, form, limit, inputs, prior, width, left),
        source_call_argument_value(source, parsed, right_wiring, entry, definition, form, limit, inputs, prior, width, right),
    ensures left == right,
{
    reveal(source_call_argument_value);
    let frame = parsed.entry_ranges@[entry as int];
    let row = parsed.definitions@[definition as int];
    if parsed.syntax.forms@[form as int]->Atom_kind is Name {
        parsed_index_evidence(*source, *parsed);
        let a = choose|at: int| row.signals.start <= at < row.signals.end <= parsed.signals@.len()
            && (#[trigger] parsed.signals@[at]) == form
            && 0 <= at - frame.signals.start < left_wiring.signals@.len()
            && {
                let driver = left_wiring.signals@[at - frame.signals.start].driver;
                &&& (match driver {
                    super::super::OutputDriver::Input(port) => port < inputs.len(),
                    super::super::OutputDriver::Definition(slot) => slot < prior.len(),
                })
                &&& left == super::semantics::driver_values(inputs, prior, driver)
            };
        let b = choose|at: int| row.signals.start <= at < row.signals.end <= parsed.signals@.len()
            && (#[trigger] parsed.signals@[at]) == form
            && 0 <= at - frame.signals.start < right_wiring.signals@.len()
            && {
                let driver = right_wiring.signals@[at - frame.signals.start].driver;
                &&& (match driver {
                    super::super::OutputDriver::Input(port) => port < inputs.len(),
                    super::super::OutputDriver::Definition(slot) => slot < prior.len(),
                })
                &&& right == super::semantics::driver_values(inputs, prior, driver)
            };
        crate::syntax::circuit::definition_signal_positions_agree(
            source.text, &parsed.build_model(), entry as int, definition as int, a, b);
        assert(left_wiring.signals@[a - frame.signals.start] == right_wiring.signals@[b - frame.signals.start]);
    }
}

/// 元の呼び出しに並ぶ引数と、呼び出し先に渡すポートの値を対応付ける。
pub(super) open spec fn source_call_arguments_match(
    source: &crate::project::ProjectSource, parsed: &crate::syntax::circuit::NamedBuildCircuit,
    wiring: &FuncWiring, entry: usize, definition: usize, call: crate::syntax::circuit::CallShape, limit: u64,
    inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>, widths: Seq<u64>, ports: Seq<Seq<bool>>,
) -> bool {
    &&& entry < parsed.entry_ranges@.len()
    &&& parsed.entry_ranges@[entry as int].definitions.start <= definition
        < parsed.entry_ranges@[entry as int].definitions.end <= parsed.definitions@.len()
    &&& call.form == parsed.definitions@[definition as int].expression.start
    &&& exists|positions: Seq<usize>| #[trigger] crate::syntax::circuit::call_argument_positions(parsed.syntax.forms@, call, positions)
        && positions.len() == ports.len() == widths.len()
        && forall|port: int| 0 <= port < positions.len() ==>
            source_call_argument_value(source, parsed, wiring, entry, definition, #[trigger] positions[port],
                limit, inputs, prior, widths[port], ports[port])
}

/// 同じ呼び出しとポート幅に対して、元の構文から得られる引数列は一意に決まる。
proof fn source_call_argument_lists_agree(
    source: &crate::project::ProjectSource, parsed: &crate::syntax::circuit::NamedBuildCircuit,
    left_wiring: &FuncWiring, right_wiring: &FuncWiring, entry: usize, definition: usize,
    call: crate::syntax::circuit::CallShape, limit: u64, inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>,
    widths: Seq<u64>, left: Seq<Seq<bool>>, right: Seq<Seq<bool>>,
)
    requires
        parsed_circuit_matches(*source, *parsed),
        entry < parsed.syntax.entries@.len(),
        left_wiring.signals@ == right_wiring.signals@,
        source_call_arguments_match(source, parsed, left_wiring, entry, definition, call, limit, inputs, prior, widths, left),
        source_call_arguments_match(source, parsed, right_wiring, entry, definition, call, limit, inputs, prior, widths, right),
    ensures left == right,
{
    let forms = parsed.syntax.forms@;
    let a = choose|positions: Seq<usize>| #[trigger] crate::syntax::circuit::call_argument_positions(forms, call, positions)
        && positions.len() == left.len() == widths.len()
        && forall|i: int| 0 <= i < positions.len() ==>
            source_call_argument_value(source, parsed, left_wiring, entry, definition, #[trigger] positions[i],
                limit, inputs, prior, widths[i], left[i]);
    let b = choose|positions: Seq<usize>| #[trigger] crate::syntax::circuit::call_argument_positions(forms, call, positions)
        && positions.len() == right.len() == widths.len()
        && forall|i: int| 0 <= i < positions.len() ==>
            source_call_argument_value(source, parsed, right_wiring, entry, definition, #[trigger] positions[i],
                limit, inputs, prior, widths[i], right[i]);
    crate::syntax::circuit::call_argument_positions_agree(forms, call, a, b);
    assert forall|i: int| 0 <= i < left.len() implies #[trigger] left[i] == right[i] by {
        source_call_argument_values_agree(source, parsed, left_wiring, right_wiring, entry, definition, a[i],
            limit, inputs, prior, widths[i], left[i], right[i]);
    };
    assert(left =~= right);
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// ソースの右辺が指す関数と、その出力を受け取る左辺の範囲を定める。
    #[verifier::opaque]
    pub(super) closed spec fn source_function_call_site(
        &self, caller: (usize, usize, u64), wiring: &FuncWiring, definition: usize,
        signature: TypedFuncCall, outputs: Range<usize>, target: (usize, usize),
    ) -> bool {
        let (file, entry, limit) = caller;
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[file as int];
        let source = &project.sources_model()[file as int];
        let frame = parsed.entry_ranges@[entry as int].definitions;
        let row = parsed.definitions@[definition as int];
        let expression = row.expression;
        let (first, end) = crate::syntax::circuit::definition_target_range(parsed.syntax.forms@, row);

        &&& self.func_wiring_evidence(file, entry, limit, Ok(FuncWiringResult::Checked(*wiring)))
        &&& file < project.circuits_model().len() && file < project.sources_model().len()
        &&& entry < parsed.entry_ranges@.len()
        &&& frame.start <= definition < frame.end <= parsed.definitions@.len()
        &&& signature.call.call.form == expression.start
        &&& crate::syntax::circuit::ordinary_call_at(source.text, parsed.syntax.forms@, expression.start as int, expression.end as int)
        &&& self.func_call_signature_evidence(file, entry, (definition - frame.start) as usize, 0, limit, Ok(Some(signature)))
        &&& signature.call.target matches super::super::FuncCallTarget::Function { file: callee_file, entry: callee_entry, .. }
        &&& (callee_file, callee_entry) == target
        &&& signature.signature matches super::super::FuncCallSignature::Function(ports)
        &&& outputs.start < outputs.end <= wiring.drivers.definitions@.len()
        &&& outputs.end - outputs.start == ports.outputs@.len() == end - first
        &&& forall|i: int| outputs.start <= i < outputs.end ==> {
            let driver = #[trigger] wiring.drivers.definitions@[i];
            &&& driver.definition == definition
            &&& driver.result_index == i - outputs.start
        }
    }

    /// 左辺の添字から、元の定義と解決済みの関数参照を取り出す。
    pub(super) proof fn source_function_call_site_evidence(
        &self, caller: (usize, usize, u64), wiring: &FuncWiring, slot: int, definition: usize,
        signature: TypedFuncCall, outputs: Range<usize>, target: (usize, usize),
    )
        requires
            self.source_function_call_site(caller, wiring, definition, signature, outputs, target),
            outputs.start <= slot < outputs.end,
        ensures ({
            let (file, entry, limit) = caller;
            let project = self.targets.project_model();
            let parsed = &project.circuits_model()[file as int];
            let row = parsed.definitions@[definition as int];
            let local = (definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
            &&& slot < wiring.drivers.definitions@.len()
            &&& wiring.drivers.definitions@[slot].definition == definition
            &&& crate::syntax::circuit::ordinary_call_at(project.sources_model()[file as int].text,
                parsed.syntax.forms@, row.expression.start as int, row.expression.end as int)
            &&& self.func_call_signature_evidence(file, entry, local, 0, limit, Ok(Some(signature)))
            &&& signature.call.target is Function
        }),
    {
        reveal(UseAliases::source_function_call_site);
        assert(wiring.drivers.definitions@[slot].definition == definition);
    }

    /// 同じ左辺を評価する二つの導出は、同じ呼び出しと左辺区間を使う。
    pub(super) proof fn source_call_sites_agree(
        &self, caller: (usize, usize, u64), left: &FuncWiring, right: &FuncWiring, slot: int,
        a: (usize, TypedFuncCall, Range<usize>, (usize, usize)),
        b: (usize, TypedFuncCall, Range<usize>, (usize, usize)),
    )
        requires
            self.can_resolve(),
            self.source_function_call_site(caller, left, a.0, a.1, a.2, a.3),
            self.source_function_call_site(caller, right, b.0, b.1, b.2, b.3),
            a.2.start <= slot < a.2.end,
            b.2.start <= slot < b.2.end,
        ensures
            a.0 == b.0, a.1.call.call == b.1.call.call, a.2 == b.2, a.3 == b.3,
            a.1.signature matches super::super::FuncCallSignature::Function(x)
                && b.1.signature matches super::super::FuncCallSignature::Function(y)
                && x.inputs@ == y.inputs@ && x.outputs@ == y.outputs@,
    {
        reveal(UseAliases::source_function_call_site);
        self.checked_func_wiring_agrees(caller.0, caller.1, caller.2, *left, *right);
        let first = left.drivers.definitions@[slot];
        let second = right.drivers.definitions@[slot];
        assert(super::super::function_drivers::same_definition_driver(first, second));
        assert(first.definition == a.0 && second.definition == b.0);
        assert(first.result_index == slot - a.2.start && second.result_index == slot - b.2.start);
        let parsed = &self.targets.project_model().circuits_model()[caller.0 as int];
        let local = (a.0 - parsed.entry_ranges@[caller.1 as int].definitions.start) as usize;
        self.successful_call_signatures_agree(caller.0, caller.1, local, 0, caller.2, a.1, b.1);
    }

    /// 引数の値と呼び出し先の出力が、元の右辺と左辺に対応することを表す。
    pub(super) closed spec fn source_function_call_values(
        &self, caller: (usize, usize, u64), wiring: &FuncWiring, definition: usize,
        signature: TypedFuncCall, outputs: Range<usize>, target: (usize, usize),
        inputs: Seq<Seq<bool>>, values: Seq<Seq<bool>>, argument_widths: Seq<u64>,
        arguments: Seq<Seq<bool>>, results: Seq<Seq<bool>>,
    ) -> bool {
        let project = self.targets.project_model();
        &&& self.source_function_call_site(caller, wiring, definition, signature, outputs, target)
        &&& outputs.end <= values.len()
        &&& source_call_arguments_match(&project.sources_model()[caller.0 as int], &project.circuits_model()[caller.0 as int],
            wiring, caller.1, definition, signature.call.call, caller.2, inputs, values.take(outputs.start as int),
            argument_widths, arguments)
        &&& results == values.subrange(outputs.start as int, outputs.end as int)
    }

    /// ソースの呼び出し評価から、参照先と入出力ポートの対応を取り出す。
    pub(super) proof fn source_function_call_values_evidence(
        &self, caller: (usize, usize, u64), wiring: &FuncWiring, definition: usize,
        signature: TypedFuncCall, outputs: Range<usize>, target: (usize, usize),
        inputs: Seq<Seq<bool>>, values: Seq<Seq<bool>>, widths: Seq<u64>,
        arguments: Seq<Seq<bool>>, results: Seq<Seq<bool>>,
    )
        requires self.source_function_call_values(caller, wiring, definition, signature, outputs, target,
            inputs, values, widths, arguments, results),
        ensures
            self.source_function_call_site(caller, wiring, definition, signature, outputs, target),
            0 <= outputs.start < outputs.end <= values.len(),
            arguments.len() == widths.len(),
            forall|i: int| 0 <= i < arguments.len() ==> (#[trigger] arguments[i]).len() == widths[i],
            results == values.subrange(outputs.start as int, outputs.end as int),
    {
        reveal(UseAliases::source_function_call_site);
        reveal(source_call_argument_value);
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[caller.0 as int];
        let source = &project.sources_model()[caller.0 as int];
        let positions = choose|positions: Seq<usize>| #[trigger] crate::syntax::circuit::call_argument_positions(
            parsed.syntax.forms@, signature.call.call, positions)
            && positions.len() == arguments.len() == widths.len()
            && forall|i: int| 0 <= i < positions.len() ==>
                source_call_argument_value(source, parsed, wiring, caller.1, definition, #[trigger] positions[i],
                    caller.2, inputs, values.take(outputs.start as int), widths[i], arguments[i]);
        assert forall|i: int| 0 <= i < positions.len() implies (#[trigger] arguments[i]).len() == widths[i] by {
            assert(source_call_argument_value(source, parsed, wiring, caller.1, definition, positions[i],
                caller.2, inputs, values.take(outputs.start as int), widths[i], arguments[i]));
        };
    }

    /// 同じ構文と呼び出し直前の値から、同じポート幅の引数列が一意に決まる。
    pub(super) proof fn source_function_call_arguments_agree(
        &self, caller: (usize, usize, u64), left_wiring: &FuncWiring, right_wiring: &FuncWiring,
        definition: usize, left_call: TypedFuncCall, right_call: TypedFuncCall, outputs: Range<usize>,
        target: (usize, usize), inputs: Seq<Seq<bool>>, left_values: Seq<Seq<bool>>, right_values: Seq<Seq<bool>>,
        widths: Seq<u64>, left: Seq<Seq<bool>>, right: Seq<Seq<bool>>, left_results: Seq<Seq<bool>>, right_results: Seq<Seq<bool>>,
    )
        requires
            self.can_resolve(),
            left_call.call.call == right_call.call.call,
            self.source_function_call_values(caller, left_wiring, definition, left_call, outputs, target,
                inputs, left_values, widths, left, left_results),
            self.source_function_call_values(caller, right_wiring, definition, right_call, outputs, target,
                inputs, right_values, widths, right, right_results),
            left_values.take(outputs.start as int) == right_values.take(outputs.start as int),
        ensures left == right,
    {
        reveal(UseAliases::source_function_call_site);
        let (file, entry, limit) = caller;
        self.checked_func_wiring_agrees(file, entry, limit, *left_wiring, *right_wiring);
        self.checked_wiring_is_func(file, entry, limit, *left_wiring);
        self.targets.parsed_project_model();
        let project = self.targets.project_model();
        source_call_argument_lists_agree(&project.sources_model()[file as int], &project.circuits_model()[file as int],
            left_wiring, right_wiring, entry, definition, left_call.call.call, limit, inputs, left_values.take(outputs.start as int),
            widths, left, right);
    }

    pub(super) proof fn source_function_call_values_intro(
        &self, caller: (usize, usize, u64), wiring: &FuncWiring, definition: usize,
        signature: TypedFuncCall, outputs: Range<usize>, target: (usize, usize),
        inputs: Seq<Seq<bool>>, values: Seq<Seq<bool>>, argument_widths: Seq<u64>,
        arguments: Seq<Seq<bool>>, results: Seq<Seq<bool>>,
    )
        requires
            self.source_function_call_site(caller, wiring, definition, signature, outputs, target),
            outputs.end <= values.len(),
            ({
                let project = self.targets.project_model();
                source_call_arguments_match(&project.sources_model()[caller.0 as int], &project.circuits_model()[caller.0 as int],
                    wiring, caller.1, definition, signature.call.call, caller.2, inputs, values.take(outputs.start as int),
                    argument_widths, arguments)
            }),
            results == values.subrange(outputs.start as int, outputs.end as int),
        ensures self.source_function_call_values(caller, wiring, definition, signature, outputs, target,
            inputs, values, argument_widths, arguments, results),
    {}

    /// 準備した呼び出しから、ソース上の参照先と出力順の対応を取り出す。
    pub(super) proof fn prepared_call_matches_source_site(
        &self, plan: &FunctionExpansionOrder, caller: (usize, usize, u64), prepared: &PreparedExpansionBody, index: int,
    )
        requires
            self.can_resolve(),
            self.prepared_expansion_body_matches(*plan, caller.0, caller.1, caller.2, prepared),
            0 <= index < prepared.calls@.len(),
        ensures ({
            let group = prepared.calls@[index];
            let root = prepared.projections.calls@[index];
            let wiring = prepared.typed.literals.wiring->Checked_0;
            &&& self.source_function_call_site(caller, &wiring, root.definition, group._signature@, group.outputs,
                (root.target_file, root.target_entry))
            &&& 0 <= group._order@.0 < group._order@.1 < plan.order_model().len()
            &&& plan.position_model(group._order@.0) == Some((root.target_file, root.target_entry))
            &&& plan.position_model(group._order@.1) == Some((caller.0, caller.1))
        }),
    {
        reveal(UseAliases::checked_expansion_call_matches);
        reveal(UseAliases::root_call_result_types_match);
        reveal(UseAliases::source_function_call_site);
        let root = prepared.projections.calls@[index];
        let group = prepared.calls@[index];
        let wiring = prepared.typed.literals.wiring->Checked_0;
        let arguments = &prepared.projections.call_arguments;
        let range = arguments.ranges@[index];
        self.checked_types_keep_wiring(caller.0, caller.1, caller.2, prepared.typed, wiring);
        self.expansion_arguments_in_source_order(*plan, caller, prepared.typed, &wiring, root, range, arguments, group);
        self.checked_wiring_is_func(caller.0, caller.1, caller.2, wiring);

        assert(self.checked_expansion_call_matches(*plan, caller, prepared.typed, &wiring, root, range, arguments, group));
        assert(self.root_call_result_types_match(prepared.typed, wiring, root, group._signature@));
        assert(group.outputs.end <= wiring.drivers.definitions@.len());
        assert forall|i: int| group.outputs.start <= i < group.outputs.end implies {
            let driver = #[trigger] wiring.drivers.definitions@[i];
            &&& driver.definition == root.definition
            &&& driver.result_index == i - group.outputs.start
        } by {
            let port = i - root.first_output;
            let expected = group._signature@.signature->Function_0.outputs@[port];
            assert(prepared.typed.types@[root.first_output + port] == Some(SignalType {
                ty: expected.ty, origin: expected.annotation,
            }));
        };
        self.root_function_call_target_count(caller, &wiring.drivers, prepared.projections.calls@,
            prepared.typed.types@.len(), index);
    }

    #[verifier::opaque]
    pub(super) closed spec fn checked_expansion_call_matches(
        &self, plan: FunctionExpansionOrder, caller: (usize, usize, u64),
        typed: FuncSignalTypes, wiring: &FuncWiring, root: RootFunctionCall, inputs: Range<usize>,
        arguments: &CallArgumentProjections, group: CheckedExpansionCall,
    ) -> bool {
        let (file, entry, limit) = caller;
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[file as int];
        let source = &project.sources_model()[file as int];
        let definitions = parsed.entry_ranges@[entry as int].definitions;
        let expression = parsed.definitions@[root.definition as int].expression;
        let signature = group._signature@;
        let (callee_at, caller_at) = group._order@;
        &&& definitions.start <= root.definition < definitions.end <= parsed.definitions@.len()
        &&& crate::syntax::circuit::ordinary_call_at(source.text, parsed.syntax.forms@, expression.start as int, expression.end as int)
        &&& group.outputs.start == root.first_output
        &&& group.outputs.end == root.first_output + root.count
        &&& 0 < root.count && group.outputs.end <= typed.types@.len()
        &&& typed.types@.len() == wiring.drivers.definitions@.len()
        &&& is_form_location(source, parsed.syntax.forms@[parsed.definitions@[root.definition as int].expression.start as int],
            group.expression)
        &&& group.arguments == inputs && inputs.start <= inputs.end <= arguments.arguments@.len()
        &&& 0 <= callee_at < caller_at < plan.order_model().len()
        &&& plan.position_model(callee_at) == Some((root.target_file, root.target_entry))
        &&& plan.position_model(caller_at) == Some((file, entry))
        &&& group.vertex == plan.order_model()[callee_at]
        &&& self.func_call_signature_evidence(file, entry, (root.definition - definitions.start) as usize, 0, limit,
            Ok(Some(signature)))
        &&& signature.call.target is Function
        &&& signature.call.target->Function_file == root.target_file
        &&& signature.call.target->Function_entry == root.target_entry
        &&& signature.signature is Function
        &&& signature.signature->Function_0.outputs@.len() == root.count
        &&& inputs.end - inputs.start == signature.signature->Function_0.inputs@.len()
        &&& self.root_call_result_types_match(typed, *wiring, root, signature)
        &&& self.projected_input_arguments((file, entry, (root.definition - definitions.start) as usize, 0), limit,
            typed.types@, wiring, arguments.arguments@.subrange(inputs.start as int, inputs.end as int))
    }

    /// 呼び出しの各左辺に、宣言上の同じ番号の出力型が付いていることを示す。
    pub(super) proof fn expansion_call_output_types(
        &self, plan: FunctionExpansionOrder, caller: (usize, usize, u64), typed: FuncSignalTypes,
        wiring: &FuncWiring, root: RootFunctionCall, inputs: Range<usize>, arguments: &CallArgumentProjections,
        group: CheckedExpansionCall,
    )
        requires self.checked_expansion_call_matches(plan, caller, typed, wiring, root, inputs, arguments, group),
        ensures
            location_in_source(group.expression),
            group._signature@.signature is Function,
            group.outputs.start < group.outputs.end <= typed.types@.len(),
            group.outputs.end - group.outputs.start == group._signature@.signature->Function_0.outputs@.len(),
            ({
                let project = self.targets.project_model();
                let parsed = &project.circuits_model()[caller.0 as int];
                let source = &project.sources_model()[caller.0 as int];
                let expression = parsed.definitions@[root.definition as int].expression;
                &&& crate::syntax::circuit::ordinary_call_at(source.text, parsed.syntax.forms@,
                    expression.start as int, expression.end as int)
                &&& forall|i: int| group.outputs.start <= i < group.outputs.end ==>
                    (#[trigger] wiring.drivers.definitions@[i]).definition == root.definition
            }),
            forall|port: int| 0 <= port < group.outputs.end - group.outputs.start ==> {
                let expected = group._signature@.signature->Function_0.outputs@[port];
                (#[trigger] typed.types@[group.outputs.start + port]) == Some(SignalType {
                    ty: expected.ty, origin: expected.annotation,
                })
            },
    {
        reveal(UseAliases::checked_expansion_call_matches);
        reveal(UseAliases::root_call_result_types_match);
        assert forall|i: int| group.outputs.start <= i < group.outputs.end implies
            (#[trigger] wiring.drivers.definitions@[i]).definition == root.definition by {
            let port = i - root.first_output;
            let output = group._signature@.signature->Function_0.outputs@[port];
            assert(0 <= port < root.count);
            assert(typed.types@[root.first_output + port] == Some(SignalType {
                ty: output.ty, origin: output.annotation,
            }));
        };
    }

    /// 平坦な引数区間が、呼び出し直下のフォームを元の順序で指すことを示す。
    pub(super) proof fn expansion_arguments_in_source_order(
        &self, plan: FunctionExpansionOrder, caller: (usize, usize, u64), typed: FuncSignalTypes,
        wiring: &FuncWiring, root: RootFunctionCall, range: Range<usize>, arguments: &CallArgumentProjections,
        group: CheckedExpansionCall,
    )
        requires
            self.can_resolve(),
            self.func_wiring_evidence(caller.0, caller.1, caller.2, Ok(FuncWiringResult::Checked(*wiring))),
            self.checked_expansion_call_matches(plan, caller, typed, wiring, root, range, arguments, group),
        ensures ({
            let forms = self.targets.project_model().circuits_model()[caller.0 as int].syntax.forms@;
            let projected = arguments.arguments@.subrange(range.start as int, range.end as int);
            let parsed = &self.targets.project_model().circuits_model()[caller.0 as int];
            &&& caller.1 < parsed.entry_ranges@.len()
            &&& parsed.entry_ranges@[caller.1 as int].definitions.start <= root.definition
                < parsed.entry_ranges@[caller.1 as int].definitions.end <= parsed.definitions@.len()
            &&& group._signature@.call.call.form == parsed.definitions@[root.definition as int].expression.start
            &&& crate::syntax::circuit::call_argument_positions(forms, group._signature@.call.call,
                Seq::new(projected.len(), |i: int| projected[i].form))
        }),
    {
        reveal(UseAliases::checked_expansion_call_matches);
        let (file, entry, limit) = caller;
        let parsed = &self.targets.project_model().circuits_model()[file as int];
        let local = (root.definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
        let projected = arguments.arguments@.subrange(range.start as int, range.end as int);
        self.projected_arguments_in_source_order((file, entry, local, 0), limit, typed.types@, wiring, group._signature@, projected);
        self.typed_call_arguments_ready(file, entry, local, 0, limit, group._signature@);
        self.targets.parsed_project_model();
        let source = &self.targets.project_model().sources_model()[file as int];
        parsed_index_evidence(*source, *parsed);
        build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, root.definition as int);
        vstd::std_specs::vec::axiom_spec_len(&parsed.syntax.forms);
        crate::syntax::circuit::root_call_shape_location(source.text, parsed.syntax.forms@,
            parsed.definitions@[root.definition as int], parsed.references@, group._signature@.call.call);
    }

    /// 展開に渡す引数の型と、呼び出し前に参照できる駆動元を取り出す。
    pub(super) proof fn expansion_argument_evidence(
        &self, plan: FunctionExpansionOrder, caller: (usize, usize, u64), typed: FuncSignalTypes,
        wiring: &FuncWiring, root: RootFunctionCall, range: Range<usize>, arguments: &CallArgumentProjections,
        group: CheckedExpansionCall, port: int,
    )
        requires
            self.can_resolve(),
            self.func_wiring_evidence(caller.0, caller.1, caller.2, Ok(FuncWiringResult::Checked(*wiring))),
            self.checked_expansion_call_matches(plan, caller, typed, wiring, root, range, arguments, group),
            0 <= port < range.end - range.start,
        ensures ({
            let argument = arguments.arguments@[range.start + port];
            let project = self.targets.project_model();
            let parsed = &project.circuits_model()[caller.0 as int];
            let source = &project.sources_model()[caller.0 as int];
            let form = parsed.syntax.forms@[argument.form as int];
            let expected = group._signature@.signature->Function_0.inputs@[port].ty;
            let frame = parsed.entry_ranges@[caller.1 as int];
            let row = parsed.definitions@[root.definition as int];
            &&& argument.form < parsed.syntax.forms@.len()
            &&& crate::syntax::circuit::direct_call_argument(
                parsed.syntax.forms@, group._signature@.call.call, argument.form as int)
            &&& form is Atom || !argument.source.has_direct_wires()
            &&& match argument.source {
                CallArgumentSource::Driver(driver) => {
                    &&& form is Atom && form->Atom_kind is Name
                    &&& signal_type_at(wiring, typed.types@, driver) matches Some(known)
                    &&& crate::project::port_types_equal(known.ty, expected)
                    &&& exists|position: int| row.signals.start <= position < row.signals.end
                        && (#[trigger] parsed.signals@[position]) == argument.form
                        && 0 <= position - frame.signals.start < wiring.signals@.len()
                        && wiring.signals@[position - frame.signals.start].driver == driver
                    &&& match driver {
                        super::super::OutputDriver::Input(i) => i < wiring.drivers.signature.inputs@.len(),
                        super::super::OutputDriver::Definition(i) => i < group.outputs.start,
                    }
                },
                CallArgumentSource::Literal(width) => {
                    let span = crate::syntax::form_span(form);
                    let bytes = source.text.spec_bytes()[span.start as int..span.end as int];
                    &&& expected == super::super::ResolvedPortType::Bits(width)
                    &&& form is Atom
                    &&& span.start < span.end <= source.text.spec_bytes().len()
                    &&& (form->Atom_kind is Natural || form->Atom_kind is Binary || form->Atom_kind is Hexadecimal)
                    &&& crate::project::circuit_literal_width_matches(bytes, Some(width), caller.2, Ok(width))
                    &&& ((width == 1 && bytes.len() == 1 && (bytes[0] == b'0' || bytes[0] == b'1'))
                        || crate::syntax::bare_atom_kind(bytes) == Some(crate::syntax::AtomKind::Binary)
                        || crate::syntax::bare_atom_kind(bytes) == Some(crate::syntax::AtomKind::Hexadecimal))
                },
                CallArgumentSource::NestedCall => {
                    let local = (root.definition - frame.definitions.start) as usize;
                    &&& form is List
                    &&& exists|reference: usize, child: TypedFuncCall|
                        #[trigger] self.func_call_form_reference(caller.0, caller.1, local, argument.form, reference)
                        && #[trigger] self.func_call_signature_evidence(caller.0, caller.1, local, reference, caller.2, Ok(Some(child)))
                        && child.call.target.port_counts().outputs == 1
                        && match child.signature {
                            crate::project::FuncCallSignature::Nor =>
                                crate::project::port_types_equal(crate::project::ResolvedPortType::Bits(1), expected),
                            crate::project::FuncCallSignature::Function(ports) =>
                                crate::project::port_types_equal(ports.outputs@[0].ty, expected),
                        }
                },
                CallArgumentSource::Deferred => true,
            }
        }),
    {
        reveal(UseAliases::checked_expansion_call_matches);
        self.expansion_call_output_types(plan, caller, typed, wiring, root, range, arguments, group);
        let (file, entry, limit) = caller;
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[file as int];
        let local = (root.definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
        let projected = arguments.arguments@.subrange(range.start as int, range.end as int);
        self.checked_projected_argument((file, entry, local, 0), limit, typed.types@, wiring, group._signature@, projected, port);
        assert(projected[port] == arguments.arguments@[range.start + port]);
        if projected[port].source is NestedCall {
            let form = projected[port].form;
            let expected = group._signature@.signature->Function_0.inputs@[port].ty;
            let (reference, child) = self.projected_nested_call_signature((file, entry, local), limit, form, expected);
            assert(self.func_call_form_reference(file, entry, local, form, reference));
            assert(self.func_call_signature_evidence(file, entry, local, reference, limit, Ok(Some(child))));
        }
        if let CallArgumentSource::Driver(super::super::OutputDriver::Definition(i)) = projected[port].source {
            self.checked_wiring_is_func(file, entry, limit, *wiring);
            let first = group.outputs.start as int;
            assert(first < wiring.drivers.definitions@.len());
            assert(wiring.drivers.definitions@[first].definition == root.definition);
            assert(wiring.drivers.definitions@[i as int].definition < root.definition);
            if first < i {
                assert(wiring.drivers.definitions@[first].definition <= wiring.drivers.definitions@[i as int].definition);
            }
            assert(i < first);
        }
    }

    /// 展開前に保持した実引数の値が、元フォームから定めた値であることを示す。
    pub(super) proof fn expansion_argument_value_from_source(
        &self, plan: FunctionExpansionOrder, caller: (usize, usize, u64), typed: FuncSignalTypes,
        wiring: &FuncWiring, root: RootFunctionCall, range: Range<usize>, arguments: &CallArgumentProjections,
        group: CheckedExpansionCall, port: int, inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>,
        width: u64, value: Seq<bool>,
    )
        requires
            self.can_resolve(),
            self.func_wiring_evidence(caller.0, caller.1, caller.2, Ok(FuncWiringResult::Checked(*wiring))),
            self.checked_expansion_call_matches(plan, caller, typed, wiring, root, range, arguments, group),
            0 <= port < range.end - range.start,
            inputs.len() == wiring.drivers.signature.inputs@.len(),
            prior.len() == group.outputs.start,
            value.len() == width,
            ({
                let argument = arguments.arguments@[range.start + port];
                match argument.source {
                    CallArgumentSource::Driver(driver) => value == super::semantics::driver_values(inputs, prior, driver),
                    CallArgumentSource::Literal(bits) => {
                        let project = self.targets.project_model();
                        let bytes = source_argument_bytes(&project.sources_model()[caller.0 as int],
                            project.circuits_model()[caller.0 as int].syntax.forms@, argument.form);
                        width == bits && value == Seq::new(width as nat, |bit: int| call_literal_bit(bytes, bit as nat))
                    },
                    CallArgumentSource::Deferred | CallArgumentSource::NestedCall => false,
                }
            }),
        ensures ({
            let project = self.targets.project_model();
            source_call_argument_value(&project.sources_model()[caller.0 as int], &project.circuits_model()[caller.0 as int],
                wiring, caller.1, root.definition, arguments.arguments@[range.start + port].form, caller.2,
                inputs, prior, width, value)
        }),
    {
        reveal(source_call_argument_value);
        self.expansion_argument_evidence(plan, caller, typed, wiring, root, range, arguments, group, port);
        self.checked_wiring_is_func(caller.0, caller.1, caller.2, *wiring);
        reveal(UseAliases::checked_expansion_call_matches);
        self.targets.parsed_project_model();
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[caller.0 as int];
        let source = &project.sources_model()[caller.0 as int];
        parsed_index_evidence(*source, *parsed);
        build_entry_ranges_evidence(source.text, &parsed.build_model(), caller.1 as int);
        build_definition_scope_evidence(source.text, &parsed.build_model(), caller.1 as int, root.definition as int);
    }

    /// 確定した呼び出し先の順位と、その宣言から得た署名を示す。
    pub(super) proof fn expansion_callee_template_evidence(
        &self, plan: FunctionExpansionOrder, caller: (usize, usize, u64),
        prepared: &PreparedExpansionBody, index: int,
    )
        requires self.prepared_expansion_body_matches(plan, caller.0, caller.1, caller.2, prepared),
            0 <= index < prepared.calls@.len(),
        ensures ({
            let group = prepared.calls@[index];
            let (callee, source) = group._order@;
            &&& 0 <= callee < source < plan.order_model().len()
            &&& plan.position_model(source) == Some((caller.0, caller.1))
            &&& group.vertex == plan.order_model()[callee]
            &&& group._signature@.signature matches crate::project::FuncCallSignature::Function(signature)
            &&& *group.expression.source == self.targets.project_model().sources_model()[caller.0 as int]
            &&& group.arguments == prepared.projections.call_arguments.ranges@[index]
            &&& group.arguments.start <= group.arguments.end <= prepared.projections.call_arguments.arguments@.len()
            &&& group.arguments.end - group.arguments.start == signature.inputs@.len()
            &&& group.outputs.start < group.outputs.end
            &&& plan.position_model(callee) matches Some(target)
            &&& self.typed_signature_evidence(target.0, target.1, caller.2, Ok(Some(signature)))
        }),
    {
        reveal(UseAliases::checked_expansion_call_matches);
        let group = prepared.calls@[index];
        let root = prepared.projections.calls@[index];
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[caller.0 as int];
        let local = (root.definition - parsed.entry_ranges@[caller.1 as int].definitions.start) as usize;
        self.resolved_function_signature_evidence((caller.0, caller.1, local, 0), caller.2, group._signature@);
    }

    fn check_expansion_call_groups(
        &self, plan: &FunctionExpansionOrder<'p, 'a>, file: usize, entry: usize, limit: u64,
        typed: &FuncSignalTypes<'p, 'a>, wiring: &FuncWiring<'p, 'a>, projections: &FuncProjections<'p, 'a>,
    ) -> (groups: Vec<CheckedExpansionCall<'p, 'a>>)
        requires
            self.can_resolve(), self.function_expansion_evidence(Ok(*plan)),
            self.func_signal_types_evidence(file, entry, limit, Ok(*typed)),
            typed.literals.wiring == FuncWiringResult::Checked(*wiring),
            typed.types@.len() == wiring.drivers.definitions@.len(),
            self.root_function_calls_match((file, entry, limit), &wiring.drivers, projections.calls@, typed.types@.len()),
            projections.call_arguments.ranges@.len() == projections.calls@.len(),
            self.projected_roots_match((file, entry, limit), typed.types@, wiring, projections.calls@,
                projections.call_arguments.ranges@, projections.call_arguments.arguments@),
        ensures
            groups@.len() == projections.calls@.len(),
            forall|i: int, j: int| 0 <= i < j < groups@.len()
                ==> (#[trigger] groups@[i]).outputs.end <= (#[trigger] groups@[j]).outputs.start,
            forall|i: int| 0 <= i < groups@.len() ==> self.checked_expansion_call_matches(*plan, (file, entry, limit), *typed,
                wiring, projections.calls@[i], projections.call_arguments.ranges@[i], &projections.call_arguments,
                #[trigger] groups@[i]),
    {
        let ghost caller = (file, entry, limit);
        let project = self.targets.project();
        proof {
            self.checked_types_keep_wiring(file, entry, limit, *typed, *wiring);
            self.checked_wiring_is_func(file, entry, limit, *wiring);
            self.root_calls_follow_definition_order(caller, wiring, projections.calls@);
        }
        let parsed = &project.circuits()[file];
        let source = &project.sources()[file];
        let forms = parsed.syntax.forms.as_slice();
        proof {
            parsed_index_evidence(*source, *parsed);
            build_entry_ranges_evidence(source.text, &parsed.build_model(), entry as int);
        }
        let mut groups: Vec<CheckedExpansionCall<'p, 'a>> = Vec::new();
        let mut index = 0;
        while index < projections.calls.len()
            invariant
                caller == (file, entry, limit),
                self.can_resolve(), self.function_expansion_evidence(Ok(*plan)),
                self.func_signal_types_evidence(file, entry, limit, Ok(*typed)),
                typed.literals.wiring == FuncWiringResult::Checked(*wiring),
                typed.types@.len() == wiring.drivers.definitions@.len(),
                self.root_function_calls_match(caller, &wiring.drivers, projections.calls@, typed.types@.len()),
                self.root_call_definitions_in_order(file, entry, projections.calls@),
                projections.call_arguments.ranges@.len() == projections.calls@.len(),
                self.projected_roots_match(caller, typed.types@, wiring, projections.calls@,
                    projections.call_arguments.ranges@, projections.call_arguments.arguments@),
                index == groups@.len() <= projections.calls@.len(),
                file < self.targets.project_model().circuits_model().len(),
                file < self.targets.project_model().sources_model().len(),
                *parsed == self.targets.project_model().circuits_model()[file as int],
                *source == self.targets.project_model().sources_model()[file as int],
                parsed_circuit_matches(*source, *parsed),
                entry < parsed.syntax.entries@.len(), entry < parsed.entry_ranges@.len(),
                forms@ == parsed.syntax.forms@,
                parsed.entry_ranges@[entry as int].definitions.end <= parsed.definitions@.len(),
                crate::syntax::form_spans_valid(source.text, forms@, source.text.spec_bytes().len() as int),
                forall|j: int| 0 <= j < groups@.len() ==> self.checked_expansion_call_matches(*plan, caller, *typed,
                    wiring, projections.calls@[j], projections.call_arguments.ranges@[j], &projections.call_arguments,
                    #[trigger] groups@[j]),
            decreases projections.calls@.len() - index,
        {
            let root = &projections.calls[index];
            let ghost group_model = self.checked_root_call_for_expansion(*plan, caller, *typed, *wiring,
                projections.calls@, index as int);
            let arguments = &projections.call_arguments.ranges[index];
            let target = (root.target_file, root.target_entry);
            let vertex = plan.template_vertex(target);
            proof { plan.template_vertex_at_position(target, group_model.1.0, vertex); }
            let Some(vertex) = vertex else {
                proof { assert(false); }
                unreachable!()
            };
            proof {
                vstd::std_specs::vec::axiom_spec_len(&typed.types);
                parsed_index_evidence(*source, *parsed);
                build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, root.definition as int);
                self.projected_root_argument_range(caller, typed.types@, wiring, projections.calls@,
                    projections.call_arguments.ranges@, projections.call_arguments.arguments@, index as int);
                let start = parsed.entry_ranges@[entry as int].definitions.start;
                self.checked_projected_input_count((file, entry, (root.definition - start) as usize, 0),
                    limit, typed.types@, wiring, group_model.0,
                    projections.call_arguments.arguments@.subrange(arguments.start as int, arguments.end as int));
            }
            let expression = form_location(source, forms, parsed.definitions[root.definition].expression.start);
            let group = CheckedExpansionCall {
                expression,
                outputs: root.first_output..root.first_output + root.count,
                arguments: arguments.start..arguments.end,
                vertex, _signature: Ghost(group_model.0), _order: Ghost(group_model.1),
            };
            assert(self.checked_expansion_call_matches(*plan, caller, *typed, wiring, *root, *arguments,
                &projections.call_arguments, group)) by { reveal(UseAliases::checked_expansion_call_matches); };
            let ghost prior = groups@;
            groups.push(group);
            assert forall|j: int| 0 <= j < groups@.len() implies self.checked_expansion_call_matches(*plan, caller, *typed,
                wiring, projections.calls@[j], projections.call_arguments.ranges@[j], &projections.call_arguments,
                #[trigger] groups@[j]) by {
                if j < index { assert(groups@[j] == prior[j]); }
            };
            index += 1;
        }
        proof {
            assert forall|i: int, j: int| 0 <= i < j < groups@.len()
                implies (#[trigger] groups@[i]).outputs.end <= (#[trigger] groups@[j]).outputs.start by {
                reveal(UseAliases::checked_expansion_call_matches);
                assert(projections.calls@[i].first_output + projections.calls@[i].count <= projections.calls@[j].first_output);
            };
        }
        groups
    }

    pub(super) open spec fn prepared_expansion_body_matches(
        &self, plan: FunctionExpansionOrder, file: usize, entry: usize, limit: u64, body: &PreparedExpansionBody,
    ) -> bool {
        &&& self.func_signal_types_evidence(file, entry, limit, Ok(body.typed))
        &&& body.typed.literals.wiring matches FuncWiringResult::Checked(wiring)
        &&& body.typed.types@.len() == wiring.drivers.definitions@.len()
        &&& body.projections.layouts.is_none() ==> body.projections.entries@.len() == 0
        &&& body.projections.layouts matches Some(table) ==> {
            &&& self.structure_types_match(limit, Ok(table))
            &&& forall|j: int| 0 <= j < body.projections.entries@.len() ==>
                structure_projection_matches(self, file, entry, limit, &wiring, table, body.typed.types@,
                    #[trigger] body.projections.entries@[j])
        }
        &&& structure_projections_in_order(body.projections.entries@, body.typed.types@.len() as int,
            wiring.drivers.signature.inputs@.len() as int)
        &&& self.func_structure_projections_complete(file, entry, limit, body.typed, &wiring, body.projections.entries@)
        &&& self.func_concat_projections_complete(file, entry, limit, body.typed, &wiring, body.projections.concats@)
        &&& concat_projections_match(file, entry, limit, &self.targets.project_model().sources_model()[file as int],
            &self.targets.project_model().circuits_model()[file as int], &wiring, body.typed.types@, body.projections.concats@)
        &&& self.root_function_calls_match((file, entry, limit), &wiring.drivers,
            body.projections.calls@, body.typed.types@.len())
        &&& body.calls@.len() == body.projections.calls@.len()
        &&& forall|i: int, j: int| 0 <= i < j < body.calls@.len() ==>
            (#[trigger] body.calls@[i]).outputs.end <= (#[trigger] body.calls@[j]).outputs.start
        &&& body.projections.call_arguments.ranges@.len() == body.calls@.len()
        &&& forall|i: int| 0 <= i < body.calls@.len() ==> self.checked_expansion_call_matches(plan, (file, entry, limit),
            body.typed, &wiring, body.projections.calls@[i], body.projections.call_arguments.ranges@[i],
            &body.projections.call_arguments, #[trigger] body.calls@[i])
    }

    pub(super) closed spec fn expansion_body_preparation_result(
        &self, plan: FunctionExpansionOrder, file: usize, entry: usize, limit: u64,
        result: Result<PreparedExpansionBody, BitFuncError>,
    ) -> bool {
        match result {
            Ok(body) => self.prepared_expansion_body_matches(plan, file, entry, limit, &body),
            Err(BitFuncError::Check(error)) => self.func_signal_types_evidence(file, entry, limit, Err(error)),
            Err(BitFuncError::NotFunc) => exists|typed: FuncSignalTypes|
                #[trigger] self.func_signal_types_evidence(file, entry, limit, Ok(typed)) && typed.literals.wiring is NotFunc,
            Err(BitFuncError::NeedsExpansion(site)) => exists|typed: FuncSignalTypes|
                #[trigger] self.func_signal_types_evidence(file, entry, limit, Ok(typed))
                    && typed.literals.wiring == FuncWiringResult::NeedsExpansion(site),
            _ => false,
        }
    }

    /// 構文と型を検査し、通常呼び出しを一回ずつ展開できる形で保持する。
    pub(super) fn prepare_expansion_body(
        &self, plan: &FunctionExpansionOrder<'p, 'a>, file: usize, entry: usize, limit: u64,
    ) -> (result: Result<PreparedExpansionBody<'p, 'a>, BitFuncError<'p, 'a>>)
        requires self.can_resolve(), self.function_expansion_evidence(Ok(*plan)),
        ensures
            self.expansion_body_preparation_result(*plan, file, entry, limit, result),
            result matches Ok(body) ==> self.prepared_expansion_body_matches(*plan, file, entry, limit, &body),
    {
        let (typed, projections) = match self.check_func_signal_projections(file, entry, limit, true, true) {
            Ok(result) => result,
            Err(error) => return Err(BitFuncError::Check(error)),
        };
        let wiring = match &typed.literals.wiring {
            FuncWiringResult::Checked(wiring) => wiring,
            FuncWiringResult::NotFunc => return Err(BitFuncError::NotFunc),
            FuncWiringResult::NeedsExpansion(site) => return Err(BitFuncError::NeedsExpansion(
                super::super::function_atoms::copy_location(site))),
        };
        let calls = self.check_expansion_call_groups(plan, file, entry, limit, &typed, wiring, &projections);
        Ok(PreparedExpansionBody { typed, projections, calls })
    }
}

} // verus!
