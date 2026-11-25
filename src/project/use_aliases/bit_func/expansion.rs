//! 型検査済みの通常呼び出しを、展開順と出力の左辺に結び付ける。

use super::frontend::BitFuncError;
#[cfg(verus_only)]
use super::frontend::nor_definition_determined;
use super::super::{FuncSignalTypes, FuncWiring, FuncWiringResult, FunctionExpansionOrder, TypedFuncCall, UseAliases};
use super::super::call_arity::RetainedCallTarget;
#[cfg(verus_only)]
use super::super::call_arity::{CallArgumentProjections, CallArgumentSource, ProjectedCallArgument, RootFunctionCall};
use super::super::function_atoms::{FuncProjections, SignalType};
#[cfg(verus_only)]
use super::super::function_atoms::{concat_projections_match, signal_type_at, structure_projection_matches,
    structure_projections_in_order};
use crate::project::LocatedName;
#[cfg(verus_only)]
use crate::project::{DefinitionPosition, FuncCallTarget};
#[cfg(verus_only)]
use crate::project::location_in_source;
use crate::project::circuits::form_location;
#[cfg(verus_only)]
use crate::project::circuits::{is_form_location, parsed_circuit_matches, parsed_index_evidence};
#[cfg(verus_only)]
use crate::syntax::circuit::{build_definition_scope_evidence, build_entry_ranges_evidence};
use crate::syntax::circuit::{definition_root_is_call, definition_target_atoms, postorder_call_references};
#[cfg(verus_only)]
use crate::syntax::circuit::{
    call_postorder_positions, call_postorder_reference, call_postorder_references_distinct, call_references_in_postorder,
    definition_reference_form_unique,
    nested_call_postorder_position, root_call_postorder_last, root_call_reference,
};
use alloc::vec::Vec;
use core::ops::Range;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

#[cfg(test)]
mod tests {
    use alloc::vec::Vec;
    use crate::project::{SourceSnapshot, check_use_aliases, index_use_targets, parse_circuit_project};
    use crate::project::use_aliases::call_arity::CallArgumentSource;

    #[test]
    fn prepares_the_nested_call_order_for_a_checked_root() {
        let text = concat!(
            "(using nor) (func id (in a) (out a)) ",
            "(func caller (in a) (out y) ",
            " (def earlier (id a)) (def y (id (id (nor earlier a)))))",
        );
        let project = parse_circuit_project(&[SourceSnapshot { path: "calls.ncg2", revision: 1, text }]).unwrap();
        let targets = index_use_targets(&project).unwrap();
        let aliases = check_use_aliases(&targets).unwrap();
        let plan = aliases.prepare_function_expansion().unwrap();
        let prepared = aliases.prepare_expansion_body(&plan, 0, 2, 8).unwrap();
        assert!(prepared.calls[0].postorder.is_none());
        let order = prepared.calls[1].postorder.as_deref().unwrap();
        let refs = &project.circuits()[0].references;
        let locations: Vec<_> = order.iter().map(|call| refs[call.reference].span.start).collect();
        assert_eq!(locations, [
            text.find("nor earlier").unwrap(),
            text.find("id (nor").unwrap(),
        ]);
        assert!(order[0].vertex.is_none());
        assert_eq!(order[0].arguments, 3..5);
        assert_eq!(order[1].vertex, Some(prepared.calls[1].vertex));
        assert_eq!(order[1].arguments, 2..3);
        assert_eq!(prepared.calls[1].arguments, 1..2);
        let arguments = &prepared.projections.call_arguments.arguments;
        assert!(matches!(arguments[1].source, CallArgumentSource::NestedCall(1)));
        assert!(matches!(arguments[2].source, CallArgumentSource::NestedCall(2)));
    }
}

verus! {

/// 元の参照に対応する実引数と、既に展開順が決まった呼び出し先。
pub(super) struct PreparedExpressionCall<'p, 'a> {
    /// 厳格解析で作ったファイル全体の参照配列を指す添字。
    pub(super) reference: usize,
    /// 呼び出し式全体の UTF-8 半開バイト範囲と、その文書版を持つソース。
    pub(super) expression: LocatedName<'p, 'a>,
    /// 型検査済みの実引数配列で、この呼び出しの引数を指す半開範囲。
    pub(super) arguments: Range<usize>,
    /// 通常関数のテンプレート番号。組み込み NOR には番号がない。
    pub(super) vertex: Option<usize>,
    pub(super) _signature: Ghost<TypedFuncCall<'p, 'a>>,
    pub(super) _rank: Ghost<Option<int>>,
}

pub(super) open spec fn prepared_nested_output_matches(
    children: Seq<PreparedExpressionCall>, first: usize, before: int, argument: ProjectedCallArgument,
    expected: crate::project::ResolvedPortType,
) -> bool {
    &&& argument.source is NestedCall
    &&& 0 <= before <= children.len()
    &&& exists|i: int| 0 <= i < before
        && (#[trigger] children[i]).reference == first + argument.source->NestedCall_0
        && children[i]._signature@.call.call.form == argument.form
        && children[i]._signature@.call.target.port_counts().outputs == 1
        && match children[i]._signature@.signature {
            crate::project::FuncCallSignature::Nor =>
                crate::project::port_types_equal(crate::project::ResolvedPortType::Bits(1), expected),
            crate::project::FuncCallSignature::Function(ports) =>
                ports.outputs@.len() == 1 && crate::project::port_types_equal(ports.outputs@[0].ty, expected),
        }
}

/// 一回の呼び出しで割り当てる左辺、引数範囲、展開済みの呼び出し先。
pub(super) struct CheckedExpansionCall<'p, 'a> {
    /// 呼び出し全体の元ソース範囲。
    pub(super) expression: LocatedName<'p, 'a>,
    /// 左辺の駆動元一覧で、出力ポートと同じ順の連続区間。
    pub(super) outputs: Range<usize>,
    /// 関数の平坦な実引数列における区間。
    pub(super) arguments: Range<usize>,
    /// 入れ子の呼び出しを、内側から外側へ処理する順に保持する。
    pub(super) postorder: Option<Vec<PreparedExpressionCall<'p, 'a>>>,
    /// 同じ定義に属する参照が収まる、ファイル全体の参照配列上の区間。
    pub(super) references: Range<usize>,
    /// 展開済み回路を保持する配列における呼び出し先の番号。
    pub(super) vertex: usize,
    pub(super) _signature: Ghost<TypedFuncCall<'p, 'a>>,
    pub(super) _order: Ghost<(int, int)>,
}

/// 入れ子の引数を持つ基底 NOR の根と、その定義に属する子呼び出し。
pub(super) struct PreparedNorRoot<'p, 'a> {
    /// ファイルの定義配列を参照する添字。
    pub(super) definition: usize,
    /// 駆動元配列で、この根の一ビット出力を指す添字。
    pub(super) output_slot: usize,
    pub(super) root: PreparedExpressionCall<'p, 'a>,
    pub(super) postorder: Vec<PreparedExpressionCall<'p, 'a>>,
    pub(super) _caller_rank: Ghost<int>,
}

/// 通常呼び出しを展開する前の関数本体と、型検査から得た各呼び出しの位置。
pub(super) struct PreparedExpansionBody<'p, 'a> {
    pub(super) typed: FuncSignalTypes<'p, 'a>,
    pub(super) projections: FuncProjections<'p, 'a>,
    pub(super) calls: Vec<CheckedExpansionCall<'p, 'a>>,
    /// 根 NOR の候補索引と同じ定義順に並ぶ。
    pub(super) nor_roots: Vec<PreparedNorRoot<'p, 'a>>,
}

/// 現在の出力スロットを持つ定義の種類。
pub(super) enum ExpansionSlot {
    Local,
    Function,
    Nor,
}

/// 現在の出力スロットと、通常呼び出しおよび根 NOR の次の出力を照合する。
///
/// 通常呼び出しの場合は、呼び出し側が出力区間の末尾まで進む。
/// 根 NOR と通常の右辺は1スロット分を占める。
#[inline]
pub(super) fn expansion_call_at_slot(function: Option<usize>, nor: Option<usize>, slot: usize) -> (position: ExpansionSlot)
    requires function.is_some() && nor.is_some() ==> function != nor,
    ensures
        (position is Function) <==> function == Some(slot),
        (position is Nor) <==> nor == Some(slot),
        (position is Local) <==> function != Some(slot) && nor != Some(slot),
{
    if function == Some(slot) {
        ExpansionSlot::Function
    } else if nor == Some(slot) {
        ExpansionSlot::Nor
    } else {
        ExpansionSlot::Local
    }
}

pub(super) open spec fn expansion_parent_range(group: &CheckedExpansionCall, children: Seq<PreparedExpressionCall>, parent: int)
    -> Range<usize> {
    if parent == children.len() { group.arguments } else { children[parent].arguments }
}

pub(super) open spec fn expansion_arguments_determined(group: &CheckedExpansionCall, arguments: Seq<ProjectedCallArgument>)
    -> bool {
    &&& group.postorder matches Some(children)
    &&& forall|parent: int| 0 <= parent <= children@.len() ==> {
        let range = #[trigger] expansion_parent_range(group, children@, parent);
        &&& range.start <= range.end <= arguments.len()
        &&& forall|i: int| range.start <= i < range.end ==> !((#[trigger] arguments[i]).source is Deferred)
    }
}

/// 親の実引数が同じフォームと相対参照で子を指すとき、その子を一段でたどれる。
pub(super) closed spec fn expansion_child_edge(group: &CheckedExpansionCall, arguments: Seq<ProjectedCallArgument>,
    parent: int, child: int,
) -> bool {
    &&& group.postorder matches Some(children)
    &&& 0 <= child < parent <= children@.len()
    &&& {
        let range = expansion_parent_range(group, children@, parent);
        exists|i: int| {
            let argument = #[trigger] arguments[i];
            &&& range.start <= i < range.end <= arguments.len()
            &&& argument.source matches CallArgumentSource::NestedCall(reference)
            &&& children@[child].reference == group.references.start + reference
            &&& children@[child]._signature@.call.call.form == argument.form
        }
    }
}

/// 根または親を起点とし、実引数が指す子だけを後順添字の小さい方へたどる。
pub(super) closed spec fn expansion_child_reachable(group: &CheckedExpansionCall, arguments: Seq<ProjectedCallArgument>,
    parent: int, child: int,
) -> bool
    decreases parent,
{
    &&& group.postorder matches Some(children)
    &&& 0 <= child < children@.len()
    &&& child <= parent <= children@.len()
    &&& (parent == child || exists|next: int| 0 <= next < parent
        && #[trigger] expansion_child_edge(group, arguments, parent, next)
        && expansion_child_reachable(group, arguments, next, child))
}

/// 根から子をたどり、その子の出力を直接使う親を得る。
proof fn expansion_child_consumer(
    group: &CheckedExpansionCall, arguments: Seq<ProjectedCallArgument>, parent: int, child: int,
) -> (consumer: int)
    requires child < parent, expansion_child_reachable(group, arguments, parent, child),
    ensures child < consumer <= parent, expansion_child_edge(group, arguments, consumer, child),
    decreases parent,
{
    reveal_with_fuel(expansion_child_reachable, 1);
    let next = choose|next: int| 0 <= next < parent
        && #[trigger] expansion_child_edge(group, arguments, parent, next)
        && expansion_child_reachable(group, arguments, next, child);
    if next == child {
        parent
    } else {
        expansion_child_consumer(group, arguments, next, child)
    }
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
pub(super) proof fn source_call_argument_values_agree(
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
            let (first, end) = crate::syntax::circuit::definition_target_range(parsed.syntax.forms@, row);
            let local = (definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
            &&& self.func_wiring_evidence(file, entry, limit, Ok(FuncWiringResult::Checked(*wiring)))
            &&& outputs.end <= wiring.drivers.definitions@.len()
            &&& outputs.end - outputs.start == end - first
            &&& slot < wiring.drivers.definitions@.len()
            &&& wiring.drivers.definitions@[slot].definition == definition
            &&& wiring.drivers.definitions@[slot].result_index == slot - outputs.start
            &&& entry < parsed.entry_ranges@.len()
            &&& parsed.entry_ranges@[entry as int].definitions.start <= definition
                < parsed.entry_ranges@[entry as int].definitions.end <= parsed.definitions@.len()
            &&& crate::syntax::circuit::ordinary_call_at(project.sources_model()[file as int].text,
                parsed.syntax.forms@, row.expression.start as int, row.expression.end as int)
            &&& self.func_call_signature_evidence(file, entry, local, 0, limit, Ok(Some(signature)))
            &&& signature.call.target matches FuncCallTarget::Function { file: target_file, entry: target_entry, .. }
            &&& (target_file, target_entry) == target
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
            ({
                let project = self.targets.project_model();
                source_call_arguments_match(&project.sources_model()[caller.0 as int], &project.circuits_model()[caller.0 as int],
                    wiring, caller.1, definition, signature.call.call, caller.2, inputs, values.take(outputs.start as int),
                    widths, arguments)
            }),
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
        let row = parsed.definitions@[root.definition as int];
        let expression = row.expression;
        let signature = group._signature@;
        let (callee_at, caller_at) = group._order@;
        &&& self.function_template_plan(plan)
        &&& definitions.start <= root.definition < definitions.end <= parsed.definitions@.len()
        &&& crate::syntax::circuit::ordinary_call_at(source.text, parsed.syntax.forms@, expression.start as int, expression.end as int)
        &&& group.outputs.start == root.first_output
        &&& group.outputs.end == root.first_output + root.count
        &&& 0 < root.count && group.outputs.end <= typed.types@.len()
        &&& typed.types@.len() == wiring.drivers.definitions@.len()
        &&& is_form_location(source, parsed.syntax.forms@[parsed.definitions@[root.definition as int].expression.start as int],
            group.expression)
        &&& group.arguments == inputs && inputs.start <= inputs.end <= arguments.arguments@.len()
        &&& group.references == row.references
        &&& group.references.start <= group.references.end
        &&& match group.postorder {
            None => row.references.end == row.references.start + 1,
            Some(children) => row.references.end > row.references.start + 1
                && self.prepared_expression_children_match(plan, caller, (root.definition - definitions.start) as usize,
                    arguments, typed.types@, wiring, caller_at, children@),
        }
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
            &&& self.func_call_signature_evidence(caller.0, caller.1,
                (root.definition - parsed.entry_ranges@[caller.1 as int].definitions.start) as usize,
                0, caller.2, Ok(Some(group._signature@)))
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
    ///
    /// 入れ子の関数呼び出しでは、呼び出し先が呼び出し元より先に展開されることも示す。
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
                CallArgumentSource::NestedCall(_) => {
                    let local = (root.definition - frame.definitions.start) as usize;
                    &&& form is List
                    &&& group._signature@.call.call.form + 2 <= argument.form < form->List_end
                        <= parsed.syntax.forms@[group._signature@.call.call.form as int]->List_end
                    &&& group.postorder matches Some(children) && prepared_nested_output_matches(
                        children@, group.references.start, children@.len() as int, argument, expected)
                    &&& exists|reference: usize, child: TypedFuncCall|
                        #[trigger] self.func_call_form_reference(caller.0, caller.1, local, argument.form, reference)
                        && #[trigger] self.func_call_signature_evidence(caller.0, caller.1, local, reference, caller.2, Ok(Some(child)))
                        && child.call.call.form == argument.form
                        && child.call.target.port_counts().outputs == 1
                        && (child.call.target matches FuncCallTarget::Function { file, entry, .. } ==>
                            exists|rank: int| 0 <= rank < group._order@.1
                                && #[trigger] plan.position_model(rank) == Some((file, entry)))
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
            self.typed_call_arguments_ready(file, entry, local, 0, limit, group._signature@);
            self.typed_call_arguments_ready(file, entry, local, reference, limit, child);
            crate::syntax::circuit::direct_call_argument_bounds(
                parsed.syntax.forms@, group._signature@.call.call, form as int);
            self.call_form_matches_reference(file, entry, local, form, reference, child.call);
            assert(self.func_call_form_reference(file, entry, local, form, reference));
            assert(self.func_call_signature_evidence(file, entry, local, reference, limit, Ok(Some(child))));
            match group.postorder {
                Some(children) => {
                    let position = self.prepared_nested_argument(plan, caller, local, arguments, typed.types@, wiring,
                        group._order@.1, children@, children@.len() as int, 0, group._signature@, projected, port);
                    assert(children@[position]._signature@.call.call.form == form);
                },
                None => {
                    let row = parsed.definitions@[root.definition as int];
                    assert(reference < row.references.end - row.references.start);
                    assert(reference == 0);
                    self.call_form_matches_reference(file, entry, local, form, 0, group._signature@.call);
                    assert(false);
                },
            }
            if let FuncCallTarget::Function { file: target_file, entry: target_entry, .. } = child.call.target {
                let source = DefinitionPosition { file, entry, definition: local, reference };
                let site = self.expansion_site_for_call(source, child.call);
                let callee = self.template_callee_precedes(plan, group._order@.1, site);
                assert(plan.position_model(callee) == Some((target_file, target_entry)));
            }
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
                    CallArgumentSource::Deferred | CallArgumentSource::NestedCall(_) => false,
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

    #[verifier::opaque]
    pub(super) closed spec fn prepared_expression_call_matches(
        &self, plan: FunctionExpansionOrder, caller: (usize, usize, u64), definition: usize,
        projections: &CallArgumentProjections, types: Seq<Option<SignalType>>, wiring: &FuncWiring,
        caller_rank: int, item: PreparedExpressionCall,
    ) -> bool {
        let (file, entry, limit) = caller;
        let parsed = &self.targets.project_model().circuits_model()[file as int];
        let frame = parsed.entry_ranges@[entry as int];
        let row = parsed.definitions@[frame.definitions.start + definition];
        let local = (item.reference - row.references.start) as usize;
        let key = item.reference - frame.references.start;
        let args = projections;
        let range = item.arguments;
        let form = item._signature@.call.call.form;
        &&& row.references.start <= item.reference < row.references.end
        &&& form < parsed.syntax.forms@.len() && parsed.syntax.forms@[form as int] is List
        &&& is_form_location(&self.targets.project_model().sources_model()[file as int],
            parsed.syntax.forms@[form as int], item.expression)
        &&& 0 <= key < args.reference_argument_ends@.len()
        &&& range.start == if key == 0 { 0 } else { args.reference_argument_ends@[key - 1] }
        &&& range.end == args.reference_argument_ends@[key]
        &&& range.start <= range.end <= args.arguments@.len()
        &&& self.projected_input_arguments((file, entry, definition, local), limit, types, wiring,
            args.arguments@.subrange(range.start as int, range.end as int))
        &&& self.func_call_signature_evidence(file, entry, definition, local, limit, Ok(Some(item._signature@)))
        &&& match item._signature@.call.target {
            FuncCallTarget::Nor => item.vertex.is_none() && item._rank@.is_none(),
            FuncCallTarget::Function { file, entry, .. } =>
                item._rank@ matches Some(rank) && 0 <= rank < caller_rank < plan.order_model().len()
                    && plan.position_model(rank) == Some((file, entry))
                    && item.vertex == Some(plan.order_model()[rank]),
        }
    }

    pub(super) open spec fn expansion_child_scope(&self, group: &CheckedExpansionCall) -> bool {
        self.expression_children_in_reference_range(group.references, group.expression.source, group.postorder)
    }

    /// 子の参照が同じ定義の区間に収まり、重複しないことを表す。
    pub(super) open spec fn expression_children_in_reference_range(
        &self, references: Range<usize>, source: &crate::project::ProjectSource,
        postorder: Option<Vec<PreparedExpressionCall>>,
    ) -> bool {
        &&& references.start <= references.end
        &&& postorder matches Some(children) ==> {
            &&& forall|i: int| 0 <= i < children@.len() ==> {
                let child = #[trigger] children@[i];
                &&& references.start <= child.reference < references.end
                &&& *child.expression.source == *source
                &&& location_in_source(child.expression)
            }
            &&& forall|i: int, j: int| 0 <= i < j < children@.len() ==>
                (#[trigger] children@[i]).reference != (#[trigger] children@[j]).reference
        }
    }

    /// 子が同じ定義の参照区間に属し、同じ参照を繰り返さないことを示す。
    pub(super) proof fn expansion_child_scope_evidence(
        &self, plan: FunctionExpansionOrder, caller: (usize, usize, u64), prepared: &PreparedExpansionBody, index: int,
    )
        requires
            self.prepared_expansion_body_matches(plan, caller.0, caller.1, caller.2, prepared),
            0 <= index < prepared.calls@.len(),
        ensures self.expansion_child_scope(&prepared.calls@[index]),
    {
        reveal(UseAliases::checked_expansion_call_matches);
        reveal(UseAliases::prepared_expression_children_match);
        reveal(UseAliases::prepared_expression_call_matches);
    }

    /// 子の引数位置を厳格構文木の出現順に対応付ける。引数がない場合も空の位置列を得る。
    pub(super) proof fn expansion_child_arguments_in_source_order(
        &self, plan: FunctionExpansionOrder, caller: (usize, usize, u64),
        prepared: &PreparedExpansionBody, group_index: int, child_index: int,
    )
        requires
            self.can_resolve(),
            self.prepared_expansion_body_matches(plan, caller.0, caller.1, caller.2, prepared),
            0 <= group_index < prepared.calls@.len(),
            prepared.calls@[group_index].postorder matches Some(children) && 0 <= child_index < children@.len(),
        ensures ({
            let child = prepared.calls@[group_index].postorder->Some_0@[child_index];
            let forms = self.targets.project_model().circuits_model()[caller.0 as int].syntax.forms@;
            let projected = prepared.projections.call_arguments.arguments@.subrange(
                child.arguments.start as int, child.arguments.end as int);
            &&& child.arguments.start <= child.arguments.end <= prepared.projections.call_arguments.arguments@.len()
            &&& crate::syntax::circuit::call_argument_positions(forms, child._signature@.call.call,
                Seq::new(projected.len(), |i: int| projected[i].form))
        }),
    {
        reveal(UseAliases::checked_expansion_call_matches);
        reveal(UseAliases::prepared_expression_children_match);
        reveal(UseAliases::prepared_expression_call_matches);
        let (file, entry, limit) = caller;
        let child = prepared.calls@[group_index].postorder->Some_0@[child_index];
        let wiring = prepared.typed.literals.wiring->Checked_0;
        self.checked_types_keep_wiring(file, entry, limit, prepared.typed, wiring);
        let parsed = &self.targets.project_model().circuits_model()[file as int];
        let definition = prepared.projections.calls@[group_index].definition;
        let local = (definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
        let reference = (child.reference - parsed.definitions@[definition as int].references.start) as usize;
        let projected = prepared.projections.call_arguments.arguments@.subrange(
            child.arguments.start as int, child.arguments.end as int);
        self.projected_arguments_in_source_order((file, entry, local, reference), limit, prepared.typed.types@,
            &wiring, child._signature@, projected);
    }

    /// 確定した引数をたどり、対象のリストを含む直下の子呼び出しを見つける。
    pub(super) proof fn expansion_child_containing_form(
        &self, plan: FunctionExpansionOrder, caller: (usize, usize, u64),
        prepared: &PreparedExpansionBody, group_index: int, parent: int, descendant: int,
    ) -> (edge: (int, int))
        requires
            self.can_resolve(),
            self.prepared_expansion_body_matches(plan, caller.0, caller.1, caller.2, prepared),
            0 <= group_index < prepared.calls@.len(),
            ({
                let group = prepared.calls@[group_index];
                let forms = self.targets.project_model().circuits_model()[caller.0 as int].syntax.forms@;
                &&& group.postorder matches Some(children)
                &&& 0 <= parent <= children@.len()
                &&& {
                    let (call, range) = if parent == children@.len() {
                        (group._signature@.call.call, group.arguments)
                    } else {
                        (children@[parent]._signature@.call.call, children@[parent].arguments)
                    };
                    &&& call.form < descendant < forms[call.form as int]->List_end <= forms.len()
                    &&& forms[descendant] is List
                    &&& forall|i: int| range.start <= i < range.end ==>
                        !((#[trigger] prepared.projections.call_arguments.arguments@[i]).source is Deferred)
                }
            }),
        ensures ({
            let group = prepared.calls@[group_index];
            let children = group.postorder->Some_0@;
            let (port, child) = edge;
            let range = if parent == children.len() { group.arguments } else { children[parent].arguments };
            let forms = self.targets.project_model().circuits_model()[caller.0 as int].syntax.forms@;
            let argument = prepared.projections.call_arguments.arguments@[range.start + port];
            &&& 0 <= port < range.end - range.start
            &&& range.end <= prepared.projections.call_arguments.arguments@.len()
            &&& 0 <= child < parent
            &&& argument.source is NestedCall
            &&& children[child].reference == group.references.start + argument.source->NestedCall_0
            &&& children[child]._signature@.call.call.form == argument.form
            &&& forms[argument.form as int] is List
            &&& argument.form <= descendant < forms[argument.form as int]->List_end <= forms.len()
        }),
    {
        reveal(UseAliases::checked_expansion_call_matches);
        reveal(UseAliases::prepared_expression_children_match);
        reveal(UseAliases::prepared_expression_call_matches);
        let (file, entry, limit) = caller;
        let group = prepared.calls@[group_index];
        let root = prepared.projections.calls@[group_index];
        let children = group.postorder->Some_0@;
        let arguments = &prepared.projections.call_arguments;
        let wiring = prepared.typed.literals.wiring->Checked_0;
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[file as int];
        let forms = parsed.syntax.forms@;
        let source = &project.sources_model()[file as int];
        let row = parsed.definitions@[root.definition as int];
        let local = (root.definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
        self.checked_types_keep_wiring(file, entry, limit, prepared.typed, wiring);
        let (typed, range, reference) = if parent == children.len() {
            self.expansion_arguments_in_source_order(plan, caller, prepared.typed, &wiring, root, group.arguments,
                arguments, group);
            (group._signature@, group.arguments, 0usize)
        } else {
            let child = children[parent];
            self.expansion_child_arguments_in_source_order(plan, caller, prepared, group_index, parent);
            (child._signature@, child.arguments, (child.reference - row.references.start) as usize)
        };
        let projected = arguments.arguments@.subrange(range.start as int, range.end as int);
        let positions = Seq::new(projected.len(), |i: int| projected[i].form);
        self.typed_call_arguments_ready(file, entry, local, reference, limit, typed);
        crate::syntax::circuit::indexed_call_arguments(source.text, forms, row,
            parsed.references@[row.references.start + reference], typed.call.call);
        let port = crate::syntax::circuit::call_argument_containing_list(source.text, forms, typed.call.call, positions,
            row.expression.end as int, descendant);
        let argument = projected[port];
        assert(argument == arguments.arguments@[range.start + port]);
        self.checked_projected_argument((file, entry, local, reference), limit, prepared.typed.types@,
            &wiring, typed, projected, port);
        assert(argument.source is NestedCall);
        let child = self.prepared_nested_argument(plan, caller, local, arguments, prepared.typed.types@,
            &wiring, group._order@.1, children, parent, reference, typed, projected, port);
        (port, child)
    }

    /// 根の引数がすべて信号またはリテラルなら、先に展開する子は存在しない。
    #[verifier::spinoff_prover]
    pub(super) proof fn direct_expansion_has_no_children(
        &self, plan: FunctionExpansionOrder, caller: (usize, usize, u64), prepared: &PreparedExpansionBody,
        group_index: int,
    )
        requires
            self.can_resolve(),
            self.prepared_expansion_body_matches(plan, caller.0, caller.1, caller.2, prepared),
            0 <= group_index < prepared.calls@.len(),
            ({
                let range = prepared.calls@[group_index].arguments;
                forall|i: int| range.start <= i < range.end ==>
                    (#[trigger] prepared.projections.call_arguments.arguments@[i]).source.has_direct_wires()
            }),
        ensures
            prepared.calls@[group_index].postorder matches Some(children) ==> children@.len() == 0,
    {
        let group = prepared.calls@[group_index];
        if let Some(children) = group.postorder {
            if children@.len() > 0 {
                reveal(UseAliases::checked_expansion_call_matches);
                reveal(UseAliases::prepared_expression_children_match);
                let (file, entry, limit) = caller;
                let project = self.targets.project_model();
                let parsed = &project.circuits_model()[file as int];
                let source = &project.sources_model()[file as int];
                let absolute = prepared.projections.calls@[group_index].definition;
                let local = (absolute - parsed.entry_ranges@[entry as int].definitions.start) as usize;
                let row = parsed.definitions@[absolute as int];
                let forms = parsed.syntax.forms@;
                let refs = parsed.references@;
                let child = children@[0];
                let relative = (child.reference - group.references.start) as usize;
                self.expansion_child_template_evidence(plan, caller, prepared, group_index, 0);
                self.typed_call_arguments_ready(file, entry, local, relative, limit, child._signature@);
                self.typed_call_arguments_ready(file, entry, local, 0, limit, group._signature@);
                self.resolved_call_reference_form(file, entry, local, 0, group._signature@.call);
                self.targets.parsed_project_model();
                parsed_index_evidence(*source, *parsed);
                build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, absolute as int);
                vstd::std_specs::vec::axiom_spec_len(&parsed.syntax.forms);
                root_call_reference(source.text, forms, refs, row);
                crate::syntax::circuit::call_form_bounds(forms, child._signature@.call.call);
                crate::syntax::circuit::call_form_bounds(forms, group._signature@.call.call);

                let last = children@.len() as int;
                let order = Seq::new(children@.len(), |i: int| children@[i].reference).push(group.references.start);
                assert(order[0] == child.reference && order[last] == group.references.start);
                let (parent, position) = call_postorder_positions(source.text, forms, refs, row,
                    order, group.references.start, child.reference);
                if parent < last {
                    call_postorder_references_distinct(forms, refs, row.references, order, parent, last);
                }
                if position > 0 {
                    call_postorder_references_distinct(forms, refs, row.references, order, 0, position);
                }
                assert(position == 0 && parent == last);

                let range = group.arguments;
                let arguments = prepared.projections.call_arguments.arguments@;
                assert forall|i: int| range.start <= i < range.end implies
                    !((#[trigger] arguments[i]).source is Deferred) by {
                    assert(arguments[i].source.has_direct_wires());
                };
                let (port, _) = self.expansion_child_containing_form(plan, caller, prepared, group_index, last,
                    child._signature@.call.call.form as int);
                assert(arguments[range.start + port].source.has_direct_wires());
            }
        }
    }

    /// 一つの定義で、対象の子と同じフォームを指す後順項目を同定する。
    pub(super) proof fn expansion_children_at_same_form(
        &self, plan: FunctionExpansionOrder, caller: (usize, usize, u64), prepared: &PreparedExpansionBody,
        group_index: int, left: int, right: int,
    )
        requires
            self.can_resolve(),
            self.prepared_expansion_body_matches(plan, caller.0, caller.1, caller.2, prepared),
            0 <= group_index < prepared.calls@.len(),
            ({
                let group = prepared.calls@[group_index];
                &&& group.postorder matches Some(children)
                &&& 0 <= left < children@.len() && 0 <= right < children@.len()
                &&& children@[left]._signature@.call.call.form == children@[right]._signature@.call.call.form
            }),
        ensures left == right,
    {
        reveal(UseAliases::checked_expansion_call_matches);
        reveal(UseAliases::prepared_expression_children_match);
        reveal(UseAliases::prepared_expression_call_matches);
        self.targets.parsed_project_model();
        let (file, entry, limit) = caller;
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[file as int];
        let source = &project.sources_model()[file as int];
        let absolute = prepared.projections.calls@[group_index].definition;
        let local = (absolute - parsed.entry_ranges@[entry as int].definitions.start) as usize;
        let row = parsed.definitions@[absolute as int];
        let children = prepared.calls@[group_index].postorder->Some_0@;
        let a = children[left];
        let b = children[right];
        let a_ref = (a.reference - row.references.start) as usize;
        let b_ref = (b.reference - row.references.start) as usize;
        self.typed_call_arguments_ready(file, entry, local, a_ref, limit, a._signature@);
        self.typed_call_arguments_ready(file, entry, local, b_ref, limit, b._signature@);
        self.resolved_call_reference_form(file, entry, local, a_ref, a._signature@.call);
        self.resolved_call_reference_form(file, entry, local, b_ref, b._signature@.call);
        parsed_index_evidence(*source, *parsed);
        build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, absolute as int);
        vstd::std_specs::vec::axiom_spec_len(&parsed.syntax.forms);
        definition_reference_form_unique(source.text, parsed.syntax.forms@, parsed.references@, row, a.reference, b.reference);
        if left < right {
            assert(children[left].reference != children[right].reference);
        } else if right < left {
            assert(children[right].reference != children[left].reference);
        }
    }

    /// 対象のフォームを含む引数を選び、後順添字が小さくなる方向へたどる。
    proof fn expansion_reaches_child_in_list(
        &self, plan: FunctionExpansionOrder, caller: (usize, usize, u64), prepared: &PreparedExpansionBody,
        group_index: int, parent: int, target: int,
    )
        requires
            self.can_resolve(),
            self.prepared_expansion_body_matches(plan, caller.0, caller.1, caller.2, prepared),
            0 <= group_index < prepared.calls@.len(),
            caller.0 < self.targets.project_model().circuits_model().len(),
            ({
                let group = &prepared.calls@[group_index];
                let args = prepared.projections.call_arguments.arguments@;
                let forms = self.targets.project_model().circuits_model()[caller.0 as int].syntax.forms@;
                &&& expansion_arguments_determined(group, args)
                &&& group.postorder matches Some(children)
                &&& 0 <= parent <= children@.len() && 0 <= target < children@.len()
                &&& {
                    let first = if parent == children@.len() {
                        group._signature@.call.call.form
                    } else { children@[parent]._signature@.call.call.form };
                    let descendant = children@[target]._signature@.call.call.form;
                    &&& first < descendant < forms.len()
                    &&& forms[first as int] is List
                    &&& descendant < forms[first as int]->List_end <= forms.len()
                    &&& forms[descendant as int] is List
                }
            }),
        ensures expansion_child_reachable(&prepared.calls@[group_index], prepared.projections.call_arguments.arguments@,
            parent, target),
        decreases parent,
    {
        reveal(expansion_child_edge);
        reveal_with_fuel(expansion_child_reachable, 1);
        let group = &prepared.calls@[group_index];
        let args = prepared.projections.call_arguments.arguments@;
        let children = group.postorder->Some_0@;
        let descendant = children[target]._signature@.call.call.form as int;
        let range = expansion_parent_range(group, children, parent);
        let (port, next) = self.expansion_child_containing_form(plan, caller, prepared, group_index, parent, descendant);
        let argument = args[range.start + port];
        assert(expansion_child_edge(group, args, parent, next));
        if argument.form == descendant {
            self.expansion_children_at_same_form(plan, caller, prepared, group_index, next, target);
            assert(expansion_child_reachable(group, args, next, target));
        } else {
            self.expansion_reaches_child_in_list(plan, caller, prepared, group_index, next, target);
        }
        assert(expansion_child_reachable(group, args, parent, target));
    }

    /// 引数が確定していれば、後順に並べたすべての子を根からたどれる。
    pub(super) proof fn expansion_reaches_every_child(
        &self, plan: FunctionExpansionOrder, caller: (usize, usize, u64), prepared: &PreparedExpansionBody,
        group_index: int,
    )
        requires
            self.can_resolve(),
            self.prepared_expansion_body_matches(plan, caller.0, caller.1, caller.2, prepared),
            0 <= group_index < prepared.calls@.len(),
            expansion_arguments_determined(&prepared.calls@[group_index], prepared.projections.call_arguments.arguments@),
        ensures ({
            let group = &prepared.calls@[group_index];
            let arguments = prepared.projections.call_arguments.arguments@;
            let children = group.postorder->Some_0@;
            forall|i: int| 0 <= i < children.len() ==>
                #[trigger] expansion_child_reachable(group, arguments, children.len() as int, i)
        }),
    {
        reveal(UseAliases::checked_expansion_call_matches);
        reveal(UseAliases::prepared_expression_children_match);
        reveal(UseAliases::prepared_expression_call_matches);
        let (file, entry, limit) = caller;
        let group = &prepared.calls@[group_index];
        let root = prepared.projections.calls@[group_index];
        let children = group.postorder->Some_0@;
        let arguments = &prepared.projections.call_arguments;
        let wiring = prepared.typed.literals.wiring->Checked_0;
        let project = self.targets.project_model();
        let source = &project.sources_model()[file as int];
        let parsed = &project.circuits_model()[file as int];
        let forms = parsed.syntax.forms@;
        let row = parsed.definitions@[root.definition as int];
        let local = (root.definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
        self.targets.parsed_project_model();
        self.checked_types_keep_wiring(file, entry, limit, prepared.typed, wiring);
        self.expansion_arguments_in_source_order(plan, caller, prepared.typed, &wiring, root, group.arguments, arguments, *group);
        self.typed_call_arguments_ready(file, entry, local, 0, limit, group._signature@);
        self.resolved_call_reference_form(file, entry, local, 0, group._signature@.call);
        crate::syntax::circuit::call_form_bounds(forms, group._signature@.call.call);
        reveal(crate::syntax::complete_list_indices);
        parsed_index_evidence(*source, *parsed);
        build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, root.definition as int);
        vstd::std_specs::vec::axiom_spec_len(&parsed.syntax.forms);
        let order = Seq::new(children.len(), |i: int| children[i].reference).push(row.references.start);
        assert forall|i: int| 0 <= i < children.len() implies
            #[trigger] expansion_child_reachable(group, arguments.arguments@, children.len() as int, i) by {
            let child = children[i];
            let reference = (child.reference - row.references.start) as usize;
            self.typed_call_arguments_ready(file, entry, local, reference, limit, child._signature@);
            self.resolved_call_reference_form(file, entry, local, reference, child._signature@.call);
            let last = children.len() as int;
            call_postorder_reference(forms, parsed.references@, row.references, order, i);
            call_postorder_reference(forms, parsed.references@, row.references, order, last);
            call_postorder_references_distinct(forms, parsed.references@, row.references, order, i, last);
            let (root_position, child_position) = call_postorder_positions(source.text, forms, parsed.references@,
                row, order, row.references.start, child.reference);
            if root_position < last {
                call_postorder_references_distinct(forms, parsed.references@, row.references, order, root_position, last);
            }
            assert(root_position == last);
            if child_position < i {
                call_postorder_references_distinct(forms, parsed.references@, row.references, order, child_position, i);
            } else if i < child_position {
                call_postorder_references_distinct(forms, parsed.references@, row.references, order, i, child_position);
            }
            assert(child_position == i);
            self.expansion_reaches_child_in_list(plan, caller, prepared, group_index, children.len() as int, i);
        };
    }

    /// 子の実引数を呼び出し直下のフォームに対応付ける。
    ///
    /// 信号、リテラル、入れ子の呼び出しについて、入力ポートとの型の一致を示す。
    /// 信号は先行する駆動元に、入れ子の呼び出しは後順で先行する単一出力に対応する。
    pub(super) proof fn expansion_child_argument_evidence(
        &self, plan: FunctionExpansionOrder, caller: (usize, usize, u64),
        prepared: &PreparedExpansionBody, group_index: int, parent_index: int, port: int,
    )
        requires
            self.can_resolve(),
            self.prepared_expansion_body_matches(plan, caller.0, caller.1, caller.2, prepared),
            0 <= group_index < prepared.calls@.len(),
            prepared.calls@[group_index].postorder matches Some(children)
                && 0 <= parent_index < children@.len()
                && 0 <= port < children@[parent_index].arguments.end - children@[parent_index].arguments.start,
        ensures ({
            let group = prepared.calls@[group_index];
            let children = group.postorder->Some_0@;
            let parent = children[parent_index];
            let project = self.targets.project_model();
            let parsed = &project.circuits_model()[caller.0 as int];
            let source = &project.sources_model()[caller.0 as int];
            let wiring = prepared.typed.literals.wiring->Checked_0;
            let arg = prepared.projections.call_arguments.arguments@[parent.arguments.start + port];
            let form = parsed.syntax.forms@[arg.form as int];
            let frame = parsed.entry_ranges@[caller.1 as int];
            let definition = prepared.projections.calls@[group_index].definition;
            let row = parsed.definitions@[definition as int];
            let expected = match parent._signature@.signature {
                crate::project::FuncCallSignature::Nor => crate::project::ResolvedPortType::Bits(1),
                crate::project::FuncCallSignature::Function(ports) => ports.inputs@[port].ty,
            };
            &&& parent.arguments.start <= parent.arguments.end <= prepared.projections.call_arguments.arguments@.len()
            &&& match parent._signature@.signature {
                crate::project::FuncCallSignature::Nor => parent.arguments.end - parent.arguments.start == 2,
                crate::project::FuncCallSignature::Function(ports) =>
                    parent.arguments.end - parent.arguments.start == ports.inputs@.len(),
            }
            &&& arg.form < parsed.syntax.forms@.len()
            &&& crate::syntax::circuit::direct_call_argument(parsed.syntax.forms@, parent._signature@.call.call, arg.form as int)
            &&& caller.1 < parsed.entry_ranges@.len()
            &&& frame.definitions.start <= definition < frame.definitions.end <= parsed.definitions@.len()
            &&& row.signals.end <= parsed.signals@.len()
            &&& match arg.source {
                CallArgumentSource::Driver(driver) => {
                    &&& form is Atom && form->Atom_kind is Name
                    &&& signal_type_at(&wiring, prepared.typed.types@, driver) matches Some(known)
                        && crate::project::port_types_equal(known.ty, expected)
                    &&& exists|position: int| row.signals.start <= position < row.signals.end
                        && (#[trigger] parsed.signals@[position]) == arg.form
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
                    &&& expected == crate::project::ResolvedPortType::Bits(width)
                    &&& form is Atom
                    &&& (form->Atom_kind is Natural || form->Atom_kind is Binary || form->Atom_kind is Hexadecimal)
                    &&& span.start < span.end <= source.text.spec_bytes().len()
                    &&& crate::project::circuit_literal_width_matches(bytes, Some(width), caller.2, Ok(width))
                    &&& ((width == 1 && bytes.len() == 1 && (bytes[0] == b'0' || bytes[0] == b'1'))
                        || crate::syntax::bare_atom_kind(bytes) == Some(crate::syntax::AtomKind::Binary)
                        || crate::syntax::bare_atom_kind(bytes) == Some(crate::syntax::AtomKind::Hexadecimal))
                    &&& super::lowering::literal_argument_matches_width(source, parsed.syntax.forms@, arg.form, width as int)
                },
                CallArgumentSource::NestedCall(_) =>
                    form is List && prepared_nested_output_matches(children, group.references.start, parent_index, arg, expected),
                CallArgumentSource::Deferred => true,
            }
        }),
    {
        reveal(UseAliases::checked_expansion_call_matches);
        reveal(UseAliases::prepared_expression_children_match);
        reveal(UseAliases::prepared_expression_call_matches);
        let (file, entry, limit) = caller;
        let group = prepared.calls@[group_index];
        let children = group.postorder->Some_0@;
        let parent = children[parent_index];
        let root = prepared.projections.calls@[group_index];
        let wiring = prepared.typed.literals.wiring->Checked_0;
        self.checked_types_keep_wiring(file, entry, limit, prepared.typed, wiring);
        self.checked_wiring_is_func(file, entry, limit, wiring);
        self.targets.parsed_project_model();
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[file as int];
        let source = &project.sources_model()[file as int];
        parsed_index_evidence(*source, *parsed);
        build_entry_ranges_evidence(source.text, &parsed.build_model(), entry as int);
        let definition = (root.definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
        build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, root.definition as int);
        let row = parsed.definitions@[root.definition as int];
        let reference = (parent.reference - row.references.start) as usize;
        let arguments = &prepared.projections.call_arguments;
        let projected = arguments.arguments@.subrange(parent.arguments.start as int, parent.arguments.end as int);
        assert(projected[port] == arguments.arguments@[parent.arguments.start + port]);
        self.typed_call_arguments_ready(file, entry, definition, reference, limit, parent._signature@);
        self.checked_projected_argument((file, entry, definition, reference), limit, prepared.typed.types@,
            &wiring, parent._signature@, projected, port);
        if projected[port].source is NestedCall {
            let i = self.prepared_nested_argument(plan, caller, definition, arguments, prepared.typed.types@,
                &wiring, group._order@.1, children, parent_index, reference, parent._signature@, projected, port);
            assert(children[i].reference == group.references.start + projected[port].source->NestedCall_0);
        }
        if let CallArgumentSource::Driver(super::super::OutputDriver::Definition(driver)) = projected[port].source {
            self.expansion_call_output_types(plan, caller, prepared.typed, &wiring, root, group.arguments, arguments, group);
            let first = group.outputs.start as int;
            assert(wiring.drivers.definitions@[first].definition == root.definition);
            assert(wiring.drivers.definitions@[driver as int].definition < root.definition);
            if first < driver {
                assert(wiring.drivers.definitions@[first].definition <= wiring.drivers.definitions@[driver as int].definition);
            }
            assert(driver < first);
        }
    }

    /// 子の実引数に渡す信号またはリテラルの値を、元のフォームの評価値に結び付ける。
    pub(super) proof fn expansion_child_atom_value_from_source(
        &self, plan: FunctionExpansionOrder, caller: (usize, usize, u64),
        prepared: &PreparedExpansionBody, group_index: int, child_index: int, port: int,
        inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>, width: u64, value: Seq<bool>,
    )
        requires
            self.can_resolve(),
            self.prepared_expansion_body_matches(plan, caller.0, caller.1, caller.2, prepared),
            0 <= group_index < prepared.calls@.len(),
            caller.0 < self.targets.project_model().sources_model().len(),
            caller.0 < self.targets.project_model().circuits_model().len(),
            ({
                let group = prepared.calls@[group_index];
                let wiring = prepared.typed.literals.wiring->Checked_0;
                &&& group.postorder matches Some(children)
                &&& 0 <= child_index < children@.len()
                &&& children@[child_index].arguments.end <= prepared.projections.call_arguments.arguments@.len()
                &&& 0 <= port < children@[child_index].arguments.end - children@[child_index].arguments.start
                &&& inputs.len() == wiring.drivers.signature.inputs@.len()
                &&& prior.len() == group.outputs.start
                &&& value.len() == width
                &&& {
                    let arg = prepared.projections.call_arguments.arguments@[children@[child_index].arguments.start + port];
                    match arg.source {
                        CallArgumentSource::Driver(driver) => value == super::semantics::driver_values(inputs, prior, driver),
                        CallArgumentSource::Literal(bits) => {
                            let project = self.targets.project_model();
                            let source = &project.sources_model()[caller.0 as int];
                            let forms = project.circuits_model()[caller.0 as int].syntax.forms@;
                            let bytes = source_argument_bytes(source, forms, arg.form);
                            width == bits && value == Seq::new(width as nat, |bit: int| call_literal_bit(bytes, bit as nat))
                        },
                        CallArgumentSource::NestedCall(_) | CallArgumentSource::Deferred => false,
                    }
                }
            }),
        ensures ({
            let child = prepared.calls@[group_index].postorder->Some_0@[child_index];
            let arg = prepared.projections.call_arguments.arguments@[child.arguments.start + port];
            let project = self.targets.project_model();
            let parsed = &project.circuits_model()[caller.0 as int];
            let source = &project.sources_model()[caller.0 as int];
            let wiring = prepared.typed.literals.wiring->Checked_0;
            source_call_argument_value(source, parsed, &wiring, caller.1, prepared.projections.calls@[group_index].definition,
                arg.form, caller.2, inputs, prior, width, value)
        }),
    {
        reveal(source_call_argument_value);
        self.expansion_child_argument_evidence(plan, caller, prepared, group_index, child_index, port);
    }

    /// 親の型付き引数が参照する子は、出力ポートを一つだけ持つ。
    pub(super) proof fn expansion_child_single_output(
        &self, plan: FunctionExpansionOrder, caller: (usize, usize, u64), prepared: &PreparedExpansionBody,
        group_index: int, index: int,
    )
        requires
            self.can_resolve(),
            self.prepared_expansion_body_matches(plan, caller.0, caller.1, caller.2, prepared),
            0 <= group_index < prepared.calls@.len(),
            ({
                let group = &prepared.calls@[group_index];
                &&& group.postorder matches Some(children)
                &&& 0 <= index < children@.len()
                &&& expansion_child_reachable(group, prepared.projections.call_arguments.arguments@, children@.len() as int, index)
            }),
        ensures ({
            let child = prepared.calls@[group_index].postorder->Some_0@[index];
            &&& child._signature@.call.target.port_counts().outputs == 1
            &&& child._signature@.signature matches crate::project::FuncCallSignature::Function(ports)
                ==> ports.outputs@.len() == 1
        }),
    {
        let group = &prepared.calls@[group_index];
        let children = group.postorder->Some_0@;
        let projections = &prepared.projections.call_arguments;
        let arguments = projections.arguments@;
        let parent = expansion_child_consumer(group, arguments, children.len() as int, index);
        reveal(expansion_child_edge);
        let range = expansion_parent_range(group, children, parent);
        let at = choose|at: int| {
            let argument = #[trigger] arguments[at];
            &&& range.start <= at < range.end <= arguments.len()
            &&& argument.source matches CallArgumentSource::NestedCall(reference)
            &&& children[index].reference == group.references.start + reference
            &&& children[index]._signature@.call.call.form == argument.form
        };
        let port = at - range.start;
        let argument = arguments[at];
        let expected = if parent == children.len() {
            self.expansion_callee_template_evidence(plan, caller, prepared, group_index);
            let wiring = prepared.typed.literals.wiring->Checked_0;
            self.checked_types_keep_wiring(caller.0, caller.1, caller.2, prepared.typed, wiring);
            self.expansion_argument_evidence(plan, caller, prepared.typed, &wiring, prepared.projections.calls@[group_index],
                range, projections, *group, port);
            group._signature@.signature->Function_0.inputs@[port].ty
        } else {
            self.expansion_child_argument_evidence(plan, caller, prepared, group_index, parent, port);
            match children[parent]._signature@.signature {
                crate::project::FuncCallSignature::Nor => crate::project::ResolvedPortType::Bits(1),
                crate::project::FuncCallSignature::Function(ports) => ports.inputs@[port].ty,
            }
        };
        assert(prepared_nested_output_matches(children, group.references.start, parent, argument, expected));
        let producer = choose|i: int| 0 <= i < parent
            && (#[trigger] children[i]).reference == group.references.start + argument.source->NestedCall_0
            && children[i]._signature@.call.call.form == argument.form
            && children[i]._signature@.call.target.port_counts().outputs == 1
            && match children[i]._signature@.signature {
                crate::project::FuncCallSignature::Nor =>
                    crate::project::port_types_equal(crate::project::ResolvedPortType::Bits(1), expected),
                crate::project::FuncCallSignature::Function(ports) =>
                    ports.outputs@.len() == 1 && crate::project::port_types_equal(ports.outputs@[0].ty, expected),
            };
        self.expansion_child_scope_evidence(plan, caller, prepared, group_index);
        assert(producer == index);
    }

    /// 子の引数区間と、構文上の同じ呼び出しから得た署名を取り出す。
    pub(super) proof fn expansion_child_template_evidence(
        &self, plan: FunctionExpansionOrder, caller: (usize, usize, u64),
        prepared: &PreparedExpansionBody, group_index: int, child_index: int,
    )
        requires
            self.can_resolve(),
            self.prepared_expansion_body_matches(plan, caller.0, caller.1, caller.2, prepared),
            0 <= group_index < prepared.calls@.len(),
            prepared.calls@[group_index].postorder matches Some(children) && 0 <= child_index < children@.len(),
        ensures ({
            let group = prepared.calls@[group_index];
            let child = group.postorder->Some_0@[child_index];
            let parsed = self.targets.project_model().circuits_model()[caller.0 as int];
            let definition = prepared.projections.calls@[group_index].definition;
            let row = parsed.definitions@[definition as int];
            let local = (definition - parsed.entry_ranges@[caller.1 as int].definitions.start) as usize;
            let reference = (child.reference - group.references.start) as usize;
            &&& group.references == row.references && group.references.start < child.reference < group.references.end
            &&& row.expression.start < child._signature@.call.call.form < row.expression.end
            &&& self.func_call_form_reference(caller.0, caller.1, local, child._signature@.call.call.form, reference)
            &&& self.func_call_signature_evidence(caller.0, caller.1, local, reference, caller.2, Ok(Some(child._signature@)))
            &&& child.arguments.start <= child.arguments.end <= prepared.projections.call_arguments.arguments@.len()
            &&& match child._signature@.call.target {
                FuncCallTarget::Nor => child.vertex.is_none() && child._rank@.is_none() && child._signature@.signature is Nor
                    && child.arguments.end - child.arguments.start == 2,
                FuncCallTarget::Function { file, entry, .. } => {
                    &&& child._rank@ matches Some(rank) && 0 <= rank < group._order@.1 < plan.order_model().len()
                        && child.vertex == Some(plan.order_model()[rank]) && plan.position_model(rank) == Some((file, entry))
                    &&& child._signature@.signature matches crate::project::FuncCallSignature::Function(signature)
                        && self.typed_signature_evidence(file, entry, caller.2, Ok(Some(signature)))
                        && child.arguments.end - child.arguments.start == signature.inputs@.len()
                },
            }
        }),
    {
        reveal(UseAliases::checked_expansion_call_matches);
        reveal(UseAliases::prepared_expression_children_match);
        reveal(UseAliases::prepared_expression_call_matches);
        let group = prepared.calls@[group_index];
        let child = group.postorder->Some_0@[child_index];
        let parsed = &self.targets.project_model().circuits_model()[caller.0 as int];
        let root = prepared.projections.calls@[group_index];
        let definition = (root.definition - parsed.entry_ranges@[caller.1 as int].definitions.start) as usize;
        let row = parsed.definitions@[root.definition as int];
        let local = (child.reference - row.references.start) as usize;
        let wiring = prepared.typed.literals.wiring->Checked_0;
        let projected = prepared.projections.call_arguments.arguments@.subrange(
            child.arguments.start as int, child.arguments.end as int);
        self.typed_call_arguments_ready(caller.0, caller.1, definition, local, caller.2, child._signature@);
        self.resolved_call_reference_form(caller.0, caller.1, definition, local, child._signature@.call);
        let children = group.postorder->Some_0@;
        let order = Seq::new(children.len(), |i: int| children[i].reference).push(row.references.start);
        assert(order[child_index] == child.reference && order.last() == row.references.start);
        crate::syntax::circuit::call_postorder_references_distinct(
            parsed.syntax.forms@, parsed.references@, row.references, order, child_index, children.len() as int);
        let root_form = group._signature@.call.call.form;
        let source = &self.targets.project_model().sources_model()[caller.0 as int];
        self.typed_call_arguments_ready(caller.0, caller.1, definition, 0, caller.2, group._signature@);
        self.resolved_call_reference_form(caller.0, caller.1, definition, 0, group._signature@.call);
        self.targets.parsed_project_model();
        parsed_index_evidence(*source, *parsed);
        build_definition_scope_evidence(source.text, &parsed.build_model(), caller.1 as int, root.definition as int);
        vstd::std_specs::vec::axiom_spec_len(&parsed.syntax.forms);
        crate::syntax::circuit::root_call_shape_location(source.text, parsed.syntax.forms@, row, parsed.references@,
            group._signature@.call.call);
        assert(root_form == row.expression.start);
        if child._signature@.call.call.form == root_form {
            definition_reference_form_unique(source.text, parsed.syntax.forms@, parsed.references@, row,
                row.references.start, child.reference);
        }
        crate::syntax::circuit::indexed_call_arguments(child._signature@.call.source.text, parsed.syntax.forms@, row,
            parsed.references@[child.reference as int], child._signature@.call.call);
        self.checked_projected_input_count((caller.0, caller.1, definition, local), caller.2,
            prepared.typed.types@, &wiring, child._signature@, projected);
        if child._signature@.call.target is Function {
            self.resolved_function_signature_evidence((caller.0, caller.1, definition, local), caller.2, child._signature@);
        }
    }

    /// 型検査で保持された呼び出し先と引数範囲を、元の参照から取り出す。
    fn prepare_expression_call(
        &self, plan: &FunctionExpansionOrder<'p, 'a>, file: usize, entry: usize, definition: usize,
        reference: usize, projections: &FuncProjections<'p, 'a>,
        Ghost(context): Ghost<(u64, Seq<Option<SignalType<'p, 'a>>>, &FuncWiring<'p, 'a>, int)>,
    ) -> (item: PreparedExpressionCall<'p, 'a>)
        requires
            self.can_resolve(), self.function_template_plan(*plan),
            self.func_wiring_evidence(file, entry, context.0, Ok(FuncWiringResult::Checked(*context.2))),
            self.projected_references_match((file, entry, context.0), context.1, context.2,
                &projections.call_arguments, projections.calls@),
            plan.position_model(context.3) == Some((file, entry)),
            ({
                let circuits = self.targets.project_model().circuits_model();
                &&& file < circuits.len()
                &&& ({
                    let parsed = &circuits[file as int];
                    &&& entry < parsed.entry_ranges@.len()
                    &&& definition < super::super::definitions::definition_count(parsed, entry as int)
                    &&& ({
                        let absolute = parsed.entry_ranges@[entry as int].definitions.start + definition;
                        &&& absolute < parsed.definitions@.len()
                        &&& parsed.definitions@[absolute].references.start <= reference
                            < parsed.definitions@[absolute].references.end
                        &&& reference < parsed.references@.len()
                        &&& parsed.references@[reference as int].kind is Callee
                    })
                })
            }),
        ensures
            item.reference == reference,
            self.prepared_expression_call_matches(*plan, (file, entry, context.0), definition, &projections.call_arguments,
                context.1, context.2, context.3, item),
            match item._signature@.signature {
                crate::project::FuncCallSignature::Nor => item.arguments.end - item.arguments.start == 2,
                crate::project::FuncCallSignature::Function(ports) =>
                    item.arguments.end - item.arguments.start == ports.inputs@.len(),
            },
            ({
                let parsed = &self.targets.project_model().circuits_model()[file as int];
                let absolute = parsed.entry_ranges@[entry as int].definitions.start + definition;
                let row = parsed.definitions@[absolute];
                reference == row.references.start ==> forall|i: int| 0 <= i < projections.calls@.len()
                    && (#[trigger] projections.calls@[i]).definition == absolute
                    ==> item.arguments == projections.call_arguments.ranges@[i]
            }),
    {
        let ghost caller = (file, entry, context.0);
        let project = self.targets.project();
        proof { self.checked_wiring_is_func(file, entry, context.0, *context.2); }
        let parsed = &project.circuits()[file];
        proof {
            let source = project.sources_model()[file as int];
            parsed_index_evidence(source, *parsed);
            build_entry_ranges_evidence(source.text, &parsed.build_model(), entry as int);
        }
        let frame = &parsed.entry_ranges[entry];
        let absolute = frame.definitions.start + definition;
        proof {
            let source = project.sources_model()[file as int];
            build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, absolute as int);
        }
        let row = &parsed.definitions[absolute];
        let local = reference - row.references.start;
        let (arguments, target) = self.retained_call_reference(file, entry, definition, local, &projections.call_arguments,
            Ghost(context.0), Ghost(context.1), Ghost(*context.2), Ghost(projections.calls@));
        let ghost signature = self.retained_callee_signature(file, entry, definition, local, context.0, target);
        proof {
            self.typed_call_arguments_ready(file, entry, definition, local, context.0, signature);
            self.resolved_call_reference_form(file, entry, definition, local, signature.call);
            crate::syntax::circuit::call_form_bounds(parsed.syntax.forms@, signature.call.call);
            self.checked_projected_input_count((file, entry, definition, local), context.0, context.1, context.2,
                signature, projections.call_arguments.arguments@.subrange(arguments.start as int, arguments.end as int));
        }
        let form = parsed.references[reference].form - 1;
        let source = &project.sources()[file];
        let expression = form_location(source, parsed.syntax.forms.as_slice(), form);
        let Some(target) = target else {
            proof { assert(false); }
            unreachable!()
        };
        let item = match target {
            RetainedCallTarget::Nor => PreparedExpressionCall {
                reference, expression, arguments, vertex: None, _signature: Ghost(signature), _rank: Ghost(None),
            },
            RetainedCallTarget::Function(target_file, target_entry) => {
                let ghost at = DefinitionPosition { file, entry, definition, reference: local };
                let ghost site = self.expansion_site_for_call(at, signature.call);
                let ghost rank = self.template_callee_precedes(*plan, context.3, site);
                let target = (target_file, target_entry);
                let vertex = plan.template_vertex(target);
                proof { plan.template_vertex_at_position(target, rank, vertex); }
                PreparedExpressionCall {
                    reference, expression, arguments, vertex, _signature: Ghost(signature), _rank: Ghost(Some(rank)),
                }
            },
        };
        assert(self.prepared_expression_call_matches(*plan, caller, definition, &projections.call_arguments,
            context.1, context.2, context.3, item)) by { reveal(UseAliases::prepared_expression_call_matches); };
        item
    }

    #[verifier::opaque]
    pub(super) closed spec fn prepared_expression_children_match(
        &self, plan: FunctionExpansionOrder, caller: (usize, usize, u64), definition: usize,
        projections: &CallArgumentProjections, types: Seq<Option<SignalType>>, wiring: &FuncWiring,
        caller_rank: int, children: Seq<PreparedExpressionCall>,
    ) -> bool {
        let parsed = &self.targets.project_model().circuits_model()[caller.0 as int];
        let frame = parsed.entry_ranges@[caller.1 as int];
        let row = parsed.definitions@[frame.definitions.start + definition];
        let source_order = Seq::new(children.len(), |i: int| children[i].reference).push(row.references.start);
        &&& call_references_in_postorder(parsed.syntax.forms@, parsed.references@, row.references, source_order)
        &&& forall|i: int| 0 <= i < children.len() ==> self.prepared_expression_call_matches(
            plan, caller, definition, projections, types, wiring, caller_rank, #[trigger] children[i])
        &&& forall|i: int, j: int| 0 <= i < j < children.len() ==>
            (#[trigger] children[i]).reference != (#[trigger] children[j]).reference
    }

    /// 実引数の位置から、親より先に展開する子の位置と出力型を取り出す。
    pub(super) proof fn prepared_nested_argument(
        &self, plan: FunctionExpansionOrder, caller: (usize, usize, u64), definition: usize,
        arguments: &CallArgumentProjections, types: Seq<Option<SignalType>>, wiring: &FuncWiring,
        caller_rank: int, children: Seq<PreparedExpressionCall>, parent_position: int,
        parent_reference: usize, parent: TypedFuncCall, projected: Seq<ProjectedCallArgument>, port: int,
    ) -> (position: int)
        requires
            self.can_resolve(),
            self.func_wiring_evidence(caller.0, caller.1, caller.2, Ok(FuncWiringResult::Checked(*wiring))),
            self.prepared_expression_children_match(plan, caller, definition, arguments, types, wiring, caller_rank, children),
            self.func_call_signature_evidence(caller.0, caller.1, definition, parent_reference, caller.2, Ok(Some(parent))),
            self.projected_input_arguments((caller.0, caller.1, definition, parent_reference), caller.2, types, wiring, projected),
            self.position_exists(caller.0, caller.1, definition, parent_reference),
            0 <= port < projected.len(),
            projected[port].source is NestedCall,
            0 <= parent_position <= children.len(),
            if parent_position == children.len() {
                parent_reference == 0
            } else {
                let parsed = &self.targets.project_model().circuits_model()[caller.0 as int];
                let row = parsed.definitions@[parsed.entry_ranges@[caller.1 as int].definitions.start + definition];
                children[parent_position].reference == row.references.start + parent_reference
            },
        ensures
            0 <= position < parent_position <= children.len(),
            match parent.signature {
                crate::project::FuncCallSignature::Nor => projected.len() == 2,
                crate::project::FuncCallSignature::Function(ports) => projected.len() == ports.inputs@.len(),
            },
            ({
                let child = children[position];
                let signature = child._signature@;
                let parsed = &self.targets.project_model().circuits_model()[caller.0 as int];
                let row = parsed.definitions@[parsed.entry_ranges@[caller.1 as int].definitions.start + definition];
                let expected = match parent.signature {
                    crate::project::FuncCallSignature::Nor => crate::project::ResolvedPortType::Bits(1),
                    crate::project::FuncCallSignature::Function(ports) => ports.inputs@[port].ty,
                };
                &&& self.prepared_expression_call_matches(plan, caller, definition, arguments, types, wiring, caller_rank, child)
                &&& child.reference == row.references.start + projected[port].source->NestedCall_0
                &&& signature.call.call.form == projected[port].form
                &&& parsed.syntax.forms@[projected[port].form as int] is List
                &&& signature.call.target.port_counts().outputs == 1
                &&& match signature.signature {
                    crate::project::FuncCallSignature::Nor =>
                        crate::project::port_types_equal(crate::project::ResolvedPortType::Bits(1), expected),
                    crate::project::FuncCallSignature::Function(ports) =>
                        ports.outputs@.len() == 1 && crate::project::port_types_equal(ports.outputs@[0].ty, expected),
                }
            }),
    {
        let (file, entry, limit) = caller;
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[file as int];
        let source = &project.sources_model()[file as int];
        let absolute = parsed.entry_ranges@[entry as int].definitions.start + definition;
        let row = parsed.definitions@[absolute];
        let forms = parsed.syntax.forms@;
        let refs = parsed.references@;
        self.typed_call_arguments_ready(file, entry, definition, parent_reference, limit, parent);
        self.targets.parsed_project_model();
        parsed_index_evidence(*source, *parsed);
        build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, absolute);
        vstd::std_specs::vec::axiom_spec_len(&parsed.syntax.forms);
        self.checked_projected_argument((file, entry, definition, parent_reference), limit, types, wiring, parent, projected, port);
        let form = projected[port].form;
        let expected = match parent.signature {
            crate::project::FuncCallSignature::Nor => crate::project::ResolvedPortType::Bits(1),
            crate::project::FuncCallSignature::Function(ports) => ports.inputs@[port].ty,
        };
        let (relative, signature) = self.projected_nested_call_signature((file, entry, definition), limit, form, expected);
        self.typed_call_arguments_ready(file, entry, definition, relative, limit, signature);
        self.call_form_matches_reference(file, entry, definition, form, relative, signature.call);
        crate::syntax::circuit::direct_call_argument_bounds(forms, parent.call.call, form as int);
        self.resolved_call_reference_form(file, entry, definition, parent_reference, parent.call);
        let parent_absolute = (row.references.start + parent_reference) as usize;
        let child_absolute = (row.references.start + relative) as usize;
        let retained = (row.references.start + projected[port].source->NestedCall_0) as usize;
        definition_reference_form_unique(source.text, forms, refs, row, retained, child_absolute);
        reveal(UseAliases::prepared_expression_children_match);
        let order = Seq::new(children.len(), |i: int| children[i].reference).push(row.references.start);
        assert(order[parent_position] == parent_absolute);
        let position = nested_call_postorder_position(source.text, forms, refs, row, order,
            parent_absolute, child_absolute, parent_position);
        let child = children[position];
        assert(child.reference == child_absolute);
        assert(self.prepared_expression_call_matches(plan, caller, definition, arguments, types, wiring, caller_rank, child));
        reveal(UseAliases::prepared_expression_call_matches);
        self.successful_call_signatures_agree(file, entry, definition, relative, limit, signature, child._signature@);
        self.typed_call_arguments_ready(file, entry, definition, relative, limit, child._signature@);
        crate::syntax::circuit::call_form_bounds(forms, child._signature@.call.call);
        assert(child._signature@.call.call.form == form);
        assert(child._signature@.call.target.port_counts().outputs == 1);
        position
    }

    /// 入れ子の呼び出しごとに、型検査済みの引数範囲と展開先を処理順に集める。
    fn prepare_expression_children(
        &self, plan: &FunctionExpansionOrder<'p, 'a>, file: usize, entry: usize, definition: usize,
        order: &[usize], projections: &FuncProjections<'p, 'a>,
        Ghost(context): Ghost<(u64, Seq<Option<SignalType<'p, 'a>>>, &FuncWiring<'p, 'a>, int)>,
    ) -> (children: Vec<PreparedExpressionCall<'p, 'a>>)
        requires
            self.can_resolve(), self.function_template_plan(*plan),
            self.func_wiring_evidence(file, entry, context.0, Ok(FuncWiringResult::Checked(*context.2))),
            self.projected_references_match((file, entry, context.0), context.1, context.2,
                &projections.call_arguments, projections.calls@),
            plan.position_model(context.3) == Some((file, entry)),
            ({
                let circuits = self.targets.project_model().circuits_model();
                &&& file < circuits.len()
                &&& ({
                    let parsed = &circuits[file as int];
                    &&& entry < parsed.entry_ranges@.len()
                    &&& definition < super::super::definitions::definition_count(parsed, entry as int)
                    &&& ({
                        let absolute = parsed.entry_ranges@[entry as int].definitions.start + definition;
                        &&& absolute < parsed.definitions@.len()
                        &&& ({
                            let row = parsed.definitions@[absolute];
                            &&& row.references.end <= parsed.references@.len()
                            &&& order@.len() > 0 && order@.last() == row.references.start
                            &&& call_references_in_postorder(parsed.syntax.forms@, parsed.references@, row.references, order@)
                        })
                    })
                })
            }),
        ensures self.prepared_expression_children_match(*plan, (file, entry, context.0), definition, &projections.call_arguments,
            context.1, context.2, context.3, children@),
    {
        let ghost caller = (file, entry, context.0);
        let ghost parsed = &self.targets.project_model().circuits_model()[file as int];
        let ghost row = parsed.definitions@[parsed.entry_ranges@[entry as int].definitions.start + definition];
        let stop = order.len() - 1;
        let mut children: Vec<PreparedExpressionCall<'p, 'a>> = Vec::new();
        let mut index = 0;
        while index < stop
            invariant
                self.can_resolve(), self.function_template_plan(*plan),
                caller == (file, entry, context.0),
                self.func_wiring_evidence(file, entry, context.0, Ok(FuncWiringResult::Checked(*context.2))),
                self.projected_references_match(caller, context.1, context.2, &projections.call_arguments, projections.calls@),
                plan.position_model(context.3) == Some((file, entry)),
                *parsed == self.targets.project_model().circuits_model()[file as int],
                row == parsed.definitions@[parsed.entry_ranges@[entry as int].definitions.start + definition],
                definition < super::super::definitions::definition_count(parsed, entry as int),
                stop + 1 == order@.len(), order@.last() == row.references.start,
                call_references_in_postorder(parsed.syntax.forms@, parsed.references@, row.references, order@),
                file < self.targets.project_model().circuits_model().len(),
                entry < parsed.entry_ranges@.len(),
                parsed.entry_ranges@[entry as int].definitions.start + definition < parsed.definitions@.len(),
                row.references.end <= parsed.references@.len(),
                index == children@.len() <= stop,
                forall|i: int| 0 <= i < children@.len() ==> {
                    let child = #[trigger] children@[i];
                    &&& child.reference == order@[i]
                    &&& self.prepared_expression_call_matches(*plan, caller, definition, &projections.call_arguments,
                        context.1, context.2, context.3, child)
                },
            decreases stop - index,
        {
            let reference = order[index];
            proof { call_postorder_reference(parsed.syntax.forms@, parsed.references@, row.references, order@, index as int); }
            let child = self.prepare_expression_call(plan, file, entry, definition, reference, projections, Ghost(context));
            let ghost before = children@;
            children.push(child);
            assert forall|i: int| 0 <= i < children@.len() implies {
                let item = #[trigger] children@[i];
                &&& item.reference == order@[i]
                &&& self.prepared_expression_call_matches(*plan, caller, definition, &projections.call_arguments,
                    context.1, context.2, context.3, item)
            } by {
                if i < index { assert(children@[i] == before[i]); }
            };
            index += 1;
        }
        proof {
            reveal(UseAliases::prepared_expression_children_match);
            let references = Seq::new(children@.len(), |i: int| children@[i].reference);
            assert(references.push(row.references.start) =~= order@);
            assert forall|i: int, j: int| 0 <= i < j < children@.len() implies
                (#[trigger] children@[i]).reference != (#[trigger] children@[j]).reference by {
                assert(order@[i] == children@[i].reference && order@[j] == children@[j].reference);
                call_postorder_references_distinct(parsed.syntax.forms@, parsed.references@, row.references, order@, i, j);
            };
        }
        children
    }

    /// 右辺の根を準備し、内側の呼び出しを後順に並べる。
    fn prepare_root_expression(
        &self, plan: &FunctionExpansionOrder<'p, 'a>, file: usize, entry: usize, definition: usize,
        projections: &FuncProjections<'p, 'a>,
        Ghost(context): Ghost<(u64, Seq<Option<SignalType<'p, 'a>>>, &FuncWiring<'p, 'a>, int)>,
    ) -> (calls: (PreparedExpressionCall<'p, 'a>, Option<Vec<PreparedExpressionCall<'p, 'a>>>))
        requires
            self.can_resolve(), self.function_template_plan(*plan),
            self.func_wiring_evidence(file, entry, context.0, Ok(FuncWiringResult::Checked(*context.2))),
            self.projected_references_match((file, entry, context.0), context.1, context.2,
                &projections.call_arguments, projections.calls@),
            plan.position_model(context.3) == Some((file, entry)),
            ({
                let project = self.targets.project_model();
                &&& file < project.circuits_model().len() && file < project.sources_model().len()
                &&& {
                    let parsed = &project.circuits_model()[file as int];
                    let source = &project.sources_model()[file as int];
                    &&& entry < parsed.entry_ranges@.len()
                    &&& definition < super::super::definitions::definition_count(parsed, entry as int)
                    &&& {
                        let absolute = parsed.entry_ranges@[entry as int].definitions.start + definition;
                        &&& absolute < parsed.definitions@.len()
                        &&& {
                            let row = parsed.definitions@[absolute];
                            crate::syntax::circuit::ordinary_call_at(source.text, parsed.syntax.forms@,
                                row.expression.start as int, row.expression.end as int)
                        }
                    }
                }
            }),
        ensures ({
            let parsed = &self.targets.project_model().circuits_model()[file as int];
            let absolute = parsed.entry_ranges@[entry as int].definitions.start + definition;
            let row = parsed.definitions@[absolute];
            &&& calls.0.reference == row.references.start
            &&& calls.0._signature@.call.call.form == row.expression.start
            &&& self.prepared_expression_call_matches(*plan, (file, entry, context.0), definition,
                &projections.call_arguments, context.1, context.2, context.3, calls.0)
            &&& match calls.0._signature@.signature {
                crate::project::FuncCallSignature::Nor => calls.0.arguments.end - calls.0.arguments.start == 2,
                crate::project::FuncCallSignature::Function(ports) =>
                    calls.0.arguments.end - calls.0.arguments.start == ports.inputs@.len(),
            }
            &&& forall|i: int| 0 <= i < projections.calls@.len()
                && (#[trigger] projections.calls@[i]).definition == absolute ==> calls.0.arguments == projections.call_arguments.ranges@[i]
            &&& match calls.1 {
                None => row.references.end == row.references.start + 1,
                Some(children) => row.references.end > row.references.start + 1
                    && self.prepared_expression_children_match(*plan, (file, entry, context.0), definition,
                        &projections.call_arguments, context.1, context.2, context.3, children@),
            }
        }),
    {
        proof {
            self.checked_wiring_is_func(file, entry, context.0, *context.2);
            self.targets.parsed_project_model();
        }
        let project = self.targets.project();
        let parsed = &project.circuits()[file];
        let source = &project.sources()[file];
        proof {
            parsed_index_evidence(*source, *parsed);
            build_entry_ranges_evidence(source.text, &parsed.build_model(), entry as int);
        }
        let absolute = parsed.entry_ranges[entry].definitions.start + definition;
        let row = &parsed.definitions[absolute];
        let forms = parsed.syntax.forms.as_slice();
        proof {
            build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, absolute as int);
            vstd::std_specs::vec::axiom_spec_len(&parsed.syntax.forms);
            root_call_reference(source.text, forms@, parsed.references@, *row);
        }
        let root = self.prepare_expression_call(plan, file, entry, definition, row.references.start, projections, Ghost(context));
        proof {
            reveal(UseAliases::prepared_expression_call_matches);
            self.typed_call_arguments_ready(file, entry, definition, 0, context.0, root._signature@);
            self.resolved_call_reference_form(file, entry, definition, 0, root._signature@.call);
        }
        let children = if row.references.end - row.references.start == 1 {
            None
        } else {
            let order = postorder_call_references(source.text, forms, row, parsed.references.as_slice());
            proof { root_call_postorder_last(source.text, forms@, parsed.references@, *row, order@); }
            Some(self.prepare_expression_children(plan, file, entry, definition, order.as_slice(), projections, Ghost(context)))
        };
        (root, children)
    }

    fn check_expansion_call_groups(
        &self, plan: &FunctionExpansionOrder<'p, 'a>, file: usize, entry: usize, limit: u64,
        typed: &FuncSignalTypes<'p, 'a>, wiring: &FuncWiring<'p, 'a>, projections: &FuncProjections<'p, 'a>,
        Ghost(caller_rank): Ghost<int>,
    ) -> (groups: Vec<CheckedExpansionCall<'p, 'a>>)
        requires
            self.can_resolve(), self.function_template_plan(*plan),
            plan.position_model(caller_rank) == Some((file, entry)),
            self.func_signal_types_evidence(file, entry, limit, Ok(*typed)),
            typed.literals.wiring == FuncWiringResult::Checked(*wiring),
            typed.types@.len() == wiring.drivers.definitions@.len(),
            self.root_function_calls_match((file, entry, limit), &wiring.drivers, projections.calls@, typed.types@.len()),
            projections.call_arguments.ranges@.len() == projections.calls@.len(),
            self.projected_references_match((file, entry, limit), typed.types@, wiring,
                &projections.call_arguments, projections.calls@),
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
        let ghost source = &project.sources_model()[file as int];
        proof {
            parsed_index_evidence(*source, *parsed);
            build_entry_ranges_evidence(source.text, &parsed.build_model(), entry as int);
        }
        let mut groups: Vec<CheckedExpansionCall<'p, 'a>> = Vec::new();
        let mut index = 0;
        while index < projections.calls.len()
            invariant
                caller == (file, entry, limit),
                self.can_resolve(), self.function_template_plan(*plan),
                plan.position_model(caller_rank) == Some((file, entry)),
                self.func_wiring_evidence(file, entry, limit, Ok(FuncWiringResult::Checked(*wiring))),
                self.func_signal_types_evidence(file, entry, limit, Ok(*typed)),
                typed.literals.wiring == FuncWiringResult::Checked(*wiring),
                typed.types@.len() == wiring.drivers.definitions@.len(),
                self.root_function_calls_match(caller, &wiring.drivers, projections.calls@, typed.types@.len()),
                self.root_call_definitions_in_order(file, entry, projections.calls@),
                projections.call_arguments.ranges@.len() == projections.calls@.len(),
                self.projected_references_match(caller, typed.types@, wiring,
                    &projections.call_arguments, projections.calls@),
                index == groups@.len() <= projections.calls@.len(),
                file < self.targets.project_model().circuits_model().len(),
                file < self.targets.project_model().sources_model().len(),
                *parsed == self.targets.project_model().circuits_model()[file as int],
                *source == self.targets.project_model().sources_model()[file as int],
                parsed_circuit_matches(*source, *parsed),
                entry < parsed.syntax.entries@.len(), entry < parsed.entry_ranges@.len(),
                parsed.entry_ranges@[entry as int].definitions.end <= parsed.definitions@.len(),
                crate::syntax::form_spans_valid(source.text, parsed.syntax.forms@, source.text.spec_bytes().len() as int),
                forall|j: int| 0 <= j < groups@.len() ==> self.checked_expansion_call_matches(*plan, caller, *typed,
                    wiring, projections.calls@[j], projections.call_arguments.ranges@[j], &projections.call_arguments,
                    #[trigger] groups@[j]),
            decreases projections.calls@.len() - index,
        {
            let root = &projections.calls[index];
            let ghost group_model = self.checked_root_call_for_expansion(*plan, caller, *typed, *wiring,
                projections.calls@, index as int, caller_rank);
            let start = parsed.entry_ranges[entry].definitions.start;
            let definition = root.definition - start;
            let row = &parsed.definitions[root.definition];
            proof {
                parsed_index_evidence(*source, *parsed);
                build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, root.definition as int);
                let refs = row.references;
                assert(definition < super::super::definitions::definition_count(parsed, entry as int));
                assert(super::super::definitions::reference_count(parsed, entry as int, definition as int)
                    == refs.end - refs.start > 0);
            }
            let (root_call, postorder) = self.prepare_root_expression(plan, file, entry, definition, projections,
                Ghost((limit, typed.types@, wiring, group_model.1.1)));
            let arguments = root_call.arguments;
            proof {
                reveal(UseAliases::prepared_expression_call_matches);
                vstd::std_specs::vec::axiom_spec_len(&typed.types);
                self.successful_call_signatures_agree(file, entry, definition, 0, limit, group_model.0, root_call._signature@);
                let rank = root_call._rank@->Some_0;
                self.function_template_rank_at(*plan, (root.target_file, root.target_entry), rank, group_model.1.0);
                assert(root_call.vertex == Some(plan.order_model()[group_model.1.0]));
                assert(arguments == projections.call_arguments.ranges@[index as int]);
            }
            let Some(vertex) = root_call.vertex else {
                proof { assert(false); }
                unreachable!()
            };
            let group = CheckedExpansionCall {
                expression: root_call.expression,
                outputs: root.first_output..root.first_output + root.count,
                arguments: arguments.start..arguments.end,
                references: row.references.start..row.references.end,
                postorder, vertex, _signature: Ghost(group_model.0), _order: Ghost(group_model.1),
            };
            assert(self.checked_expansion_call_matches(*plan, caller, *typed, wiring, *root, arguments,
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

    /// 根と子が、同じ厳格構文木と型検査済み引数を参照することを表す。
    pub(super) closed spec fn prepared_nor_root_matches(
        &self, plan: FunctionExpansionOrder, caller: (usize, usize, u64), types: Seq<Option<SignalType>>,
        wiring: &FuncWiring, projections: &CallArgumentProjections, absolute: usize, prepared: PreparedNorRoot,
    ) -> bool {
        let (file, entry, _) = caller;
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[file as int];
        let frame = parsed.entry_ranges@[entry as int];
        let row = parsed.definitions@[absolute as int];
        let definition = (absolute - frame.definitions.start) as usize;
        let range = prepared.root.arguments;
        let rank = prepared._caller_rank@;
        &&& frame.definitions.start <= absolute < frame.definitions.end <= parsed.definitions@.len()
        &&& prepared.definition == absolute
        &&& prepared.output_slot < wiring.drivers.definitions@.len() && prepared.output_slot < types.len()
        &&& wiring.drivers.definitions@[prepared.output_slot as int].definition == absolute
        &&& wiring.drivers.definitions@[prepared.output_slot as int].result_index == 0
        &&& types[prepared.output_slot as int] matches Some(ty) && ty.ty == crate::project::ResolvedPortType::Bits(1)
        &&& forall|i: int| 0 <= i < wiring.drivers.definitions@.len()
            && (#[trigger] wiring.drivers.definitions@[i]).definition == absolute ==> i == prepared.output_slot
        &&& 0 <= rank < plan.order_model().len() && plan.position_model(rank) == Some((file, entry))
        &&& crate::syntax::circuit::ordinary_call_at(project.sources_model()[file as int].text, parsed.syntax.forms@,
            row.expression.start as int, row.expression.end as int)
        &&& prepared.root.reference == row.references.start
        &&& prepared.root._signature@.call.call.form == row.expression.start
        &&& prepared.root._signature@.call.target is Nor
        &&& prepared.root._signature@.signature is Nor
        &&& prepared.root.vertex.is_none() && prepared.root._rank@.is_none()
        &&& self.prepared_expression_call_matches(plan, caller, definition, projections, types, wiring, rank, prepared.root)
        &&& range.start + 2 == range.end <= projections.arguments@.len()
        &&& (projections.arguments@[range.start as int].source is NestedCall
            || projections.arguments@[range.start + 1].source is NestedCall)
        &&& prepared.postorder@.len() > 0
        &&& self.prepared_expression_children_match(plan, caller, definition, projections, types, wiring,
            rank, prepared.postorder@)
    }

    /// 根とすべての子が属する参照区間を、元の厳格定義から得る。
    pub(super) proof fn prepared_nor_reference_evidence(
        &self, plan: FunctionExpansionOrder, caller: (usize, usize, u64),
        prepared: &PreparedExpansionBody, index: int,
    )
        requires
            self.can_resolve(), self.prepared_expansion_body_matches(plan, caller.0, caller.1, caller.2, prepared),
            0 <= index < prepared.nor_roots@.len(),
        ensures ({
            let root = prepared.nor_roots@[index];
            let parsed = &self.targets.project_model().circuits_model()[caller.0 as int];
            let source = &self.targets.project_model().sources_model()[caller.0 as int];
            let references = parsed.definitions@[root.definition as int].references;
            &&& root.definition < parsed.definitions@.len()
            &&& root.root.expression.source == source
            &&& references.start == root.root.reference
            &&& self.expression_children_in_reference_range(references, root.root.expression.source, Some(root.postorder))
            &&& forall|i: int| 0 <= i < root.postorder@.len() ==>
                references.start < (#[trigger] root.postorder@[i]).reference
        }),
    {
        reveal(UseAliases::prepared_nor_root_matches);
        reveal(UseAliases::prepared_expression_children_match);
        reveal(UseAliases::prepared_expression_call_matches);
        let root = prepared.nor_roots@[index];
        let parsed = &self.targets.project_model().circuits_model()[caller.0 as int];
        let references = parsed.definitions@[root.definition as int].references;
        let children = root.postorder@;
        let last = children.len() as int;
        let order = Seq::new(children.len(), |i: int| children[i].reference).push(references.start);
        assert forall|i: int| 0 <= i < children.len() implies
            references.start < (#[trigger] children[i]).reference by {
            assert(order[i] == children[i].reference && order[last] == references.start);
            call_postorder_references_distinct(parsed.syntax.forms@, parsed.references@, references, order, i, last);
        };
    }

    /// 根 NOR の出力スロットと式全体のソース範囲を、定義の投影に渡す。
    pub(super) proof fn prepared_nor_output_evidence(
        &self, plan: FunctionExpansionOrder, caller: (usize, usize, u64),
        prepared: &PreparedExpansionBody, index: int,
    )
        requires
            self.can_resolve(), self.prepared_expansion_body_matches(plan, caller.0, caller.1, caller.2, prepared),
            0 <= index < prepared.nor_roots@.len(),
        ensures ({
            let root = prepared.nor_roots@[index];
            let wiring = prepared.typed.literals.wiring->Checked_0;
            let project = self.targets.project_model();
            let parsed = &project.circuits_model()[caller.0 as int];
            let expr = parsed.definitions@[root.definition as int].expression;
            let frame = parsed.entry_ranges@[caller.1 as int].definitions;
            let at = root.output_slot as int;
            &&& caller.1 < parsed.entry_ranges@.len()
            &&& frame.start <= root.definition < frame.end <= parsed.definitions@.len()
            &&& at < prepared.typed.types@.len() == wiring.drivers.definitions@.len()
            &&& prepared.typed.types@[at] matches Some(ty) && ty.ty == crate::project::ResolvedPortType::Bits(1)
            &&& wiring.drivers.definitions@[at].definition == root.definition
            &&& wiring.drivers.definitions@[at].result_index == 0
            &&& forall|i: int| 0 <= i < wiring.drivers.definitions@.len()
                && (#[trigger] wiring.drivers.definitions@[i]).definition == root.definition ==> i == at
            &&& location_in_source(root.root.expression)
            &&& crate::syntax::circuit::ordinary_call_at(project.sources_model()[caller.0 as int].text,
                parsed.syntax.forms@, expr.start as int, expr.end as int)
        }),
    {
        reveal(UseAliases::prepared_nor_root_matches);
        reveal(UseAliases::prepared_expression_call_matches);
        let root = prepared.nor_roots@[index];
        let project = self.targets.project_model();
        let source = &project.sources_model()[caller.0 as int];
        let parsed = &project.circuits_model()[caller.0 as int];
        let wiring = prepared.typed.literals.wiring->Checked_0;
        self.checked_types_keep_wiring(caller.0, caller.1, caller.2, prepared.typed, wiring);
        self.checked_wiring_is_func(caller.0, caller.1, caller.2, wiring);
        self.targets.parsed_project_model();
        parsed_index_evidence(*source, *parsed);
        let form = root.root._signature@.call.call.form;
        assert(is_form_location(source, parsed.syntax.forms@[form as int], root.root.expression));
    }

    /// 根と子の引数位置を厳格構文木の出現順に対応付ける。引数のない子には空の列を対応させる。
    pub(super) proof fn prepared_nor_arguments_in_source_order(
        &self, plan: FunctionExpansionOrder, caller: (usize, usize, u64),
        prepared: &PreparedExpansionBody, index: int, parent_index: int,
    )
        requires
            self.can_resolve(),
            self.prepared_expansion_body_matches(plan, caller.0, caller.1, caller.2, prepared),
            0 <= index < prepared.nor_roots@.len(),
            0 <= parent_index <= prepared.nor_roots@[index].postorder@.len(),
        ensures ({
            let root = prepared.nor_roots@[index];
            let children = root.postorder@;
            let parent = if parent_index == children.len() { root.root } else { children[parent_index] };
            let parsed = &self.targets.project_model().circuits_model()[caller.0 as int];
            let row = parsed.definitions@[root.definition as int];
            let local = (root.definition - parsed.entry_ranges@[caller.1 as int].definitions.start) as usize;
            let reference = (parent.reference - row.references.start) as usize;
            let call = parent._signature@;
            let forms = parsed.syntax.forms@;
            let projected = prepared.projections.call_arguments.arguments@.subrange(parent.arguments.start as int, parent.arguments.end as int);
            &&& row.references.start <= parent.reference < row.references.end
            &&& if parent_index == children.len() {
                parent.reference == row.references.start && call.call.call.form == row.expression.start
                    && call.call.target is Nor && call.signature is Nor
                    && projected.len() == 2
                    && (projected[0].source is NestedCall || projected[1].source is NestedCall)
            } else {
                row.expression.start < call.call.call.form < row.expression.end
            }
            &&& self.func_call_form_reference(caller.0, caller.1, local, call.call.call.form, reference)
            &&& self.func_call_signature_evidence(caller.0, caller.1, local, reference, caller.2, Ok(Some(call)))
            &&& parent.arguments.start <= parent.arguments.end <= prepared.projections.call_arguments.arguments@.len()
            &&& crate::syntax::circuit::call_argument_positions(forms, parent._signature@.call.call,
                Seq::new(projected.len(), |port: int| projected[port].form))
        }),
    {
        reveal(UseAliases::prepared_nor_root_matches);
        reveal(UseAliases::prepared_expression_children_match);
        reveal(UseAliases::prepared_expression_call_matches);
        let (file, entry, limit) = caller;
        let root = prepared.nor_roots@[index];
        let children = root.postorder@;
        let parent = if parent_index == children.len() { root.root } else { children[parent_index] };
        let wiring = prepared.typed.literals.wiring->Checked_0;
        self.checked_types_keep_wiring(file, entry, limit, prepared.typed, wiring);
        let parsed = &self.targets.project_model().circuits_model()[file as int];
        let local = (root.definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
        let row = parsed.definitions@[root.definition as int];
        let reference = (parent.reference - row.references.start) as usize;
        let forms = parsed.syntax.forms@;
        let signature = parent._signature@;
        self.typed_call_arguments_ready(file, entry, local, reference, limit, signature);
        self.resolved_call_reference_form(file, entry, local, reference, signature.call);
        crate::syntax::circuit::indexed_call_arguments(signature.call.source.text, forms, row,
            parsed.references@[parent.reference as int], signature.call.call);
        if parent_index < children.len() && signature.call.call.form == row.expression.start {
            self.targets.parsed_project_model();
            let source = &self.targets.project_model().sources_model()[file as int];
            parsed_index_evidence(*source, *parsed);
            build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, root.definition as int);
            vstd::std_specs::vec::axiom_spec_len(&parsed.syntax.forms);
            self.typed_call_arguments_ready(file, entry, local, 0, limit, root.root._signature@);
            self.resolved_call_reference_form(file, entry, local, 0, root.root._signature@.call);
            let order = Seq::new(children.len(), |i: int| children[i].reference).push(row.references.start);
            call_postorder_references_distinct(forms, parsed.references@, row.references, order, parent_index, children.len() as int);
            definition_reference_form_unique(source.text, forms, parsed.references@, row, row.references.start, parent.reference);
        }
        let projected = prepared.projections.call_arguments.arguments@.subrange(parent.arguments.start as int, parent.arguments.end as int);
        self.projected_arguments_in_source_order((file, entry, local, reference), limit, prepared.typed.types@,
            &wiring, parent._signature@, projected);
    }

    /// 根と子の実引数を元のフォーム、先行する定義、または後順の子の出力に対応付ける。
    pub(super) proof fn prepared_nor_argument_evidence(
        &self, plan: FunctionExpansionOrder, caller: (usize, usize, u64), prepared: &PreparedExpansionBody,
        index: int, first: usize, parent_index: int, port: int,
    )
        requires
            self.can_resolve(),
            self.prepared_expansion_body_matches(plan, caller.0, caller.1, caller.2, prepared),
            0 <= index < prepared.nor_roots@.len(),
            ({
                let root = prepared.nor_roots@[index];
                let wiring = prepared.typed.literals.wiring->Checked_0;
                let children = root.postorder@;
                let parent = if parent_index == children.len() { root.root } else { children[parent_index] };
                &&& first < wiring.drivers.definitions@.len()
                &&& wiring.drivers.definitions@[first as int].definition == root.definition
                &&& wiring.drivers.definitions@[first as int].result_index == 0
                &&& 0 <= parent_index <= children.len()
                &&& 0 <= port < parent.arguments.end - parent.arguments.start
            }),
        ensures ({
            let root = prepared.nor_roots@[index];
            let children = root.postorder@;
            let parent = if parent_index == children.len() { root.root } else { children[parent_index] };
            let project = self.targets.project_model();
            let parsed = &project.circuits_model()[caller.0 as int];
            let source = &project.sources_model()[caller.0 as int];
            let row = parsed.definitions@[root.definition as int];
            let frame = parsed.entry_ranges@[caller.1 as int];
            let wiring = prepared.typed.literals.wiring->Checked_0;
            let arg = prepared.projections.call_arguments.arguments@[parent.arguments.start + port];
            let form = parsed.syntax.forms@[arg.form as int];
            let expected = match parent._signature@.signature {
                crate::project::FuncCallSignature::Nor => crate::project::ResolvedPortType::Bits(1),
                crate::project::FuncCallSignature::Function(ports) => ports.inputs@[port].ty,
            };
            &&& parent.arguments.start <= parent.arguments.end <= prepared.projections.call_arguments.arguments@.len()
            &&& arg.form < parsed.syntax.forms@.len()
            &&& caller.1 < parsed.entry_ranges@.len()
            &&& frame.definitions.start <= root.definition < frame.definitions.end <= parsed.definitions@.len()
            &&& row.signals.end <= parsed.signals@.len()
            &&& match arg.source {
                CallArgumentSource::Driver(driver) => {
                    &&& form is Atom && form->Atom_kind is Name
                    &&& exists|position: int| row.signals.start <= position < row.signals.end
                        && (#[trigger] parsed.signals@[position]) == arg.form
                        && 0 <= position - frame.signals.start < wiring.signals@.len()
                        && wiring.signals@[position - frame.signals.start].driver == driver
                    &&& signal_type_at(&wiring, prepared.typed.types@, driver) matches Some(known)
                        && crate::project::port_types_equal(known.ty, expected)
                    &&& match driver {
                        super::super::OutputDriver::Input(i) => i < wiring.drivers.signature.inputs@.len(),
                        super::super::OutputDriver::Definition(i) => i < first,
                    }
                },
                CallArgumentSource::Literal(width) => {
                    let span = crate::syntax::form_span(form);
                    let bytes = source.text.spec_bytes()[span.start as int..span.end as int];
                    &&& expected == crate::project::ResolvedPortType::Bits(width)
                    &&& form is Atom && !(form->Atom_kind is Name)
                    &&& span.start < span.end <= source.text.spec_bytes().len()
                    &&& super::lowering::literal_argument_matches_width(source, parsed.syntax.forms@, arg.form, width as int)
                    &&& crate::project::circuit_literal_width_matches(bytes, Some(width), caller.2, Ok(width))
                    &&& ((width == 1 && bytes.len() == 1 && (bytes[0] == b'0' || bytes[0] == b'1'))
                        || crate::syntax::bare_atom_kind(bytes) == Some(crate::syntax::AtomKind::Binary)
                        || crate::syntax::bare_atom_kind(bytes) == Some(crate::syntax::AtomKind::Hexadecimal))
                },
                CallArgumentSource::NestedCall(_) =>
                    form is List && prepared_nested_output_matches(children, row.references.start, parent_index, arg, expected),
                CallArgumentSource::Deferred => true,
            }
        }),
    {
        reveal(UseAliases::prepared_nor_root_matches);
        reveal(UseAliases::prepared_expression_children_match);
        reveal(UseAliases::prepared_expression_call_matches);
        let (file, entry, limit) = caller;
        let root = prepared.nor_roots@[index];
        let children = root.postorder@;
        let parent = if parent_index == children.len() { root.root } else { children[parent_index] };
        let wiring = prepared.typed.literals.wiring->Checked_0;
        self.checked_types_keep_wiring(file, entry, limit, prepared.typed, wiring);
        self.checked_wiring_is_func(file, entry, limit, wiring);
        self.targets.parsed_project_model();
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[file as int];
        let source = &project.sources_model()[file as int];
        parsed_index_evidence(*source, *parsed);
        build_entry_ranges_evidence(source.text, &parsed.build_model(), entry as int);
        build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, root.definition as int);
        let row = parsed.definitions@[root.definition as int];
        let definition = (root.definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
        let reference = (parent.reference - row.references.start) as usize;
        let arguments = &prepared.projections.call_arguments;
        let projected = arguments.arguments@.subrange(parent.arguments.start as int, parent.arguments.end as int);
        assert(projected[port] == arguments.arguments@[parent.arguments.start + port]);
        self.typed_call_arguments_ready(file, entry, definition, reference, limit, parent._signature@);
        self.checked_projected_argument((file, entry, definition, reference), limit, prepared.typed.types@,
            &wiring, parent._signature@, projected, port);
        if projected[port].source is NestedCall {
            self.prepared_nested_argument(plan, caller, definition, arguments, prepared.typed.types@, &wiring,
                root._caller_rank@, children, parent_index, reference, parent._signature@, projected, port);
        }
        if let CallArgumentSource::Driver(super::super::OutputDriver::Definition(driver)) = projected[port].source {
            assert(wiring.drivers.definitions@[driver as int].definition < root.definition);
            if first < driver {
                assert(wiring.drivers.definitions@[first as int].definition <= wiring.drivers.definitions@[driver as int].definition);
            }
            assert(driver < first);
        }
    }

    /// 根で決めた引数範囲と、子の回路を選ぶための根拠を取り出す。
    pub(super) proof fn nor_root_template_evidence(
        &self, plan: FunctionExpansionOrder, caller: (usize, usize, u64),
        prepared: &PreparedExpansionBody, index: int,
    )
        requires
            self.can_resolve(),
            self.prepared_expansion_body_matches(plan, caller.0, caller.1, caller.2, prepared),
            0 <= index < prepared.nor_roots@.len(),
        ensures ({
            let root = prepared.nor_roots@[index];
            let args = prepared.projections.call_arguments.arguments@;
            &&& plan.position_model(root._caller_rank@) == Some((caller.0, caller.1))
            &&& root.root._signature@.signature is Nor
            &&& root.root.arguments.start + 2 == root.root.arguments.end <= args.len()
            &&& forall|i: int| 0 <= i < root.postorder@.len() ==> self.expression_template_ready(
                &plan, caller.2, root._caller_rank@, args.len(), #[trigger] root.postorder@[i])
        }),
    {
        let root = prepared.nor_roots@[index];
        let (file, entry, limit) = caller;
        let parsed = &self.targets.project_model().circuits_model()[file as int];
        let definition = (root.definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
        let row = parsed.definitions@[root.definition as int];
        let args = &prepared.projections.call_arguments;
        let wiring = prepared.typed.literals.wiring->Checked_0;
        reveal(UseAliases::prepared_nor_root_matches);
        reveal(UseAliases::prepared_expression_children_match);
        assert forall|i: int| 0 <= i < root.postorder@.len() implies self.expression_template_ready(
            &plan, limit, root._caller_rank@, args.arguments@.len(), #[trigger] root.postorder@[i]) by {
            let child = root.postorder@[i];
            reveal(UseAliases::prepared_expression_call_matches);
            let reference = (child.reference - row.references.start) as usize;
            let span = child.arguments;
            let projected = args.arguments@.subrange(span.start as int, span.end as int);
            self.checked_projected_input_count((file, entry, definition, reference), limit,
                prepared.typed.types@, &wiring, child._signature@, projected);
            self.typed_call_arguments_ready(file, entry, definition, reference, limit, child._signature@);
            if child._signature@.call.target is Function {
                self.resolved_function_signature_evidence((file, entry, definition, reference), limit, child._signature@);
            }
        };
    }

    /// 同じ厳格構文木のフォームを指す二つの後順項目を同定する。
    pub(super) proof fn prepared_nor_children_at_same_form(
        &self, plan: FunctionExpansionOrder, caller: (usize, usize, u64), prepared: &PreparedExpansionBody,
        index: int, left: int, right: int,
    )
        requires
            self.can_resolve(),
            self.prepared_expansion_body_matches(plan, caller.0, caller.1, caller.2, prepared),
            0 <= index < prepared.nor_roots@.len(),
            ({
                let children = prepared.nor_roots@[index].postorder@;
                &&& 0 <= left < children.len() && 0 <= right < children.len()
                &&& children[left]._signature@.call.call.form == children[right]._signature@.call.call.form
            }),
        ensures left == right,
    {
        reveal(UseAliases::prepared_nor_root_matches);
        reveal(UseAliases::prepared_expression_children_match);
        reveal(UseAliases::prepared_expression_call_matches);
        self.targets.parsed_project_model();
        let (file, entry, limit) = caller;
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[file as int];
        let source = &project.sources_model()[file as int];
        let root = prepared.nor_roots@[index];
        let local = (root.definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
        let row = parsed.definitions@[root.definition as int];
        let children = root.postorder@;
        let a = children[left];
        let b = children[right];
        let a_ref = (a.reference - row.references.start) as usize;
        let b_ref = (b.reference - row.references.start) as usize;
        self.typed_call_arguments_ready(file, entry, local, a_ref, limit, a._signature@);
        self.typed_call_arguments_ready(file, entry, local, b_ref, limit, b._signature@);
        self.resolved_call_reference_form(file, entry, local, a_ref, a._signature@.call);
        self.resolved_call_reference_form(file, entry, local, b_ref, b._signature@.call);
        parsed_index_evidence(*source, *parsed);
        build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, root.definition as int);
        vstd::std_specs::vec::axiom_spec_len(&parsed.syntax.forms);
        definition_reference_form_unique(source.text, parsed.syntax.forms@, parsed.references@, row, a.reference, b.reference);
        if left < right {
            assert(children[left].reference != children[right].reference);
        } else if right < left {
            assert(children[right].reference != children[left].reference);
        }
    }

    /// 対象フォームを含む引数をたどり、その子を直接使う親と入力ポートを求める。
    #[verifier::spinoff_prover]
    proof fn prepared_nor_child_input(
        &self, plan: FunctionExpansionOrder, caller: (usize, usize, u64), prepared: &PreparedExpansionBody,
        index: int, parent_index: int, target: int,
    ) -> (edge: (int, int))
        requires
            self.can_resolve(),
            self.prepared_expansion_body_matches(plan, caller.0, caller.1, caller.2, prepared),
            0 <= index < prepared.nor_roots@.len(),
            ({
                let root = prepared.nor_roots@[index];
                let children = root.postorder@;
                let forms = self.targets.project_model().circuits_model()[caller.0 as int].syntax.forms@;
                let parent = if parent_index == children.len() { root.root } else { children[parent_index] };
                let first = parent._signature@.call.call.form as int;
                let descendant = children[target]._signature@.call.call.form as int;
                &&& nor_definition_determined(&root, prepared.projections.call_arguments.arguments@)
                &&& 0 <= parent_index <= children.len() && 0 <= target < children.len()
                &&& 0 <= first < descendant < forms.len()
                &&& forms[first] is List && forms[descendant] is List
                &&& descendant < forms[first]->List_end <= forms.len()
            }),
        ensures ({
            let root = prepared.nor_roots@[index];
            let children = root.postorder@;
            let (i, port) = edge;
            let parent = if i == children.len() { root.root } else { children[i] };
            let argument = prepared.projections.call_arguments.arguments@[parent.arguments.start + port];
            let child = children[target];
            let parsed = &self.targets.project_model().circuits_model()[caller.0 as int];
            let start = parsed.definitions@[root.definition as int].references.start;
            &&& 0 <= target < i <= parent_index
            &&& 0 <= port < parent.arguments.end - parent.arguments.start
            &&& parent.arguments.end <= prepared.projections.call_arguments.arguments@.len()
            &&& argument.form == child._signature@.call.call.form
            &&& argument.source is NestedCall && child.reference == start + argument.source->NestedCall_0
            &&& child._signature@.call.target.port_counts().outputs == 1
            &&& child._signature@.signature matches crate::project::FuncCallSignature::Function(ports) ==>
                ports.outputs@.len() == 1
        }),
        decreases parent_index,
    {
        reveal(UseAliases::prepared_nor_root_matches);
        reveal(UseAliases::prepared_expression_children_match);
        reveal(UseAliases::prepared_expression_call_matches);
        reveal(nor_definition_determined);
        let (file, entry, limit) = caller;
        let root = prepared.nor_roots@[index];
        let children = root.postorder@;
        let parent = if parent_index == children.len() { root.root } else { children[parent_index] };
        let args = prepared.projections.call_arguments.arguments@;
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[file as int];
        let source = &project.sources_model()[file as int];
        let forms = parsed.syntax.forms@;
        let row = parsed.definitions@[root.definition as int];
        let local = (root.definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
        let reference = (parent.reference - row.references.start) as usize;
        let typed = parent._signature@;
        self.prepared_nor_arguments_in_source_order(plan, caller, prepared, index, parent_index);
        self.typed_call_arguments_ready(file, entry, local, reference, limit, typed);
        crate::syntax::circuit::indexed_call_arguments(source.text, forms, row,
            parsed.references@[row.references.start + reference], typed.call.call);
        let range = parent.arguments;
        let projected = args.subrange(range.start as int, range.end as int);
        let positions = Seq::new(projected.len(), |p: int| projected[p].form);
        let descendant = children[target]._signature@.call.call.form as int;
        let port = crate::syntax::circuit::call_argument_containing_list(source.text, forms, typed.call.call,
            positions, row.expression.end as int, descendant);
        self.prepared_nor_argument_evidence(plan, caller, prepared, index, root.output_slot, parent_index, port);
        let argument = projected[port];
        assert(argument == args[range.start + port]);
        assert(argument.source is NestedCall);
        let next = choose|i: int| 0 <= i < parent_index
            && (#[trigger] children[i]).reference == row.references.start + argument.source->NestedCall_0
            && children[i]._signature@.call.call.form == argument.form
            && children[i]._signature@.call.target.port_counts().outputs == 1
            && (children[i]._signature@.signature matches crate::project::FuncCallSignature::Function(ports)
                ==> ports.outputs@.len() == 1);
        if argument.form == descendant {
            self.prepared_nor_children_at_same_form(plan, caller, prepared, index, next, target);
            (parent_index, port)
        } else {
            self.prepared_nor_child_input(plan, caller, prepared, index, next, target)
        }
    }

    /// 根 NOR の後順列にある各子は、いずれかの親の実引数として評価できる単一出力の呼び出しである。
    #[verifier::spinoff_prover]
    pub(super) proof fn prepared_nor_child_single_output(
        &self, plan: FunctionExpansionOrder, caller: (usize, usize, u64), prepared: &PreparedExpansionBody,
        index: int, target: int,
    )
        requires
            self.can_resolve(),
            self.prepared_expansion_body_matches(plan, caller.0, caller.1, caller.2, prepared),
            0 <= index < prepared.nor_roots@.len(),
            ({
                let root = prepared.nor_roots@[index];
                &&& 0 <= target < root.postorder@.len()
                &&& nor_definition_determined(&root, prepared.projections.call_arguments.arguments@)
            }),
        ensures ({
            let child = prepared.nor_roots@[index].postorder@[target];
            &&& child._signature@.call.target.port_counts().outputs == 1
            &&& child._signature@.signature matches crate::project::FuncCallSignature::Function(ports) ==>
                ports.outputs@.len() == 1
        }),
    {
        reveal(UseAliases::prepared_nor_root_matches);
        reveal(UseAliases::prepared_expression_children_match);
        reveal(UseAliases::prepared_expression_call_matches);
        let (file, entry, limit) = caller;
        let root = prepared.nor_roots@[index];
        let children = root.postorder@;
        let child = children[target];
        let project = self.targets.project_model();
        let source = &project.sources_model()[file as int];
        let parsed = &project.circuits_model()[file as int];
        let forms = parsed.syntax.forms@;
        let row = parsed.definitions@[root.definition as int];
        let local = (root.definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
        let reference = (child.reference - row.references.start) as usize;
        let last = children.len() as int;
        let order = Seq::new(children.len(), |i: int| children[i].reference).push(row.references.start);
        self.targets.parsed_project_model();
        self.typed_call_arguments_ready(file, entry, local, 0, limit, root.root._signature@);
        self.resolved_call_reference_form(file, entry, local, 0, root.root._signature@.call);
        self.typed_call_arguments_ready(file, entry, local, reference, limit, child._signature@);
        self.resolved_call_reference_form(file, entry, local, reference, child._signature@.call);
        parsed_index_evidence(*source, *parsed);
        build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, root.definition as int);
        vstd::std_specs::vec::axiom_spec_len(&parsed.syntax.forms);
        call_postorder_reference(forms, parsed.references@, row.references, order, target);
        call_postorder_reference(forms, parsed.references@, row.references, order, last);
        call_postorder_references_distinct(forms, parsed.references@, row.references, order, target, last);
        let (parent_position, child_position) = call_postorder_positions(source.text, forms, parsed.references@,
            row, order, row.references.start, child.reference);
        if parent_position < last {
            call_postorder_references_distinct(forms, parsed.references@, row.references, order, parent_position, last);
        }
        if child_position < target {
            call_postorder_references_distinct(forms, parsed.references@, row.references, order, child_position, target);
        } else if target < child_position {
            call_postorder_references_distinct(forms, parsed.references@, row.references, order, target, child_position);
        }
        assert(parent_position == last && child_position == target);
        crate::syntax::circuit::call_form_bounds(forms, root.root._signature@.call.call);
        reveal(crate::syntax::complete_list_indices);
        self.prepared_nor_child_input(plan, caller, prepared, index, last, target);
    }

    /// ソース順のカーソルを進め、次の根 NOR に対応する出力スロットを得る。
    fn next_nor_output(
        drivers: &[super::super::function_drivers::DefinitionDriver], start: usize, definition: usize,
        Ghost(expected): Ghost<int>,
    ) -> (output: usize)
        requires
            start <= expected < drivers@.len(),
            drivers@[expected].definition == definition,
            forall|i: int| 0 <= i < expected ==> (#[trigger] drivers@[i]).definition < definition,
        ensures output == expected,
    {
        let mut cursor = start;
        while drivers[cursor].definition < definition
            invariant
                start <= cursor <= expected < drivers@.len(),
                drivers@[expected].definition == definition,
                forall|i: int| 0 <= i < expected ==> (#[trigger] drivers@[i]).definition < definition,
            decreases expected - cursor,
        {
            assert(cursor < expected);
            cursor += 1;
        }
        cursor
    }

    proof fn nor_output_type_and_uniqueness(
        &self, caller: (usize, usize, u64), typed: FuncSignalTypes, wiring: FuncWiring,
        definition: usize, output: usize, builtin: TypedFuncCall,
    )
        requires
            self.can_resolve(),
            self.func_signal_types_evidence(caller.0, caller.1, caller.2, Ok(typed)),
            typed.literals.wiring == FuncWiringResult::Checked(wiring),
            typed.types@.len() == wiring.drivers.definitions@.len(),
            output < wiring.drivers.definitions@.len(),
            wiring.drivers.definitions@[output as int].definition == definition,
            builtin.call.target is Nor,
            ({
                let parsed = &self.targets.project_model().circuits_model()[caller.0 as int];
                let local = (definition - parsed.entry_ranges@[caller.1 as int].definitions.start) as usize;
                &&& builtin.call.call.form == parsed.definitions@[definition as int].expression.start
                &&& self.func_call_signature_evidence(caller.0, caller.1, local, 0, caller.2, Ok(Some(builtin)))
            }),
        ensures
            typed.types@[output as int] matches Some(ty) && ty.ty == crate::project::ResolvedPortType::Bits(1),
            wiring.drivers.definitions@[output as int].result_index == 0,
            forall|i: int| 0 <= i < wiring.drivers.definitions@.len()
                && (#[trigger] wiring.drivers.definitions@[i]).definition == definition ==> i == output,
    {
        self.checked_types_keep_wiring(caller.0, caller.1, caller.2, typed, wiring);
        self.checked_wiring_is_func(caller.0, caller.1, caller.2, wiring);
        self.checked_nor_type(caller.0, caller.1, caller.2, typed, wiring, output as int, builtin);
        assert forall|i: int| 0 <= i < wiring.drivers.definitions@.len()
            && (#[trigger] wiring.drivers.definitions@[i]).definition == definition implies i == output by {
            if i != output {
                self.checked_nor_type(caller.0, caller.1, caller.2, typed, wiring, i, builtin);
                if i < output {
                    assert(wiring.drivers.definitions@[i].result_index < wiring.drivers.definitions@[output as int].result_index);
                } else {
                    assert(wiring.drivers.definitions@[output as int].result_index < wiring.drivers.definitions@[i].result_index);
                }
            }
        };
    }

    fn prepare_nested_nor_roots(
        &self, plan: &FunctionExpansionOrder<'p, 'a>, file: usize, entry: usize, _limit: u64,
        _typed: &FuncSignalTypes<'p, 'a>, _wiring: &FuncWiring<'p, 'a>, projections: &FuncProjections<'p, 'a>,
        Ghost(rank): Ghost<int>,
    ) -> (roots: Vec<PreparedNorRoot<'p, 'a>>)
        requires
            self.can_resolve(), self.function_template_plan(*plan),
            0 <= rank < plan.order_model().len(), plan.position_model(rank) == Some((file, entry)),
            self.func_signal_types_evidence(file, entry, _limit, Ok(*_typed)),
            _typed.literals.wiring == FuncWiringResult::Checked(*_wiring),
            _typed.types@.len() == _wiring.drivers.definitions@.len(),
            self.func_wiring_evidence(file, entry, _limit, Ok(FuncWiringResult::Checked(*_wiring))),
            self.projected_references_match((file, entry, _limit), _typed.types@, _wiring,
                &projections.call_arguments, projections.calls@),
        ensures
            roots@.len() == projections.call_arguments.nested_nor_roots@.len(),
            forall|i: int, j: int| 0 <= i < j < roots@.len() ==>
                (#[trigger] roots@[i]).output_slot < (#[trigger] roots@[j]).output_slot,
            forall|i: int| 0 <= i < roots@.len() ==> self.prepared_nor_root_matches(*plan, (file, entry, _limit),
                _typed.types@, _wiring, &projections.call_arguments, projections.call_arguments.nested_nor_roots@[i],
                #[trigger] roots@[i]),
    {
        let ghost caller = (file, entry, _limit);
        proof { self.checked_wiring_is_func(file, entry, _limit, *_wiring); }
        let project = self.targets.project();
        let parsed = &project.circuits()[file];
        let source = &project.sources()[file];
        proof {
            parsed_index_evidence(*source, *parsed);
            build_entry_ranges_evidence(source.text, &parsed.build_model(), entry as int);
        }
        let first = parsed.entry_ranges[entry].definitions.start;
        let indices = &projections.call_arguments.nested_nor_roots;
        let mut roots: Vec<PreparedNorRoot<'p, 'a>> = Vec::new();
        let mut index = 0;
        let mut cursor = 0;
        let drivers = _wiring.drivers.definitions.as_slice();
        while index < indices.len()
            invariant
                self.can_resolve(), self.function_template_plan(*plan),
                self.func_signal_types_evidence(file, entry, _limit, Ok(*_typed)),
                _typed.literals.wiring == FuncWiringResult::Checked(*_wiring),
                _typed.types@.len() == _wiring.drivers.definitions@.len() == drivers@.len(),
                drivers@ == _wiring.drivers.definitions@,
                index == 0 ==> cursor == 0,
                index > 0 ==> cursor == roots@[index - 1].output_slot + 1,
                self.func_wiring_evidence(file, entry, _limit, Ok(FuncWiringResult::Checked(*_wiring))),
                caller == (file, entry, _limit),
                0 <= rank < plan.order_model().len(), plan.position_model(rank) == Some((file, entry)),
                file < self.targets.project_model().circuits_model().len(),
                file < self.targets.project_model().sources_model().len(),
                *parsed == self.targets.project_model().circuits_model()[file as int],
                *source == self.targets.project_model().sources_model()[file as int],
                crate::syntax::circuit::build_index_matches(source.text, parsed.build_model()),
                parsed_circuit_matches(*source, *parsed), entry < parsed.syntax.entries@.len(),
                entry < parsed.entry_ranges@.len(), first == parsed.entry_ranges@[entry as int].definitions.start,
                indices@ == projections.call_arguments.nested_nor_roots@,
                self.projected_references_match(caller, _typed.types@, _wiring, &projections.call_arguments, projections.calls@),
                roots@.len() == index <= indices@.len(),
                forall|i: int| 0 <= i < roots@.len() ==> (#[trigger] roots@[i]).output_slot < cursor,
                forall|i: int, j: int| 0 <= i < j < roots@.len() ==>
                    (#[trigger] roots@[i]).output_slot < (#[trigger] roots@[j]).output_slot,
                forall|i: int| 0 <= i < roots@.len() ==> self.prepared_nor_root_matches(*plan, caller, _typed.types@,
                    _wiring, &projections.call_arguments, indices@[i], #[trigger] roots@[i]),
            decreases indices@.len() - index,
        {
            let absolute = indices[index];
            let ghost arguments = self.retained_nested_nor_root(caller, _typed.types@, _wiring,
                &projections.call_arguments, projections.calls@, index as int);
            proof {
                build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, absolute as int);
            }
            let row = &parsed.definitions[absolute];
            if !definition_root_is_call(source.text, parsed.syntax.forms.as_slice(), row, parsed.references.as_slice()) {
                proof { assert(false); }
                unreachable!();
            }
            let _targets = definition_target_atoms(parsed.syntax.forms.as_slice(), row);
            let ghost output_slot = self.checked_wiring_first_definition_driver(file, entry, _limit, *_wiring, absolute);
            proof {
                self.checked_wiring_is_func(file, entry, _limit, *_wiring);
                assert forall|i: int| 0 <= i < output_slot implies (#[trigger] drivers@[i]).definition < absolute by {
                    assert(drivers@[i] == _wiring.drivers.definitions@[i]);
                };
                if index > 0 {
                    reveal(UseAliases::prepared_nor_root_matches);
                    let prior = roots@[index - 1];
                    assert(prior.definition < absolute);
                    assert(drivers@[prior.output_slot as int].definition == prior.definition);
                    if output_slot < prior.output_slot {
                        assert(drivers@[output_slot].definition <= drivers@[prior.output_slot as int].definition);
                    }
                    assert(cursor <= output_slot);
                }
            }
            let output = Self::next_nor_output(drivers, cursor, absolute, Ghost(output_slot));
            let definition = absolute - first;
            let (root, postorder) = self.prepare_root_expression(plan, file, entry, definition, projections,
                Ghost((_limit, _typed.types@, _wiring, rank)));
            let ghost projected = projections.call_arguments.arguments@.subrange(arguments.start as int, arguments.end as int);
            let ghost port = if projected[0].source is NestedCall { 0int } else { 1int };
            proof {
                reveal(UseAliases::prepared_expression_call_matches);
                self.retained_target_agrees_with_call(file, entry, definition, 0, _limit, Some(RetainedCallTarget::Nor),
                    root._signature@);
                self.typed_call_arguments_ready(file, entry, definition, 0, _limit, root._signature@);
                assert(root.arguments == arguments);
                assert(projected[port] == projections.call_arguments.arguments@[arguments.start + port]);
                self.checked_projected_argument((file, entry, definition, 0), _limit, _typed.types@, _wiring,
                    root._signature@, projected, port);
                let child_form = projected[port].form;
                let reference = projected[port].source->NestedCall_0;
                crate::syntax::circuit::direct_call_argument_bounds(parsed.syntax.forms@,
                    root._signature@.call.call, child_form as int);
                assert(self.func_call_form_reference(file, entry, definition, child_form, reference));
                assert(reference > 0);
                assert(row.references.start + 1 < row.references.end);
            }
            let Some(postorder) = postorder else {
                proof { assert(false); }
                unreachable!();
            };
            proof {
                self.prepared_nested_argument(*plan, caller, definition, &projections.call_arguments, _typed.types@,
                    _wiring, rank, postorder@, postorder@.len() as int, 0, root._signature@, projected, port);
                assert(postorder@.len() > 0);
            }
            proof { self.nor_output_type_and_uniqueness(caller, *_typed, *_wiring, absolute, output, root._signature@); }
            let prepared = PreparedNorRoot { definition: absolute, output_slot: output, root, postorder, _caller_rank: Ghost(rank) };
            assert(self.prepared_nor_root_matches(*plan, caller, _typed.types@, _wiring, &projections.call_arguments,
                absolute, prepared)) by { reveal(UseAliases::prepared_nor_root_matches); };
            let ghost before = roots@;
            roots.push(prepared);
            assert forall|i: int| 0 <= i < roots@.len() implies self.prepared_nor_root_matches(*plan, caller, _typed.types@,
                _wiring, &projections.call_arguments, indices@[i], #[trigger] roots@[i]) by {
                if i < index { assert(roots@[i] == before[i]); }
            };
            proof {
                assert forall|i: int| 0 <= i < roots@.len() implies (#[trigger] roots@[i]).output_slot <= output by {
                    if i < index { assert(roots@[i] == before[i]); }
                };
                assert forall|i: int, j: int| 0 <= i < j < roots@.len() implies
                    (#[trigger] roots@[i]).output_slot < (#[trigger] roots@[j]).output_slot by {
                    assert(roots@[i] == before[i]);
                    if j < index { assert(roots@[j] == before[j]); }
                };
            }
            proof {
                vstd::std_specs::vec::axiom_spec_len(&_wiring.drivers.definitions);
                assert(output < drivers@.len() <= usize::MAX);
            }
            cursor = output + 1;
            index += 1;
        }
        roots
    }

    /// 通常関数の出力区間と、根 NOR の一ビット出力が重ならないことを表す。
    #[verifier::opaque]
    pub(super) open spec fn nor_call_slots_disjoint(calls: Seq<CheckedExpansionCall>, roots: Seq<PreparedNorRoot>) -> bool {
        forall|i: int, j: int| 0 <= i < calls.len() && 0 <= j < roots.len() ==>
            !((#[trigger] calls[i]).outputs.start <= (#[trigger] roots[j]).output_slot < calls[i].outputs.end)
    }

    /// 通常呼び出しは一つ以上の左辺を持ち、先行する呼び出しの左辺と重ならない。
    pub(super) proof fn prepared_expansion_ordered_call_ranges(
        &self, plan: FunctionExpansionOrder, caller: (usize, usize, u64), prepared: &PreparedExpansionBody,
    )
        requires self.prepared_expansion_body_matches(plan, caller.0, caller.1, caller.2, prepared),
        ensures
            forall|i: int| 0 <= i < prepared.calls@.len() ==> {
                let call = #[trigger] prepared.calls@[i];
                call.outputs.start < call.outputs.end <= prepared.typed.types@.len()
            },
            forall|i: int, j: int| 0 <= i < j < prepared.calls@.len() ==>
                (#[trigger] prepared.calls@[i]).outputs.end <= (#[trigger] prepared.calls@[j]).outputs.start,
    {
        assert forall|i: int| 0 <= i < prepared.calls@.len() implies {
            let call = #[trigger] prepared.calls@[i];
            call.outputs.start < call.outputs.end <= prepared.typed.types@.len()
        } by {
            reveal(UseAliases::checked_expansion_call_matches);
        };
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
        &&& self.projected_references_match((file, entry, limit), body.typed.types@, &wiring,
            &body.projections.call_arguments, body.projections.calls@)
        &&& Self::nor_call_slots_disjoint(body.calls@, body.nor_roots@)
        &&& body.nor_roots@.len() == body.projections.call_arguments.nested_nor_roots@.len()
        &&& forall|i: int, j: int| 0 <= i < j < body.nor_roots@.len() ==>
            (#[trigger] body.nor_roots@[i]).output_slot < (#[trigger] body.nor_roots@[j]).output_slot
        &&& forall|i: int| 0 <= i < body.nor_roots@.len() ==> self.prepared_nor_root_matches(plan, (file, entry, limit),
            body.typed.types@, &wiring, &body.projections.call_arguments,
            body.projections.call_arguments.nested_nor_roots@[i], #[trigger] body.nor_roots@[i])
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

    /// 構文と型を検査し、通常呼び出しと入れ子の引数を持つ根 NOR を展開用に保持する。
    pub(super) fn prepare_expansion_body(
        &self, plan: &FunctionExpansionOrder<'p, 'a>, file: usize, entry: usize, limit: u64,
    ) -> (result: Result<PreparedExpansionBody<'p, 'a>, BitFuncError<'p, 'a>>)
        requires
            self.can_resolve(), self.function_template_plan(*plan),
            exists|rank: int| 0 <= rank < plan.order_model().len()
                && #[trigger] plan.position_model(rank) == Some((file, entry)),
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
        let ghost rank = choose|rank: int| 0 <= rank < plan.order_model().len()
            && #[trigger] plan.position_model(rank) == Some((file, entry));
        let calls = self.check_expansion_call_groups(plan, file, entry, limit, &typed, wiring, &projections, Ghost(rank));
        proof { self.checked_types_keep_wiring(file, entry, limit, typed, *wiring); }
        let nor_roots = self.prepare_nested_nor_roots(plan, file, entry, limit, &typed, wiring, &projections, Ghost(rank));
        assert(Self::nor_call_slots_disjoint(calls@, nor_roots@)) by {
            reveal(UseAliases::nor_call_slots_disjoint);
            assert forall|i: int, j: int| 0 <= i < calls@.len() && 0 <= j < nor_roots@.len() implies
                !((#[trigger] calls@[i]).outputs.start <= (#[trigger] nor_roots@[j]).output_slot < calls@[i].outputs.end) by {
                let call = calls@[i];
                let nor = nor_roots@[j];
                let root = projections.calls@[i];
                if call.outputs.start <= nor.output_slot < call.outputs.end {
                    self.expansion_call_output_types(*plan, (file, entry, limit), typed, wiring, root,
                        projections.call_arguments.ranges@[i], &projections.call_arguments, call);
                    reveal(UseAliases::prepared_nor_root_matches);
                    reveal(UseAliases::prepared_expression_call_matches);
                    reveal(UseAliases::checked_expansion_call_matches);
                    assert(nor.definition == root.definition);
                    let parsed = &self.targets.project_model().circuits_model()[file as int];
                    let definition = (root.definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
                    self.successful_call_signatures_agree(file, entry, definition, 0, limit,
                        call._signature@, nor.root._signature@);
                }
            };
        };
        Ok(PreparedExpansionBody { typed, projections, calls, nor_roots })
    }
}

#[cfg(all(test, not(verus_only)))]
#[test]
fn prepares_a_nor_root_without_a_function_vertex() {
    use crate::project::{SourceSnapshot, check_use_aliases, index_use_targets, parse_circuit_project};

    let text = "(using nor) (func id (in a) (out a))
                (func caller (in a) (out y) (def y (nor (id a) a)))
                (func only-nor (in a) (out y) (def y (nor (nor a a) a)))
                (func both (in a b) (out a b))
                (func multiple (in a b) (out y)
                    (def (p q) (both a b))
                    (def x (nor (nor p q) a))
                    (def y (nor (id x) q)))";
    let project = parse_circuit_project(&[SourceSnapshot {
        path: "root-nor.ncg2", revision: 1, text,
    }]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let plan = aliases.prepare_function_expansion().unwrap();
    let prepared = aliases.prepare_expansion_body(&plan, 0, 2, 1).unwrap();
    let [group] = prepared.nor_roots.as_slice() else {
        panic!("expected one NOR root");
    };
    assert_eq!(group.definition, project.circuits()[0].entry_ranges[2].definitions.start);
    let root = &group.root;
    let children = &group.postorder;
    assert_eq!(&text[root.expression.span.clone()], "(nor (id a) a)");
    assert!(root.vertex.is_none());
    assert_eq!(root.arguments, 0..2);
    let [child] = children.as_slice() else {
        panic!("expected one child call");
    };
    assert_eq!(&text[child.expression.span.clone()], "(id a)");
    assert_eq!(child.vertex, plan.template_vertex((0, 1)));
    assert_eq!(child.arguments, 2..3);
    let only_nor = aliases.prepare_expansion_body(&plan, 0, 3, 1).unwrap();
    let [group] = only_nor.nor_roots.as_slice() else {
        panic!("expected one NOR root without function dependencies");
    };
    assert!(group.root.vertex.is_none());
    let [child] = group.postorder.as_slice() else {
        panic!("expected one NOR child");
    };
    assert_eq!(&text[child.expression.span.clone()], "(nor a a)");
    assert!(child.vertex.is_none());

    let multiple = aliases.prepare_expansion_body(&plan, 0, 5, 1).unwrap();
    let [first, second] = multiple.nor_roots.as_slice() else {
        panic!("expected two NOR roots");
    };
    let base = project.circuits()[0].entry_ranges[5].definitions.start;
    assert_eq!((first.definition, first.output_slot), (base + 1, 2));
    assert_eq!((second.definition, second.output_slot), (base + 2, 3));
    let calls = multiple.calls.as_slice();
    let roots = multiple.nor_roots.as_slice();
    assert!(matches!(expansion_call_at_slot(Some(calls[0].outputs.start), Some(roots[0].output_slot), 0),
        ExpansionSlot::Function));
    assert_eq!(calls[0].outputs, 0..2);
    assert!(matches!(expansion_call_at_slot(None, Some(roots[0].output_slot), 2), ExpansionSlot::Nor));
    assert!(matches!(expansion_call_at_slot(None, Some(roots[1].output_slot), 3), ExpansionSlot::Nor));
    assert!(matches!(expansion_call_at_slot(None, None, 4), ExpansionSlot::Local));
}

} // verus!
