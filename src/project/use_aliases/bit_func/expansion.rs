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

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
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
            crate::syntax::circuit::call_argument_positions(forms, group._signature@.call.call,
                Seq::new(projected.len(), |i: int| projected[i].form))
        }),
    {
        reveal(UseAliases::checked_expansion_call_matches);
        let (file, entry, limit) = caller;
        let parsed = &self.targets.project_model().circuits_model()[file as int];
        let local = (root.definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
        let projected = arguments.arguments@.subrange(range.start as int, range.end as int);
        self.projected_arguments_in_source_order((file, entry, local, 0), limit, typed.types@, wiring, group._signature@, projected);
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
            &&& form is Atom || argument.source is Deferred
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
                    CallArgumentSource::Deferred => false,
                }
            }),
        ensures ({
            let project = self.targets.project_model();
            source_call_argument_value(&project.sources_model()[caller.0 as int], &project.circuits_model()[caller.0 as int],
                wiring, caller.1, root.definition, arguments.arguments@[range.start + port].form, caller.2,
                inputs, prior, width, value)
        }),
    {
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
