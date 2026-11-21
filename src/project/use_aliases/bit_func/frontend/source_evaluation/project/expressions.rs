//! 厳格構文木にある呼び出し式の引数と、単一の出力値を対応付ける。

use super::*;
use crate::project::{FuncCallSignature, FuncCallTarget, ResolvedPortType, port_types_equal};
use crate::project::use_aliases::bit_func::expansion::{
    source_call_argument_value, source_call_argument_values_agree, source_call_arguments_match,
};
use crate::syntax::circuit::{
    build_definition_scope_evidence, call_argument_position_bounds, call_argument_positions,
    call_argument_positions_agree, definition_reference_form_unique,
};

verus! {

/// 一つの定義の右辺を評価するときに読めるソース上の値と、先行する関数の評価。
struct SourceExpressionScope<'s, 'w, 'p, 'a> {
    context: &'s SourceFunc<'w, 'p, 'a>,
    definition: usize,
    plan: &'s FunctionExpansionOrder<'p, 'a>,
    rank: int,
    derivation: ISet<SourceInvocation>,
    typed: FuncSignalTypes<'p, 'a>,
    layouts: Option<&'s StructureLayouts<'p, 'a>>,
    inputs: Seq<Seq<bool>>,
    prior: Seq<Seq<bool>>,
}

/// 一つの入れ子呼び出しが使う相対参照と、宣言順の引数値および単一の出力値。
struct SourceExpressionCall<'p, 'a> {
    reference: usize,
    signature: TypedFuncCall<'p, 'a>,
    callee_rank: Option<int>,
    widths: Seq<u64>,
    arguments: Seq<Seq<bool>>,
    result: Seq<bool>,
}

spec fn source_expression_output_type<'p, 'a>(call: TypedFuncCall<'p, 'a>) -> Option<ResolvedPortType<'p, 'a>> {
    match call.signature {
        FuncCallSignature::Nor => Some(ResolvedPortType::Bits(1)),
        FuncCallSignature::Function(ports) => if ports.outputs@.len() == 1 {
            Some(ports.outputs@[0].ty)
        } else { None },
    }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn source_expression_scope_matches(&self, scope: &SourceExpressionScope) -> bool {
        let source = scope.context;
        let project = self.targets.project_model();
        &&& self.can_resolve()
        &&& self.function_expansion_evidence(Ok(*scope.plan))
        &&& 0 <= scope.rank < scope.plan.order_model().len()
        &&& scope.plan.position_model(scope.rank) == Some((source.file, source.entry))
        &&& source.file < project.sources_model().len() && source.file < project.circuits_model().len()
        &&& *source.source == project.sources_model()[source.file as int]
        &&& *source.parsed == project.circuits_model()[source.file as int]
        &&& source.entry < source.parsed.entry_ranges@.len()
        &&& source.parsed.entry_ranges@[source.entry as int].definitions.start <= scope.definition
            < source.parsed.entry_ranges@[source.entry as int].definitions.end <= source.parsed.definitions@.len()
        &&& self.func_wiring_evidence(source.file, source.entry, source.limit, Ok(FuncWiringResult::Checked(*source.wiring)))
        &&& self.func_signal_types_evidence(source.file, source.entry, source.limit, Ok(scope.typed))
        &&& scope.typed.literals.wiring == FuncWiringResult::Checked(*source.wiring)
        &&& scope.prior.len() <= source.wiring.drivers.definitions@.len()
        &&& forall|i: int| 0 <= i < source.wiring.drivers.definitions@.len() ==>
            (i < scope.prior.len()) == ((#[trigger] source.wiring.drivers.definitions@[i]).definition < scope.definition)
        &&& self.structure_layout_for_ports(source.limit, scope.layouts)
    }

    spec fn source_expression_atom_type(
        &self, scope: &SourceExpressionScope, form: usize, expected: ResolvedPortType,
    ) -> bool {
        let context = scope.context;
        let frame = context.parsed.entry_ranges@[context.entry as int];
        let row = context.parsed.definitions@[scope.definition as int];
        let forms = context.parsed.syntax.forms@;
        &&& form < forms.len() && forms[form as int] is Atom
        &&& if forms[form as int]->Atom_kind is Name {
            exists|i: int| row.signals.start <= i < row.signals.end <= context.parsed.signals@.len()
                && (#[trigger] context.parsed.signals@[i]) == form
                && 0 <= i - frame.signals.start < context.wiring.signals@.len()
                && (signal_type_at(context.wiring, scope.typed.types@,
                    context.wiring.signals@[i - frame.signals.start].driver) matches Some(known)
                    && port_types_equal(known.ty, expected))
        } else { expected is Bits }
    }

    spec fn source_expression_argument_matches(
        &self, scope: &SourceExpressionScope, call: TypedFuncCall, port: int, form: usize,
        width: u64, value: Seq<bool>, children: Map<usize, SourceExpressionCall>,
    ) -> bool {
        let context = scope.context;
        let forms = context.parsed.syntax.forms@;
        let expected = match call.signature {
            FuncCallSignature::Nor => ResolvedPortType::Bits(1),
            FuncCallSignature::Function(ports) => ports.inputs@[port].ty,
        };
        &&& call.call.call.form < form < forms.len()
        &&& value.len() == width
        &&& match forms[form as int] {
            Form::Atom { .. } => {
                &&& self.source_expression_atom_type(scope, form, expected)
                &&& source_call_argument_value(context.source, context.parsed, context.wiring, context.entry,
                    scope.definition, form, context.limit, scope.inputs, scope.prior, width, value)
            },
            Form::List { .. } => {
                &&& children.contains_key(form)
                &&& source_expression_output_type(children[form].signature) matches Some(output)
                    && port_types_equal(output, expected)
                &&& value == children[form].result
            },
        }
    }

    /// 実引数を元の出現順に評価する。リストの引数は同じフォームに対応する子の出力を読む。
    spec fn source_expression_arguments_match(
        &self, scope: &SourceExpressionScope, call: TypedFuncCall,
        widths: Seq<u64>, values: Seq<Seq<bool>>, children: Map<usize, SourceExpressionCall>,
    ) -> bool {
        let context = scope.context;
        let forms = context.parsed.syntax.forms@;
        &&& match call.signature {
            FuncCallSignature::Nor => widths == seq![1u64, 1u64],
            FuncCallSignature::Function(ports) => self.port_widths_match(ports.inputs@, widths, scope.layouts),
        }
        &&& exists|positions: Seq<usize>| #[trigger] call_argument_positions(forms, call.call.call, positions)
            && positions.len() == widths.len() == values.len()
            && forall|port: int| 0 <= port < positions.len() ==>
                self.source_expression_argument_matches(scope, call, port, #[trigger] positions[port],
                    widths[port], values[port], children)
    }

    proof fn source_expression_argument_positions(
        &self, scope: &SourceExpressionScope, call: TypedFuncCall, widths: Seq<u64>,
        values: Seq<Seq<bool>>, children: Map<usize, SourceExpressionCall>,
    ) -> (positions: Seq<usize>)
        requires self.source_expression_arguments_match(scope, call, widths, values, children),
        ensures
            call_argument_positions(scope.context.parsed.syntax.forms@, call.call.call, positions),
            positions.len() == widths.len() == values.len(),
            forall|port: int| 0 <= port < positions.len() ==>
                self.source_expression_argument_matches(scope, call, port, #[trigger] positions[port],
                    widths[port], values[port], children),
    {
        choose|positions: Seq<usize>| #[trigger] call_argument_positions(scope.context.parsed.syntax.forms@, call.call.call, positions)
            && positions.len() == widths.len() == values.len()
            && forall|port: int| 0 <= port < positions.len() ==>
                self.source_expression_argument_matches(scope, call, port, #[trigger] positions[port],
                    widths[port], values[port], children)
    }

    /// 子の出力は、依存先の参照評価または基底 NOR の真理値から定まる。
    spec fn source_expression_call_evaluates(
        &self, scope: &SourceExpressionScope, form: usize, child: SourceExpressionCall,
        children: Map<usize, SourceExpressionCall>,
    ) -> bool {
        let context = scope.context;
        let entry = context.parsed.entry_ranges@[context.entry as int];
        let definition = (scope.definition - entry.definitions.start) as usize;
        let signature = child.signature;
        &&& signature.call.call.form == form
        &&& self.func_call_form_reference(context.file, context.entry, definition, form, child.reference)
        &&& self.func_call_signature_evidence(context.file, context.entry, definition, child.reference,
            context.limit, Ok(Some(signature)))
        &&& source_expression_output_type(signature) matches Some(output)
            && 0 < child.result.len() <= u64::MAX
            && self.port_width_matches(output, child.result.len() as u64, scope.layouts)
        &&& self.source_expression_arguments_match(scope, signature, child.widths, child.arguments, children)
        &&& match (signature.call.target, signature.signature, child.callee_rank) {
            (FuncCallTarget::Nor, FuncCallSignature::Nor, None) =>
                child.arguments.len() == 2 && child.arguments[0].len() == 1 && child.arguments[1].len() == 1
                && child.result == seq![!(child.arguments[0][0] || child.arguments[1][0])],
            (FuncCallTarget::Function { file, entry, .. }, FuncCallSignature::Function(_), Some(rank)) =>
                0 <= rank < scope.rank && scope.plan.position_model(rank) == Some((file, entry))
                && scope.derivation.contains(SourceInvocation {
                    rank, inputs: child.arguments, outputs: seq![child.result],
                }),
            _ => false,
        }
    }

    /// 元の右辺の根から引数をたどり、各リストの呼び出しをソースの規則で評価する。
    ///
    /// 引数のフォーム添字は呼び出しの添字より大きいため、値を得るために同じ呼び出しへ戻ることはない。
    spec fn source_nested_arguments_match(
        &self, scope: &SourceExpressionScope, root: TypedFuncCall, widths: Seq<u64>,
        values: Seq<Seq<bool>>, children: Map<usize, SourceExpressionCall>,
    ) -> bool {
        let context = scope.context;
        let row = context.parsed.definitions@[scope.definition as int];
        let frame = context.parsed.entry_ranges@[context.entry as int].definitions;
        &&& self.source_expression_scope_matches(scope)
        &&& root.call.call.form == row.expression.start
        &&& self.func_call_signature_evidence(context.file, context.entry, (scope.definition - frame.start) as usize,
            0, context.limit, Ok(Some(root)))
        &&& self.source_expression_arguments_match(scope, root, widths, values, children)
        &&& forall|form: usize| #[trigger] children.contains_key(form) ==>
            root.call.call.form < form < row.expression.end
            && self.source_expression_call_evaluates(scope, form, children[form], children)
    }

    /// 型検査済みの原子だけを渡す場合、従来の引数評価を子が空の評価として使える。
    proof fn source_flat_arguments_match_nested(
        &self, scope: &SourceExpressionScope, root: TypedFuncCall, widths: Seq<u64>, values: Seq<Seq<bool>>,
    )
        requires
            self.source_expression_scope_matches(scope),
            self.func_call_signature_evidence(scope.context.file, scope.context.entry,
                (scope.definition - scope.context.parsed.entry_ranges@[scope.context.entry as int].definitions.start) as usize,
                0, scope.context.limit, Ok(Some(root))),
            match root.signature {
                FuncCallSignature::Nor => widths == seq![1u64, 1u64],
                FuncCallSignature::Function(ports) => self.port_widths_match(ports.inputs@, widths, scope.layouts),
            },
            source_call_arguments_match(scope.context.source, scope.context.parsed, scope.context.wiring,
                scope.context.entry, scope.definition, root.call.call, scope.context.limit, scope.inputs, scope.prior,
                widths, values),
            forall|positions: Seq<usize>, port: int| #[trigger] call_argument_positions(
                scope.context.parsed.syntax.forms@, root.call.call, positions) && 0 <= port < positions.len() ==>
                self.source_expression_atom_type(scope, #[trigger] positions[port], match root.signature {
                    FuncCallSignature::Nor => ResolvedPortType::Bits(1),
                    FuncCallSignature::Function(ports) => ports.inputs@[port].ty,
                }),
        ensures self.source_nested_arguments_match(scope, root, widths, values, Map::empty()),
    {
        let context = scope.context;
        let forms = context.parsed.syntax.forms@;
        let call = root.call.call;
        let positions = choose|positions: Seq<usize>| #[trigger] call_argument_positions(forms, call, positions)
            && positions.len() == values.len() == widths.len()
            && forall|port: int| 0 <= port < positions.len() ==>
                source_call_argument_value(context.source, context.parsed, context.wiring, context.entry,
                    scope.definition, #[trigger] positions[port], context.limit, scope.inputs, scope.prior,
                    widths[port], values[port]);
        reveal(source_call_argument_value);
        assert forall|port: int| 0 <= port < positions.len() implies
            self.source_expression_argument_matches(scope, root, port, #[trigger] positions[port],
                widths[port], values[port], Map::empty()) by {
            call_argument_position_bounds(forms, call, positions, port);
        };
    }

    /// 同じソースの引数値は、依存順位の小さい関数の評価が一意なら、子の評価表の選び方によらない。
    proof fn source_expression_arguments_agree(
        &self, left: &SourceExpressionScope, right: &SourceExpressionScope,
        a: (TypedFuncCall, Seq<Seq<bool>>, Map<usize, SourceExpressionCall>),
        b: (TypedFuncCall, Seq<Seq<bool>>, Map<usize, SourceExpressionCall>),
        widths: Seq<u64>,
    )
        requires
            self.source_expression_scope_matches(left), self.source_expression_scope_matches(right),
            same_source_bindings(left.context, right.context),
            left.plan == right.plan && left.rank == right.rank && left.definition == right.definition,
            left.inputs == right.inputs && left.prior == right.prior,
            a.0.call.call == b.0.call.call,
            self.source_expression_arguments_match(left, a.0, widths, a.1, a.2),
            self.source_expression_arguments_match(right, b.0, widths, b.1, b.2),
            forall|form: usize| #[trigger] a.2.contains_key(form) ==>
                self.source_expression_call_evaluates(left, form, a.2[form], a.2),
            forall|form: usize| #[trigger] b.2.contains_key(form) ==>
                self.source_expression_call_evaluates(right, form, b.2[form], b.2),
            forall|x: SourceInvocation, y: SourceInvocation|
                #[trigger] left.derivation.contains(x) && #[trigger] right.derivation.contains(y)
                && 0 <= x.rank == y.rank < left.rank && x.inputs == y.inputs ==> x.outputs == y.outputs,
        ensures a.1 == b.1,
        decreases left.context.parsed.syntax.forms@.len() - a.0.call.call.form,
    {
        let context = left.context;
        let forms = context.parsed.syntax.forms@;
        self.checked_wiring_is_func(context.file, context.entry, context.limit, *context.wiring);
        self.targets.parsed_project_model();
        let positions_a = self.source_expression_argument_positions(left, a.0, widths, a.1, a.2);
        let positions_b = self.source_expression_argument_positions(right, b.0, widths, b.1, b.2);
        call_argument_positions_agree(forms, a.0.call.call, positions_a, positions_b);
        assert forall|port: int| 0 <= port < a.1.len() implies #[trigger] a.1[port] == b.1[port] by {
            let form = positions_a[port];
            assert(form == positions_b[port]);
            assert(self.source_expression_argument_matches(left, a.0, port, form, widths[port], a.1[port], a.2));
            assert(self.source_expression_argument_matches(right, b.0, port, form, widths[port], b.1[port], b.2));
            if forms[form as int] is Atom {
                source_call_argument_values_agree(context.source, context.parsed, context.wiring, right.context.wiring,
                    context.entry, left.definition, form, context.limit, left.inputs, left.prior, widths[port], a.1[port], b.1[port]);
            } else {
                let x = a.2[form];
                let y = b.2[form];
                assert(self.source_expression_call_evaluates(left, form, x, a.2));
                assert(self.source_expression_call_evaluates(right, form, y, b.2));
                let parsed = context.parsed;
                let row = parsed.definitions@[left.definition as int];
                let frame = parsed.entry_ranges@[context.entry as int].definitions;
                let local = (left.definition - frame.start) as usize;
                parsed_index_evidence(*context.source, *parsed);
                build_definition_scope_evidence(context.source.text, &parsed.build_model(), context.entry as int, left.definition as int);
                vstd::std_specs::vec::axiom_spec_len(&parsed.syntax.forms);
                let first = (row.references.start + x.reference) as usize;
                let second = (row.references.start + y.reference) as usize;
                definition_reference_form_unique(context.source.text, forms, parsed.references@, row, first, second);
                assert(x.reference == y.reference);
                self.successful_call_signatures_agree(context.file, context.entry, local, x.reference, context.limit, x.signature, y.signature);
                match (x.signature.signature, y.signature.signature) {
                    (FuncCallSignature::Nor, FuncCallSignature::Nor) => {},
                    (FuncCallSignature::Function(p), FuncCallSignature::Function(q)) => {
                        assert(p.inputs@ == q.inputs@);
                        assert forall|i: int| 0 <= i < x.widths.len() implies #[trigger] x.widths[i] == y.widths[i] by {
                            let ty = p.inputs@[i].ty;
                            assert(self.port_width_matches(ty, x.widths[i], left.layouts));
                            assert(self.port_width_matches(ty, y.widths[i], right.layouts));
                            if ty is Struct {
                                self.layout_port_widths_agree_across_tables(context.limit, left.layouts->Some_0, right.layouts->Some_0,
                                    ty, x.widths[i] as int, y.widths[i] as int);
                            }
                        };
                    },
                    _ => assert(false),
                }
                assert(x.widths =~= y.widths);
                self.source_expression_arguments_agree(left, right, (x.signature, x.arguments, a.2),
                    (y.signature, y.arguments, b.2), x.widths);
                assert(x.arguments == y.arguments);
                if let FuncCallTarget::Function { file, entry, .. } = x.signature.call.target {
                    let target = (file, entry);
                    let r = x.callee_rank->Some_0;
                    let s = y.callee_rank->Some_0;
                    self.template_rank_from_position(*left.plan, target, r, s);
                    let cx = SourceInvocation { rank: r, inputs: x.arguments, outputs: seq![x.result] };
                    let cy = SourceInvocation { rank: s, inputs: y.arguments, outputs: seq![y.result] };
                    assert(left.derivation.contains(cx) && right.derivation.contains(cy));
                    assert(cx.outputs == cy.outputs);
                    assert(cx.outputs[0] == x.result && cy.outputs[0] == y.result);
                } else {
                    assert(x.signature.signature is Nor && y.signature.signature is Nor);
                    let bit = !(x.arguments[0][0] || x.arguments[1][0]);
                    assert(x.result == seq![bit] && y.result == seq![bit]);
                }
                assert(x.result == y.result);
            }
        };
        assert(a.1 =~= b.1);
    }
}

} // verus!
