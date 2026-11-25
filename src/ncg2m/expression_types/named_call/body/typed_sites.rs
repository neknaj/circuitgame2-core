//! 計画と同じ呼び出し表を使い、本体内で式に要求された型を保持する。

use super::*;
use crate::ncg2m::call_evaluation::DefnEvaluationBody;
use super::super::fragment::{declared_call_syntax_uses_signature, scalar_call_syntax_from_decoded};
use super::super::super::typing::scalar::{
    accepted_call_has_entry, checked_if_keeps_child_types, checked_scalar_atom_has_local_type,
};

verus! {

pub(crate) closed spec fn defn_checked_expression_site<'p, 'a>(
    aliases: &MixedUseAliases<'_, 'p, 'a>, caller: DefnPosition, row: Seq<DefnCallEdge<'p, 'a>>,
    body: DefnEvaluationBody<'p, 'a>, at: usize, expected: DataType,
) -> bool {
    let project = aliases.targets_model().project_model();
    let source = body.source.text_model();
    let forms = body.forms@;
    &&& defn_body_calls_cover_slots(aliases, caller, row)
    &&& caller.file < project.sources_model().len()
    &&& *body.source == project.sources_model()[caller.file as int]
    &&& project.functional_forms_model(caller.file) == Some(forms)
    &&& project.defn_signature_matches_index(caller.file, caller.item, Some(body.signature))
    &&& body.at == recorded_call_typing(aliases, caller, row).1
    &&& body.at < forms.len()
    &&& body.at <= at < subtree_limit(forms, body.at) <= forms.len()
    &&& typed_body_with_calls(recorded_call_typing(aliases, caller, row).4, source, forms,
        environment_view(body.signature.parameters@), at, type_shape(expected)) == BodyVerdict::Accepted
}

pub(crate) proof fn defn_checked_site_at_body_root<'p, 'a>(
    aliases: &MixedUseAliases<'_, 'p, 'a>, caller: DefnPosition, row: Seq<DefnCallEdge<'p, 'a>>,
    body: DefnEvaluationBody<'p, 'a>,
)
    requires
        defn_body_calls_cover_slots(aliases, caller, row),
        {
            let project = aliases.targets_model().project_model();
            &&& caller.file < project.sources_model().len()
            &&& *body.source == project.sources_model()[caller.file as int]
            &&& project.functional_forms_model(caller.file) == Some(body.forms@)
            &&& project.defn_signature_matches_index(caller.file, caller.item, Some(body.signature))
        },
        body.at < body.forms@.len(), form_span(body.forms@[body.at as int]) == body.signature.body_span,
        crate::ncg2m::file::retained_forms_in_source_order(body.forms@),
    ensures defn_checked_expression_site(aliases, caller, row, body, body.at, body.signature.result_type.ty),
{
    recorded_call_typing_matches(aliases, caller, row);
    let project = aliases.targets_model().project_model();
    let header = project.indexed_defn(caller.file, caller.item)->Some_0;
    let source = body.source.text_model();
    let (_, root, signature, ..) = recorded_call_typing(aliases, caller, row);
    project.indexed_defn_signature_origin(caller.file, caller.item, Some(body.signature));
    let actual = body.signature;
    crate::ncg2m::data_types::signature_result_origin(source, header, actual);
    crate::ncg2m::data_types::signatures_from_header_agree(source, header, signature, actual);
    signature_environments_agree(signature, actual);
    reveal(crate::ncg2m::file::retained_forms_in_source_order);
    crate::ncg2m::file::meta_ast_unique_start(body.forms@, root, body.at);
}

proof fn nested_site_ends_inside_body(forms: Seq<Form>, body: usize, at: usize)
    requires
        complete_list_indices(forms), nested_list_indices(forms), forms.len() <= usize::MAX,
        body <= at < subtree_limit(forms, body) <= forms.len(),
    ensures subtree_limit(forms, at) <= subtree_limit(forms, body),
{
    if body < at {
        assert(forms[body as int] is List);
        crate::ncg2m::forms::child_stays_inside(forms, body, at);
    }
}

pub(crate) proof fn defn_checked_if_child_sites<'p, 'a>(
    aliases: &MixedUseAliases<'_, 'p, 'a>, caller: DefnPosition, row: Seq<DefnCallEdge<'p, 'a>>,
    body: DefnEvaluationBody<'p, 'a>, at: usize, expected: DataType,
    condition: usize, yes: usize, no: usize,
)
    requires defn_checked_expression_site(aliases, caller, row, body, at, expected),
        conditional_positions(body.source.text_model(), body.forms@, at) == Some((condition, yes, no)),
    ensures
        defn_checked_expression_site(aliases, caller, row, body, condition,
            DataType { atom: DataTypeAtom::Builtin(BuiltinDataType::Bool), list_depth: 0 }),
        defn_checked_expression_site(aliases, caller, row, body, yes, expected),
        defn_checked_expression_site(aliases, caller, row, body, no, expected),
{
    recorded_call_typing_matches(aliases, caller, row);
    let calls = recorded_call_typing(aliases, caller, row).4;
    let forms = body.forms@;
    assert(children3(forms, at) == Some((condition, yes, no)));
    nested_site_ends_inside_body(forms, body.at, at);
    assert(at < condition < yes < no < subtree_limit(forms, at));
    checked_if_keeps_child_types(calls, body.source.text_model(), forms, body.signature.parameters@,
        at, expected, condition, yes, no);
}

pub(crate) proof fn recorded_edge_has_call_syntax<'p, 'a>(
    aliases: &MixedUseAliases<'_, 'p, 'a>, caller: DefnPosition, row: Seq<DefnCallEdge<'p, 'a>>,
    body: DefnEvaluationBody<'p, 'a>, site: usize,
)
    requires
        defn_body_calls_cover_slots(aliases, caller, row), site < row.len(),
        ({
            let project = aliases.targets_model().project_model();
            &&& caller.file < project.sources_model().len()
            &&& *body.source == project.sources_model()[caller.file as int]
            &&& project.functional_forms_model(caller.file) == Some(body.forms@)
        }),
    ensures scalar_call_syntax_at(body.source.text_model(), body.forms@, row[site as int].at),
{
    recorded_call_typing_matches(aliases, caller, row);
    let (_, root, _, outcomes, calls, issues, trace) = recorded_call_typing(aliases, caller, row);
    let index = trace[site as int];
    trace_entry_in_range(calls, trace, root, body.forms@.len(), site as int);
    let (form, _, _) = trace_entry_resolution(aliases, caller, body.forms@, root, outcomes, calls, issues, index);
    assert(edge_projects(body.source, body.forms@, calls[index as int], row[site as int]));
    scalar_call_syntax_from_decoded(body.source.text_model(), body.forms@, row[site as int].at, form);
}

pub(crate) proof fn checked_body_scalar_position<'p, 'a>(
    aliases: &MixedUseAliases<'_, 'p, 'a>, caller: DefnPosition, row: Seq<DefnCallEdge<'p, 'a>>,
    body: DefnEvaluationBody<'p, 'a>, at: usize, expected: DataType,
)
    requires
        defn_checked_expression_site(aliases, caller, row, body, at, expected),
        scalar_evaluator_syntax(body.source.text_model(), body.forms@, body.at),
        scalar_call_syntax_at(body.source.text_model(), body.forms@, at),
    ensures expression_slot(body.source.text_model(), body.forms@, body.at, at),
{
    let source = body.source.text_model();
    let forms = body.forms@;
    declared_call_syntax_uses_signature(source, forms, at);
    list_in_supported_body_is_expression_slot(source, forms, body.at, at);
}

pub(crate) proof fn checked_atom_uses_only_parameters<'p, 'a>(
    aliases: &MixedUseAliases<'_, 'p, 'a>, caller: DefnPosition, row: Seq<DefnCallEdge<'p, 'a>>,
    body: DefnEvaluationBody<'p, 'a>, at: usize, expected: DataType,
)
    requires
        defn_checked_expression_site(aliases, caller, row, body, at, expected), scalar_atom_at(body.forms@, at),
        expected.list_depth == 0,
        expected.atom matches DataTypeAtom::Builtin(BuiltinDataType::Bool | BuiltinDataType::Integer(_)),
    ensures local_scalar_site_is_typed(body.source.text_model(), body.forms@, body.signature.parameters@, at, expected),
{
    checked_scalar_atom_has_local_type(recorded_call_typing(aliases, caller, row).4,
        body.source.text_model(), body.forms@, body.signature.parameters@, at, expected);
}

// 型検査で使った署名から、同じ宣言を指す元の式位置の辺を取り出す。
#[verifier::spinoff_prover]
pub(crate) proof fn defn_checked_call_has_edge<'p, 'a>(
    aliases: &MixedUseAliases<'_, 'p, 'a>, caller: DefnPosition, row: Seq<DefnCallEdge<'p, 'a>>,
    body: DefnEvaluationBody<'p, 'a>, at: usize, expected: DataType,
) -> (site: int)
    requires
        defn_checked_expression_site(aliases, caller, row, body, at, expected),
        expression_slot(body.source.text_model(), body.forms@, body.at, at),
        scalar_call_syntax_at(body.source.text_model(), body.forms@, at),
    ensures
        0 <= site < row.len(),
        row[site].at == at,
        row[site].from == caller,
        *row[site].call.source == *body.source,
        row[site].call.span == form_span(body.forms@[at as int]),
        row[site].call.head == form_span(body.forms@[at + 1]),
{
    recorded_call_typing_matches(aliases, caller, row);
    let (root, start, signature, outcomes, calls, issues, trace) = recorded_call_typing(aliases, caller, row);
    let source = body.source.text_model();
    let forms = body.forms@;
    declared_call_syntax_uses_signature(source, forms, at);
    let index = accepted_call_has_entry(calls, source, forms, body.signature.parameters@, at, expected);
    let entry = calls[index as int];
    assert(entry_witness(entry, outcomes, start)) by { reveal(call_inputs_match); };
    reveal(entry_witness);
    assert(start <= at < start + outcomes.len());
    let result = outcomes[at - start]->Some_0->Ok_0;
    let declaration = result->Declared_declaration;
    let target = DefnPosition { file: declaration.file, item: declaration.item };
    reveal(all_slots_projected);
    assert(exists|i: int| 0 <= i < row.len() && {
        let edge = #[trigger] row[i];
        &&& edge.from == caller && edge.at == at && edge.to == target
        &&& edge.call.span == form_span(forms[at as int]) && edge.call.head == form_span(forms[at + 1])
    });
    let site = choose|i: int| 0 <= i < row.len() && {
        let edge = #[trigger] row[i];
        &&& edge.from == caller && edge.at == at && edge.to == target
        &&& edge.call.span == form_span(forms[at as int]) && edge.call.head == form_span(forms[at + 1])
    };
    trace_entry_in_range(calls, trace, start, forms.len(), site);
    assert(edge_projects(body.source, forms, calls[trace[site] as int], row[site]));
    site
}

// 同じ型検査の記録から、選んだ呼び出しとその引数の型を取り出す。
#[verifier::spinoff_prover]
pub(crate) proof fn defn_checked_call_arguments<'p, 'a>(
    aliases: &MixedUseAliases<'_, 'p, 'a>, caller: DefnPosition, row: Seq<DefnCallEdge<'p, 'a>>, site: usize,
    body: DefnEvaluationBody<'p, 'a>, expected: DataType, callee: DefnEvaluationBody<'p, 'a>,
)
    requires
        site < row.len(),
        defn_checked_expression_site(aliases, caller, row, body, row[site as int].at, expected),
        {
            let project = aliases.targets_model().project_model();
            let to = row[site as int].to;
            &&& to.file < project.sources_model().len()
            &&& *callee.source == project.sources_model()[to.file as int]
            &&& project.defn_signature_matches_index(to.file, to.item, Some(callee.signature))
        },
        expected.list_depth == 0,
        expected.atom matches DataTypeAtom::Builtin(BuiltinDataType::Bool | BuiltinDataType::Integer(_)),
    ensures
        expected == callee.signature.result_type.ty,
        row[site as int].arguments@.len() == callee.signature.parameters@.len(),
        forall|slot: int| 0 <= slot < row[site as int].arguments@.len() ==> {
            let at = #[trigger] row[site as int].arguments@[slot];
            let ty = callee.signature.parameters@[slot].ty.ty;
            &&& defn_checked_expression_site(aliases, caller, row, body, at, ty)
            &&& at < body.forms@.len()
            &&& (local_scalar_fragment(body.source.text_model(), body.forms@, at) && ty.list_depth == 0
                && (ty.atom matches DataTypeAtom::Builtin(BuiltinDataType::Bool | BuiltinDataType::Integer(_)))
                ==> local_scalar_site_is_typed(body.source.text_model(), body.forms@, body.signature.parameters@, at, ty))
        },
{
    recorded_call_typing_matches(aliases, caller, row);
    let project = aliases.targets_model().project_model();
    let source = body.source.text_model();
    let forms = body.forms@;
    let edge = row[site as int];
    let (_, root, _, outcomes, calls, issues, trace) = recorded_call_typing(aliases, caller, row);
    let index = trace[site as int];
    trace_entry_in_range(calls, trace, root, forms.len(), site as int);
    let entry = calls[index as int];
    assert(edge_projects(body.source, forms, entry, edge));
    let (call, _, target) = trace_entry_resolution(aliases, caller, forms, root, outcomes, calls, issues, index);
    super::super::declared_head_is_deferred_by_local_typing(source, forms, edge.at, call);
    let to = edge.to;
    project.indexed_defn_signature_origin(to.file, to.item, Some(target));
    project.indexed_defn_signature_origin(to.file, to.item, Some(callee.signature));
    let target_header = project.indexed_defn(to.file, to.item)->Some_0;
    crate::ncg2m::data_types::signatures_from_header_agree(callee.source.text_model(), target_header, target, callee.signature);
    signature_environments_agree(target, callee.signature);
    crate::ncg2m::data_types::signature_result_types_agree(target, callee.signature);
    assert forall|slot: int| 0 <= slot < entry.arguments@.len() implies
        (#[trigger] entry.arguments@[slot]).expected == type_shape(callee.signature.parameters@[slot].ty.ty) by {
        signature_parameter_types_agree(target, callee.signature, slot);
    };
    assert(call_signature_types_match(entry, callee.signature));
    reveal(call_inputs_match);
    nested_site_ends_inside_body(forms, body.at, edge.at);
    super::super::super::typing::scalar::call_preserves_checked_types(calls, source, forms, body.signature.parameters@,
        callee.signature, edge.at, expected, index);
    assert forall|slot: int| 0 <= slot < edge.arguments@.len() implies {
        let arg = #[trigger] edge.arguments@[slot];
        let ty = callee.signature.parameters@[slot].ty.ty;
        &&& defn_checked_expression_site(aliases, caller, row, body, arg, ty)
        &&& arg < forms.len()
        &&& (local_scalar_fragment(source, forms, arg) && ty.list_depth == 0
            && (ty.atom matches DataTypeAtom::Builtin(BuiltinDataType::Bool | BuiltinDataType::Integer(_)))
            ==> local_scalar_site_is_typed(source, forms, body.signature.parameters@, arg, ty))
    } by {
        assert(canonical_call(forms, entry));
        assert(edge.arguments@[slot] == entry.arguments@[slot].at);
    };
}


}
