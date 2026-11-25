//! 対応するスカラー本体のリストを、元の式位置に結び付ける。

use super::*;
use super::super::body::call_argument_intervals;
use super::super::fragment::declared_call_syntax_uses_signature;
use crate::ncg2m::expression_types::scalar_atom_at;

verus! {

proof fn argument_containing_position(
    forms: Seq<Form>, owner: usize, args: Seq<usize>, target: usize, at: int,
) -> (child: usize)
    requires
        defn_call_arguments(forms, owner, args),
        0 <= at < args.len(),
        args[at] <= target < subtree_limit(forms, owner),
    ensures
        contains(forms, child, target), owner < child <= target,
        argument_containing(forms, args[at], subtree_limit(forms, owner), target) == Some(child),
        exists|i: int| at <= i < args.len() && (#[trigger] args[i]) == child,
    decreases args.len() - at,
{
    let current = args[at];
    let limit = subtree_limit(forms, current);
    let end = subtree_limit(forms, owner);
    call_argument_intervals(forms, owner, args, at);
    assert(owner < current < limit <= end);
    if target < limit {
        assert(exists|i: int| at <= i < args.len() && (#[trigger] args[i]) == current);
        current
    } else {
        assert(at + 1 < args.len());
        assert(args[at + 1] == limit);
        argument_containing_position(forms, owner, args, target, at + 1)
    }
}

proof fn conditional_shape(source: &str, forms: Seq<Form>, at: usize, condition: usize, yes: usize, no: usize)
    requires conditional_positions(source, forms, at) == Some((condition, yes, no)),
    ensures
        at < forms.len(), forms[at as int] is List,
        at + 1 < forms.len(), forms[at + 1] is Atom,
        children3(forms, at) == Some((condition, yes, no)),
        shape(source, forms, at) == Ok(Expression::Conditional { condition, yes, no }),
{
    reveal(conditional_positions);
    let word = spelling(source, forms[at + 1]);
    assert(plain_name(forms[at + 1]) && word == "if".spec_bytes());
    assert(keyword(word) == Some(FormTag::Conditional)) by {
        reveal_strlit("as-type");
        reveal_strlit("if");
        vstd::utf8::encode_utf8_decode_utf8("as-type"@);
        vstd::utf8::encode_utf8_decode_utf8("if"@);
        assert("as-type".spec_bytes() != "if".spec_bytes());
    };
}

/// 対応するスカラー本体の部分木にあるリストは、本体の根から式としてたどれる。
///
/// 条件式と呼び出し形の先頭に置く名前はアトムであり、リストは部分式の位置にだけ現れる。
#[verifier::spinoff_prover]
pub(in crate::ncg2m::expression_types) proof fn list_in_supported_body_is_expression_slot(source: &str, forms: Seq<Form>, root: usize, at: usize)
    requires
        scalar_evaluator_syntax(source, forms, root),
        root < forms.len(),
        root <= at < subtree_limit(forms, root) <= forms.len(),
        forms[at as int] is List,
    ensures expression_slot(source, forms, root, at),
    decreases at - root,
{
    if root == at { return; }
    scalar_syntax_form_kind(source, forms, root);
    assert(!scalar_atom_at(forms, root));
    if let Some((condition, yes, no)) = conditional_positions(source, forms, root) {
        scalar_syntax_if_children(source, forms, root, condition, yes, no);
        conditional_shape(source, forms, root, condition, yes, no);
        assert(forms[root + 1] is Atom);
        assert(root + 2 == condition && condition <= at);
        let child = if at < yes { condition } else if at < no { yes } else { no };
        assert(contains(forms, child, at));
        assert(expression_child(source, forms, root, at) == Some(child));
        list_in_supported_body_is_expression_slot(source, forms, child, at);
    } else {
        declared_call_syntax_uses_signature(source, forms, root);
        assert(named_call_head(source, forms, root));
        let args = scalar_syntax_call_arguments(source, forms, root);
        call_argument_intervals(forms, root, args, 0);
        assert(root + 2 <= at && args.len() > 0 && args[0] == root + 2);
        let child = argument_containing_position(forms, root, args, at, 0);
        let index = choose|i: int| 0 <= i < args.len() && (#[trigger] args[i]) == child;
        assert(scalar_evaluator_syntax(source, forms, args[index]));
        call_argument_intervals(forms, root, args, index);
        assert(subtree_limit(forms, child) <= forms.len());
        assert(expression_child(source, forms, root, at) == Some(child));
        list_in_supported_body_is_expression_slot(source, forms, child, at);
    }
}

}
