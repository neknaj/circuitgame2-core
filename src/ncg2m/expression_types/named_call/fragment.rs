//! スカラー評価器が扱う式の構文を、型付けや実行結果と独立に定める。

use super::*;

verus! {

/// 補助関数名を先頭に書く呼び出し形を表す。名前と署名の照合は別の判断で扱う。
pub closed spec fn scalar_call_syntax_at(source: &str, forms: Seq<Form>, at: usize) -> bool {
    named_call_head(source, forms, at)
}

/// スカラー評価器が扱う構文を表す。
///
/// 名前、真偽値、整数のアトム、条件式、補助関数の呼び出しを含む。条件式では条件と両分岐、
/// 呼び出しではすべての実引数を同じ規則で判定する。整数の表現範囲と呼び出し先の本体は別の判断で扱う。
#[verifier::opaque]
pub closed spec fn scalar_evaluator_syntax(source: &str, forms: Seq<Form>, at: usize) -> bool
    decreases forms.len() - at,
{
    super::super::scalar_atom_at(forms, at)
    || match conditional_positions(source, forms, at) {
        Some((condition, yes, no)) if at < condition < yes < no < forms.len() =>
            scalar_evaluator_syntax(source, forms, condition)
                && scalar_evaluator_syntax(source, forms, yes)
                && scalar_evaluator_syntax(source, forms, no),
        _ => scalar_call_syntax_at(source, forms, at)
            && exists|arguments: Seq<usize>| #[trigger] defn_call_arguments(forms, at, arguments)
                && forall|i: int| 0 <= i < arguments.len() ==> {
                    let argument = #[trigger] arguments[i];
                    at < argument < forms.len() && scalar_evaluator_syntax(source, forms, argument)
                },
    }
}

/// アトムの字句種別から、スカラー評価器の構文に属することを示す。
pub proof fn scalar_syntax_atom_from_kind(source: &str, forms: Seq<Form>, at: usize)
    requires super::super::scalar_atom_at(forms, at),
    ensures scalar_evaluator_syntax(source, forms, at),
{
    reveal(scalar_evaluator_syntax);
}

/// 条件と両方の分岐が対応する構文なら、条件式も対応する構文に属する。
pub proof fn scalar_syntax_if_from_children(
    source: &str, forms: Seq<Form>, at: usize, condition: usize, yes: usize, no: usize,
)
    requires
        conditional_positions(source, forms, at) == Some((condition, yes, no)),
        scalar_evaluator_syntax(source, forms, condition),
        scalar_evaluator_syntax(source, forms, yes),
        scalar_evaluator_syntax(source, forms, no),
    ensures scalar_evaluator_syntax(source, forms, at),
{
    reveal(conditional_positions);
    assert(children3(forms, at) == Some((condition, yes, no)));
    assert(at < condition < yes < no < forms.len());
    reveal(scalar_evaluator_syntax);
}

/// 呼び出しの直下の実引数がすべて対応する構文なら、呼び出しも対応する構文に属する。
pub proof fn scalar_syntax_call_from_arguments(source: &str, forms: Seq<Form>, at: usize, arguments: Seq<usize>)
    requires
        scalar_call_syntax_at(source, forms, at), defn_call_arguments(forms, at, arguments),
        forall|i: int| 0 <= i < arguments.len() ==> scalar_evaluator_syntax(source, forms, #[trigger] arguments[i]),
    ensures scalar_evaluator_syntax(source, forms, at),
{
    declared_call_syntax_uses_signature(source, forms, at);
    assert forall|i: int| 0 <= i < arguments.len() implies {
        let arg = #[trigger] arguments[i];
        at < arg < forms.len() && scalar_evaluator_syntax(source, forms, arg)
    } by {
        super::body::call_argument_intervals(forms, at, arguments, i);
    };
    assert(exists|args: Seq<usize>| #[trigger] defn_call_arguments(forms, at, args)
        && forall|i: int| 0 <= i < args.len() ==> {
            let arg = #[trigger] args[i];
            at < arg < forms.len() && scalar_evaluator_syntax(source, forms, arg)
        });
    reveal(scalar_evaluator_syntax);
}

pub(super) proof fn scalar_call_syntax_from_decoded(source: &str, forms: Seq<Form>, at: usize, call: CallForm)
    requires call_form_matches(source, forms, at, Some(call)),
    ensures scalar_call_syntax_at(source, forms, at),
{}

/// 対応する条件式では、条件と両方の分岐も対応する構文である。
pub proof fn scalar_syntax_if_children(
    source: &str, forms: Seq<Form>, at: usize, condition: usize, yes: usize, no: usize,
)
    requires
        scalar_evaluator_syntax(source, forms, at),
        conditional_positions(source, forms, at) == Some((condition, yes, no)),
    ensures
        scalar_evaluator_syntax(source, forms, condition),
        scalar_evaluator_syntax(source, forms, yes),
        scalar_evaluator_syntax(source, forms, no),
{
    conditional_position_is_list(source, forms, at);
    if scalar_call_syntax_at(source, forms, at) {
        declared_call_syntax_uses_signature(source, forms, at);
        assert(false);
    }
    reveal(scalar_evaluator_syntax);
}

/// 対応する呼び出しから、対応する構文の実引数の位置をソース順に取り出す。
pub proof fn scalar_syntax_call_arguments(source: &str, forms: Seq<Form>, at: usize)
    -> (arguments: Seq<usize>)
    requires scalar_evaluator_syntax(source, forms, at), scalar_call_syntax_at(source, forms, at),
    ensures
        defn_call_arguments(forms, at, arguments),
        forall|i: int| 0 <= i < arguments.len()
            ==> scalar_evaluator_syntax(source, forms, #[trigger] arguments[i]),
{
    declared_call_syntax_uses_signature(source, forms, at);
    reveal(scalar_evaluator_syntax);
    choose|arguments: Seq<usize>| #[trigger] defn_call_arguments(forms, at, arguments)
        && forall|i: int| 0 <= i < arguments.len() ==> {
            let argument = #[trigger] arguments[i];
            at < argument < forms.len() && scalar_evaluator_syntax(source, forms, argument)
        }
}

/// 対応する呼び出しの実引数は、元の構文木から取得したどの引数列でも対応する式を指す。
pub proof fn scalar_syntax_matches_call_arguments(source: &str, forms: Seq<Form>, at: usize, arguments: Seq<usize>)
    requires
        scalar_evaluator_syntax(source, forms, at), scalar_call_syntax_at(source, forms, at),
        defn_call_arguments(forms, at, arguments),
    ensures forall|i: int| 0 <= i < arguments.len()
        ==> scalar_evaluator_syntax(source, forms, #[trigger] arguments[i]),
{
    let origin = scalar_syntax_call_arguments(source, forms, at);
    super::body::call_argument_positions_are_unique(forms, at, origin, arguments);
}

// Nat の範囲を超える十進字句も構文には属し、回路用の十六進ビット列はこの断片の外にある。
#[allow(dead_code)]
proof fn integer_range_is_separate_from_scalar_syntax() {
    let decimal = seq![Form::Atom { kind: AtomKind::Natural, span: 0..20 }];
    let hex = seq![Form::Atom { kind: AtomKind::Hexadecimal, span: 0..3 }];
    reveal(scalar_evaluator_syntax);
    assert(scalar_evaluator_syntax("18446744073709551616", decimal, 0));
    assert(!scalar_evaluator_syntax("#x0", hex, 0));
}

/// 対応する構文が、アトム、条件式、または補助関数の呼び出し形のいずれかであることを示す。
pub proof fn scalar_syntax_form_kind(source: &str, forms: Seq<Form>, at: usize)
    requires scalar_evaluator_syntax(source, forms, at),
    ensures super::super::scalar_atom_at(forms, at)
        || conditional_positions(source, forms, at).is_some() || scalar_call_syntax_at(source, forms, at),
{
    reveal(scalar_evaluator_syntax);
}

// 呼び出し形を先に見分け、型規則の呼び出し表を使う分岐につなぐ。
pub(super) proof fn declared_call_syntax_uses_signature(source: &str, forms: Seq<Form>, at: usize)
    requires scalar_call_syntax_at(source, forms, at),
    ensures
        named_call_head(source, forms, at),
        at + 1 < subtree_limit(forms, at) <= forms.len(),
        forms[at as int] is List, forms[at + 1] is Atom,
        shape(source, forms, at) == Err(ExpressionCheckFailure::Deferred(
            DeferredExpression::Form(form_span(forms[at as int])),
        )),
        conditional_positions(source, forms, at).is_none(),
{}

}
