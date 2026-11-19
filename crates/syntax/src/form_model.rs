use super::{
    Form, InputDerivation, Lexeme, LexemeKind, form_span, lexical::chosen_input_derivation,
};
use vstd::prelude::*;

verus! {

#[verifier::opaque]
pub(super) open spec fn apply_lexeme(
    forms: Seq<Form>, open: Seq<usize>, lexeme: Lexeme,
) -> (Seq<Form>, Seq<usize>) {
    let span = lexeme.start as usize..lexeme.end as usize;
    match lexeme.kind {
        LexemeKind::Whitespace | LexemeKind::Comment => (forms, open),
        LexemeKind::Atom(kind) => (forms.push(Form::Atom { kind, span }), open),
        LexemeKind::Open => (forms.push(Form::List { span, end: 0 }), open.push(forms.len() as usize)),
        LexemeKind::Close => {
            if open.len() > 0 && open.last() < forms.len() {
                let index = open.last() as int;
                let finished = Form::List {
                    span: form_span(forms[index]).start..span.end,
                    end: forms.len() as usize,
                };
                (forms.update(index, finished), open.drop_last())
            } else {
                (forms, open)
            }
        },
    }
}

#[verifier::opaque]
pub(super) open spec fn form_model_prefix(lexemes: Seq<Lexeme>, count: int) -> (Seq<Form>, Seq<usize>)
    decreases count,
{
    if 0 < count <= lexemes.len() {
        let old = form_model_prefix(lexemes, count - 1);
        apply_lexeme(old.0, old.1, lexemes[count - 1])
    } else {
        (Seq::empty(), Seq::empty())
    }
}

/// 妥当な入力について、厳格解析と回復解析が共通に返す構文木を定める。
///
/// 妥当でない入力には `None` を返す。両モードが共有する字句導出は、解析モードに依存せず入力から選ぶ。
#[verifier::opaque]
pub closed spec fn sexpr_form_model(source: &str) -> Option<Seq<Form>> {
    match chosen_input_derivation(source) {
        Some(witness) => Some(form_model_prefix(witness.lexemes, witness.lexemes.len() as int).0),
        None => None,
    }
}

#[verifier::opaque]
pub(super) open spec fn model_matches(
    lexemes: Seq<Lexeme>, count: int, forms: Seq<Form>, open: Seq<usize>,
) -> bool {
    form_model_prefix(lexemes, count) == (forms, open)
}

pub(super) proof fn model_starts(lexemes: Seq<Lexeme>, forms: Seq<Form>, open: Seq<usize>)
    requires forms.len() == 0, open.len() == 0,
    ensures model_matches(lexemes, 0, forms, open),
{
    reveal(model_matches);
    reveal(form_model_prefix);
    assert(forms =~= Seq::<Form>::empty());
    assert(open =~= Seq::<usize>::empty());
}

pub(super) proof fn model_advances(
    lexemes: Seq<Lexeme>, index: int, prev_forms: Seq<Form>, prev_open: Seq<usize>,
    forms: Seq<Form>, open: Seq<usize>,
)
    requires
        0 <= index < lexemes.len(),
        model_matches(lexemes, index, prev_forms, prev_open),
        apply_lexeme(prev_forms, prev_open, lexemes[index]) == (forms, open),
    ensures model_matches(lexemes, index + 1, forms, open),
{
    reveal(model_matches);
    reveal(form_model_prefix);
}

proof fn model_prefix_preserved(lexemes: Seq<Lexeme>, next: Seq<Lexeme>, count: int)
    requires
        0 <= count <= lexemes.len() <= next.len(),
        next.take(lexemes.len() as int) == lexemes,
    ensures form_model_prefix(lexemes, count) == form_model_prefix(next, count),
    decreases count,
{
    reveal(form_model_prefix);
    if count > 0 {
        model_prefix_preserved(lexemes, next, count - 1);
        assert(next[count - 1] == lexemes[count - 1]);
    }
}

/// 構文モデルの末尾に字句を一つ追加して、その字句を処理した状態を得る。
pub(super) proof fn model_appends(
    lexemes: Seq<Lexeme>, lexeme: Lexeme, before: Seq<Form>, before_open: Seq<usize>,
    forms: Seq<Form>, open: Seq<usize>,
)
    requires
        model_matches(lexemes, lexemes.len() as int, before, before_open),
        apply_lexeme(before, before_open, lexeme) == (forms, open),
    ensures model_matches(lexemes.push(lexeme), lexemes.len() as int + 1, forms, open),
{
    let next = lexemes.push(lexeme);
    assert(next.take(lexemes.len() as int) =~= lexemes);
    model_prefix_preserved(lexemes, next, lexemes.len() as int);
    reveal(model_matches);
    model_advances(next, lexemes.len() as int, before, before_open, forms, open);
}

pub(super) proof fn model_finishes(
    source: &str, witness: InputDerivation, forms: Seq<Form>, open: Seq<usize>,
)
    requires
        chosen_input_derivation(source) == Some(witness),
        model_matches(witness.lexemes, witness.lexemes.len() as int, forms, open),
    ensures sexpr_form_model(source) == Some(forms),
{
    reveal(sexpr_form_model);
    reveal(model_matches);
}

} // verus!
