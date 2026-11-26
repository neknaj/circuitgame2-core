use super::{
    Form, InputDerivation, Lexeme, LexemeKind, form_span, list_delimited, list_source_delimiters,
    lexical::{
        choose_input_derivation, chosen_input_derivation, chosen_input_derivation_bytes,
        input_lexeme_valid, lexical_extent_facts, sexpr_input_derivation, well_formed_sexpr,
    },
};
use vstd::prelude::*;
use vstd::string::StringSliceAdditionalSpecFns;

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

/// 妥当な字句導出から、平坦な構文木を得る。
#[verifier::opaque]
pub(super) open spec fn sexpr_form_model_bytes(bytes: Seq<u8>) -> Option<Seq<Form>> {
    match chosen_input_derivation_bytes(bytes) {
        Some(witness) => Some(form_model_prefix(witness.lexemes, witness.lexemes.len() as int).0),
        None => None,
    }
}

/// 妥当な入力について、厳格解析と回復解析が共通に返す構文木を定める。
///
/// 妥当でない入力には `None` を返す。両モードが共有する字句導出は、解析モードに依存せず入力から選ぶ。
#[verifier::opaque]
pub closed spec fn sexpr_form_model(source: &str) -> Option<Seq<Form>> {
    sexpr_form_model_bytes(source.spec_bytes())
}

/// 元の UTF-8 バイト列が同じであれば、S 式としての妥当性と構文木のモデルが一致する。
pub proof fn sexpr_models_agree_on_bytes(left: &str, right: &str)
    requires left.spec_bytes() == right.spec_bytes(),
    ensures
        well_formed_sexpr(left) == well_formed_sexpr(right),
        sexpr_form_model(left) == sexpr_form_model(right),
{
    reveal(well_formed_sexpr);
    reveal(sexpr_form_model);
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
    reveal(sexpr_form_model_bytes);
    reveal(chosen_input_derivation);
    reveal(model_matches);
}

proof fn lexeme_prefix_length(bytes: Seq<u8>, witness: InputDerivation, count: int)
    requires sexpr_input_derivation(bytes, witness), 0 <= count <= witness.lexemes.len(),
    ensures count > 0 ==> count <= witness.lexemes[count - 1].end <= bytes.len(),
    decreases count,
{
    if count > 0 {
        lexeme_prefix_length(bytes, witness, count - 1);
        reveal(sexpr_input_derivation);
        reveal(input_lexeme_valid);
        let lexeme = witness.lexemes[count - 1];
        assert(input_lexeme_valid(bytes, witness, count - 1));
        lexical_extent_facts(bytes, lexeme.start, lexeme.end, lexeme.kind);
    }
}

proof fn form_model_prefix_delimiters(source: &str, witness: InputDerivation, count: int)
    requires sexpr_input_derivation(source.spec_bytes(), witness),
        0 <= count <= witness.lexemes.len() <= usize::MAX,
        source.spec_bytes().len() <= usize::MAX,
    ensures
        list_source_delimiters(source, form_model_prefix(witness.lexemes, count).0, false),
        form_model_prefix(witness.lexemes, count).0.len() <= count,
        forall|i: int| 0 <= i < form_model_prefix(witness.lexemes, count).1.len() ==> {
            let state = form_model_prefix(witness.lexemes, count);
            let node = #[trigger] form_model_prefix(witness.lexemes, count).1[i];
            node < state.0.len() && state.0[node as int] is List
        },
    decreases count,
{
    reveal(form_model_prefix);
    reveal(list_source_delimiters);
    if count > 0 {
        let bytes = source.spec_bytes();
        let old = form_model_prefix(witness.lexemes, count - 1);
        let lexeme = witness.lexemes[count - 1];
        let new = form_model_prefix(witness.lexemes, count);
        form_model_prefix_delimiters(source, witness, count - 1);
        reveal(sexpr_input_derivation);
        reveal(input_lexeme_valid);
        assert(input_lexeme_valid(bytes, witness, count - 1));
        lexical_extent_facts(bytes, lexeme.start, lexeme.end, lexeme.kind);
        reveal(apply_lexeme);
        match lexeme.kind {
            LexemeKind::Close if old.1.len() > 0 => {
                let node = old.1.last() as int;
                assert(old.1[old.1.len() - 1] == old.1.last());
                assert(old.0[node] is List && list_delimited(bytes, old.0[node], false));
                assert(list_delimited(bytes, new.0[node], false));
            },
            _ => {},
        }
        assert forall|i: int| 0 <= i < new.0.len()
            implies list_delimited(bytes, #[trigger] new.0[i], false) by {
            if i < old.0.len() && new.0[i] == old.0[i] {
                assert(list_delimited(bytes, old.0[i], false));
            }
        };
        assert forall|i: int| 0 <= i < new.1.len() implies {
            let node = #[trigger] new.1[i];
            node < new.0.len() && new.0[node as int] is List
        } by {
            if i < old.1.len() {
                assert(old.1[i] < old.0.len() && old.0[old.1[i] as int] is List);
            }
        };
    }
}

/// 厳格な S 式から得たリストの範囲を、同じ入力上の括弧に結び付ける。
pub proof fn sexpr_model_delimiters(source: &str, forms: Seq<Form>)
    requires sexpr_form_model(source) == Some(forms), source.spec_bytes().len() <= usize::MAX,
    ensures list_source_delimiters(source, forms, false),
{
    let choice = choose_input_derivation(source);
    reveal(sexpr_form_model);
    reveal(sexpr_form_model_bytes);
    reveal(chosen_input_derivation);
    let witness = choice->Some_0;
    let count = witness.lexemes.len() as int;
    lexeme_prefix_length(source.spec_bytes(), witness, count);
    form_model_prefix_delimiters(source, witness, count);
}

} // verus!
