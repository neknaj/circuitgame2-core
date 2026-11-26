//! 出典を持つ構文イベントから、回路文法の検査に渡す木と本文を組み立てる。

use super::{ArgumentSyntaxToken, MacroSyntaxEvent, MacroTemplateSyntax, MacroTemplateSyntaxError, MacroTemplateSyntaxStep};
use super::super::{macro_binding::BoundMacroCall, macro_expansion::MacroExpandedBody};
use alloc::{string::String, vec::Vec};
use core::ops::Range;
use crate::project::read_source_span;
use crate::syntax::{
    Form, circuit::{GeneratedDefinition, GeneratedDefinitionError, check_generated_definition},
};
#[cfg(verus_only)]
use super::{completed_macro_template_syntax_consumed, macro_template_syntax_starts_at,
    macro_template_syntax_step_matches, syntax_event_in_source};
#[cfg(verus_only)]
use crate::syntax::circuit::{generated_definition_error, generated_definition_matches,
    generated_definition_matches_on_same_bytes, generated_definition_sites};
#[cfg(verus_only)]
use crate::syntax::{
    AtomKind, bare_atom_delimiter, bare_atom_extent, bare_atom_kind, complete_list_indices, form_atom_matches,
    form_span, form_spans_valid, list_source_delimiters, nested_list_indices, quoted_atom,
};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::{
    seq_lib::lemma_seq_contains_after_push,
    string::{StringSliceAdditionalSpecFns, is_ascii, is_ascii_spec_bytes},
    utf8::{encode_utf8, encode_utf8_concat, encode_utf8_valid_utf8, is_char_boundary_iff_not_is_continuation_byte,
        is_continuation_byte},
};

verus! {

/// 投影した本文のバイト列、平坦な木、各項目の出典、未終了リストの位置。
pub type TemplateProjectionModel<'b, 'p, 'a> =
    (Seq<u8>, Seq<Form>, Seq<MacroSyntaxEvent<'b, 'p, 'a>>, Seq<usize>);

/// 元の字句または括弧を表すバイト列。
pub open spec fn projected_event_bytes(event: MacroSyntaxEvent) -> Seq<u8> {
    match event.token {
        ArgumentSyntaxToken::Atom(at) => {
            let span = form_span(event.origin.forms_model()[at as int]);
            event.origin.source_model().text_model().spec_bytes()[span.start as int..span.end as int]
        },
        ArgumentSyntaxToken::Open(_) => seq![b'('],
        ArgumentSyntaxToken::Close(_) => seq![b')'],
    }
}

/// 元のイベント一つが、本文、平坦な添字、リストの対応と出典をどう進めるかを定める。
pub open spec fn projected_event_step(
    before: TemplateProjectionModel, after: TemplateProjectionModel, event: MacroSyntaxEvent,
) -> bool {
    let (bytes, forms, origins, open) = before;
    let piece = projected_event_bytes(event);
    let span = bytes.len() as usize .. (bytes.len() + piece.len()) as usize;
    &&& syntax_event_in_source(event)
    &&& after.0 == bytes + piece + seq![b' ']
    &&& match event.token {
        ArgumentSyntaxToken::Atom(at) => {
            let kind = event.origin.forms_model()[at as int]->Atom_kind;
            after.1 == forms.push(Form::Atom { kind, span }) && after.2 == origins.push(event) && after.3 == open
        },
        ArgumentSyntaxToken::Open(_) => after.1 == forms.push(Form::List { span, end: 0 })
            && after.2 == origins.push(event) && after.3 == open.push(forms.len() as usize),
        ArgumentSyntaxToken::Close(_) => {
            &&& open.len() > 0 && open.last() < forms.len()
            &&& after.1 == forms.update(open.last() as int, Form::List {
                span: form_span(forms[open.last() as int]).start..span.end, end: forms.len() as usize,
            })
            &&& after.2 == origins && after.3 == open.drop_last()
        },
    }
}

/// 回路文法を検査するための本文と、各項目の元の文書を保持する。
struct ProjectedSyntax<'b, 'p, 'a> {
    text: String,
    forms: Vec<Form>,
    origins: Vec<MacroSyntaxEvent<'b, 'p, 'a>>,
    open: Vec<usize>,
}

/// 平坦な構文木へ変換できなかった段階。
#[derive(Debug, Eq, PartialEq)]
enum ProjectionShapeError {
    /// 閉じる対象のリストがない。
    UnexpectedClose,
}

// 本文には各項目の直後に空白があり、既存の項目は本文を延ばしても再分類を要しない。
spec fn form_in_projected_bytes(bytes: Seq<u8>, form: Form) -> bool {
    let span = form_span(form);
    let a = span.start as int;
    let b = span.end as int;
    &&& 0 <= a < b < bytes.len()
    &&& !is_continuation_byte(bytes[a])
    &&& bytes[b] == b' '
    &&& match form {
        Form::Atom { kind: AtomKind::String, .. } => quoted_atom(bytes[a..b]),
        Form::Atom { kind, .. } => bare_atom_extent(bytes, a, b) && bare_atom_kind(bytes[a..b]) == Some(kind),
        Form::List { end, .. } => bytes[a] == b'(' && (end > 0 ==> bytes[b - 1] == b')'),
    }
}

/// 投影したアトムとリストが、元の構文項目に対応することを表す。
pub open spec fn projected_form_has_origin(bytes: Seq<u8>, form: Form, event: MacroSyntaxEvent) -> bool {
    &&& syntax_event_in_source(event)
    &&& match (form, event.token) {
        (Form::List { .. }, ArgumentSyntaxToken::Open(_)) => true,
        (Form::Atom { kind, span }, ArgumentSyntaxToken::Atom(at)) => {
            let original = event.origin.forms_model()[at as int];
            let original_span = form_span(original);
            &&& original is Atom && original->Atom_kind == kind
            &&& bytes[span.start as int..span.end as int] == event.origin.source_model().text_model().spec_bytes()
                [original_span.start as int..original_span.end as int]
        },
        _ => false,
    }
}

proof fn projected_prefix_preserves_row(
    before: Seq<u8>, after: Seq<u8>, form: Form, origin: MacroSyntaxEvent,
)
    requires before.is_prefix_of(after), form_in_projected_bytes(before, form), projected_form_has_origin(before, form, origin),
    ensures form_in_projected_bytes(after, form), projected_form_has_origin(after, form, origin),
{
    reveal(bare_atom_extent);
    let span = form_span(form);
    let a = span.start as int;
    let b = span.end as int;
    assert(before[a..b] =~= after[a..b]);
    if form is Atom && form->Atom_kind != AtomKind::String {
        assert forall|i: int| a <= i < b implies !bare_atom_delimiter(#[trigger] after[i]) by {
            assert(before[i] == after[i]);
        };
    }
}

spec fn projection_rows(bytes: Seq<u8>, forms: Seq<Form>, origins: Seq<MacroSyntaxEvent>) -> bool {
    &&& forms.len() == origins.len()
    &&& forall|i: int| 0 <= i < forms.len() ==> {
        let form = #[trigger] forms[i];
        &&& form_in_projected_bytes(bytes, form)
        &&& projected_form_has_origin(bytes, form, origins[i])
        &&& (i > 0 ==> form_span(forms[i - 1]).start < form_span(form).start)
    }
}

spec fn projection_lists(forms: Seq<Form>, open: Seq<usize>) -> bool {
    &&& nested_list_indices(forms)
    &&& forall|i: int| 0 <= i < forms.len() ==> match #[trigger] forms[i] {
        Form::Atom { .. } => !open.contains(i as usize),
        Form::List { end, .. } => if end == 0 { open.contains(i as usize) }
            else { i < end <= forms.len() && !open.contains(i as usize) },
    }
    &&& forall|i: int| 0 <= i < open.len() ==> (#[trigger] open[i]) < forms.len()
    &&& forall|i: int, j: int| 0 <= i < j < open.len() ==> (#[trigger] open[i]) < (#[trigger] open[j])
}

proof fn append_row_preserves_lists(forms: Seq<Form>, open: Seq<usize>, form: Form)
    requires projection_lists(forms, open), forms.len() <= usize::MAX,
        form is Atom || (form is List && form->List_end == 0),
    ensures projection_lists(forms.push(form), if form is List { open.push(forms.len() as usize) } else { open }),
{
    reveal(nested_list_indices);
    let after = forms.push(form);
    let stack = if form is List { open.push(forms.len() as usize) } else { open };
    assert forall|i: int| 0 <= i < after.len() implies match #[trigger] after[i] {
        Form::Atom { .. } => !stack.contains(i as usize),
        Form::List { end, .. } => if end == 0 { stack.contains(i as usize) }
            else { i < end <= after.len() && !stack.contains(i as usize) },
    } by {
        if i < forms.len() {
            assert(after[i] == forms[i]);
            lemma_seq_contains_after_push(open, forms.len() as usize, i as usize);
            assert(stack.contains(i as usize) == open.contains(i as usize));
        } else {
            assert(after[i] == form);
            assert(!open.contains(i as usize)) by {
                if open.contains(i as usize) {
                    let j = open.lemma_contains_to_index(i as usize);
                    assert(open[j] < forms.len());
                }
            };
            lemma_seq_contains_after_push(open, forms.len() as usize, i as usize);
        }
    };
    assert forall|i: int, j: int| 0 <= i < j < after.len() && #[trigger] after[i] is List
        && #[trigger] after[j] is List && j < after[i]->List_end
        implies 0 < after[j]->List_end <= after[i]->List_end by {
        assert(after[i] == forms[i]);
        if j == forms.len() {
            assert(after[i]->List_end <= forms.len());
        } else {
            assert(after[j] == forms[j]);
        }
    };
}

proof fn close_row_preserves_lists(forms: Seq<Form>, open: Seq<usize>, at: usize, closed: Form)
    requires projection_lists(forms, open), open.len() > 0, at == open.last(),
        at < forms.len() && forms[at as int] is List && forms[at as int]->List_end == 0,
        closed is List && closed->List_end == forms.len(),
    ensures projection_lists(forms.update(at as int, closed), open.drop_last()),
{
    reveal(nested_list_indices);
    let after = forms.update(at as int, closed);
    let remaining = open.drop_last();
    assert(remaining.push(at) =~= open);
    assert(!remaining.contains(at)) by {
        if remaining.contains(at) {
            let i = choose|i: int| 0 <= i < remaining.len() && #[trigger] remaining[i] == at;
            assert(remaining[i] == open[i] && open[i] < open.last());
        }
    };
    assert forall|i: int| 0 <= i < after.len() implies match #[trigger] after[i] {
        Form::Atom { .. } => !remaining.contains(i as usize),
        Form::List { end, .. } => if end == 0 { remaining.contains(i as usize) }
            else { i < end <= after.len() && !remaining.contains(i as usize) },
    } by {
        if i != at {
            assert(after[i] == forms[i]);
            lemma_seq_contains_after_push(remaining, at, i as usize);
            assert(remaining.contains(i as usize) == open.contains(i as usize));
        }
    };
    assert forall|i: int, j: int| 0 <= i < j < after.len() && #[trigger] after[i] is List
        && #[trigger] after[j] is List && j < after[i]->List_end
        implies 0 < after[j]->List_end <= after[i]->List_end by {
        if i != at {
            assert(after[i] == forms[i]);
            if j == at {
                assert(forms[j]->List_end > 0);
            } else {
                assert(after[j] == forms[j]);
            }
        } else {
            assert(after[j] == forms[j]);
            assert(!open.contains(j as usize)) by {
                if open.contains(j as usize) {
                    let k = choose|k: int| 0 <= k < open.len() && #[trigger] open[k] == j;
                    if k < open.len() - 1 {
                        assert(open[k] < open.last());
                    } else {
                        assert(open[k] == at);
                    }
                }
            };
        }
    };
}

proof fn projection_delimiter_bytes()
    ensures
        "(".spec_bytes() == seq![b'('],
        ")".spec_bytes() == seq![b')'],
        " ".spec_bytes() == seq![b' '],
{
    reveal_strlit("(");
    reveal_strlit(")");
    reveal_strlit(" ");
    assert("("@ =~= seq!['(']);
    assert(")"@ =~= seq![')']);
    assert(" "@ =~= seq![' ']);
    assert(is_ascii("(") && is_ascii(")") && is_ascii(" "));
    is_ascii_spec_bytes("(");
    is_ascii_spec_bytes(")");
    is_ascii_spec_bytes(" ");
    assert("(".spec_bytes() =~= seq![b'(']);
    assert(")".spec_bytes() =~= seq![b')']);
    assert(" ".spec_bytes() =~= seq![b' ']);
}

fn append_padded(text: &mut String, piece: &str) -> (span: Range<usize>)
    requires piece.spec_bytes().len() > 0,
    ensures
        span.start == encode_utf8(old(text)@).len(),
        span.end == span.start + piece.spec_bytes().len(),
        encode_utf8(final(text)@) == encode_utf8(old(text)@) + piece.spec_bytes() + seq![b' '],
        !is_continuation_byte(piece.spec_bytes()[0]),
{
    let start = text.as_str().as_bytes().len();
    let ghost before = text@;
    text.push_str(piece);
    let end = text.as_str().as_bytes().len();
    let ghost after_piece = text@;
    text.push_str(" ");
    proof {
        encode_utf8_concat(before, piece@);
        encode_utf8_concat(after_piece, " "@);
        encode_utf8_valid_utf8(piece@);
        vstd::utf8::is_char_boundary_start_end_of_seq(piece.spec_bytes());
        is_char_boundary_iff_not_is_continuation_byte(piece.spec_bytes(), 0);
        projection_delimiter_bytes();
    }
    start..end
}

impl<'b, 'p, 'a> ProjectedSyntax<'b, 'p, 'a> {
    spec fn valid(&self) -> bool {
        &&& projection_rows(encode_utf8(self.text@), self.forms@, self.origins@)
        &&& projection_lists(self.forms@, self.open@)
    }

    spec fn text_model(&self) -> Seq<char> { self.text@ }

    spec fn forms_model(&self) -> Seq<Form> { self.forms@ }

    spec fn origins_model(&self) -> Seq<MacroSyntaxEvent<'b, 'p, 'a>> { self.origins@ }

    spec fn model(&self) -> TemplateProjectionModel<'b, 'p, 'a> {
        (encode_utf8(self.text@), self.forms@, self.origins@, self.open@)
    }

    fn new() -> (output: Self)
        ensures output.valid(),
            output.model().0.len() == 0, output.model().1.len() == 0,
            output.model().2.len() == 0, output.model().3.len() == 0,
    {
        let output = Self { text: String::new(), forms: Vec::new(), origins: Vec::new(), open: Vec::new() };
        proof {
            reveal(nested_list_indices);
            assert(projection_rows(encode_utf8(output.text@), output.forms@, output.origins@));
            assert(encode_utf8(output.text@).len() == 0);
        }
        output
    }

    fn append_form(&mut self, piece: &str, kind: Option<crate::syntax::AtomKind>, event: MacroSyntaxEvent<'b, 'p, 'a>)
        requires
            old(self).valid(), syntax_event_in_source(event), piece.spec_bytes().len() > 0,
            match (event.token, kind) {
                (ArgumentSyntaxToken::Open(_), None) => piece.spec_bytes() == seq![b'('],
                (ArgumentSyntaxToken::Atom(at), Some(kind)) => {
                    let original = event.origin.forms_model()[at as int];
                    let source = event.origin.source_model().text_model();
                    let span = form_span(original);
                    &&& original is Atom && original->Atom_kind == kind
                    &&& span.start < span.end <= source.spec_bytes().len()
                    &&& piece.spec_bytes() == source.spec_bytes()[span.start as int..span.end as int]
                    &&& form_atom_matches(source, original)
                },
                _ => false,
            },
        ensures final(self).valid(), projected_event_step(old(self).model(), final(self).model(), event),
    {
        let at = self.forms.len();
        let ghost before = encode_utf8(self.text@);
        let ghost forms = self.forms@;
        let ghost origins = self.origins@;
        let ghost open = self.open@;
        let span = append_padded(&mut self.text, piece);
        let form = match kind {
            Some(kind) => Form::Atom { kind, span },
            None => {
                self.open.push(at);
                Form::List { end: 0, span }
            },
        };
        proof {
            reveal(bare_atom_extent);
            let after = encode_utf8(self.text@);
            let new_span = form_span(form);
            let first = new_span.start as int;
            assert(after[first..new_span.end as int] =~= piece.spec_bytes());
            if let ArgumentSyntaxToken::Atom(index) = event.token {
                let old = event.origin.forms_model()[index as int];
                let old_span = form_span(old);
                let source = event.origin.source_model().text_model();
                if kind != Some(AtomKind::String) {
                    assert forall|i: int| first <= i < new_span.end implies
                        !bare_atom_delimiter(#[trigger] after[i]) by {
                        let original_at = old_span.start + i - first;
                        assert(after[i] == piece.spec_bytes()[i - first]);
                        assert(piece.spec_bytes()[i - first] == source.spec_bytes()[original_at]);
                    };
                }
            }
            assert(form_in_projected_bytes(after, form) && projected_form_has_origin(after, form, event));
            append_row_preserves_lists(forms, open, form);
        }
        self.forms.push(form);
        self.origins.push(event);
        assert forall|i: int| 0 <= i < self.forms@.len() implies {
            let row = #[trigger] self.forms@[i];
            let bytes = encode_utf8(self.text@);
            &&& form_in_projected_bytes(bytes, row)
            &&& projected_form_has_origin(bytes, row, self.origins@[i])
            &&& (i > 0 ==> form_span(self.forms@[i - 1]).start < form_span(row).start)
        } by {
            if i < at {
                assert(self.forms@[i] == forms[i] && self.origins@[i] == origins[i]);
                projected_prefix_preserves_row(before, encode_utf8(self.text@), forms[i], origins[i]);
            }
        };
    }

    fn close_list(&mut self, event: MacroSyntaxEvent<'b, 'p, 'a>) -> (result: Result<(), ProjectionShapeError>)
        requires old(self).valid(), syntax_event_in_source(event), event.token is Close,
        ensures final(self).valid(),
            result.is_ok() ==> projected_event_step(old(self).model(), final(self).model(), event),
            result.is_err() ==> old(self).model().3.len() == 0,
            result.is_ok() <==> old(self).model().3.len() > 0,
    {
        let ghost open = self.open@;
        let Some(at) = self.open.pop() else { return Err(ProjectionShapeError::UnexpectedClose); };
        let Form::List { span, .. } = &self.forms[at] else { unreachable!() };
        let start = span.start;
        let end = self.forms.len();
        let ghost before = encode_utf8(self.text@);
        let ghost forms = self.forms@;
        proof { projection_delimiter_bytes(); }
        let closing = append_padded(&mut self.text, ")");
        let closed = Form::List { end, span: start..closing.end };
        proof {
            let after = encode_utf8(self.text@);
            assert(form_in_projected_bytes(after, closed));
            assert(projected_form_has_origin(after, closed, self.origins@[at as int]));
            close_row_preserves_lists(forms, open, at, closed);
        }
        self.forms[at] = closed;
        assert forall|i: int| 0 <= i < self.forms@.len() implies {
            let row = #[trigger] self.forms@[i];
            let bytes = encode_utf8(self.text@);
            &&& form_in_projected_bytes(bytes, row)
            &&& projected_form_has_origin(bytes, row, self.origins@[i])
            &&& (i > 0 ==> form_span(self.forms@[i - 1]).start < form_span(row).start)
        } by {
            assert(form_span(self.forms@[i]).start == form_span(forms[i]).start);
            if i > 0 { assert(form_span(self.forms@[i - 1]).start == form_span(forms[i - 1]).start); }
            if i != at {
                projected_prefix_preserves_row(before, encode_utf8(self.text@), forms[i], self.origins@[i]);
            }
        };
        Ok(())
    }

    fn push(&mut self, event: MacroSyntaxEvent<'b, 'p, 'a>)
        -> (result: Result<(), ProjectionShapeError>)
        requires old(self).valid(), syntax_event_in_source(event),
        ensures final(self).valid(),
            result.is_ok() ==> projected_event_step(old(self).model(), final(self).model(), event),
            result.is_err() ==> old(self).model().3.len() == 0 && event.token is Close,
    {
        match event.token {
            ArgumentSyntaxToken::Open(_) => {
                proof { projection_delimiter_bytes(); }
                self.append_form("(", None, event);
            },
            ArgumentSyntaxToken::Close(_) => return self.close_list(event),
            ArgumentSyntaxToken::Atom(at) => {
                let forms = event.origin.forms();
                let source = event.origin.source().text();
                let Form::Atom { kind, span } = &forms[at] else { unreachable!() };
                proof { reveal(form_spans_valid); }
                let piece = read_source_span(source, span.start, span.end);
                self.append_form(piece, Some(*kind), event);
            },
        }
        Ok(())
    }
}

/// 展開したテンプレートから得た回路定義と、定義内の各フォームの出典。
pub struct CheckedTemplateDefinition<'b, 'p, 'a> {
    syntax: ProjectedSyntax<'b, 'p, 'a>,
    row: GeneratedDefinition,
}

#[verifier::opaque]
spec fn projected_row_matches(text: Seq<char>, forms: Seq<Form>, row: GeneratedDefinition) -> bool {
    exists|source: &str| source@ == text && #[trigger] generated_definition_matches(source, forms, row)
        && generated_definition_sites(source, forms, row)
}

impl<'b, 'p, 'a> CheckedTemplateDefinition<'b, 'p, 'a> {
    /// 回路文法を満たし、構文木の各添字に元の出典があることを表す。
    pub closed spec fn valid(&self) -> bool {
        &&& self.syntax.valid()
        &&& self.syntax.open@.len() == 0
        &&& projected_row_matches(self.text_model(), self.forms_model(), self.row_model())
    }

    #[verifier::type_invariant]
    spec fn checked_template_invariant(&self) -> bool { self.valid() }

    /// 回路文法で確認した左辺、右辺、回路参照と信号を返す。
    pub fn row(&self) -> (row: &GeneratedDefinition)
        ensures *row == self.row_model(),
    { &self.row }

    /// 回路文法で確認した定義を表す。
    pub closed spec fn row_model(&self) -> GeneratedDefinition { self.row }

    /// 各項目の元の文書とスコープを並べた列を表す。
    pub closed spec fn origins_model(&self) -> Seq<MacroSyntaxEvent<'b, 'p, 'a>> { self.syntax.origins_model() }

    /// 回路文法の添字で参照するための平坦な構文木を借りる。
    pub fn forms(&self) -> (forms: &[Form])
        ensures forms@ == self.forms_model(),
    { self.syntax.forms.as_slice() }

    /// 投影した構文木を表す。
    pub closed spec fn forms_model(&self) -> Seq<Form> { self.syntax.forms_model() }

    /// 構文検査のバイト範囲が指す本文。
    pub fn text(&self) -> (text: &str)
        ensures text@ == self.text_model(),
            generated_definition_matches(text, self.forms_model(), self.row_model()),
            generated_definition_sites(text, self.forms_model(), self.row_model()),
    {
        let text = self.syntax.text.as_str();
        proof {
            use_type_invariant(self);
            reveal(projected_row_matches);
            let known = choose|s: &str| s@ == self.text_model()
                && #[trigger] generated_definition_matches(s, self.forms_model(), self.row_model())
                && generated_definition_sites(s, self.forms_model(), self.row_model());
            generated_definition_matches_on_same_bytes(known, text, self.forms_model(), self.row_model());
        }
        text
    }

    /// 検査に渡した本文、構文木、出典の組を表す。
    pub open spec fn projection_model(&self) -> TemplateProjectionModel<'b, 'p, 'a> {
        (encode_utf8(self.text_model()), self.forms_model(), self.origins_model(), Seq::empty())
    }

    /// 構文検査用の本文を表す。
    pub closed spec fn text_model(&self) -> Seq<char> { self.syntax.text_model() }


    /// 投影したフォームの番号から元の文書とスコープを返す。
    ///
    /// 添字が範囲外なら `None` を返す。
    pub fn origin(&self, form: usize) -> (origin: Option<MacroSyntaxEvent<'b, 'p, 'a>>)
        ensures
            origin.is_some() <==> form < self.forms_model().len(),
            origin matches Some(event) ==> event == self.origins_model()[form as int]
                && projected_form_has_origin(encode_utf8(self.text_model()), self.forms_model()[form as int], event),
    {
        proof { use_type_invariant(self); }
        match self.syntax.origins.get(form) {
            Some(origin) => Some(*origin),
            None => None,
        }
    }
}

/// 展開したテンプレートを回路定義にするときに見つかった違反。
#[derive(Debug)]
pub enum TemplateDefinitionError<'b, 'p, 'a> {
    /// 投影しようとしたリテラルと元の構文木の不一致。
    Source(MacroTemplateSyntaxError<'b, 'p, 'a>),
    /// 対応する開き括弧がない。
    UnexpectedClose(MacroSyntaxEvent<'b, 'p, 'a>),
    /// 閉じていないリスト。最後に開いたリストの出典。
    Unclosed(MacroSyntaxEvent<'b, 'p, 'a>),
    /// 通常の回路文法と生成時の制限による診断。
    Definition {
        /// 構文検査用の本文上の診断。
        kind: GeneratedDefinitionError,
        /// 診断に対応する元の項目。該当項目がない場合は、呼び出しと要素番号から元のテンプレートを参照できる。
        related: Option<MacroSyntaxEvent<'b, 'p, 'a>>,
    },
}

/// 回路文法の診断に、元の展開呼び出しを添えた結果。
#[derive(Debug)]
pub struct TemplateDefinitionDiagnostic<'b, 'p, 'a> {
    /// 診断の主範囲と文書版がある元の展開呼び出し。
    pub call: &'b BoundMacroCall<'p, 'a>,
    /// 展開結果のリスト内の要素番号。
    pub element: usize,
    /// 違反の種別と対応する元の項目。
    pub error: TemplateDefinitionError<'b, 'p, 'a>,
}

/// 回路文法の診断が指す、構文検査用の本文上の範囲を返す。
pub open spec fn projection_diagnostic_span(error: GeneratedDefinitionError) -> Option<Range<usize>> {
    match error {
        GeneratedDefinitionError::Empty => None,
        GeneratedDefinitionError::ExtraRoot(span) | GeneratedDefinitionError::ExpectedDefinition(span)
        | GeneratedDefinitionError::Invalid { span, .. } | GeneratedDefinitionError::ForbiddenHead { span, .. } => Some(span),
    }
}

fn diagnostic_span(error: &GeneratedDefinitionError) -> (range: Option<&Range<usize>>)
    ensures match range { Some(span) => projection_diagnostic_span(*error) == Some(*span),
        None => projection_diagnostic_span(*error).is_none() },
{
    match error {
        GeneratedDefinitionError::Empty => None,
        GeneratedDefinitionError::ExtraRoot(span) | GeneratedDefinitionError::ExpectedDefinition(span)
        | GeneratedDefinitionError::Invalid { span, .. } | GeneratedDefinitionError::ForbiddenHead { span, .. } => Some(span),
    }
}

/// フォームの全体またはリストの閉じ括弧に診断があることを表す。
pub open spec fn is_diagnostic_anchor(form: Form, span: Range<usize>) -> bool {
    let here = form_span(form);
    here == span || (form is List && span.start == span.end && span.start + 1 == here.end)
}

/// 指定位置のフォームが診断範囲に対応する最初の項目であることを表す。
pub open spec fn first_diagnostic_anchor(forms: Seq<Form>, range: Range<usize>, at: int) -> bool {
    &&& 0 <= at < forms.len()
    &&& is_diagnostic_anchor(forms[at], range)
    &&& forall|i: int| 0 <= i < at ==> !#[trigger] is_diagnostic_anchor(forms[i], range)
}

/// 構文検査用の範囲に対応する最初のフォームから、元文書の関連項目を選ぶ。
///
/// 長さ0の範囲が閉じ括弧の位置にある場合は、その元リストを示す。
#[verifier::opaque]
pub open spec fn projected_definition_related(
    projection: TemplateProjectionModel, range: Option<Range<usize>>, related: Option<MacroSyntaxEvent>,
) -> bool {
    let (_, forms, origins, _) = projection;
    &&& forms.len() == origins.len()
    &&& if let Some(range) = range {
        if exists|i: int| #[trigger] first_diagnostic_anchor(forms, range, i) {
            let i = choose|i: int| #[trigger] first_diagnostic_anchor(forms, range, i);
            related == Some(origins[i])
        } else {
            related.is_none()
        }
    } else {
        related.is_none()
    }
}

proof fn projected_related_found<'b, 'p, 'a>(
    projection: TemplateProjectionModel<'b, 'p, 'a>, range: Range<usize>, at: int,
)
    requires projection.1.len() == projection.2.len(), 0 <= at < projection.1.len(),
        is_diagnostic_anchor(projection.1[at], range),
        forall|i: int| 0 <= i < at ==> !#[trigger] is_diagnostic_anchor(projection.1[i], range),
    ensures projected_definition_related(projection, Some(range), Some(projection.2[at])),
{
    reveal(projected_definition_related);
    let (_, forms, origins, _) = projection;
    assert(first_diagnostic_anchor(forms, range, at));
    assert(exists|i: int| #[trigger] first_diagnostic_anchor(forms, range, i));
    let first = choose|i: int| #[trigger] first_diagnostic_anchor(forms, range, i);
    if first < at {
        assert(is_diagnostic_anchor(forms[first], range));
        assert(!is_diagnostic_anchor(forms[first], range));
    } else if at < first {
        assert(!is_diagnostic_anchor(forms[at], range));
    }
    assert(first == at);
    assert(projected_definition_related(projection, Some(range), Some(origins[at])));
}

fn diagnostic_anchor(form: &Form, range: &Range<usize>) -> (matches: bool)
    ensures matches == is_diagnostic_anchor(*form, *range),
{
    let span = match form { Form::Atom { span, .. } | Form::List { span, .. } => span };
    if span.start == range.start && span.end == range.end {
        true
    } else {
        matches!(form, Form::List { .. }) && span.end > 0 && range.start == range.end && range.start == span.end - 1
    }
}

proof fn projected_tree_evidence(
    text: &str, forms: Seq<Form>, origins: Seq<MacroSyntaxEvent>, open: Seq<usize>,
)
    requires projection_rows(text.spec_bytes(), forms, origins), projection_lists(forms, open), open.len() == 0,
    ensures
        complete_list_indices(forms), nested_list_indices(forms),
        form_spans_valid(text, forms, text.spec_bytes().len() as int),
        list_source_delimiters(text, forms, false),
{
    reveal(form_spans_valid);
    reveal(list_source_delimiters);
    encode_utf8_valid_utf8(text@);
    assert forall|i: int| 0 <= i < forms.len() implies {
        let form = #[trigger] forms[i];
        let span = form_span(form);
        &&& span.start < span.end <= text.spec_bytes().len()
        &&& vstd::utf8::is_char_boundary(text.spec_bytes(), span.start as int)
        &&& vstd::utf8::is_char_boundary(text.spec_bytes(), span.end as int)
        &&& (i > 0 ==> form_span(forms[i - 1]).start < span.start)
        &&& form_atom_matches(text, form)
    } by {
        let form = forms[i];
        let span = form_span(form);
        assert(form_in_projected_bytes(text.spec_bytes(), form));
        is_char_boundary_iff_not_is_continuation_byte(text.spec_bytes(), span.start as int);
        is_char_boundary_iff_not_is_continuation_byte(text.spec_bytes(), span.end as int);
    };
    assert forall|i: int| 0 <= i < forms.len()
        implies crate::syntax::list_delimited(text.spec_bytes(), #[trigger] forms[i], false) by {
        assert(form_in_projected_bytes(text.spec_bytes(), forms[i]));
    };
    assert forall|i: int| 0 <= i < forms.len() && #[trigger] forms[i] is List
        implies i < forms[i]->List_end <= forms.len() by {
        if forms[i]->List_end == 0 {
            assert(open.contains(i as usize));
            vstd::seq_lib::lemma_seq_empty_contains_nothing(i as usize);
            assert(open =~= Seq::<usize>::empty());
        }
    };
}

/// 全項目を投影した木の検査結果を、通常の回路契約と元の関連位置に結び付ける。
#[verifier::opaque]
pub open spec fn projected_definition_finish_matches(
    projection: TemplateProjectionModel,
    result: Result<CheckedTemplateDefinition, TemplateDefinitionError>,
) -> bool {
    let (bytes, forms, origins, open) = projection;
    if open.len() > 0 {
        open.last() < origins.len() && result == Err(TemplateDefinitionError::Unclosed(origins[open.last() as int]))
    } else {
        match result {
            Ok(checked) => checked.valid() && checked.projection_model() == projection,
            Err(TemplateDefinitionError::Definition { kind, related }) => {
                &&& exists|text: &str| text.spec_bytes() == bytes
                    && #[trigger] generated_definition_error(text, forms, kind)
                &&& projected_definition_related(projection, projection_diagnostic_span(kind), related)
            },
            _ => false,
        }
    }
}

proof fn projected_definition_failed<'b, 'p, 'a>(
    projection: TemplateProjectionModel<'b, 'p, 'a>, text: &str, kind: GeneratedDefinitionError,
    related: Option<MacroSyntaxEvent<'b, 'p, 'a>>,
)
    requires projection.3.len() == 0, projection.0 == text.spec_bytes(),
        generated_definition_error(text, projection.1, kind),
        projected_definition_related(projection, projection_diagnostic_span(kind), related),
    ensures projected_definition_finish_matches(projection, Err(TemplateDefinitionError::Definition { kind, related })),
{
    reveal(projected_definition_finish_matches);
    assert(exists|source: &str| source.spec_bytes() == projection.0
        && #[trigger] generated_definition_error(source, projection.1, kind));
}

impl<'b, 'p, 'a> ProjectedSyntax<'b, 'p, 'a> {
    fn related(&self, range: &Range<usize>) -> (origin: Option<MacroSyntaxEvent<'b, 'p, 'a>>)
        requires self.valid(),
        ensures projected_definition_related(self.model(), Some(*range), origin),
    {
        let forms = self.forms.as_slice();
        let origins = self.origins.as_slice();
        assert(forms@.len() == origins@.len());
        let mut i = 0;
        while i < forms.len()
            invariant i <= forms@.len(), forms@.len() == origins@.len(),
                forms@ == self.model().1, origins@ == self.model().2,
                forall|j: int| 0 <= j < i ==> !#[trigger] is_diagnostic_anchor(forms@[j], *range),
            decreases forms@.len() - i,
        {
            if diagnostic_anchor(&forms[i], range) {
                proof { projected_related_found(self.model(), *range, i as int); }
                return Some(origins[i]);
            }
            i += 1;
        }
        proof {
            reveal(projected_definition_related);
            assert(forall|j: int| !#[trigger] first_diagnostic_anchor(forms@, *range, j));
            assert(projected_definition_related(self.model(), Some(*range), None));
        }
        None
    }

    fn finish(self) -> (result: Result<CheckedTemplateDefinition<'b, 'p, 'a>, TemplateDefinitionError<'b, 'p, 'a>>)
        requires self.valid(),
        ensures projected_definition_finish_matches(self.model(), result),
            result matches Err(error) ==> !(error is Source) && !(error is UnexpectedClose),
    {
        if let Some(last) = self.open.last() {
            let result = Err(TemplateDefinitionError::Unclosed(self.origins[*last]));
            proof {
                reveal(projected_definition_finish_matches);
                assert(*last == self.model().3.last());
                assert(*last < self.model().2.len());
                assert(projected_definition_finish_matches(self.model(), result));
            }
            return result;
        }
        let text = self.text.as_str();
        let forms = self.forms.as_slice();
        proof { projected_tree_evidence(text, forms@, self.origins@, self.open@); }
        match check_generated_definition(text, forms) {
            Ok(row) => {
                proof {
                    assert(projected_row_matches(self.text_model(), forms@, row)) by {
                        reveal(projected_row_matches);
                        assert(generated_definition_matches(text, forms@, row));
                    };
                }
                let ghost projection = self.model();
                let checked = CheckedTemplateDefinition { syntax: self, row };
                proof {
                    use_type_invariant(&checked);
                    reveal(projected_definition_finish_matches);
                    assert(projection.3 =~= Seq::<usize>::empty());
                    assert(checked.projection_model() == projection);
                    assert(projected_definition_finish_matches(projection, Ok(checked)));
                }
                Ok(checked)
            },
            Err(kind) => {
                let related = match diagnostic_span(&kind) {
                    Some(span) => self.related(span),
                    None => {
                        proof {
                            reveal(projected_definition_related);
                            assert(projected_definition_related(self.model(), None, None));
                        }
                        None
                    },
                };
                proof { projected_definition_failed(self.model(), text, kind, related); }
                Err(TemplateDefinitionError::Definition { kind, related })
            },
        }
    }
}

type ProjectionResult<'b, 'p, 'a> =
    Result<CheckedTemplateDefinition<'b, 'p, 'a>, TemplateDefinitionError<'b, 'p, 'a>>;

/// 続行した各ステップが、テンプレートの次の項目から投影を進めたことを表す。
pub open spec fn template_projection_prefix<'s, 'b, 'p, 'a>(
    initial: MacroTemplateSyntax<'s, 'b, 'p, 'a>, cursors: Seq<MacroTemplateSyntax<'s, 'b, 'p, 'a>>,
    projections: Seq<TemplateProjectionModel<'b, 'p, 'a>>, events: Seq<Option<MacroSyntaxEvent<'b, 'p, 'a>>>,
) -> bool {
    &&& cursors.len() == projections.len() == events.len() + 1
    &&& cursors[0] == initial
    &&& projections[0].0.len() == 0 && projections[0].1.len() == 0
    &&& projections[0].2.len() == 0 && projections[0].3.len() == 0
    &&& forall|i: int| 0 <= i < events.len() ==> #[trigger]
        template_projection_continue(cursors[i], projections[i], events[i], cursors[i + 1], projections[i + 1])
}

/// 一歩から得た構文イベントを、元の順序のまま投影に適用する。
pub open spec fn template_projection_continue<'s, 'b, 'p, 'a>(
    before: MacroTemplateSyntax<'s, 'b, 'p, 'a>, prior: TemplateProjectionModel<'b, 'p, 'a>,
    event: Option<MacroSyntaxEvent<'b, 'p, 'a>>,
    next: MacroTemplateSyntax<'s, 'b, 'p, 'a>, after: TemplateProjectionModel<'b, 'p, 'a>,
) -> bool {
    &&& macro_template_syntax_step_matches(before, Ok(MacroTemplateSyntaxStep::Continue { event, next }))
    &&& match event {
        Some(event) => projected_event_step(prior, after, event),
        None => after == prior,
    }
}

/// 続行可能な全ステップの後で、最初に止まった理由と診断を定める。
pub open spec fn template_projection_trace_result<'s, 'b, 'p, 'a>(
    initial: MacroTemplateSyntax<'s, 'b, 'p, 'a>, cursors: Seq<MacroTemplateSyntax<'s, 'b, 'p, 'a>>,
    projections: Seq<TemplateProjectionModel<'b, 'p, 'a>>, events: Seq<Option<MacroSyntaxEvent<'b, 'p, 'a>>>,
    result: ProjectionResult<'b, 'p, 'a>,
) -> bool {
    &&& template_projection_prefix(initial, cursors, projections, events)
    &&& match result {
        Err(TemplateDefinitionError::Source(error)) => macro_template_syntax_step_matches(cursors.last(), Err(error)),
        Err(TemplateDefinitionError::UnexpectedClose(event)) => {
            &&& event.token is Close && projections.last().3.len() == 0
            &&& exists|next: MacroTemplateSyntax<'s, 'b, 'p, 'a>| #[trigger]
                macro_template_syntax_step_matches(cursors.last(), Ok(MacroTemplateSyntaxStep::Continue {
                    event: Some(event), next,
                }))
        },
        _ => {
            let last = cursors.last();
            &&& macro_template_syntax_step_matches(last, Ok(MacroTemplateSyntaxStep::Complete))
            &&& last.at_model() == last.parts_model().len() && last.splice_at_model() == last.splice_model().len()
            &&& last.argument_model().is_none()
            &&& projected_definition_finish_matches(projections.last(), result)
        },
    }
}

/// 指定のテンプレートから、構文イベント列を順に消費して検査結果を得る。
pub open spec fn template_projection_matches<'s, 'b, 'p, 'a>(
    initial: MacroTemplateSyntax<'s, 'b, 'p, 'a>, result: ProjectionResult<'b, 'p, 'a>,
) -> bool {
    exists|cursors: Seq<MacroTemplateSyntax<'s, 'b, 'p, 'a>>,
        projections: Seq<TemplateProjectionModel<'b, 'p, 'a>>, events: Seq<Option<MacroSyntaxEvent<'b, 'p, 'a>>>|
        #[trigger] template_projection_trace_result(initial, cursors, projections, events, result)
}

proof fn extend_projection_trace<'s, 'b, 'p, 'a>(
    initial: MacroTemplateSyntax<'s, 'b, 'p, 'a>, cursors: Seq<MacroTemplateSyntax<'s, 'b, 'p, 'a>>,
    projections: Seq<TemplateProjectionModel<'b, 'p, 'a>>, events: Seq<Option<MacroSyntaxEvent<'b, 'p, 'a>>>,
    next: MacroTemplateSyntax<'s, 'b, 'p, 'a>, after: TemplateProjectionModel<'b, 'p, 'a>,
    event: Option<MacroSyntaxEvent<'b, 'p, 'a>>,
)
    requires template_projection_prefix(initial, cursors, projections, events),
        template_projection_continue(cursors.last(), projections.last(), event, next, after),
    ensures template_projection_prefix(initial, cursors.push(next), projections.push(after), events.push(event)),
{
    let steps = cursors.push(next);
    let states = projections.push(after);
    let items = events.push(event);
    assert forall|i: int| 0 <= i < items.len() implies #[trigger]
        template_projection_continue(steps[i], states[i], items[i], steps[i + 1], states[i + 1]) by {
        if i < events.len() {
            assert(template_projection_continue(cursors[i], projections[i], events[i], cursors[i + 1], projections[i + 1]));
        }
    };
}

proof fn projection_trace_witness<'s, 'b, 'p, 'a>(
    initial: MacroTemplateSyntax<'s, 'b, 'p, 'a>, cursors: Seq<MacroTemplateSyntax<'s, 'b, 'p, 'a>>,
    projections: Seq<TemplateProjectionModel<'b, 'p, 'a>>, events: Seq<Option<MacroSyntaxEvent<'b, 'p, 'a>>>,
    result: ProjectionResult<'b, 'p, 'a>,
)
    requires template_projection_trace_result(initial, cursors, projections, events, result),
    ensures template_projection_matches(initial, result),
{}

fn project_template<'s, 'b, 'p, 'a>(initial: MacroTemplateSyntax<'s, 'b, 'p, 'a>)
    -> (result: ProjectionResult<'b, 'p, 'a>)
    requires initial.valid(),
    ensures template_projection_matches(initial, result),
{
    let mut cursor = initial;
    let mut output = ProjectedSyntax::new();
    let ghost mut cursors = seq![initial];
    let ghost mut projections = seq![output.model()];
    let ghost mut events = Seq::<Option<MacroSyntaxEvent<'b, 'p, 'a>>>::empty();
    loop
        invariant cursor.valid(), output.valid(),
            template_projection_prefix(initial, cursors, projections, events),
            cursor == cursors.last(), output.model() == projections.last(),
        decreases cursor.remaining().0, cursor.remaining().1, cursor.remaining().2,
    {
        let ghost before = cursor;
        let ghost prior = output.model();
        match cursor.step() {
            Ok(MacroTemplateSyntaxStep::Complete) => {
                let result = output.finish();
                proof {
                    completed_macro_template_syntax_consumed(before);
                    projection_trace_witness(initial, cursors, projections, events, result);
                }
                return result;
            },
            Ok(MacroTemplateSyntaxStep::Continue { event, next }) => {
                if let Some(item) = event {
                    if output.push(item).is_err() {
                        let result = Err(TemplateDefinitionError::UnexpectedClose(item));
                        proof { projection_trace_witness(initial, cursors, projections, events, result); }
                        return result;
                    }
                }
                proof {
                    assert(template_projection_continue(before, prior, event, next, output.model()));
                    extend_projection_trace(initial, cursors, projections, events, next, output.model(), event);
                    cursors = cursors.push(next);
                    projections = projections.push(output.model());
                    events = events.push(event);
                }
                cursor = next;
            },
            Err(error) => {
                let result = Err(TemplateDefinitionError::Source(error));
                proof { projection_trace_witness(initial, cursors, projections, events, result); }
                return result;
            },
        }
    }
}

/// 選んだテンプレートの展開順と、回路文法に基づく検査結果を対応付ける。
#[verifier::opaque]
pub open spec fn template_definition_check_matches<'s, 'b, 'p, 'a>(
    body: &'s MacroExpandedBody<'b, 'p, 'a>, element: usize,
    result: Option<Result<CheckedTemplateDefinition<'b, 'p, 'a>, TemplateDefinitionDiagnostic<'b, 'p, 'a>>>,
) -> bool {
    if element < body.elements_model().len() && body.elements_model()[element as int] is Template {
        match result {
            Some(Ok(checked)) => checked.valid() && exists|initial: MacroTemplateSyntax<'s, 'b, 'p, 'a>|
                macro_template_syntax_starts_at(&initial, body, element)
                    && #[trigger] template_projection_matches(initial, Ok(checked)),
            Some(Err(error)) => error.call == body.call_model() && error.element == element
                && exists|initial: MacroTemplateSyntax<'s, 'b, 'p, 'a>|
                    macro_template_syntax_starts_at(&initial, body, element)
                        && #[trigger] template_projection_matches(initial, Err(error.error)),
            None => false,
        }
    } else {
        result.is_none()
    }
}

proof fn checked_template_projection_matches<'s, 'b, 'p, 'a>(
    initial: MacroTemplateSyntax<'s, 'b, 'p, 'a>, body: &'s MacroExpandedBody<'b, 'p, 'a>,
    element: usize, checked: CheckedTemplateDefinition<'b, 'p, 'a>,
)
    requires macro_template_syntax_starts_at(&initial, body, element), checked.valid(),
        template_projection_matches(initial, Ok(checked)),
    ensures template_definition_check_matches(body, element, Some(Ok(checked))),
{
    reveal(template_definition_check_matches);
    assert(exists|start: MacroTemplateSyntax<'s, 'b, 'p, 'a>|
        macro_template_syntax_starts_at(&start, body, element)
        && #[trigger] template_projection_matches(start, Ok(checked)));
}

impl<'b, 'p, 'a> MacroExpandedBody<'b, 'p, 'a> {
    /// 展開したテンプレートを再解析せず、一つの回路定義として検査する。
    ///
    /// 範囲外、または直接の実引数を返す要素には `None` を返す。
    /// 定義を受理した後も、左辺や右辺の名前から元の文書とスコープを読める。
    ///
    /// # Errors
    ///
    /// 構文の組み立て・回路文法の順に検査し、最初の違反とその出典を返す。
    pub fn check_template_definition<'s>(&'s self, element: usize)
        -> (result: Option<Result<CheckedTemplateDefinition<'b, 'p, 'a>, TemplateDefinitionDiagnostic<'b, 'p, 'a>>>)
        ensures template_definition_check_matches(self, element, result),
    {
        let Some(cursor) = self.template_syntax(element) else {
            proof { reveal(template_definition_check_matches); }
            return None;
        };
        let ghost initial = cursor;
        let outcome = project_template(cursor);
        proof {
            assert(element < self.elements_model().len() && self.elements_model()[element as int] is Template);
            assert(macro_template_syntax_starts_at(&initial, self, element));
        }
        match outcome {
            Ok(checked) => {
                proof {
                    use_type_invariant(&checked);
                    checked_template_projection_matches(initial, self, element, checked);
                }
                Some(Ok(checked))
            },
            Err(error) => {
                let diagnostic = TemplateDefinitionDiagnostic { call: self.call(), element, error };
                proof {
                    assert(diagnostic.call == self.call_model() && diagnostic.element == element);
                    assert(diagnostic.error == error);
                    assert(exists|start: MacroTemplateSyntax<'s, 'b, 'p, 'a>|
                        macro_template_syntax_starts_at(&start, self, element)
                        && #[trigger] template_projection_matches(start, Err(diagnostic.error)));
                    reveal(template_definition_check_matches);
                    assert(template_definition_check_matches(self, element, Some(Err(diagnostic))));
                }
                Some(Err(diagnostic))
            },
        }
    }
}

} // verus!
