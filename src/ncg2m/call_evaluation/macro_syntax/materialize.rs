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
use super::syntax_event_in_source;
#[cfg(verus_only)]
use crate::syntax::circuit::{generated_definition_matches, generated_definition_sites};
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

/// 回路文法を検査するための本文と、各項目の元の文書を保持する。
pub(super) struct ProjectedSyntax<'b, 'p, 'a> {
    text: String,
    forms: Vec<Form>,
    origins: Vec<MacroSyntaxEvent<'b, 'p, 'a>>,
    open: Vec<usize>,
}

/// 平坦な構文木へ変換できなかった段階。
#[derive(Debug, Eq, PartialEq)]
pub(super) enum ProjectionShapeError {
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
    pub(super) closed spec fn valid(&self) -> bool {
        &&& projection_rows(encode_utf8(self.text@), self.forms@, self.origins@)
        &&& projection_lists(self.forms@, self.open@)
    }

    pub(super) closed spec fn text_model(&self) -> Seq<char> { self.text@ }

    pub(super) closed spec fn forms_model(&self) -> Seq<Form> { self.forms@ }

    pub(super) closed spec fn origins_model(&self) -> Seq<MacroSyntaxEvent<'b, 'p, 'a>> { self.origins@ }

    pub(super) fn new() -> (output: Self)
        ensures output.valid(), output.origins_model().len() == 0,
    {
        let output = Self { text: String::new(), forms: Vec::new(), origins: Vec::new(), open: Vec::new() };
        proof {
            reveal(nested_list_indices);
            assert(projection_rows(encode_utf8(output.text@), output.forms@, output.origins@));
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
        ensures final(self).valid(), final(self).origins_model() =~= old(self).origins_model().push(event),
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

    fn close_list(&mut self) -> (result: Result<(), ProjectionShapeError>)
        requires old(self).valid(),
        ensures final(self).valid(), final(self).origins_model() == old(self).origins_model(),
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

    pub(super) fn push(&mut self, event: MacroSyntaxEvent<'b, 'p, 'a>)
        -> (result: Result<(), ProjectionShapeError>)
        requires old(self).valid(), syntax_event_in_source(event),
        ensures final(self).valid(),
            result.is_ok() ==> final(self).origins_model() =~= if event.token is Close {
                old(self).origins_model()
            } else { old(self).origins_model().push(event) },
    {
        match event.token {
            ArgumentSyntaxToken::Open(_) => {
                proof { projection_delimiter_bytes(); }
                self.append_form("(", None, event);
            },
            ArgumentSyntaxToken::Close(_) => return self.close_list(),
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
    { self.syntax.text.as_str() }

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
        /// 診断に対応する元の項目。欠落の場合は対応する元のリストを示す。
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

spec fn projection_diagnostic_span(error: GeneratedDefinitionError) -> Option<Range<usize>> {
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

spec fn is_diagnostic_anchor(form: Form, span: Range<usize>) -> bool {
    let here = form_span(form);
    here == span || (form is List && span.start == span.end && span.start + 1 == here.end)
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

impl<'b, 'p, 'a> ProjectedSyntax<'b, 'p, 'a> {
    fn related(&self, range: &Range<usize>) -> (origin: Option<MacroSyntaxEvent<'b, 'p, 'a>>)
        requires self.valid(),
        ensures match origin {
            Some(origin) => exists|i: int| 0 <= i < self.forms_model().len()
                && #[trigger] is_diagnostic_anchor(self.forms_model()[i], *range) && origin == self.origins_model()[i]
                && (forall|j: int| 0 <= j < i ==> !#[trigger] is_diagnostic_anchor(self.forms_model()[j], *range)),
            None => forall|i: int| 0 <= i < self.forms_model().len()
                ==> !#[trigger] is_diagnostic_anchor(self.forms_model()[i], *range),
        },
    {
        let mut i = 0;
        while i < self.forms.len()
            invariant self.valid(), i <= self.forms_model().len(),
                forall|j: int| 0 <= j < i ==> !#[trigger] is_diagnostic_anchor(self.forms_model()[j], *range),
            decreases self.forms_model().len() - i,
        {
            if diagnostic_anchor(&self.forms[i], range) {
                return Some(self.origins[i]);
            }
            i += 1;
        }
        None
    }

    fn finish(self) -> (result: Result<CheckedTemplateDefinition<'b, 'p, 'a>, TemplateDefinitionError<'b, 'p, 'a>>)
        requires self.valid(),
        ensures result matches Ok(ok) ==> ok.valid() && ok.origins_model() == self.origins_model()
            && ok.forms_model() == self.forms_model(),
    {
        if let Some(last) = self.open.last() {
            return Err(TemplateDefinitionError::Unclosed(self.origins[*last]));
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
                Ok(CheckedTemplateDefinition { syntax: self, row })
            },
            Err(kind) => {
                let related = match diagnostic_span(&kind) {
                    Some(span) => self.related(span),
                    None => None,
                };
                Err(TemplateDefinitionError::Definition { kind, related })
            },
        }
    }
}

fn project_template<'s, 'b, 'p, 'a>(mut cursor: MacroTemplateSyntax<'s, 'b, 'p, 'a>)
    -> (result: Result<CheckedTemplateDefinition<'b, 'p, 'a>, TemplateDefinitionError<'b, 'p, 'a>>)
    requires cursor.valid(),
    ensures result matches Ok(checked) ==> checked.valid(),
{
    let mut output = ProjectedSyntax::new();
    loop
        invariant cursor.valid(), output.valid(),
        decreases cursor.remaining().0, cursor.remaining().1, cursor.remaining().2,
    {
        match cursor.step() {
            Ok(MacroTemplateSyntaxStep::Complete) => return output.finish(),
            Ok(MacroTemplateSyntaxStep::Continue { event, next }) => {
                if let Some(event) = event {
                    if output.push(event).is_err() {
                        return Err(TemplateDefinitionError::UnexpectedClose(event));
                    }
                }
                cursor = next;
            },
            Err(error) => return Err(TemplateDefinitionError::Source(error)),
        }
    }
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
    pub fn check_template_definition(&self, element: usize)
        -> (result: Option<Result<CheckedTemplateDefinition<'b, 'p, 'a>, TemplateDefinitionDiagnostic<'b, 'p, 'a>>>)
        ensures
            result.is_some() <==> element < self.elements_model().len() && self.elements_model()[element as int] is Template,
            result matches Some(Ok(checked)) ==> checked.valid(),
            result matches Some(Err(error)) ==> error.call == self.call_model() && error.element == element,
    {
        let cursor = self.template_syntax(element)?;
        let result = project_template(cursor);
        Some(match result {
            Ok(checked) => Ok(checked),
            Err(error) => Err(TemplateDefinitionDiagnostic { call: self.call(), element, error }),
        })
    }
}

} // verus!
