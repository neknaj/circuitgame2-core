//! テンプレートのリテラルと評価済みの挿入値を、構文の順序で取り出す。

use alloc::vec::Vec;
use core::ops::Range;
use crate::syntax::Form;
use super::{InsertionKind, TemplateError, TemplatePart, TemplateWalk, walk_template};
#[cfg(verus_only)]
use super::{template_walk_step, super::forms::{child_stays_inside, subtree_limit}};
#[cfg(verus_only)]
use crate::syntax::{complete_list_indices, form_spans_valid, nested_list_indices};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 挿入式を評価して得た構文値。構文値が保持する出典とスコープを引き継ぐ。
#[derive(Debug)]
pub enum TemplateSubstitution<'v, T> {
    /// `unsyntax` で挿入する構文を1個借りる。
    One(&'v T),
    /// `splice` で挿入する構文を元の値の順に借りる。
    Many(&'v [T]),
}

/// 展開した構文を組み立てるための一項目。
#[derive(Debug)]
pub enum TemplateEmission<'v, T> {
    /// 元のテンプレートのアトム。添字はテンプレートの構文木を参照する。
    Atom(usize),
    /// リテラルのリストの開始。添字はテンプレートにあるリストの根を指す。
    Open(usize),
    /// 対応するリストの終了。開始と同じ元の添字を持つ。
    Close(usize),
    /// 評価した構文を1個挿入する。
    Insert(&'v T),
    /// 評価した構文の列をその順に挿入する。空の列はリストに要素を追加しない。
    Splice(&'v [T]),
}

/// テンプレートに評価済みの値を対応付けられなかった最初の理由。
#[derive(Debug)]
pub enum TemplateEmissionError {
    /// テンプレートの位置または引数の個数に関する診断。
    Template(TemplateError),
    /// 指定した挿入フォームに対応する評価済みの値がない。添字は元の構文木上の位置。
    MissingValue(usize),
    /// 挿入フォームが要求する形と値の形が異なる。添字は元の構文木上の位置。
    ValueKind(usize),
    /// テンプレート末尾で余った最初の評価済みの値の添字。
    ExtraValue(usize),
}

pub(super) enum TemplateValues<'v, T> {
    Borrowed(&'v [TemplateSubstitution<'v, T>]),
    Owned(Vec<TemplateSubstitution<'v, T>>),
}

impl<'v, T> TemplateValues<'v, T> {
    pub(super) open spec fn model(&self) -> Seq<TemplateSubstitution<'v, T>> {
        match self {
            Self::Borrowed(values) => values@,
            Self::Owned(values) => values@,
        }
    }

    fn as_slice(&self) -> (values: &[TemplateSubstitution<'v, T>])
        ensures values@ == self.model(),
    {
        match self {
            Self::Borrowed(values) => values,
            Self::Owned(values) => values.as_slice(),
        }
    }
}

/// 元の構文木と挿入する構文を参照しながら、展開した構文の並びを取り出す。
pub struct TemplateEmitter<'s, 'v, T> {
    walk: TemplateWalk<'s>,
    values: TemplateValues<'v, T>,
    used: usize,
    lists: Vec<Range<usize>>,
    finished: bool,
}

impl<'s, 'v, T> TemplateEmitter<'s, 'v, T> {
    /// 元のテンプレートを読む走査の状態を表す。
    pub closed spec fn walk_model(&self) -> TemplateWalk<'s> { self.walk }

    /// 挿入式を評価した順に並べた値を表す。
    pub closed spec fn values_model(&self) -> Seq<TemplateSubstitution<'v, T>> { self.values.model() }

    /// 使用した挿入値の個数を表す。
    pub closed spec fn used_model(&self) -> usize { self.used }

    /// 開いているリストの根と、元の構文木上での末尾を外側から順に表す。
    pub closed spec fn lists_model(&self) -> Seq<Range<usize>> { self.lists@ }

    /// 末尾に達したか、診断を返した後の状態を表す。
    pub closed spec fn finished_model(&self) -> bool { self.finished }

    /// 元の走査が有効で、入力と開いているリストの末尾が走査範囲に収まる。
    pub closed spec fn valid(&self) -> bool {
        let walk = self.walk_model();
        &&& walk.valid()
        &&& walk.range_model().start < walk.range_model().end <= walk.forms_model().len()
        &&& walk.range_model().end == subtree_limit(walk.forms_model(), walk.range_model().start)
        &&& walk.range_model().start <= walk.position_model() <= walk.range_model().end
        &&& complete_list_indices(walk.forms_model())
        &&& self.used <= self.values.model().len()
        &&& nested_list_indices(walk.forms_model())
        &&& !self.finished ==> open_template_lists(walk.forms_model(), walk.position_model(),
            walk.range_model().end, self.lists@)
    }

    /// 残る遷移数の上界を表す。リストを開く遷移では閉じる遷移が一つ増える。
    pub open spec fn remaining_bound(&self) -> nat {
        if self.finished_model() { 0 }
        else {
            (1 + 2 * (self.walk_model().range_model().end - self.walk_model().position_model())
                + self.lists_model().len()) as nat
        }
    }

    /// リテラル項目の出典である元テキストを返す。
    pub fn source(&self) -> (source: &'s str)
        ensures source == self.walk_model().source_model(),
    {
        self.walk.source
    }

    /// リテラル項目の添字が参照する、元の平坦な構文木を返す。
    pub fn forms(&self) -> (forms: &'s [Form])
        ensures forms@ == self.walk_model().forms_model(),
    {
        self.walk.forms
    }

    /// 展開した構文の次の項目を返す。
    ///
    /// 1回の呼び出しはリストの終了を1件返すか、テンプレートのフォームを1件進める。
    /// 挿入値の構文をコピーせず、splice の列もまとめて借りる。診断または末尾の後は None。
    /// 呼び出し側は診断なしで末尾に達した場合に、構文の並びを確定できる。
    pub fn next_emission(&mut self)
        -> (result: Option<Result<TemplateEmission<'v, T>, TemplateEmissionError>>)
        requires old(self).valid(),
        ensures
            final(self).valid(), template_emission_step(old(self), final(self), result),
            !old(self).finished_model() ==> final(self).remaining_bound() < old(self).remaining_bound(),
            !old(self).finished_model() && result.is_none() ==> final(self).finished_model()
                && final(self).lists_model().len() == 0 && final(self).used_model() == final(self).values_model().len()
                && final(self).walk_model().position_model() == final(self).walk_model().range_model().end,
    {
        if self.finished {
            return None;
        }
        if let Some(list) = self.lists.last() {
            if list.end == self.walk.current {
                let list = self.lists.pop().unwrap();
                return Some(Ok(TemplateEmission::Close(list.start)));
            }
        }
        let ghost prior = self.walk;
        let ghost open = self.lists@;
        let ghost part_range = prior.range_model();
        proof {
            no_closing_before_form(prior.forms_model(), prior.position_model(), prior.range_model().end, open);
        }
        let Some((at, part)) = self.walk.next_part() else {
            assert(open.len() == 0);
            self.finished = true;
            if self.used != self.values.as_slice().len() {
                return Some(Err(TemplateEmissionError::ExtraValue(self.used)));
            }
            return None;
        };
        match part {
            Err(error) => {
                self.finished = true;
                Some(Err(TemplateEmissionError::Template(error)))
            },
            Ok(TemplatePart::Atom) => Some(Ok(TemplateEmission::Atom(at))),
            Ok(TemplatePart::List { children }) => {
                proof {
                    if at != part_range.start {
                        reveal(complete_list_indices);
                        child_stays_inside(prior.forms_model(), part_range.start, at);
                    }
                    advance_open_lists(prior.forms_model(), at, children.end, part_range.end, open);
                }
                self.lists.push(at..children.end);
                Some(Ok(TemplateEmission::Open(at)))
            },
            Ok(TemplatePart::Insertion { kind, next, .. }) => {
                proof {
                    if at != part_range.start {
                        reveal(complete_list_indices);
                        child_stays_inside(prior.forms_model(), part_range.start, at);
                    }
                    advance_open_lists(prior.forms_model(), at, next, part_range.end, open);
                }
                let values = self.values.as_slice();
                if self.used == values.len() {
                    self.finished = true;
                    return Some(Err(TemplateEmissionError::MissingValue(at)));
                }
                let piece = match (kind, &values[self.used]) {
                    (InsertionKind::Syntax, TemplateSubstitution::One(value)) => TemplateEmission::Insert(*value),
                    (InsertionKind::List, TemplateSubstitution::Many(values)) => TemplateEmission::Splice(*values),
                    _ => {
                        self.finished = true;
                        return Some(Err(TemplateEmissionError::ValueKind(at)));
                    },
                };
                self.used += 1;
                Some(Ok(piece))
            },
        }
    }
}

spec fn open_template_lists(forms: Seq<Form>, at: usize, stop: usize, lists: Seq<Range<usize>>) -> bool {
    &&& forall|i: int| 0 <= i < lists.len() ==> {
        let list = #[trigger] lists[i];
        &&& list.start < at <= list.end <= stop <= forms.len()
        &&& forms[list.start as int] is List && forms[list.start as int]->List_end == list.end
    }
    &&& forall|i: int, j: int| 0 <= i < j < lists.len() ==> (#[trigger] lists[j]).end <= (#[trigger] lists[i]).end
}

proof fn no_closing_before_form(forms: Seq<Form>, at: usize, stop: usize, lists: Seq<Range<usize>>)
    requires open_template_lists(forms, at, stop, lists), lists.len() > 0 ==> lists.last().end != at,
    ensures forall|i: int| 0 <= i < lists.len() ==> at < (#[trigger] lists[i]).end,
{
    if lists.len() > 0 {
        let last = lists.len() - 1;
        assert(at < lists[last].end);
    }
}

proof fn advance_open_lists(forms: Seq<Form>, at: usize, next: usize, stop: usize, lists: Seq<Range<usize>>)
    requires
        nested_list_indices(forms), at < next <= stop <= forms.len(),
        forms[at as int] is List && forms[at as int]->List_end == next,
        open_template_lists(forms, at, stop, lists),
        forall|i: int| 0 <= i < lists.len() ==> at < (#[trigger] lists[i]).end,
    ensures forall|i: int| 0 <= i < lists.len() ==> next <= (#[trigger] lists[i]).end,
{
    reveal(nested_list_indices);
    assert forall|i: int| 0 <= i < lists.len() implies next <= (#[trigger] lists[i]).end by {
        let parent = lists[i].start as int;
        assert(parent < at < forms[parent]->List_end);
    };
}

/// 指定した挿入位置で次の値を使うか、値の不足と種別の違いを診断する。
pub open spec fn template_substitution_at<'v, T>(
    values: Seq<TemplateSubstitution<'v, T>>, index: usize, at: usize, kind: InsertionKind,
) -> Result<TemplateEmission<'v, T>, TemplateEmissionError> {
    if index >= values.len() {
        Err(TemplateEmissionError::MissingValue(at))
    } else {
        match (kind, values[index as int]) {
            (InsertionKind::Syntax, TemplateSubstitution::One(value)) => Ok(TemplateEmission::Insert(value)),
            (InsertionKind::List, TemplateSubstitution::Many(values)) => Ok(TemplateEmission::Splice(values)),
            _ => Err(TemplateEmissionError::ValueKind(at)),
        }
    }
}

/// 展開の1遷移が、同じテンプレートと値を使い、直前に開いたリストから閉じることを表す。
pub open spec fn template_emission_step<'s, 'v, T>(
    before: &TemplateEmitter<'s, 'v, T>, after: &TemplateEmitter<'s, 'v, T>,
    result: Option<Result<TemplateEmission<'v, T>, TemplateEmissionError>>,
) -> bool {
    let past = before.walk_model();
    let next = after.walk_model();
    let values = before.values_model();
    let used = before.used_model();
    let lists = before.lists_model();
    let cursor = past.position_model();
    &&& after.values_model() == values
    &&& next.source_model() == past.source_model() && next.forms_model() == past.forms_model()
    &&& next.range_model() == past.range_model()
    &&& if before.finished_model() {
        result.is_none() && *after == *before
    } else if lists.len() > 0 && lists.last().end == cursor {
        result == Some(Ok(TemplateEmission::Close(lists.last().start)))
            && next == past && after.lists_model() == lists.drop_last()
            && after.used_model() == used && !after.finished_model()
    } else {
        exists|part: Option<(usize, Result<TemplatePart, TemplateError>)>|
            #[trigger] template_walk_step(past.source_model(), past.forms_model(), past.range_model(),
                cursor, next.position_model(), part)
            && template_emission_from_part(after, values, used, lists, part, result)
    }
}

/// テンプレートから読んだフォームを、リスト状態と挿入値から出力に変える。
pub open spec fn template_emission_from_part<'s, 'v, T>(
    after: &TemplateEmitter<'s, 'v, T>, values: Seq<TemplateSubstitution<'v, T>>,
    used: usize, lists: Seq<Range<usize>>, part: Option<(usize, Result<TemplatePart, TemplateError>)>,
    result: Option<Result<TemplateEmission<'v, T>, TemplateEmissionError>>,
) -> bool {
    match part {
        None => after.finished_model() && after.lists_model() == lists && after.used_model() == used
            && result == if used == values.len() { None } else { Some(Err(TemplateEmissionError::ExtraValue(used))) },
        Some((_, Err(error))) => after.finished_model() && after.lists_model() == lists
            && after.used_model() == used && result == Some(Err(TemplateEmissionError::Template(error))),
        Some((at, Ok(part))) => match part {
            TemplatePart::Atom => !after.finished_model() && after.lists_model() == lists
                && after.used_model() == used && result == Some(Ok(TemplateEmission::Atom(at))),
            TemplatePart::List { children } => !after.finished_model()
                && after.lists_model() == lists.push(at..children.end)
                && after.used_model() == used && result == Some(Ok(TemplateEmission::Open(at))),
            TemplatePart::Insertion { kind, .. } => {
                let replacement = template_substitution_at(values, used, at, kind);
                result == Some(replacement) && after.lists_model() == lists
                    && after.finished_model() == replacement.is_err()
                    && after.used_model() == used + if replacement.is_ok() { 1int } else { 0int }
            },
        },
    }
}

/// 出力の続きを決める、構文木・位置・開いたリスト・挿入値が等しいことを表す。
pub open spec fn template_emitters_agree<'s, 'v, T>(
    a: &TemplateEmitter<'s, 'v, T>, b: &TemplateEmitter<'s, 'v, T>,
) -> bool {
    &&& a.walk_model().source_model() == b.walk_model().source_model()
    &&& a.walk_model().forms_model() == b.walk_model().forms_model()
    &&& a.walk_model().range_model() == b.walk_model().range_model()
    &&& a.walk_model().position_model() == b.walk_model().position_model()
    &&& a.values_model() == b.values_model()
    &&& a.used_model() == b.used_model()
    &&& a.lists_model() == b.lists_model()
    &&& a.finished_model() == b.finished_model()
}

/// 同じ状態からの1遷移は、同じ出力と続きの状態を持つことを示す。
pub proof fn template_emission_steps_agree<'s, 'v, T>(
    a: &TemplateEmitter<'s, 'v, T>, b: &TemplateEmitter<'s, 'v, T>,
    next_a: &TemplateEmitter<'s, 'v, T>, next_b: &TemplateEmitter<'s, 'v, T>,
    out_a: Option<Result<TemplateEmission<'v, T>, TemplateEmissionError>>,
    out_b: Option<Result<TemplateEmission<'v, T>, TemplateEmissionError>>,
)
    requires template_emitters_agree(a, b),
        template_emission_step(a, next_a, out_a), template_emission_step(b, next_b, out_b),
    ensures template_emitters_agree(next_a, next_b), out_a == out_b,
{
    let past = a.walk_model();
    let values = a.values_model();
    let used = a.used_model();
    let lists = a.lists_model();
    let cursor = past.position_model();
    if !a.finished_model() && !(lists.len() > 0 && lists.last().end == cursor) {
        let part_a = choose|part: Option<(usize, Result<TemplatePart, TemplateError>)>|
            #[trigger] template_walk_step(past.source_model(), past.forms_model(), past.range_model(),
                cursor, next_a.walk_model().position_model(), part)
                && template_emission_from_part(next_a, values, used, lists, part, out_a);
        let part_b = choose|part: Option<(usize, Result<TemplatePart, TemplateError>)>|
            #[trigger] template_walk_step(past.source_model(), past.forms_model(), past.range_model(),
                cursor, next_b.walk_model().position_model(), part)
                && template_emission_from_part(next_b, values, used, lists, part, out_b);
        assert(part_a == part_b);
    }
}

/// テンプレートの根と、出現順に評価した挿入値から、展開結果の走査を始める。
///
/// 範囲外の根には `None` を返す。構文は元の構文木と挿入値から借りる。
///
/// # Panics
///
/// 元ソースに対応する厳格な構文木を渡さなかった場合は、後続の走査でパニックすることがある。
///
/// # Examples
///
/// ```
/// use circuitgame2_core::ncg2m::template::{TemplateEmission, TemplateSubstitution, emit_template};
/// use circuitgame2_core::syntax::parse;
///
/// let text = "(outer (inner (unsyntax x) (splice ys)))";
/// let forms = parse(text)?;
/// let value = "caller-x";
/// let rest = ["caller-y", "caller-z"];
/// let substitutions = [TemplateSubstitution::One(&value), TemplateSubstitution::Many(&rest)];
/// let mut output = emit_template(text, &forms, 0, &substitutions).unwrap();
/// assert!(matches!(output.next_emission(), Some(Ok(TemplateEmission::Open(0)))));
/// assert!(matches!(output.next_emission(), Some(Ok(TemplateEmission::Atom(1)))));
/// assert!(matches!(output.next_emission(), Some(Ok(TemplateEmission::Open(2)))));
/// assert!(matches!(output.next_emission(), Some(Ok(TemplateEmission::Atom(3)))));
/// assert!(matches!(output.next_emission(), Some(Ok(TemplateEmission::Insert(x))) if x == &value));
/// assert!(matches!(output.next_emission(), Some(Ok(TemplateEmission::Splice(xs))) if xs == rest));
/// assert!(matches!(output.next_emission(), Some(Ok(TemplateEmission::Close(2)))));
/// assert!(matches!(output.next_emission(), Some(Ok(TemplateEmission::Close(0)))));
/// assert!(output.next_emission().is_none());
/// # Ok::<(), circuitgame2_core::syntax::Error>(())
/// ```
pub fn emit_template<'s, 'v, T>(
    source: &'s str, forms: &'s [Form], root: usize, values: &'v [TemplateSubstitution<'v, T>],
) -> (result: Option<TemplateEmitter<'s, 'v, T>>)
    requires complete_list_indices(forms@), nested_list_indices(forms@),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures emitter_start(source, forms@, root, values@, result),
{
    start_emitter(source, forms, root, TemplateValues::Borrowed(values))
}

/// 展開走査が、渡されたテンプレートと評価済みの値の先頭から始まることを表す。
pub open spec fn emitter_start<'s, 'v, T>(
    source: &'s str, forms: Seq<Form>, root: usize, values: Seq<TemplateSubstitution<'v, T>>,
    result: Option<TemplateEmitter<'s, 'v, T>>,
) -> bool {
    &&& result.is_some() <==> root < forms.len()
    &&& result matches Some(result) ==> {
        &&& result.valid()
        &&& result.walk_model().source_model() == source
        &&& result.walk_model().forms_model() == forms
        &&& result.walk_model().range_model().start == root
        &&& result.walk_model().position_model() == root
        &&& result.walk_model().range_model().end == match forms[root as int] {
            Form::Atom { .. } => root + 1,
            Form::List { end, .. } => end as int,
        }
        &&& result.values_model() == values && result.used_model() == 0
        &&& result.lists_model().len() == 0 && !result.finished_model()
    }
}

pub(super) fn start_emitter<'s, 'v, T>(
    source: &'s str, forms: &'s [Form], root: usize, values: TemplateValues<'v, T>,
) -> (result: Option<TemplateEmitter<'s, 'v, T>>)
    requires complete_list_indices(forms@), nested_list_indices(forms@),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures emitter_start(source, forms@, root, values.model(), result),
{
    let walk = walk_template(source, forms, root)?;
    Some(TemplateEmitter { walk, values, used: 0, lists: Vec::new(), finished: false })
}

} // verus!
