//! テンプレートをたどるとき、評価する挿入式とそのまま残す構文を区別する。

use core::ops::Range;
use crate::syntax::Form;
#[cfg(verus_only)]
use crate::syntax::{complete_list_indices, form_span, form_spans_valid, nested_list_indices};
use super::defn::{is_name, span_of};
use super::forms::{is_spelling, source_word, subtree_end};
#[cfg(verus_only)]
use super::forms::{child_stays_inside, subtree_limit};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// テンプレートに挿入する値の形。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum InsertionKind {
    /// `unsyntax` が構文を1個挿入する。
    Syntax,
    /// `splice` がリスト要素として構文の列を挿入する。
    List,
}

/// テンプレートを構成する次のフォーム。
#[derive(Debug, Eq, PartialEq)]
pub enum TemplatePart {
    /// 元のアトムを構文として残す。
    Atom,
    /// リストを作り、子を元の順に調べる。
    List {
        /// 平坦な構文木における子の半開区間。入れ子も含む。
        children: Range<usize>,
    },
    /// ここから通常の式として評価する。
    Insertion {
        /// 式に求める値の形。
        kind: InsertionKind,
        /// 元の構文木で式の根を指す添字。
        expression: usize,
        /// 式全体と挿入フォームを飛ばした次の位置。
        next: usize,
    },
}

/// 挿入フォームの位置または個数に関する診断。
#[derive(Debug, Eq, PartialEq)]
pub enum TemplateError {
    /// リストの要素以外に現れた `splice`。フォーム全体の範囲。
    SpliceAtRoot(Range<usize>),
    /// 挿入フォームにちょうど1個の式がない。フォーム全体の範囲。
    InsertionArity(Range<usize>),
}

/// 無修飾の先頭語が挿入を表す場合に、必要な値の形を返す。
pub open spec fn template_insertion_head(source: &str, forms: Seq<Form>, at: usize, stop: usize) -> Option<InsertionKind> {
    if at + 1 >= stop || !(forms[(at + 1) as int] matches Form::Atom { kind, .. } && kind is Name) {
        None
    } else {
        let span = form_span(forms[(at + 1) as int]);
        let word = source.spec_bytes()[span.start as int..span.end as int];
        if word == "unsyntax".spec_bytes() { Some(InsertionKind::Syntax) }
        else if word == "splice".spec_bytes() { Some(InsertionKind::List) }
        else { None }
    }
}

/// 元のフォームの先頭語と位置から、残す構文、挿入式、または診断を定める。
pub open spec fn template_part(
    source: &str, forms: Seq<Form>, at: usize, root: bool,
) -> Result<TemplatePart, TemplateError> {
    match forms[at as int] {
        Form::Atom { .. } => Ok(TemplatePart::Atom),
        Form::List { end, span } => match template_insertion_head(source, forms, at, end) {
            Some(kind) => {
                if root && kind is List {
                    Err(TemplateError::SpliceAtRoot(span))
                } else if at + 2 == end || match forms[(at + 2) as int] {
                    Form::Atom { .. } => at + 3 != end,
                    Form::List { end: expression_end, .. } => expression_end != end,
                } {
                    Err(TemplateError::InsertionArity(span))
                } else {
                    Ok(TemplatePart::Insertion { kind, expression: (at + 2) as usize, next: end })
                }
            },
            None => Ok(TemplatePart::List { children: (at + 1) as usize..end }),
        },
    }
}

fn read_insertion_head(source: &str, forms: &[Form], at: usize, stop: usize)
    -> (kind: Option<InsertionKind>)
    requires
        at < stop <= forms@.len(),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures kind == template_insertion_head(source, forms@, at, stop),
{
    if at + 1 == stop || !is_name(&forms[at + 1]) {
        return None;
    }
    let word = source_word(source, forms, at + 1);
    if is_spelling(word, "unsyntax") { Some(InsertionKind::Syntax) }
    else if is_spelling(word, "splice") { Some(InsertionKind::List) }
    else { None }
}

/// 評価する挿入式と、テンプレートとして残すフォームを区別する。
///
/// `root` はテンプレート全体の根を調べるときだけ指定する。挿入式では `next` から
/// テンプレートの走査を続けるため、その式の内部をテンプレートとして解釈しない。
///
/// # Errors
///
/// 根にある `splice` を先に診断する。挿入フォームの式が欠けているか複数ある場合も診断する。
///
/// # Panics
///
/// 厳格に解析した同じ元ソースと構文木の組を渡さなかった場合、または `at` が配列外の場合に
/// パニックすることがある。
///
/// # Examples
///
/// ```
/// use circuitgame2_core::ncg2m::template::{InsertionKind, TemplatePart, inspect_template_part};
/// use circuitgame2_core::syntax::parse;
///
/// let text = "(unsyntax value)";
/// let forms = parse(text)?;
/// let part = inspect_template_part(text, &forms, 0, true).unwrap();
/// assert_eq!(part, TemplatePart::Insertion {
///     kind: InsertionKind::Syntax, expression: 2, next: forms.len(),
/// });
/// # Ok::<(), circuitgame2_core::syntax::Error>(())
/// ```
pub fn inspect_template_part(source: &str, forms: &[Form], at: usize, root: bool)
    -> (part: Result<TemplatePart, TemplateError>)
    requires
        at < forms@.len(), complete_list_indices(forms@), nested_list_indices(forms@),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures part == template_part(source, forms@, at, root),
        part matches Ok(TemplatePart::Insertion { kind, expression, next }) ==>
            at + 2 == expression < next <= forms@.len()
            && forms@[at as int] is List && forms@[at as int]->List_end == next
            && !(root && kind is List),
        part matches Ok(TemplatePart::List { children }) ==>
            children.start == at + 1 <= children.end <= forms@.len()
            && forms@[at as int] is List && forms@[at as int]->List_end == children.end,
        part matches Err(error) ==> match error {
            TemplateError::SpliceAtRoot(span) | TemplateError::InsertionArity(span) =>
                span == form_span(forms@[at as int]),
        },
{
    let Form::List { end, .. } = &forms[at] else { return Ok(TemplatePart::Atom); };
    proof { reveal(complete_list_indices); }
    let Some(kind) = read_insertion_head(source, forms, at, *end) else {
        return Ok(TemplatePart::List { children: at + 1..*end });
    };
    if root && matches!(kind, InsertionKind::List) {
        return Err(TemplateError::SpliceAtRoot(span_of(&forms[at])));
    }
    let expression = at + 2;
    if expression == *end {
        return Err(TemplateError::InsertionArity(span_of(&forms[at])));
    }
    proof { child_stays_inside(forms@, at, expression); }
    if subtree_end(forms, expression) != *end {
        return Err(TemplateError::InsertionArity(span_of(&forms[at])));
    }
    Ok(TemplatePart::Insertion { kind, expression, next: *end })
}

/// 元の構文木からテンプレートのフォームを先行順に読む。
pub struct TemplateWalk<'a> {
    source: &'a str,
    forms: &'a [Form],
    root: usize,
    stop: usize,
    current: usize,
}

impl<'a> TemplateWalk<'a> {
    /// 診断の範囲が対応する元ソース。
    pub closed spec fn source_model(&self) -> &str { self.source }

    /// フォームの添字が対応する元の構文木。
    pub closed spec fn forms_model(&self) -> Seq<Form> { self.forms@ }

    /// テンプレート全体の半開区間。
    pub closed spec fn range_model(&self) -> Range<usize> { self.root..self.stop }

    /// 次に読むフォームの添字。
    pub closed spec fn position_model(&self) -> usize { self.current }

    /// 元の構文木と走査位置が対応することを表す。
    pub closed spec fn valid(&self) -> bool {
        &&& self.root <= self.current <= self.stop <= self.forms@.len()
        &&& self.root < self.stop
        &&& self.stop == subtree_limit(self.forms@, self.root)
        &&& complete_list_indices(self.forms@) && nested_list_indices(self.forms@)
        &&& form_spans_valid(self.source, self.forms@, self.source.spec_bytes().len() as int)
    }

    /// 次のフォームを返す。挿入式の部分木は走査せず、診断を返した時点で末尾に進む。
    ///
    /// # Panics
    ///
    /// 元ソースに対応する厳格構文木から走査を始めなかった場合は、パニックすることがある。
    pub fn next_part(&mut self) -> (part: Option<(usize, Result<TemplatePart, TemplateError>)>)
        requires old(self).valid(),
        ensures
            final(self).valid(), final(self).source_model() == old(self).source_model(),
            final(self).forms_model() == old(self).forms_model(),
            final(self).range_model() == old(self).range_model(),
            template_walk_step(old(self).source_model(), old(self).forms_model(), old(self).range_model(),
                old(self).position_model(), final(self).position_model(), part),
    {
        let at = self.current;
        if at == self.stop {
            return None;
        }
        let part = inspect_template_part(self.source, self.forms, at, at == self.root);
        self.current = match &part {
            Ok(TemplatePart::Insertion { next, .. }) => {
                proof {
                    if at != self.root {
                        reveal(complete_list_indices);
                        child_stays_inside(self.forms@, self.root, at);
                    }
                }
                *next
            },
            Ok(_) => at + 1,
            Err(_) => self.stop,
        };
        Some((at, part))
    }
}

/// 走査の一歩が次の構文を返し、挿入式の内部へ降りないことを表す。
pub open spec fn template_walk_step(
    source: &str, forms: Seq<Form>, range: Range<usize>, at: usize, next: usize,
    part: Option<(usize, Result<TemplatePart, TemplateError>)>,
) -> bool {
    if at == range.end {
        part.is_none() && next == at
    } else {
        &&& at < next <= range.end
        &&& part matches Some((position, result)) && position == at
            && result == template_part(source, forms, at, at == range.start)
            && next == match result {
                Ok(TemplatePart::Insertion { next, .. }) => next,
                Ok(_) => (at + 1) as usize,
                Err(_) => range.end,
            }
    }
}

/// 元の構文木内の根からテンプレートの走査を始める。添字が範囲外なら `None` を返す。
///
/// # Panics
///
/// 元ソースと構文木の対応を壊すと、後続の走査でパニックすることがある。
///
/// # Examples
///
/// ```
/// use circuitgame2_core::ncg2m::template::{InsertionKind, TemplatePart, walk_template};
/// use circuitgame2_core::syntax::parse;
///
/// let text = "(left (splice (make-list (unsyntax expression))) right)";
/// let forms = parse(text)?;
/// let mut walk = walk_template(text, &forms, 0).unwrap();
/// assert!(matches!(walk.next_part(), Some((0, Ok(TemplatePart::List { .. })))));
/// assert!(matches!(walk.next_part(), Some((1, Ok(TemplatePart::Atom)))));
/// let Some((2, Ok(TemplatePart::Insertion { kind: InsertionKind::List, next, .. }))) = walk.next_part()
/// else { panic!("splice の位置が異なる") };
/// assert_eq!(walk.next_part(), Some((next, Ok(TemplatePart::Atom))));
/// assert!(walk.next_part().is_none());
/// # Ok::<(), circuitgame2_core::syntax::Error>(())
/// ```
pub fn walk_template<'a>(source: &'a str, forms: &'a [Form], root: usize) -> (walk: Option<TemplateWalk<'a>>)
    requires
        complete_list_indices(forms@), nested_list_indices(forms@),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures walk.is_some() <==> root < forms@.len(),
        walk matches Some(walk) ==> walk.valid() && walk.source_model() == source && walk.forms_model() == forms@
            && walk.range_model().start == root && walk.position_model() == root
            && root < walk.range_model().end <= forms@.len()
            && walk.range_model().end == match forms@[root as int] {
                Form::Atom { .. } => root + 1,
                Form::List { end, .. } => end as int,
            },
{
    if root >= forms.len() { return None; }
    let stop = subtree_end(forms, root);
    proof { reveal(complete_list_indices); }
    Some(TemplateWalk { source, forms, root, stop, current: root })
}

} // verus!
