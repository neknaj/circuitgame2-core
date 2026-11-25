//! 反復式の引数と束縛名を、元の構文木の添字で表す。

use super::*;

verus! {

/// 反復式の束縛名の位置に見つかった文法違反。
#[derive(Debug, Eq, PartialEq)]
pub enum FoldSyntaxError {
    /// 要素または添字の名前と累積値の名前を持つリストが必要な範囲。
    Binders(Range<usize>),
    /// 無修飾名が必要な範囲。
    Name(Range<usize>),
    /// 二つの束縛名が重複している。
    Duplicate {
        /// 先に現れた要素または添字の名前の範囲。
        first: Range<usize>,
        /// 後に現れた累積値の名前の範囲。
        duplicate: Range<usize>,
    },
}

#[derive(Clone, Copy)]
pub(super) enum FoldKind {
    List,
    Nat,
}

#[derive(Clone, Copy)]
pub(super) struct FoldHeader {
    pub(super) kind: FoldKind,
    pub(super) _at: usize,
    pub(super) input: usize,
    pub(super) initial: usize,
    pub(super) item: usize,
    pub(super) accumulator: usize,
    pub(super) body: usize,
}

spec fn four_arguments(forms: Seq<Form>, at: usize) -> Option<(usize, usize, usize, usize)> {
    let end = subtree_limit(forms, at);
    if !(at + 2 < end <= forms.len()) {
        None
    } else {
        let input = (at + 2) as usize;
        let initial = subtree_limit(forms, input);
        if !(input < initial < end) {
            None
        } else {
            let binders = subtree_limit(forms, initial);
            if !(initial < binders < end) {
                None
            } else {
                let body = subtree_limit(forms, binders);
                if binders < body < end && subtree_limit(forms, body) == end {
                    Some((input, initial, binders, body))
                } else {
                    None
                }
            }
        }
    }
}

fn read_four_arguments(forms: &[Form], at: usize) -> (result: Option<(usize, usize, usize, usize)>)
    requires at < forms@.len(),
    ensures result == four_arguments(forms@, at),
{
    let end = subtree_end(forms, at);
    if end <= at || end - at <= 2 || end > forms.len() { return None; }
    let input = at + 2;
    let initial = subtree_end(forms, input);
    if initial <= input || initial >= end { return None; }
    let binders = subtree_end(forms, initial);
    if binders <= initial || binders >= end { return None; }
    let body = subtree_end(forms, binders);
    if body <= binders || body >= end || subtree_end(forms, body) != end { return None; }
    Some((input, initial, binders, body))
}

spec fn binder_pair(forms: Seq<Form>, at: usize) -> Option<(usize, usize)> {
    match forms[at as int] {
        Form::List { end, .. } if at + 1 < end <= forms.len() => {
            let first = (at + 1) as usize;
            let second = subtree_limit(forms, first);
            if first < second < end && subtree_limit(forms, second) == end {
                Some((first, second))
            } else {
                None
            }
        }
        _ => None,
    }
}

fn read_binder_pair(forms: &[Form], at: usize) -> (result: Option<(usize, usize)>)
    requires at < forms@.len(),
    ensures result == binder_pair(forms@, at),
{
    let Form::List { end: list_end, .. } = &forms[at] else { return None; };
    let end = *list_end;
    if end <= at || end > forms.len() || end - at <= 1 { return None; }
    let first = at + 1;
    let second = subtree_end(forms, first);
    if second <= first || second >= end || subtree_end(forms, second) != end { return None; }
    Some((first, second))
}

pub(super) open spec fn fold_positions(forms: Seq<Form>, at: usize, header: FoldHeader) -> bool {
    &&& header._at == at
    &&& at < header.input < header.initial < header.item < header.accumulator < header.body
    &&& header.body < subtree_limit(forms, header.body) == subtree_limit(forms, at) <= forms.len()
    &&& subtree_limit(forms, header.input) == header.initial
    &&& header.initial < subtree_limit(forms, header.initial) <= header.item
}

pub(super) closed spec fn fold_header<'a>(
    source: &'a str, forms: Seq<Form>, at: usize, kind: FoldKind,
) -> Result<FoldHeader, ExpressionCheckFailure<'a>> {
    match four_arguments(forms, at) {
        None => Err(ExpressionCheckFailure::Type(ExpressionTypeError::Arguments {
            span: form_span(forms[at as int]), expected_count: 4,
        })),
        Some((input, initial, binders, body)) => match binder_pair(forms, binders) {
            None => Err(ExpressionCheckFailure::Type(ExpressionTypeError::Fold(FoldSyntaxError::Binders(
                form_span(forms[binders as int]),
            )))),
            Some((item, accumulator)) => {
                if !plain_name(forms[item as int]) {
                    Err(ExpressionCheckFailure::Type(ExpressionTypeError::Fold(FoldSyntaxError::Name(
                        form_span(forms[item as int]),
                    ))))
                } else if !plain_name(forms[accumulator as int]) {
                    Err(ExpressionCheckFailure::Type(ExpressionTypeError::Fold(FoldSyntaxError::Name(
                        form_span(forms[accumulator as int]),
                    ))))
                } else if spelling(source, forms[item as int]) == spelling(source, forms[accumulator as int]) {
                    Err(ExpressionCheckFailure::Type(ExpressionTypeError::Fold(FoldSyntaxError::Duplicate {
                        first: form_span(forms[item as int]),
                        duplicate: form_span(forms[accumulator as int]),
                    })))
                } else {
                    Ok(FoldHeader { kind, _at: at, input, initial, item, accumulator, body })
                }
            }
        }
    }
}

pub(super) fn read_fold_header<'a>(source: &'a str, forms: &[Form], at: usize, kind: FoldKind)
    -> (result: Result<FoldHeader, ExpressionCheckFailure<'a>>)
    requires usable_forms(source, forms@), at < forms@.len(),
    ensures result == fold_header(source, forms@, at, kind),
        result matches Ok(header) ==> fold_positions(forms@, at, header),
{
    let Some((input, initial, binders, body)) = read_four_arguments(forms, at) else {
        return Err(ExpressionCheckFailure::Type(ExpressionTypeError::Arguments {
            span: span_of(&forms[at]), expected_count: 4,
        }));
    };
    let Some((item, accumulator)) = read_binder_pair(forms, binders) else {
        return Err(ExpressionCheckFailure::Type(ExpressionTypeError::Fold(FoldSyntaxError::Binders(
            span_of(&forms[binders]),
        ))));
    };
    if !is_name(&forms[item]) {
        return Err(ExpressionCheckFailure::Type(ExpressionTypeError::Fold(FoldSyntaxError::Name(span_of(&forms[item])))));
    }
    if !is_name(&forms[accumulator]) {
        return Err(ExpressionCheckFailure::Type(ExpressionTypeError::Fold(FoldSyntaxError::Name(
            span_of(&forms[accumulator]),
        ))));
    }
    if is_spelling(source_word(source, forms, item), source_word(source, forms, accumulator)) {
        return Err(ExpressionCheckFailure::Type(ExpressionTypeError::Fold(FoldSyntaxError::Duplicate {
            first: span_of(&forms[item]), duplicate: span_of(&forms[accumulator]),
        })));
    }
    Ok(FoldHeader { kind, _at: at, input, initial, item, accumulator, body })
}

pub(super) open spec fn fold_item_type<'a>(kind: FoldKind, input: TypeShape, span: Range<usize>)
    -> Result<TypeShape, ExpressionCheckFailure<'a>>
{
    match kind {
        FoldKind::Nat => Ok(scalar_type(BuiltinDataType::Integer(IntegerType::Nat))),
        FoldKind::List => if input.list_depth > 0 {
            Ok(TypeShape { builtin: input.builtin, list_depth: (input.list_depth - 1) as usize })
        } else {
            Err(ExpressionCheckFailure::Type(ExpressionTypeError::FoldListInput(span)))
        },
    }
}

pub(super) fn checked_fold_item<'a>(kind: FoldKind, input: TypeShape, span: Range<usize>)
    -> (result: Result<TypeShape, ExpressionCheckFailure<'a>>)
    ensures result == fold_item_type(kind, input, span),
{
    match kind {
        FoldKind::Nat => Ok(scalar(BuiltinDataType::Integer(IntegerType::Nat))),
        FoldKind::List => if input.list_depth > 0 {
            Ok(TypeShape { builtin: input.builtin, list_depth: input.list_depth - 1 })
        } else {
            Err(ExpressionCheckFailure::Type(ExpressionTypeError::FoldListInput(span)))
        },
    }
}

}
