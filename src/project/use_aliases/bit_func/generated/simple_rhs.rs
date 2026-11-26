//! 単一出力の配線または基底ゲート候補を、検査済み構文木から取り出す。

use crate::project::circuits::read_indexed_atom;
use crate::syntax::{AtomKind, Form};
use core::ops::Range;
#[cfg(verus_only)]
use crate::syntax::{form_span, form_spans_valid};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

// 添字は渡された元の木を参照する。定数でも元の文書位置を取り出せる。
#[derive(Clone, Copy, Debug)]
pub(super) enum SimpleOperandSyntax {
    Signal(usize),
    Bit { at: usize, value: bool },
}

// nor の綴りを持つ呼び出しは候補として返し、束縛先は後段で確定する。
#[derive(Clone, Copy, Debug)]
pub(super) enum SimpleRhsSyntax {
    Leaf(SimpleOperandSyntax),
    Nor { callee: usize, left: SimpleOperandSyntax, right: SimpleOperandSyntax },
}

spec fn atom_spelling(source: &str, forms: Seq<Form>, at: usize) -> Seq<u8> {
    let span = form_span(forms[at as int]);
    source.spec_bytes()[span.start as int..span.end as int]
}

spec fn simple_operand(source: &str, forms: Seq<Form>, at: usize) -> Option<SimpleOperandSyntax> {
    if at >= forms.len() {
        None
    } else if forms[at as int] matches Form::Atom { kind: AtomKind::Name, .. } {
        Some(SimpleOperandSyntax::Signal(at))
    } else if forms[at as int] matches Form::Atom { kind: AtomKind::Natural, .. } {
        let word = atom_spelling(source, forms, at);
        if word == "0".spec_bytes() { Some(SimpleOperandSyntax::Bit { at, value: false }) }
        else if word == "1".spec_bytes() { Some(SimpleOperandSyntax::Bit { at, value: true }) }
        else { None }
    } else {
        None
    }
}

pub(super) closed spec fn simple_rhs(source: &str, forms: Seq<Form>, range: Range<usize>) -> Option<SimpleRhsSyntax> {
    let root = range.start;
    let head = (root + 1) as usize;
    if !(root < range.end <= forms.len()) {
        None
    } else if range.end == root + 1 {
        match simple_operand(source, forms, root) {
            Some(operand) => Some(SimpleRhsSyntax::Leaf(operand)),
            None => None,
        }
    } else if range.end == root + 4
        && (forms[root as int] matches Form::List { end, .. } && end == range.end)
        && (forms[head as int] matches Form::Atom { kind: AtomKind::Name, .. })
        && atom_spelling(source, forms, head) == "nor".spec_bytes()
    {
        match (simple_operand(source, forms, (root + 2) as usize), simple_operand(source, forms, (root + 3) as usize)) {
            (Some(left), Some(right)) => Some(SimpleRhsSyntax::Nor { callee: head, left, right }),
            _ => None,
        }
    } else {
        None
    }
}

pub(super) open spec fn simple_operand_uses_atom(forms: Seq<Form>, operand: SimpleOperandSyntax) -> bool {
    match operand {
        SimpleOperandSyntax::Signal(i) => i < forms.len()
            && (forms[i as int] matches Form::Atom { kind: AtomKind::Name, .. }),
        SimpleOperandSyntax::Bit { at, .. } => at < forms.len()
            && (forms[at as int] matches Form::Atom { kind: AtomKind::Natural, .. }),
    }
}

pub(super) proof fn simple_rhs_sites(
    source: &str, forms: Seq<Form>, range: Range<usize>, rhs: SimpleRhsSyntax,
)
    requires simple_rhs(source, forms, range) == Some(rhs),
    ensures
        range.start < range.end <= forms.len(),
        match rhs {
            SimpleRhsSyntax::Leaf(operand) => simple_operand_uses_atom(forms, operand),
            SimpleRhsSyntax::Nor { callee, left, right } =>
                callee == range.start + 1 && callee < forms.len()
                    && (forms[callee as int] matches Form::Atom { kind: AtomKind::Name, .. })
                    && source.spec_bytes()[form_span(forms[callee as int]).start as int
                        ..form_span(forms[callee as int]).end as int] == "nor".spec_bytes()
                    && simple_operand_uses_atom(forms, left) && simple_operand_uses_atom(forms, right),
        },
{}

fn read_simple_operand(source: &str, forms: &[Form], at: usize) -> (operand: Option<SimpleOperandSyntax>)
    requires form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures operand == simple_operand(source, forms@, at),
{
    match forms.get(at) {
        Some(Form::Atom { kind: AtomKind::Name, .. }) => Some(SimpleOperandSyntax::Signal(at)),
        Some(Form::Atom { kind: AtomKind::Natural, .. }) => {
            let (word, _) = read_indexed_atom(source, forms, at);
            proof {
                vstd::utf8::encode_utf8_decode_utf8(word@);
                vstd::utf8::encode_utf8_decode_utf8("0"@);
                vstd::utf8::encode_utf8_decode_utf8("1"@);
            }
            if word == "0" { Some(SimpleOperandSyntax::Bit { at, value: false }) }
            else if word == "1" { Some(SimpleOperandSyntax::Bit { at, value: true }) }
            else { None }
        },
        _ => None,
    }
}

pub(super) fn read_simple_rhs(source: &str, forms: &[Form], range: Range<usize>) -> (outcome: Option<SimpleRhsSyntax>)
    requires form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures outcome == simple_rhs(source, forms@, range),
{
    let root = range.start;
    if root >= range.end || range.end > forms.len() { return None; }
    if range.end - root == 1 {
        return match read_simple_operand(source, forms, root) {
            Some(operand) => Some(SimpleRhsSyntax::Leaf(operand)),
            None => None,
        };
    }
    if range.end - root != 4 { return None; }
    let Form::List { end, .. } = &forms[root] else { return None; };
    if *end != range.end || !matches!(forms[root + 1], Form::Atom { kind: AtomKind::Name, .. }) { return None; }
    let (word, _) = read_indexed_atom(source, forms, root + 1);
    proof {
        vstd::utf8::encode_utf8_decode_utf8(word@);
        vstd::utf8::encode_utf8_decode_utf8("nor"@);
    }
    if word != "nor" { return None; }
    let left = read_simple_operand(source, forms, root + 2)?;
    let right = read_simple_operand(source, forms, root + 3)?;
    Some(SimpleRhsSyntax::Nor { callee: root + 1, left, right })
}

} // verus!
