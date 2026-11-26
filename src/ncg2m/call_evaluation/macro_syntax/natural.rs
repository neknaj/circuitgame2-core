//! 呼び出し元の構文を借りたまま `syntax-nat` の自然数を読み取る。

use crate::ncg2m::forms::source_word;
use crate::project::{LocatedName, MacroArgument};
use crate::syntax::{AtomKind, Form, NaturalRangeError, NaturalReadStep, NaturalReader};
#[cfg(verus_only)]
use crate::syntax::{
    decimal_natural_value, form_span, form_spans_valid, natural_atom_has_value, natural_digits,
    natural_read_step_matches, natural_u64_matches,
};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::{string::StringSliceAdditionalSpecFns, utf8::is_char_boundary};

verus! {

/// `syntax-nat` が呼び出し元の構文を自然数として扱えなかった理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MacroNaturalError {
    /// 非負の十進リテラルが必要な位置に別の構文がある。
    ExpectedNatural,
    /// リテラルの値が `Nat` の表現範囲を超える。
    OutOfRange,
}

/// `syntax-nat` の失敗種別と、判定の根拠となった実引数の位置。
#[derive(Debug)]
pub struct MacroNaturalDiagnostic<'p, 'a> {
    /// 構文の形または自然数の範囲に関する診断種別。
    pub kind: MacroNaturalError,
    /// 実引数を渡した元の文書版と、部分木全体の UTF-8 半開バイト範囲。
    pub location: LocatedName<'p, 'a>,
}

/// 元の実引数と、十進リテラルの次の桁を保持する。
pub struct MacroNatural<'b, 'p, 'a> {
    argument: &'b MacroArgument<'p, 'a>,
    reader: NaturalReader<'a>,
}

/// 実引数の自然数を一歩評価した結果。
pub enum MacroNaturalStep<'b, 'p, 'a> {
    /// 元の字句が表す `Nat` の値。
    Done(u64),
    /// 次の桁または字句の末尾から処理する状態。
    Continue(MacroNatural<'b, 'p, 'a>),
}

/// 実引数の根が非負の十進リテラルであることを表す。
pub open spec fn syntax_nat_argument_is_natural(argument: &MacroArgument) -> bool {
    argument.forms_model()[argument.nodes_model().start as int] is Atom
        && argument.forms_model()[argument.nodes_model().start as int]->Atom_kind == AtomKind::Natural
}

/// `syntax-nat` が調べる元の実引数のバイト列を表す。
pub open spec fn syntax_nat_argument_bytes(argument: &MacroArgument) -> Seq<u8> {
    let span = form_span(argument.forms_model()[argument.nodes_model().start as int]);
    argument.scope_model().source.text_model().spec_bytes()[span.start as int..span.end as int]
}

/// 診断の種別と位置が、同じ実引数の部分木に対応することを表す。
pub open spec fn macro_natural_error_at_argument(
    argument: &MacroArgument, diagnostic: MacroNaturalDiagnostic, kind: MacroNaturalError,
) -> bool {
    let span = form_span(argument.forms_model()[argument.nodes_model().start as int]);
    let bytes = argument.scope_model().source.text_model().spec_bytes();
    &&& diagnostic.kind == kind
    &&& diagnostic.location.source == argument.scope_model().source
    &&& diagnostic.location.span == span
    &&& span.start < span.end <= bytes.len()
    &&& is_char_boundary(bytes, span.start as int) && is_char_boundary(bytes, span.end as int)
}

impl<'p, 'a> MacroArgument<'p, 'a> {
    /// 元の部分木を使って `syntax-nat` の判定を始める。
    ///
    /// `step` ごとに十進数字を最大一桁消費する。先頭の 0 を許す。
    ///
    /// # Errors
    ///
    /// 根が非負の十進リテラル以外の場合は `ExpectedNatural` を返す。
    pub fn start_syntax_nat<'b>(&'b self) -> (result: Result<MacroNatural<'b, 'p, 'a>, MacroNaturalDiagnostic<'p, 'a>>)
        ensures
            self.valid(),
            match result {
                Ok(reading) => syntax_nat_argument_is_natural(self)
                    && natural_digits(syntax_nat_argument_bytes(self))
                    && reading.valid() && reading.argument_model() == self && reading.position_model() == 0,
                Err(diagnostic) => !syntax_nat_argument_is_natural(self)
                    && macro_natural_error_at_argument(self, diagnostic, MacroNaturalError::ExpectedNatural),
            },
    {
        let forms = self.forms();
        let at = self.nodes().start;
        let Form::Atom { kind: AtomKind::Natural, .. } = &forms[at] else {
            return Err(argument_diagnostic(self, MacroNaturalError::ExpectedNatural));
        };
        let source = self.scope().source.text();
        let word = source_word(source, forms, at);
        proof {
            reveal(form_spans_valid);
            assert(crate::syntax::form_atom_matches(source, forms@[at as int]));
            natural_atom_has_value(word.spec_bytes());
        }
        Ok(MacroNatural { argument: self, reader: NaturalReader::new(word) })
    }
}

fn argument_diagnostic<'p, 'a>(
    argument: &MacroArgument<'p, 'a>, kind: MacroNaturalError,
) -> (diagnostic: MacroNaturalDiagnostic<'p, 'a>)
    ensures macro_natural_error_at_argument(argument, diagnostic, kind),
{
    let forms = argument.forms();
    let at = argument.nodes().start;
    let span = match &forms[at] {
        Form::Atom { span, .. } | Form::List { span, .. } => span,
    };
    proof {
        reveal(form_spans_valid);
        assert(*span == form_span(forms@[at as int]));
    }
    MacroNaturalDiagnostic {
        kind, location: LocatedName { source: argument.scope().source, span: span.start..span.end },
    }
}

impl<'b, 'p, 'a> MacroNatural<'b, 'p, 'a> {
    /// 走査する実引数を表す。
    pub closed spec fn argument_model(&self) -> &'b MacroArgument<'p, 'a> { self.argument }

    /// 実引数の字句内で次に読むバイトの添字を表す。
    pub closed spec fn position_model(&self) -> usize { self.reader.position_model() }

    /// 読み取り状態と実引数が同じ字句を指すことを表す。
    pub closed spec fn valid(&self) -> bool {
        let bytes = syntax_nat_argument_bytes(self.argument);
        self.argument.valid() && syntax_nat_argument_is_natural(self.argument)
            && self.reader.valid() && self.reader.bytes_model() == bytes
            && self.position_model() <= bytes.len()
            && natural_digits(bytes) && decimal_natural_value(bytes).is_some()
    }

    #[verifier::type_invariant]
    spec fn invariant(&self) -> bool { self.valid() }

    /// 次の桁を読み取るか、字句の末尾で自然数を確定する。
    ///
    /// # Errors
    ///
    /// 値が `Nat` の範囲を超える場合は、末尾で元の実引数の範囲を返す。
    pub fn step(self) -> (result: Result<MacroNaturalStep<'b, 'p, 'a>, MacroNaturalDiagnostic<'p, 'a>>)
        ensures macro_natural_step_matches(&self, result),
    {
        proof { use_type_invariant(&self); }
        let argument = self.argument;
        proof {
            let bytes = syntax_nat_argument_bytes(argument);
            let at = self.position_model() as int;
            if at < bytes.len() {
                assert(b'0' <= bytes[at] <= b'9');
            }
        }
        match self.reader.step() {
            Ok(NaturalReadStep::Done(value)) => Ok(MacroNaturalStep::Done(value)),
            Ok(NaturalReadStep::Continue(reader)) => Ok(MacroNaturalStep::Continue(Self { argument, reader })),
            Err(NaturalRangeError::InvalidDigits) => Err(argument_diagnostic(argument, MacroNaturalError::ExpectedNatural)),
            Err(NaturalRangeError::OutOfRange) => Err(argument_diagnostic(argument, MacroNaturalError::OutOfRange)),
        }
    }
}

/// 一桁分の遷移と、元の実引数から確定する値または診断との関係を表す。
pub open spec fn macro_natural_step_matches(
    before: &MacroNatural, result: Result<MacroNaturalStep, MacroNaturalDiagnostic>,
) -> bool {
    let argument = before.argument_model();
    let bytes = syntax_nat_argument_bytes(argument);
    let at = before.position_model() as int;
    &&& before.valid()
    &&& at <= bytes.len()
    &&& if at < bytes.len() {
        result matches Ok(MacroNaturalStep::Continue(after))
            && after.valid() && after.argument_model() == argument && after.position_model() == at + 1
    } else {
        match result {
            Ok(MacroNaturalStep::Done(value)) => at == bytes.len() && natural_u64_matches(bytes, Ok(value)),
            Err(diagnostic) => natural_u64_matches(bytes, Err(NaturalRangeError::OutOfRange))
                && macro_natural_error_at_argument(argument, diagnostic, MacroNaturalError::OutOfRange),
            _ => false,
        }
    }
}

} // verus!
