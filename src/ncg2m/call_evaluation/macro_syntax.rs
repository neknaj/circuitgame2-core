//! 展開に挿入する実引数の構文木を、元の添字とスコープを保って走査する。

use alloc::vec::Vec;
use core::ops::Range;
use crate::project::MacroArgument;
use crate::syntax::{
    Form,
    circuit::{GeneratedDefinition, GeneratedDefinitionError, check_generated_definition_in},
};
use super::{
    macro_binding::BoundMacroCall,
    macro_expansion::{MacroExpandedBody, MacroExpandedElement},
};
#[cfg(verus_only)]
use crate::syntax::{
    nested_list_indices,
    circuit::{generated_definition_in_error, generated_definition_in_matches, generated_definition_in_sites,
        generated_definition_in_valid},
};
use vstd::prelude::*;

mod materialize;
pub use materialize::{CheckedTemplateDefinition, TemplateDefinitionDiagnostic, TemplateDefinitionError};
#[cfg(verus_only)]
pub use materialize::{
    TemplateProjectionModel, first_diagnostic_anchor, is_diagnostic_anchor, projected_definition_finish_matches,
    projected_definition_related,
    projected_event_bytes, projected_event_step, projected_form_has_origin, projection_diagnostic_span,
    template_definition_check_matches, template_projection_continue, template_projection_matches,
    template_projection_prefix, template_projection_trace_result,
};
mod projection;
pub use projection::{
    MacroSyntaxEvent, MacroSyntaxOrigin, MacroTemplateSyntax, MacroTemplateSyntaxError, MacroTemplateSyntaxStep,
};
#[cfg(verus_only)]
pub use projection::{
    completed_macro_template_syntax_consumed, macro_template_syntax_continue_observations,
    macro_template_syntax_source_error_in_part, macro_template_syntax_starts_at,
    macro_template_syntax_step_matches, syntax_event_in_source, syntax_token_matches_forms,
};

verus! {

/// 一つの実引数の構文木を開き括弧、アトム、閉じ括弧の順にたどる項目。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ArgumentSyntaxToken {
    /// 元の構文木のアトムを指す添字。
    Atom(usize),
    /// 元の構文木のリストを開く。添字はリストの根を指す。
    Open(usize),
    /// 直前に開いたリストを閉じる。添字は対応するリストの根を指す。
    Close(usize),
}

/// 元の部分木を借り、入れ子の終わりを一つずつ処理する。
pub struct ArgumentSyntax<'b, 'p, 'a> {
    argument: &'b MacroArgument<'p, 'a>,
    at: usize,
    open: Vec<Range<usize>>,
}

impl<'p, 'a> MacroArgument<'p, 'a> {
    /// 元の引数の先頭から構文を走査する。
    ///
    /// 元の文書版やスコープは引数に残る。引数の中にある綴りは構文としてそのまま通す。
    pub fn walk_syntax<'b>(&'b self) -> (walker: ArgumentSyntax<'b, 'p, 'a>)
        requires self.valid(),
        ensures walker.valid(), walker.argument_model() == self,
            walker.at_model() == self.nodes_model().start && walker.open_model().len() == 0,
    {
        ArgumentSyntax { argument: self, at: self.nodes().start, open: Vec::new() }
    }
}

impl<'b, 'p, 'a> ArgumentSyntax<'b, 'p, 'a> {
    /// 走査対象の実引数を表す。
    pub closed spec fn argument_model(&self) -> &'b MacroArgument<'p, 'a> { self.argument }

    /// 次に開くリストまたは返すアトムの添字を表す。
    pub closed spec fn at_model(&self) -> usize { self.at }

    /// 開いたリストの根と部分木の末尾を外側から順に表す。
    pub closed spec fn open_model(&self) -> Seq<Range<usize>> { self.open@ }

    /// 次の位置と開いたリストが、引数の部分木に収まることを表す。
    pub closed spec fn valid(&self) -> bool {
        let argument = self.argument_model();
        let nodes = argument.nodes_model();
        let forms = argument.forms_model();
        let at = self.at_model();
        let open = self.open_model();
        &&& argument.valid()
        &&& nodes.start <= at <= nodes.end
        &&& forall|i: int| 0 <= i < open.len() ==> {
            let r = #[trigger] open[i];
            &&& nodes.start <= r.start < at <= r.end <= nodes.end
            &&& forms[r.start as int] is List && forms[r.start as int]->List_end == r.end
        }
        &&& forall|i: int, j: int| 0 <= i < j < open.len() ==> {
            let a = #[trigger] open[i];
            let b = #[trigger] open[j];
            a.start < b.start && b.end <= a.end
        }
    }

    /// まだ読んでいないフォームと、今後閉じるリストの個数から遷移数を上から押さえる。
    pub open spec fn remaining_bound(&self) -> nat {
        (2 * (self.argument_model().nodes_model().end - self.at_model()) + self.open_model().len()) as nat
    }

    /// 添字が指す構文木、元ソース、識別子のスコープを持つ引数を返す。
    pub fn argument(&self) -> (argument: &'b MacroArgument<'p, 'a>)
        ensures argument == self.argument_model(),
    {
        self.argument
    }

    /// 構文の項目を一つ返す。引数の部分木を閉じ終わったら `None` を返す。
    ///
    /// 元のテンプレートと異なり、実引数内のリストを挿入式として評価しない。
    pub fn next(&mut self) -> (item: Option<ArgumentSyntaxToken>)
        requires old(self).valid(),
        ensures final(self).valid(), argument_syntax_step(old(self), final(self), item),
            item.is_none() <==> old(self).remaining_bound() == 0,
            item.is_some() ==> final(self).remaining_bound() < old(self).remaining_bound(),
    {
        let argument = self.argument;
        let forms = argument.forms();
        let stop = argument.nodes().end;
        let at = self.at;
        let ghost open = self.open@;
        if let Some(top) = self.open.last() {
            if top.end == at {
                let top = self.open.pop().unwrap();
                return Some(ArgumentSyntaxToken::Close(top.start));
            }
        }
        assert forall|i: int| 0 <= i < open.len() implies
            at < (#[trigger] open[i]).end by {
            if i < open.len() - 1 {
                assert(open.last().end <= open[i].end);
            }
        };
        if at == stop {
            assert(open.len() == 0);
            return None;
        }
        match &forms[at] {
            Form::Atom { .. } => {
                self.at = at + 1;
                Some(ArgumentSyntaxToken::Atom(at))
            },
            Form::List { end, .. } => {
                let end = *end;
                proof {
                    let root = argument.nodes_model().start;
                    reveal(nested_list_indices);
                    if root < at {
                        assert(forms@[root as int] is List && forms@[root as int]->List_end == stop);
                        assert(end <= stop);
                    }
                    assert forall|i: int| 0 <= i < open.len() implies
                        end <= (#[trigger] open[i]).end by {
                        let parent = open[i].start as int;
                        assert(parent < at < forms@[parent]->List_end);
                    };
                }
                self.open.push(at..end);
                self.at = at + 1;
                Some(ArgumentSyntaxToken::Open(at))
            },
        }
    }
}

/// 元のリスト階層と添字から、次に返す項目と続きの位置を定める。
pub open spec fn argument_syntax_step<'b, 'p, 'a>(
    before: &ArgumentSyntax<'b, 'p, 'a>, after: &ArgumentSyntax<'b, 'p, 'a>,
    item: Option<ArgumentSyntaxToken>,
) -> bool {
    let arg = before.argument_model();
    let at = before.at_model();
    let open = before.open_model();
    &&& after.argument_model() == arg
    &&& if open.len() > 0 && open.last().end == at {
        &&& item == Some(ArgumentSyntaxToken::Close(open.last().start))
        &&& after.at_model() == at
        &&& after.open_model() == open.drop_last()
    } else if at == arg.nodes_model().end {
        &&& item.is_none()
        &&& after.at_model() == at && after.open_model() == open
    } else {
        &&& after.at_model() == at + 1
        &&& match arg.forms_model()[at as int] {
            Form::Atom { .. } => item == Some(ArgumentSyntaxToken::Atom(at)) && after.open_model() == open,
            Form::List { end, .. } => item == Some(ArgumentSyntaxToken::Open(at))
                && after.open_model() == open.push(at..end),
        }
    }
}

/// 直接返された実引数を回路文法で検査した定義。
///
/// 添字と参照範囲は、元の引数と同じ構文木・文書版で解釈する。
#[derive(Debug)]
pub struct CheckedArgumentDefinition<'b, 'p, 'a> {
    argument: &'b MacroArgument<'p, 'a>,
    row: GeneratedDefinition,
}

impl<'b, 'p, 'a> CheckedArgumentDefinition<'b, 'p, 'a> {
    /// 定義を提供した実引数を表す。
    pub closed spec fn argument_model(&self) -> &'b MacroArgument<'p, 'a> { self.argument }

    /// 実引数の構文木上で検査した定義を表す。
    pub closed spec fn row_model(&self) -> GeneratedDefinition { self.row }

    /// 定義の構文木、元ソースと呼び出し側のスコープを持つ実引数を返す。
    pub fn argument(&self) -> (argument: &'b MacroArgument<'p, 'a>)
        ensures argument == self.argument_model(),
    {
        self.argument
    }

    /// 左辺、右辺、回路名、型名、信号名の元の添字を借りる。
    pub fn row(&self) -> (row: &GeneratedDefinition)
        ensures *row == self.row_model(),
    {
        &self.row
    }
}

/// 回路文法で拒否された実引数と、診断の主範囲を持つ展開呼び出し。
#[derive(Debug)]
pub struct ArgumentDefinitionDiagnostic<'b, 'p, 'a> {
    /// 主範囲と文書版を含む呼び出しの出典。
    pub call: &'b BoundMacroCall<'p, 'a>,
    /// 元の構文木、文書版と名前解決のスコープを持つ実引数。
    pub argument: &'b MacroArgument<'p, 'a>,
    /// 展開結果のリスト内で拒否した要素の添字。
    pub element: usize,
    /// 種別と元の実引数の文書上の関連範囲を持つ回路構文診断。
    pub kind: GeneratedDefinitionError,
}

/// 回路文法の検査結果が、実引数の元の範囲とスコープに対応することを表す。
pub open spec fn argument_definition_matches<'b, 'p, 'a>(
    argument: &'b MacroArgument<'p, 'a>,
    result: Result<CheckedArgumentDefinition<'b, 'p, 'a>, GeneratedDefinitionError>,
) -> bool {
    let source = argument.scope_model().source.text_model();
    let forms = argument.forms_model();
    let nodes = argument.nodes_model();
    &&& result.is_ok() == generated_definition_in_valid(source, forms, nodes)
    &&& match result {
        Ok(checked) => checked.argument_model() == argument
            && generated_definition_in_matches(source, forms, nodes, checked.row_model())
            && generated_definition_in_sites(source, forms, nodes, checked.row_model()),
        Err(error) => generated_definition_in_error(source, forms, nodes, error),
    }
}

impl<'p, 'a> MacroArgument<'p, 'a> {
    /// 実引数の部分木を一つの回路定義として検査する。
    ///
    /// 検査後も添字は元の構文木を指し、診断の範囲は元の文書上にある。
    ///
    /// # Errors
    ///
    /// 実引数が有効な `def` に当たらなければ、元範囲を含む最初の構文診断を返す。
    pub fn check_definition<'b>(&'b self)
        -> (result: Result<CheckedArgumentDefinition<'b, 'p, 'a>, GeneratedDefinitionError>)
        ensures argument_definition_matches(self, result),
    {
        let source = self.scope().source.text();
        let forms = self.forms();
        let row = check_generated_definition_in(source, forms, self.nodes())?;
        Ok(CheckedArgumentDefinition { argument: self, row })
    }
}

/// 展開結果の指定要素が直接返した実引数なら、その検査結果を元の出典と結び付ける。
pub open spec fn expanded_argument_definition_matches<'b, 'p, 'a>(
    body: &MacroExpandedBody<'b, 'p, 'a>, element: usize,
    result: Option<Result<CheckedArgumentDefinition<'b, 'p, 'a>, ArgumentDefinitionDiagnostic<'b, 'p, 'a>>>,
) -> bool {
    let elements = body.elements_model();
    if element >= elements.len() {
        result.is_none()
    } else if let MacroExpandedElement::Argument(argument) = elements[element as int] {
        match result {
            Some(Ok(row)) => argument_definition_matches(argument, Ok(row)),
            Some(Err(error)) => error.call == body.call_model() && error.argument == argument
                && error.element == element && argument_definition_matches(argument, Err(error.kind)),
            None => false,
        }
    } else {
        result.is_none()
    }
}

impl<'b, 'p, 'a> MacroExpandedBody<'b, 'p, 'a> {
    /// 指定要素が直接返した実引数なら、元の構文木のまま `def` を検査する。
    ///
    /// 要素番号が範囲外か、要素がテンプレート由来なら `None` を返す。
    ///
    /// # Errors
    ///
    /// 回路文法に違反した場合、主範囲を持つ展開呼び出しと、関連範囲を持つ実引数の診断を返す。
    pub fn check_argument_definition(&self, element: usize)
        -> (result: Option<Result<CheckedArgumentDefinition<'b, 'p, 'a>, ArgumentDefinitionDiagnostic<'b, 'p, 'a>>>)
        ensures expanded_argument_definition_matches(self, element, result),
    {
        let MacroExpandedElement::Argument(argument) = self.elements().get(element)? else {
            return None;
        };
        let argument = *argument;
        Some(match argument.check_definition() {
            Ok(row) => Ok(row),
            Err(kind) => Err(ArgumentDefinitionDiagnostic { call: self.call(), argument, element, kind }),
        })
    }
}

} // verus!
