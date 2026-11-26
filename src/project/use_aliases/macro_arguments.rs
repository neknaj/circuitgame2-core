//! マクロ実引数の構文を、呼び出し元のスコープと文書版を保ったまま借りる。

use core::ops::Range;
use crate::project::ProjectSource;
use crate::syntax::{Form, circuit::next_call_argument};
#[cfg(verus_only)]
use crate::syntax::{complete_list_indices, form_spans_valid, nested_list_indices,
    circuit::{call_argument_sequence, exhausted_call_arguments, expression_region}};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 構文の出典と、その識別子を読むときに使う回路本体のスコープ。
#[derive(Clone, Copy, Debug)]
pub struct MacroArgumentScope<'p, 'a> {
    /// 呼び出し元の文書とその版。
    pub source: &'p ProjectSource<'a>,
    /// プロジェクト内のファイルの添字。
    pub file: usize,
    /// 回路フォームの索引で本体を指す添字。
    pub entry: usize,
}

/// マクロの仮引数に束縛する、呼び出し元の構文オブジェクト。
#[derive(Debug)]
pub struct MacroArgument<'p, 'a> {
    scope: MacroArgumentScope<'p, 'a>,
    forms: &'p [Form],
    nodes: Range<usize>,
}

impl<'p, 'a> MacroArgument<'p, 'a> {
    /// 元ソースと、引数に含まれる名前を解決するスコープを表す。
    pub closed spec fn scope_model(&self) -> MacroArgumentScope<'p, 'a> { self.scope }

    /// 呼び出し元の平坦な構文木を表す。
    pub closed spec fn forms_model(&self) -> Seq<Form> { self.forms@ }

    /// 引数の部分木が占める半開区間を表す。
    pub closed spec fn nodes_model(&self) -> Range<usize> { self.nodes }

    /// 元文書の版を含む呼び出し元のスコープを返す。
    pub fn scope(&self) -> (scope: MacroArgumentScope<'p, 'a>)
        ensures scope == self.scope_model(),
    {
        self.scope
    }

    /// 引数と同じ元の平坦な構文木を借りる。
    pub fn forms(&self) -> (forms: &'p [Form])
        ensures forms@ == self.forms_model(),
    {
        self.forms
    }

    /// 一つの実引数の部分木が占める半開区間を返す。
    pub fn nodes(&self) -> (nodes: Range<usize>)
        ensures nodes == self.nodes_model(),
    {
        self.nodes.start..self.nodes.end
    }
}

/// 検査済みのマクロ呼び出しから実引数を左から右へ取り出す。
pub struct MacroArguments<'p, 'a> {
    scope: MacroArgumentScope<'p, 'a>,
    forms: &'p [Form],
    remaining: Range<usize>,
    count: usize,
}

impl<'p, 'a> MacroArguments<'p, 'a> {
    /// 引数の出典と回路内でのスコープを表す。
    pub closed spec fn scope_model(&self) -> MacroArgumentScope<'p, 'a> { self.scope }

    /// 元の構文木を表す。
    pub closed spec fn forms_model(&self) -> Seq<Form> { self.forms@ }

    /// まだ取り出していない引数の構文木範囲を表す。
    pub closed spec fn remaining_model(&self) -> Range<usize> { self.remaining }

    /// 残りの引数の個数を表す。
    pub closed spec fn count_model(&self) -> usize { self.count }

    /// 残りの範囲が、妥当な同じ構文木内の引数列に対応する。
    pub closed spec fn valid(&self) -> bool {
        let source = self.scope.source.text_model();
        &&& complete_list_indices(self.forms@) && nested_list_indices(self.forms@)
        &&& form_spans_valid(source, self.forms@, source.spec_bytes().len() as int)
        &&& expression_region(self.forms@, self.remaining.start as int, self.remaining.end as int)
        &&& call_argument_sequence(self.forms@, self.remaining, self.count as int)
    }

    // 呼び出し側で検査した引数範囲と個数をそのまま保持する。
    pub(super) fn from_checked_site(
        scope: MacroArgumentScope<'p, 'a>, forms: &'p [Form], remaining: Range<usize>, count: usize,
    ) -> (arguments: Self)
        requires
            complete_list_indices(forms@), nested_list_indices(forms@),
            form_spans_valid(scope.source.text_model(), forms@,
                scope.source.text_model().spec_bytes().len() as int),
            expression_region(forms@, remaining.start as int, remaining.end as int),
            call_argument_sequence(forms@, remaining, count as int),
        ensures arguments.valid(), arguments.scope_model() == scope,
            arguments.forms_model() == forms@, arguments.remaining_model() == remaining,
            arguments.count_model() == count,
    {
        Self { scope, forms, remaining, count }
    }

    /// まだ読んでいない範囲が、元の構文木の内側にあることを示す。
    pub proof fn remaining_bounds(&self)
        requires self.valid(),
        ensures self.remaining_model().start <= self.remaining_model().end <= self.forms_model().len(),
    {
        reveal(expression_region);
    }

    /// まだ引数が残っていない場合も、呼び出し元のスコープを返す。
    pub fn scope(&self) -> (scope: MacroArgumentScope<'p, 'a>)
        ensures scope == self.scope_model(),
    {
        self.scope
    }

    /// まだ取り出していない引数の個数を返す。
    pub fn remaining_count(&self) -> (count: usize)
        ensures count == self.count_model(),
    {
        self.count
    }

    /// 次の引数全体を、元の構文木から借りる。
    ///
    /// リストは入れ子を含めて一つの引数として返す。範囲の末尾から次の走査を続ける。
    pub fn next_argument(&mut self) -> (argument: Option<MacroArgument<'p, 'a>>)
        requires old(self).valid(),
        ensures
            final(self).valid(), final(self).scope_model() == old(self).scope_model(),
            final(self).forms_model() == old(self).forms_model(),
            final(self).remaining_model().end == old(self).remaining_model().end,
            argument.is_none() <==> old(self).count_model() == 0,
            match argument {
                None => final(self).remaining_model() == old(self).remaining_model()
                    && final(self).remaining_model().start == final(self).remaining_model().end
                    && final(self).count_model() == 0,
                Some(argument) => {
                    let files = old(self).forms_model();
                    let nodes = argument.nodes_model();
                    let start = nodes.start as int;
                    let source = argument.scope_model().source.text_model();
                    &&& argument.scope_model() == old(self).scope_model() && argument.forms_model() == files
                    &&& complete_list_indices(files) && nested_list_indices(files)
                    &&& form_spans_valid(source, files, source.spec_bytes().len() as int)
                    &&& nodes.start == old(self).remaining_model().start
                    &&& start < nodes.end <= old(self).remaining_model().end <= files.len()
                    &&& nodes.end == match files[start] {
                        Form::Atom { .. } => start + 1,
                        Form::List { end, .. } => end as int,
                    }
                    &&& final(self).remaining_model().start == nodes.end
                    &&& final(self).count_model() + 1 == old(self).count_model()
                },
            },
    {
        proof { reveal(expression_region); }
        let remaining = self.remaining.start..self.remaining.end;
        let ghost before = remaining;
        let Some(nodes) = next_call_argument(self.forms, remaining) else {
            proof { exhausted_call_arguments(self.forms@, before, self.count as int); }
            return None;
        };
        self.remaining.start = nodes.end;
        self.count -= 1;
        Some(MacroArgument { scope: self.scope, forms: self.forms, nodes })
    }
}

} // verus!
