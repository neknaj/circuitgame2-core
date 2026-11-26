//! 回路本体に書いた展開呼び出しを、元の構文を保ったままマクロ定義へ結び付ける。

use super::{DefmacroNameError, MacroArgumentScope, MacroArguments, MixedUseAliases, ResolvedDefmacro};
use crate::ncg2m::{
    call_evaluation::macro_binding::{BoundMacroCall, bind_macro_call},
    expression_types::MacroBodyError,
};
#[cfg(verus_only)]
use crate::ncg2m::{
    call_evaluation::macro_binding::macro_arguments_cover,
    expression_types::defmacro_body_check,
};
#[cfg(verus_only)]
use super::indexed_defmacro_is_retained;
use crate::project::{ProjectSource, ProjectSourceIndex, circuits::read_source_span};
use crate::syntax::circuit::{
    CircuitForms, RoutineExpansionSite, RoutineExpansionSites, call_argument_count, routine_expansion_sites,
};
#[cfg(verus_only)]
use super::{defmacro_name_resolution, has_macro_caller, indexed_defmacro, macro_reference_declaration};
#[cfg(verus_only)]
use crate::project::{
    MixedFuncCalleeError, circuits::parsed_index_evidence, mixed_use_targets_match, source_indexes::project_source_index_evidence,
};
#[cfg(verus_only)]
use crate::syntax::{
    complete_list_indices,
    circuit::{call_argument_sequence, routine_expansion_sites_match},
};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::{string::StringSliceAdditionalSpecFns, utf8::is_char_boundary};

verus! {

/// 展開呼び出しを評価の入口へ渡す前に分かった診断。
#[derive(Debug)]
pub enum MacroCallError<'p, 'a> {
    /// 呼び出し先の名前を解決できない。
    Name(DefmacroNameError<'p, 'a>),
    /// 実引数の数が仮引数の数と異なる。
    Arity {
        /// マクロの元宣言と仮引数。関連診断に使える。
        definition: ResolvedDefmacro<'p, 'a>,
        /// 呼び出し元の構文木で数えた実引数の個数。
        actual: usize,
    },
}

/// 元の展開呼び出しと、評価に使うマクロの宣言または診断。
#[derive(Debug)]
pub struct MacroCall<'p, 'a> {
    /// 呼び出し位置、名前、引数を指す元の構文木範囲。
    pub site: RoutineExpansionSite,
    /// 引数の個数まで検査した宣言、または最初の診断。
    pub target: Result<ResolvedDefmacro<'p, 'a>, MacroCallError<'p, 'a>>,
}

/// 展開呼び出しを名前解決または型検査できなかった最初の理由。
#[derive(Debug)]
pub struct MacroPreparationError<'p, 'a> {
    /// 診断の対象になった元の展開呼び出し。
    pub site: RoutineExpansionSite,
    /// 呼び出しまたは本体の診断。
    pub kind: MacroPreparationFailure<'p, 'a>,
}

/// 展開に必要な検査が失敗した段階。
#[derive(Debug)]
pub enum MacroPreparationFailure<'p, 'a> {
    /// 呼び出し名の解決または引数個数の検査で失敗した。
    Call(MacroCallError<'p, 'a>),
    /// 解決先のマクロ本体の型検査で失敗したか、検査を保留した。
    Body {
        /// 診断の範囲が対応する元宣言。
        definition: ResolvedDefmacro<'p, 'a>,
        /// 本体の構造、型違反、または保留の理由。
        error: MacroBodyError<'a>,
    },
}

/// 一つの回路本体について、展開呼び出しと名前解決を元ソース順に進める。
pub struct MacroCalls<'r, 't, 'p, 'a> {
    aliases: &'r MixedUseAliases<'t, 'p, 'a>,
    file: usize,
    entry: usize,
    source: &'p ProjectSource<'a>,
    sites: RoutineExpansionSites<'p>,
}

impl<'r, 't, 'p, 'a> MacroCalls<'r, 't, 'p, 'a> {
    /// 参照に使う別名表を表す。
    pub closed spec fn aliases_model(&self) -> &MixedUseAliases<'t, 'p, 'a> { self.aliases }

    /// 元プロジェクト内のファイルと回路フォームの添字を表す。
    pub closed spec fn origin_model(&self) -> (usize, usize) { (self.file, self.entry) }

    /// 呼び出しの範囲と版が対応するソースを表す。
    pub closed spec fn source_model(&self) -> &ProjectSource<'a> { self.source }

    /// 元の構文木に対する走査位置を表す。
    pub closed spec fn sites_model(&self) -> RoutineExpansionSites<'p> { self.sites }

    /// 元の索引と別名表が、同じ回路本体を参照することを表す。
    pub open spec fn valid(&self) -> bool {
        let targets = self.aliases_model().targets_model();
        let project = targets.project_model();
        let origin = self.origin_model();
        let source = self.source_model();
        let sites = self.sites_model();
        &&& mixed_use_targets_match(&project, targets)
        &&& has_macro_caller(&project, origin.0, origin.1)
        &&& origin.0 < project.sources_model().len()
        &&& *source == project.sources_model()[origin.0 as int]
        &&& sites.valid()
        &&& sites.source_model() == source.text_model()
        &&& *sites.syntax_model() == project.indexes_model()[origin.0 as int]->Circuit_0.syntax
    }

    /// 正規化済みのファイル識別子と文書版を持つ呼び出し元のソースを借りる。
    pub fn source(&self) -> (source: &'p ProjectSource<'a>)
        ensures source == self.source_model(),
    {
        self.source
    }

    /// 呼び出しと引数の添字が参照する元の構文木を借りる。
    pub fn syntax(&self) -> (syntax: &'p CircuitForms)
        requires self.valid(),
        ensures syntax == self.sites_model().syntax_model(), complete_list_indices(syntax.forms@),
    {
        self.sites.syntax()
    }

    /// 走査が同じスコープで進み、次の呼び出しの検査結果を返すことを表す。
    pub open spec fn advances(&self, next: &Self, call: Option<MacroCall<'p, 'a>>) -> bool {
        &&& next.valid() && next.aliases_model() == self.aliases_model()
        &&& next.origin_model() == self.origin_model()
        &&& next.source_model() == self.source_model()
        &&& match call {
            Some(call) => self.sites_model().advances(&next.sites_model(), Some(call.site))
                && macro_call_matches(next, call)
                && macro_call_spans_in_source(next.source_model().text_model(), call.site)
                && {
                    let project = next.aliases_model().targets_model().project_model();
                    let forms = next.sites_model().syntax_model().forms@;
                    match call.target {
                        Ok(definition) => indexed_defmacro(&project, definition)
                            && call_argument_sequence(forms, call.site.arguments, definition.parameters@.len() as int),
                        Err(MacroCallError::Arity { definition, actual }) =>
                            indexed_defmacro(&project, definition) && actual != definition.parameters@.len()
                            && call_argument_sequence(forms, call.site.arguments, actual as int),
                        Err(MacroCallError::Name(DefmacroNameError::Reference(MixedFuncCalleeError::WrongDeclaration(declaration)))) =>
                            macro_reference_declaration(&project, declaration) && !(declaration.kind is Defmacro),
                        Err(MacroCallError::Name(_)) => true,
                    }
                },
            None => self.sites_model().advances(&next.sites_model(), None),
        }
    }

    /// 次の呼び出しを解決し、引数の個数も検査する。
    ///
    /// 名前解決を先に行う。診断が出た呼び出しも走査済みとなるため、次の呼び出しの検査を続けられる。
    /// 呼び出しが残っていなければ `None` を返す。
    pub fn next_call(&mut self) -> (call: Option<MacroCall<'p, 'a>>)
        requires old(self).valid(),
        ensures old(self).advances(final(self), call),
    {
        let site = self.sites.next_site()?;
        let source = self.source.text();
        let name = read_source_span(source, site.callee.start, site.callee.end);
        let resolved = self.aliases.resolve_defmacro_name(self.file, self.entry, name);
        let ghost selection = resolved;
        let target = match resolved {
            Err(error) => Err(MacroCallError::Name(error)),
            Ok(definition) => {
                let syntax = self.sites.syntax();
                let count = call_argument_count(syntax.forms.as_slice(), &site.arguments);
                assert(call_argument_sequence(syntax.forms@, site.arguments, count as int));
                if count == definition.parameters.len() {
                    Ok(definition)
                } else {
                    Err(MacroCallError::Arity { definition, actual: count })
                }
            }
        };
        let call = MacroCall { site, target };
        proof { macro_call_from_source(self, call, name, selection); }
        Some(call)
    }
}

spec fn macro_target_matches(
    forms: Seq<crate::syntax::Form>, site: RoutineExpansionSite,
    resolved: Result<ResolvedDefmacro, DefmacroNameError>, target: Result<ResolvedDefmacro, MacroCallError>,
) -> bool {
    match resolved {
        Err(error) => target == Err(MacroCallError::Name(error)),
        Ok(definition) => match target {
            Ok(found) => found == definition
                && call_argument_sequence(forms, site.arguments, definition.parameters@.len() as int),
            Err(MacroCallError::Arity { definition: found, actual }) =>
                found == definition && actual != definition.parameters@.len()
                    && call_argument_sequence(forms, site.arguments, actual as int),
            _ => false,
        },
    }
}

/// 呼び出しと参照の半開範囲が、呼び出し元の UTF-8 文字境界にあることを表す。
pub open spec fn macro_call_spans_in_source(source: &str, site: RoutineExpansionSite) -> bool {
    &&& site.span.start < site.span.end <= source.spec_bytes().len()
    &&& is_char_boundary(source.spec_bytes(), site.span.start as int)
    &&& is_char_boundary(source.spec_bytes(), site.span.end as int)
    &&& site.callee.start < site.callee.end <= source.spec_bytes().len()
    &&& is_char_boundary(source.spec_bytes(), site.callee.start as int)
    &&& is_char_boundary(source.spec_bytes(), site.callee.end as int)
}

/// 呼び出し名が元のバイト範囲から得られ、スコープと実引数の個数を使って解決されたことを表す。
pub closed spec fn macro_call_matches(calls: &MacroCalls, call: MacroCall) -> bool {
    let source = calls.source_model().text_model();
    let at = calls.origin_model();
    let callee = call.site.callee;
    exists|name: &str, resolved: Result<ResolvedDefmacro, DefmacroNameError>|
        #[trigger] defmacro_name_resolution(calls.aliases_model(), at.0, at.1, name, resolved)
            && name.spec_bytes() == source.spec_bytes()[callee.start as int..callee.end as int]
            && macro_target_matches(calls.sites_model().syntax_model().forms@, call.site, resolved, call.target)
}

proof fn macro_call_from_source(
    calls: &MacroCalls, call: MacroCall, name: &str, resolved: Result<ResolvedDefmacro, DefmacroNameError>,
)
    requires
        defmacro_name_resolution(calls.aliases_model(), calls.origin_model().0, calls.origin_model().1, name, resolved),
        name.spec_bytes() == calls.source_model().text_model().spec_bytes()
            [call.site.callee.start as int..call.site.callee.end as int],
        macro_target_matches(calls.sites_model().syntax_model().forms@, call.site, resolved, call.target),
    ensures macro_call_matches(calls, call),
{
    let at = calls.origin_model();
    let bytes = calls.source_model().text_model().spec_bytes();
    let span = call.site.callee;
    let forms = calls.sites_model().syntax_model().forms@;
    assert(exists|word: &str, target: Result<ResolvedDefmacro, DefmacroNameError>|
        #[trigger] defmacro_name_resolution(calls.aliases_model(), at.0, at.1, word, target)
            && word.spec_bytes() == bytes[span.start as int..span.end as int]
            && macro_target_matches(forms, call.site, target, call.target));
}

impl<'r, 't, 'p, 'a> MacroCalls<'r, 't, 'p, 'a> {
    /// 次のマクロ呼び出しを検査し、成功した場合は実引数の構文を借りる。
    ///
    /// 内側の引数列は呼び出し元のファイル・文書版・本体位置を保持し、
    /// このカーソルを次の呼び出しへ進めた後も読める。
    /// 呼び出しに診断がある場合は内側の引数列が `None` になる。呼び出しが尽きれば外側が `None` になる。
    pub fn next_call_with_arguments(&mut self)
        -> (prepared: Option<(MacroCall<'p, 'a>, Option<MacroArguments<'p, 'a>>)>)
        requires old(self).valid(),
        ensures
            match prepared {
                None => old(self).advances(final(self), None),
                Some((call, args)) => {
                    &&& old(self).advances(final(self), Some(call))
                    &&& match call.target {
                        Ok(definition) => args matches Some(args) && args.valid()
                            && args.scope_model().source == final(self).source_model()
                            && (args.scope_model().file, args.scope_model().entry) == final(self).origin_model()
                            && args.forms_model() == final(self).sites_model().syntax_model().forms@
                            && args.remaining_model() == call.site.arguments
                            && args.count_model() == definition.parameters@.len()
                            && indexed_defmacro(&final(self).aliases_model().targets_model().project_model(), definition),
                        Err(_) => args.is_none(),
                    }
                },
            },
    {
        let call = self.next_call()?;
        let arguments = if let Ok(definition) = &call.target {
            let scope = MacroArgumentScope { source: self.source, file: self.file, entry: self.entry };
            let syntax = self.sites.syntax();
            let range = call.site.arguments.start..call.site.arguments.end;
            Some(MacroArguments::from_checked_site(scope, syntax.forms.as_slice(), range, definition.parameters.len()))
        } else {
            None
        };
        Some((call, arguments))
    }
}

impl<'r, 't, 'p, 'a> MacroCalls<'r, 't, 'p, 'a> {
    /// 一つの呼び出しから型検査済みの本体と実引数を結び付けた結果を表す。
    pub open spec fn binding_advances(
        &self, next: &Self, outcome: Option<Result<BoundMacroCall<'p, 'a>, MacroPreparationError<'p, 'a>>>,
    ) -> bool {
        let project = next.aliases_model().targets_model().project_model();
        match outcome {
            None => self.advances(next, None),
            Some(Ok(bound)) => {
                let definition = bound.definition_model();
                let site = bound.site_model();
                let scope = bound.scope_model();
                &&& self.advances(next, Some(MacroCall { site, target: Ok(definition) }))
                &&& bound.valid()
                &&& scope.source == next.source_model()
                &&& (scope.file, scope.entry) == next.origin_model()
                &&& defmacro_body_check(&project, &definition, Some(Ok(bound.body_model())))
                &&& macro_arguments_cover(scope, next.sites_model().syntax_model().forms@,
                    site.arguments, bound.arguments_model())
            },
            Some(Err(error)) => match error.kind {
                MacroPreparationFailure::Call(cause) =>
                    self.advances(next, Some(MacroCall { site: error.site, target: Err(cause) })),
                MacroPreparationFailure::Body { definition, error: cause } =>
                    self.advances(next, Some(MacroCall { site: error.site, target: Ok(definition) }))
                    && defmacro_body_check(&project, &definition, Some(Err(cause))),
            },
        }
    }

    /// 次の展開呼び出しを検査し、同じ呼び出しに由来する本体と実引数を結び付ける。
    ///
    /// 返す束縛には、元の展開位置と実引数のファイル・文書版・回路内でのスコープが残る。
    /// 呼び出しが尽きると `None` を返す。
    ///
    /// # Errors
    ///
    /// 名前解決や個数の診断を先に返す。呼び出しが正しければマクロ本体の型を検査する。
    /// 診断が出た呼び出しも走査済みのため、次の呼び出しの検査を続けられる。
    pub fn next_bound_macro(&mut self)
        -> (outcome: Option<Result<BoundMacroCall<'p, 'a>, MacroPreparationError<'p, 'a>>>)
        requires old(self).valid(),
        ensures old(self).binding_advances(final(self), outcome),
    {
        let (call, arguments) = self.next_call_with_arguments()?;
        let site = call.site;
        let definition = match call.target {
            Ok(definition) => definition,
            Err(cause) => return Some(Err(MacroPreparationError {
                site, kind: MacroPreparationFailure::Call(cause),
            })),
        };
        let project = self.aliases.targets().project();
        proof { indexed_defmacro_is_retained(project, &definition); }
        let Some(checked) = project.check_defmacro_body(&definition) else { unreachable!() };
        match checked {
            Ok(body) => {
                let Some(arguments) = arguments else { unreachable!() };
                Some(Ok(bind_macro_call(site, definition, body, arguments)))
            },
            Err(error) => Some(Err(MacroPreparationError {
                site, kind: MacroPreparationFailure::Body { definition, error },
            })),
        }
    }
}

impl<'t, 'p, 'a> MixedUseAliases<'t, 'p, 'a> {
    /// 回路本体の展開呼び出しを解決するカーソルを返す。
    ///
    /// 指定位置が `func`、`module`、`module-part` のいずれにも当たらなければ `None`。
    /// カーソルは元の文書版を保持し、引数の構文を再解析しない。
    pub fn macro_calls<'r>(&'r self, file: usize, entry: usize) -> (calls: Option<MacroCalls<'r, 't, 'p, 'a>>)
        requires mixed_use_targets_match(&self.targets_model().project_model(), self.targets_model()),
        ensures
            calls.is_some() <==> has_macro_caller(&self.targets_model().project_model(), file, entry),
            calls matches Some(calls) ==> calls.valid() && calls.aliases_model() == self
                && calls.origin_model() == (file, entry)
                && routine_expansion_sites_match(calls.source_model().text_model(), calls.sites_model().syntax_model(),
                    entry as int, Some(calls.sites_model())),
    {
        let project = self.targets().project();
        let indexes = project.indexes();
        let sources = project.sources();
        if file >= indexes.len() { return None; }
        let ProjectSourceIndex::Circuit(parsed) = &indexes[file] else { return None; };
        let source = &sources[file];
        proof {
            project_source_index_evidence(*source, indexes@[file as int]);
            parsed_index_evidence(*source, *parsed);
            source.text_model_is_text();
        }
        let sites = routine_expansion_sites(source.text(), &parsed.syntax, entry)?;
        Some(MacroCalls { aliases: self, file, entry, source, sites })
    }
}

} // verus!
