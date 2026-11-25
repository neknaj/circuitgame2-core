//! 元の構文木で見つけた呼び出しを、解決済みの補助関数と署名に結び付ける。

use super::{DefnNameError, MixedUseAliases, ResolvedDefnName};
#[cfg(verus_only)]
use super::{defn_name_resolution, resolved_defn_name_origin};
use crate::ncg2m::data_types::DefnSignature;
#[cfg(verus_only)]
use crate::ncg2m::expression_types::named_call::CallForm;
use crate::project::{ProjectDeclaration, ProjectSource};
#[cfg(verus_only)]
use crate::project::mixed_use_targets_match;
#[cfg(verus_only)]
use crate::syntax::{Form, form_span};
use core::ops::Range;
use vstd::prelude::*;

verus! {

/// 補助関数の本体に書かれた呼び出し形の位置。
#[derive(Debug)]
pub struct DefnCallSite<'p, 'a> {
    /// 呼び出しを書いたファイルと文書バージョン。
    pub source: &'p ProjectSource<'a>,
    /// 呼び出し先の名前の UTF-8 半開バイト範囲。
    pub head: Range<usize>,
    /// 呼び出し形全体の UTF-8 半開バイト範囲。
    pub span: Range<usize>,
}

/// 引数の型検査に進める呼び出し。
#[derive(Debug)]
pub enum PreparedDefnCall<'p, 'a> {
    /// 署名が見つかり、直下の引数の個数が一致した呼び出し。
    Declared {
        /// 元の呼び出し位置。
        site: DefnCallSite<'p, 'a>,
        /// 呼び出し先の補助関数の宣言位置。
        declaration: ProjectDeclaration<'p, 'a>,
        /// 引数の型と戻り値の型を保持する署名。
        signature: DefnSignature<'a>,
    },
    /// 段階に応じた組み込みの探索に渡す呼び出し。
    StageName(DefnCallSite<'p, 'a>),
}

/// 呼び出し先または引数の個数を検査できなかった理由。
#[derive(Debug)]
pub enum DefnCallError<'p, 'a> {
    /// 呼び出し先の名前の診断。
    Name {
        /// 呼び出し元のファイル・文書版と名前の範囲。
        site: DefnCallSite<'p, 'a>,
        /// 名前の違反と、対象が存在する場合の関連範囲。
        error: DefnNameError<'p, 'a>,
    },
    /// 指定された引数の個数が署名と一致しなかった。
    Arity {
        /// 引数を含む呼び出し全体の範囲。
        site: DefnCallSite<'p, 'a>,
        /// 必要な個数を定めた補助関数の位置。
        declaration: ProjectDeclaration<'p, 'a>,
        /// 署名にある引数の個数。
        expected: usize,
        /// 呼び出しの直下にある引数の個数。
        found: usize,
    },
}

spec fn site_matches(source: ProjectSource, call: CallForm, site: DefnCallSite) -> bool {
    *site.source == source && site.head == call.head_span && site.span == call.span
}

spec fn call_arity_matches(
    aliases: &MixedUseAliases, file: usize, item: usize, call: CallForm,
    result: Result<PreparedDefnCall, DefnCallError>,
) -> bool {
    let project = aliases.targets_model().project_model();
    let source = project.sources_model()[file as int];
    match result {
        Ok(PreparedDefnCall::Declared { site, declaration, signature }) => {
            &&& site_matches(source, call, site)
            &&& defn_name_resolution(aliases, file, item, call.word, Ok(ResolvedDefnName::Declaration(declaration)))
            &&& project.defn_signature_matches_index(declaration.file, declaration.item, Some(signature))
            &&& call.arguments == signature.parameters@.len()
        }
        Ok(PreparedDefnCall::StageName(site)) =>
            site_matches(source, call, site)
                && defn_name_resolution(aliases, file, item, call.word, Ok(ResolvedDefnName::StageName)),
        Err(DefnCallError::Name { site, error }) =>
            site_matches(source, call, site)
                && defn_name_resolution(aliases, file, item, call.word, Err(error)),
        Err(DefnCallError::Arity { site, declaration, expected, found }) => {
            &&& site_matches(source, call, site)
            &&& defn_name_resolution(aliases, file, item, call.word, Ok(ResolvedDefnName::Declaration(declaration)))
            &&& exists|signature: DefnSignature|
                #[trigger] project.defn_signature_matches_index(declaration.file, declaration.item, Some(signature))
                && expected == signature.parameters@.len()
            &&& found == call.arguments && found != expected
        }
    }
}

/// 呼び出しの範囲、参照先、引数の個数が、保持した元の構文木と署名に対応することを表す。
pub closed spec fn prepared_defn_call_matches(
    aliases: &MixedUseAliases, file: usize, item: usize, at: usize,
    result: Option<Result<PreparedDefnCall, DefnCallError>>,
) -> bool {
    let project = aliases.targets_model().project_model();
    exists|form: Option<CallForm>| #[trigger] project.defn_call_form_matches(file, item, at, form)
        && match (form, result) {
            (Some(call), Some(resolved)) => call_arity_matches(aliases, file, item, call, resolved),
            (None, None) => true,
            _ => false,
        }
}

/// 検査の結果に記録された元の呼び出し位置を表す。
pub open spec fn prepared_call_site<'p, 'a>(result: Result<PreparedDefnCall<'p, 'a>, DefnCallError<'p, 'a>>)
    -> DefnCallSite<'p, 'a>
{
    match result {
        Ok(PreparedDefnCall::Declared { site, .. }) | Ok(PreparedDefnCall::StageName(site))
        | Err(DefnCallError::Name { site, .. }) | Err(DefnCallError::Arity { site, .. }) => site,
    }
}

/// 結果の呼び出し位置と署名が、対応する元ファイルの索引から得られたことを示す。
pub proof fn prepared_defn_call_origin(
    aliases: &MixedUseAliases, file: usize, item: usize, at: usize,
    result: Result<PreparedDefnCall, DefnCallError>,
)
    requires
        prepared_defn_call_matches(aliases, file, item, at, Some(result)),
        aliases.targets_model().project_model().has_source_indexes(),
    ensures {
        let project = aliases.targets_model().project_model();
        let site = prepared_call_site(result);
        &&& file < project.sources_model().len()
        &&& *site.source == project.sources_model()[file as int]
        &&& project.indexed_defn(file, item).is_some()
        &&& project.functional_forms_model(file) matches Some(forms) && {
            &&& at + 1 < forms.len()
            &&& forms[at as int] is List && forms[at + 1] is Atom
            &&& site.span == form_span(forms[at as int])
            &&& site.head == form_span(forms[at + 1])
        }
        &&& match result {
            Ok(PreparedDefnCall::Declared { declaration, signature, .. }) =>
                project.defn_signature_matches_index(declaration.file, declaration.item, Some(signature)),
            Err(DefnCallError::Arity { declaration, expected, found, .. }) => found != expected &&
                (exists|signature: DefnSignature| #[trigger]
                    project.defn_signature_matches_index(declaration.file, declaration.item, Some(signature))
                    && expected == signature.parameters@.len()),
            _ => true,
        }
    },
{
    let project = aliases.targets_model().project_model();
    let form = choose|form: Option<CallForm>| #[trigger] project.defn_call_form_matches(file, item, at, form)
        && form.is_some() && call_arity_matches(aliases, file, item, form->Some_0, result);
    project.defn_call_form_origin(file, item, at, form->Some_0);
}

impl<'t, 'p, 'a> MixedUseAliases<'t, 'p, 'a> {
    /// 元の補助関数本体の構文木添字から、呼び出し先と引数の個数を検査する。
    ///
    /// `item` は NCG2M のファイル内索引で補助関数を指す。 `at` は元ファイルの
    /// S 式構文木で呼び出し形を指す。呼び出し形が見つからなければ `None` を返す。
    /// 補助関数を参照する場合、引数で使う期待型と戻り値の型は返した署名に含まれる。
    /// この入口は本体の式の位置をたどる。構文テンプレート内の式はマクロ段階で扱う。
    ///
    /// # Errors
    ///
    /// 呼び出し先の名前の違反を先に返す。名前が補助関数を指す場合は、次に引数の個数を検査する。
    /// 各診断は元の呼び出し範囲を保持し、参照先がある場合はその位置も返す。
    ///
    /// # Examples
    ///
    /// 入れ子の式は引数1個として数える。同じ形が構文テンプレートにあっても、呼び出しの検査は始めない。
    ///
    /// ```
    /// use circuitgame2_core::project::{
    ///     DefnCallError, SourceSnapshot, check_mixed_use_aliases, index_mixed_use_targets, parse_project_sources,
    /// };
    /// use circuitgame2_core::syntax::{Form, parse};
    ///
    /// let program = "(defn callee (as-type (Fn (Bool Nat) Bool) (fn (flag n) flag)))
    ///     (defn caller (as-type (Fn () Bool) (fn () (callee (if true false true)))))
    ///     (defn template (as-type (Fn () Syntax) (fn () (syntax (callee true)))))";
    /// let snapshots = [SourceSnapshot { path: "program.ncg2m", revision: 4, text: program }];
    /// let project = parse_project_sources(&snapshots).unwrap();
    /// let targets = index_mixed_use_targets(&project).unwrap();
    /// let aliases = check_mixed_use_aliases(&targets).unwrap();
    /// let forms = parse(program).unwrap();
    /// let index = |prefix: &str| {
    ///     let start = program.find(prefix).unwrap();
    ///     forms.iter().position(|form| matches!(form, Form::List { span, .. } if span.start == start)).unwrap()
    /// };
    /// let call = aliases.prepare_defn_call(0, 1, index("(callee (if")).unwrap().unwrap_err();
    /// let DefnCallError::Arity { site, expected, found, .. } = call else { panic!() };
    /// assert_eq!((expected, found), (2, 1));
    /// assert_eq!(&program[site.head], "callee");
    /// assert!(aliases.prepare_defn_call(0, 2, index("(callee true)")).is_none());
    /// ```
    pub fn prepare_defn_call(&self, file: usize, item: usize, at: usize)
        -> (result: Option<Result<PreparedDefnCall<'p, 'a>, DefnCallError<'p, 'a>>>)
        requires mixed_use_targets_match(&self.targets_model().project_model(), self.targets_model()),
        ensures prepared_defn_call_matches(self, file, item, at, result),
    {
        let project = self.targets().project();
        let Some(form) = project.defn_call_form(file, item, at) else { return None; };
        let sources = project.sources();
        let _indexes = project.indexes();
        proof { project.defn_call_file_exists(file, item, at, form); }
        let source = &sources[file];
        let site = DefnCallSite { source, head: form.head_span.start..form.head_span.end,
            span: form.span.start..form.span.end };
        let found = match self.resolve_defn_name(file, item, form.word) {
            Ok(ResolvedDefnName::Declaration(declaration)) => {
                proof { resolved_defn_name_origin(self, file, item, form.word, declaration); }
                let signature = project.defn_signature(declaration.file, declaration.item);
                proof { project.indexed_defn_signature_origin(declaration.file, declaration.item, signature); }
                let Some(signature) = signature else { unreachable!() };
                let expected = signature.parameters.len();
                if expected != form.arguments {
                    Err(DefnCallError::Arity { site, declaration, expected, found: form.arguments })
                } else {
                    Ok(PreparedDefnCall::Declared { site, declaration, signature })
                }
            }
            Ok(ResolvedDefnName::StageName) => Ok(PreparedDefnCall::StageName(site)),
            Err(error) => Err(DefnCallError::Name { site, error }),
        };
        assert(call_arity_matches(self, file, item, form, found));
        Some(found)
    }
}

}
