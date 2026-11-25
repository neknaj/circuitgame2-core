//! 正規化したプロジェクトのソースを、言語ごとの厳格な索引に結び付ける。

use alloc::vec::Vec;
use crate::ncg2m::data_types::{DefnSignature, read_header_signature};
use crate::ncg2m::defn::DefnHeader;
#[cfg(verus_only)]
use crate::ncg2m::data_types::{signature_matches_header, signature_result_origin};
use crate::ncg2m::expression_types::{ExpressionCheckFailure, check_indexed_meta_defn};
#[cfg(verus_only)]
use crate::ncg2m::expression_types::{
    DefnBodyError, defn_body_matches, indexed_meta_body_agrees_with_standalone, meta_defn_check_matches, meta_defn_check_origin,
    same_defn_body_outcome,
};
use crate::ncg2m::file::{MetaFileError, MetaItem, MetaItemKind, index_meta_with_forms, indexed_meta_call};
use crate::ncg2m::expression_types::named_call::{CallForm, DefnBodyCallError, check_indexed_call_body};
#[cfg(verus_only)]
use crate::ncg2m::expression_types::named_call::{indexed_call_body_matches, indexed_call_body_origin, defn_call_edge_matches};
use crate::syntax::Form;
#[cfg(verus_only)]
use crate::syntax::form_span;
#[cfg(verus_only)]
use crate::ncg2m::file::{meta_ast_matches, meta_call_matches, meta_call_form_origin, meta_binding_span_evidence, meta_binding_spans_valid, meta_defn_signature_spans, meta_file_matches, meta_file_results_agree, valid_meta_file};
use crate::syntax::circuit::{CircuitFormError, NamedBuildCircuit};
use super::circuits::{index_project_circuit, read_source_span};
#[cfg(verus_only)]
use crate::syntax::circuit::{circuit_source_error, circuit_source_errors_agree, circuit_source_matches};
use super::{DefnCallEdge, DefnPosition, MixedUseAliases, ProjectSource, SourceKind, SourceSetError, SourceSnapshot, VirtualPath, collect_sources};
#[cfg(verus_only)]
use super::{mixed_use_targets_match, prepared_call_site, normalized_path, parsed_circuit_matches, project_sources_match, source_kind_of, valid_source_snapshots};
#[cfg(verus_only)]
use super::sources::{
    collected_source_for_input, collected_source_ids_unique, collected_source_origin,
    collected_sources_follow_input_order, first_source_input, first_source_set_error, snapshot_matches,
    source_ids_unique, source_set_errors_agree,
};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 収集したソースと、各ソースから作った言語別の構文索引。
#[derive(Debug)]
pub struct ParsedProjectSources<'a> {
    sources: Vec<ProjectSource<'a>>,
    indexes: Vec<ProjectSourceIndex<'a>>,
    // NCG2M の S 式を言語別索引と同じ添字に保持する。
    meta_asts: Vec<Option<Vec<Form>>>,
}

/// ファイルの拡張子に対応する構文索引。
#[derive(Debug)]
pub enum ProjectSourceIndex<'a> {
    /// 回路の構文木と名前・定義・参照の索引。
    Circuit(NamedBuildCircuit<'a>),
    /// NCG2M の宣言と指示フォームをファイル内の順序で並べた索引。
    Functional(Vec<MetaItem>),
}

/// プロジェクトのソースを収集または厳格に解析できなかった最初の理由。
#[derive(Debug)]
pub enum ProjectSourceParseError<'a> {
    /// 入力のパス、拡張子、または同じファイルに対するスナップショットが規則に合わない。
    Collection(SourceSetError),
    /// 収集済みのファイルが、その言語の構文に合わない。
    File {
        /// ファイルが最初に現れた入力スナップショットの添字。
        input: usize,
        /// 正規化済みのファイル識別子。
        id: VirtualPath<'a>,
        /// 診断の範囲が対応する文書バージョン。
        revision: u64,
        /// 元ファイルの UTF-8 半開バイト範囲を持つ構文診断。
        error: ProjectFileSyntaxError,
    },
}

/// 入力ファイルの言語に対応する構文診断。
#[derive(Debug, Eq, PartialEq)]
pub enum ProjectFileSyntaxError {
    /// 回路言語の字句・構文エラー。
    Circuit(CircuitFormError),
    /// NCG2M の字句・構文エラー。
    Functional(MetaFileError),
}

pub(super) open spec fn directive_entry_count(index: ProjectSourceIndex) -> nat {
    match index {
        ProjectSourceIndex::Circuit(circuit) => circuit.syntax.entries@.len(),
        ProjectSourceIndex::Functional(items) => items@.len(),
    }
}

pub(super) fn count_directive_entries(index: &ProjectSourceIndex) -> (len: usize)
    ensures len == directive_entry_count(*index),
{
    match index {
        ProjectSourceIndex::Circuit(circuit) => circuit.syntax.entries.len(),
        ProjectSourceIndex::Functional(items) => items.len(),
    }
}

/// 補助関数を宣言した名前空間と、別名の有効範囲を識別する位置。
#[derive(Clone, Copy, Debug)]
pub(super) struct DefnScope<'a> {
    pub namespace: Option<&'a str>,
    pub block: Option<usize>,
}

impl<'a> ParsedProjectSources<'a> {
    /// 正規化済みのファイル識別子でまとめたソースを、初出順に返す。
    pub fn sources(&self) -> (sources: &[ProjectSource<'a>])
        ensures sources@ == self.sources_model(),
    {
        self.sources.as_slice()
    }

    /// 各ソースの索引を [`Self::sources`] と同じ位置に並べて返す。
    pub fn indexes(&self) -> (indexes: &[ProjectSourceIndex<'a>])
        ensures indexes@ == self.indexes_model(), self.has_source_indexes(),
    {
        proof { use_type_invariant(self); }
        self.indexes.as_slice()
    }

    pub(super) closed spec fn defn_scope_matches(
        &self, file: usize, item: usize, scope: Option<DefnScope>,
    ) -> bool {
        &&& scope.is_some() == self.indexed_defn(file, item).is_some()
        &&& scope matches Some(resolved) ==> {
            &&& file < self.indexes_model().len()
            &&& self.indexes_model()[file as int] matches ProjectSourceIndex::Functional(items)
                && item < items@.len()
                && match (items@[item as int].namespace, resolved.namespace, resolved.block) {
                    (None, None, None) => true,
                    (Some(span), Some(word), Some(block)) => block == span.start
                        && word.spec_bytes() == self.sources_model()[file as int].text_model().spec_bytes()
                            [span.start as int..span.end as int],
                    _ => false,
                }
        }
    }

    pub(super) proof fn defn_scope_is_indexed(&self, file: usize, item: usize, scope: Option<DefnScope>)
        requires self.defn_scope_matches(file, item, scope),
        ensures scope.is_some() == self.indexed_defn(file, item).is_some(),
    {}

    /// 索引にある補助関数の宣言位置から、名前解決に使う所属を取り出す。
    pub(super) fn defn_scope(&self, file: usize, item: usize) -> (scope: Option<DefnScope<'a>>)
        ensures self.defn_scope_matches(file, item, scope),
    {
        let indexes = self.indexes();
        if file >= indexes.len() { return None; }
        let index = &indexes[file];
        let ProjectSourceIndex::Functional(items) = index else { return None; };
        if item >= items.len() { return None; }
        let indexed = &items[item];
        if !matches!(indexed.kind, MetaItemKind::Defn(_)) { return None; }
        let source = &self.sources()[file];
        proof {
            project_source_index_evidence(*source, *index);
            meta_binding_span_evidence(source.text, items@, item as int);
            source.text_model_is_text();
        }
        match &indexed.namespace {
            Some(span) => {
                let namespace = read_source_span(source.text(), span.start, span.end);
                Some(DefnScope { namespace: Some(namespace), block: Some(span.start) })
            }
            None => Some(DefnScope { namespace: None, block: None }),
        }
    }

    pub(super) closed spec fn defn_call_form_matches(
        &self, file: usize, item: usize, at: usize, call: Option<CallForm>,
    ) -> bool {
        match self.indexed_defn(file, item) {
            None => call.is_none(),
            Some(_) => {
                let entries = self.indexes_model()[file as int]->Functional_0@;
                let text = self.sources_model()[file as int].text_model();
                self.functional_forms_model(file) matches Some(forms)
                    && meta_call_matches(text, forms, entries, item, at, call)
            },
        }
    }

    pub(super) proof fn defn_call_file_exists(
        &self, file: usize, item: usize, at: usize, call: CallForm,
    )
        requires self.has_source_indexes(), self.defn_call_form_matches(file, item, at, Some(call)),
        ensures file < self.sources_model().len(),
    {}

    /// 指定の NCG2M ファイルについて、解析時に保持した S 式構文木を表す。
    pub closed spec fn functional_forms_model(&self, file: usize) -> Option<Seq<Form>> {
        if file < self.meta_asts@.len() {
            match self.meta_asts@[file as int] {
                Some(forms) => Some(forms@),
                None => None,
            }
        } else { None }
    }

    pub(super) proof fn defn_call_form_origin(
        &self, file: usize, item: usize, at: usize, call: CallForm,
    )
        requires self.has_source_indexes(), self.defn_call_form_matches(file, item, at, Some(call)),
        ensures
            file < self.sources_model().len(),
            self.indexed_defn(file, item).is_some(),
            self.functional_forms_model(file) matches Some(forms) && {
                &&& at + 1 < forms.len()
                &&& forms[at as int] is List && forms[at + 1] is Atom
                &&& call.span == form_span(forms[at as int]) && call.head_span == form_span(forms[at + 1])
            },
    {
        let forms = self.meta_asts@[file as int]->Some_0@;
        let entries = self.indexes_model()[file as int]->Functional_0@;
        let source = self.sources_model()[file as int];
        meta_call_form_origin(source.text_model(), forms, entries, item, at, call);
    }

    /// 保持している補助関数本体の構文木から、指定した添字にある呼び出し形を読む。
    pub(super) fn defn_call_form(&self, file: usize, item: usize, at: usize)
        -> (call: Option<CallForm<'a>>)
        ensures self.defn_call_form_matches(file, item, at, call),
    {
        let indexes = self.indexes();
        if file >= indexes.len() { return None; }
        let index = &indexes[file];
        let ProjectSourceIndex::Functional(items) = index else { return None; };
        if item >= items.len() || !matches!(items[item].kind, MetaItemKind::Defn(_)) { return None; }
        let source = &self.sources()[file];
        proof {
            use_type_invariant(self);
            assert(retained_ast_matches(*source, *index, self.meta_asts@[file as int]));
            project_source_index_evidence(*source, *index);
            source.text_model_is_text();
        }
        let Some(forms) = &self.meta_asts[file] else { unreachable!() };
        indexed_meta_call(source.text(), forms, items, item, at)
    }

    pub(super) closed spec fn named_defn_body_matches<'p>(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, file: usize, item: usize,
        result: Option<Result<DefnSignature<'a>, DefnBodyCallError<'p, 'a>>>,
    ) -> bool {
        &&& *self == aliases.targets_model().project_model()
        &&& match (self.indexed_defn(file, item), result) {
            (None, None) => true,
            (Some(_), Some(outcome)) => {
                let entries = self.indexes_model()[file as int]->Functional_0@;
                let text = self.sources_model()[file as int].text_model();
                self.functional_forms_model(file) matches Some(forms)
                    && indexed_call_body_matches(aliases, file, item, text, forms, entries, outcome)
            },
            _ => false,
        }
    }

    pub(super) proof fn named_defn_body_origin<'p>(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, file: usize, item: usize,
        result: Option<Result<DefnSignature<'a>, DefnBodyCallError<'p, 'a>>>,
    )
        requires self.named_defn_body_matches(aliases, file, item, result),
        ensures
            result.is_some() == self.indexed_defn(file, item).is_some(),
            result matches Some(Ok(signature)) ==>
                self.defn_signature_matches_index(file, item, Some(signature)),
            result matches Some(Err(DefnBodyCallError::Call(error))) ==> {
                let site = prepared_call_site(Err(error));
                &&& *site.source == self.sources_model()[file as int]
                &&& self.indexed_defn(file, item) matches Some(header) && {
                    &&& header.body_span.start <= site.span.start
                    &&& site.span.end <= header.body_span.end
                }
                &&& site.span.start <= site.head.start && site.head.end <= site.span.end
                &&& self.functional_forms_model(file) matches Some(forms)
                && exists|at: usize| at + 1 < forms.len() && (#[trigger] forms[at as int]) is List
                    && forms[at + 1] is Atom
                    && site.span == form_span(forms[at as int]) && site.head == form_span(forms[at + 1])
            },
    {
        if let Some(outcome) = result {
            let entries = self.indexes_model()[file as int]->Functional_0@;
            let text = self.sources_model()[file as int].text_model();
            let forms = self.functional_forms_model(file)->Some_0;
            indexed_call_body_origin(aliases, file, item, text, forms, entries, outcome);
        }
    }

    pub(super) fn check_named_defn_body<'p>(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, file: usize, item: usize, collect_edges: bool,
    ) -> (result: Option<(Result<DefnSignature<'a>, DefnBodyCallError<'p, 'a>>, Vec<DefnCallEdge<'p, 'a>>)>)
        requires *self == aliases.targets_model().project_model(),
            mixed_use_targets_match(self, aliases.targets_model()),
        ensures
            result.is_some() == self.indexed_defn(file, item).is_some(),
            match result {
                Some((outcome, edges)) => {
                    &&& self.named_defn_body_matches(aliases, file, item, Some(outcome))
                    &&& forall|i: int| 0 <= i < edges@.len() ==> {
                        let edge = #[trigger] edges@[i];
                        edge.from == (DefnPosition { file, item }) && defn_call_edge_matches(aliases, edge)
                    }
                }
                None => self.named_defn_body_matches(aliases, file, item, None),
            },
    {
        let indexes = self.indexes();
        if file >= indexes.len() { return None; }
        let index = &indexes[file];
        let ProjectSourceIndex::Functional(items) = index else { return None; };
        if item >= items.len() || !matches!(items[item].kind, MetaItemKind::Defn(_)) { return None; }
        let source = &self.sources()[file];
        proof {
            use_type_invariant(self);
            assert(retained_ast_matches(*source, *index, self.meta_asts@[file as int]));
            project_source_index_evidence(*source, *index);
            source.text_model_is_text();
        }
        let Some(forms) = &self.meta_asts[file] else { unreachable!() };
        assert(self.functional_forms_model(file) == Some(forms@));
        Some(check_indexed_call_body(aliases, file, item, source.text(), forms, items, collect_edges))
    }

    pub(super) fn defn_header(&self, file: usize, item: usize) -> (result: Option<&DefnHeader>)
        ensures self.has_source_indexes(),
            match result {
                Some(header) => self.indexed_defn(file, item) == Some(*header),
                None => self.indexed_defn(file, item).is_none(),
            },
    {
        let indexes = self.indexes();
        let Some(ProjectSourceIndex::Functional(items)) = indexes.get(file) else { return None; };
        let Some(MetaItem { kind: MetaItemKind::Defn(header), .. }) = items.get(item) else { return None; };
        Some(header)
    }

    pub(super) fn defn_signature_from_header(&self, file: usize, _item: usize, header: &DefnHeader)
        -> (signature: DefnSignature<'a>)
        requires self.has_source_indexes(), self.indexed_defn(file, _item) == Some(*header),
        ensures self.defn_signature_matches_index(file, _item, Some(signature)),
            signature.parameters@.len() == header.parameters@.len(),
    {
        let source = &self.sources()[file];
        proof {
            let index = self.indexes_model()[file as int];
            project_source_index_evidence(*source, index);
            meta_defn_signature_spans(source.text, index->Functional_0@, _item as int);
            source.text_model_is_text();
        }
        let signature = read_header_signature(source.text(), header);
        proof { signature_result_origin(source.text_model(), *header, signature); }
        signature
    }

    /// 言語別索引の項目が補助関数宣言なら、本体の型検査に使う署名を返す。
    ///
    /// 添字が範囲外の場合と、項目が別の種類である場合は `None` を返す。
    /// 索引にある署名から型を取り出すため、範囲の原点はファイルの先頭になる。
    pub fn defn_signature(&self, file: usize, item: usize) -> (signature: Option<DefnSignature<'a>>)
        ensures self.defn_signature_matches_index(file, item, signature),
    {
        let header = self.defn_header(file, item)?;
        Some(self.defn_signature_from_header(file, item, header))
    }

    /// 指定した補助関数の本体を、保持している構文木と署名を使って型検査する。
    ///
    /// ファイルや項目の添字が範囲外の場合と、補助関数に当たらない項目では `None` を返す。
    /// 診断や署名の範囲は、同じ添字で `sources()` から得られるファイルの先頭を基準とする。
    /// 署名の取り出しと式の走査に使う作業領域を確保する。構文木はプロジェクトの解析時に作ったものを使う。
    pub fn check_defn_body(&self, file: usize, item: usize)
        -> (result: Option<Result<DefnSignature<'a>, ExpressionCheckFailure<'a>>>)
        ensures self.defn_body_matches_index(file, item, result),
    {
        let indexes = self.indexes();
        if file >= indexes.len() {
            return None;
        }
        let index = &indexes[file];
        let ProjectSourceIndex::Functional(items) = index else { return None; };
        let source = &self.sources()[file];
        proof {
            use_type_invariant(self);
            assert(retained_ast_matches(*source, *index, self.meta_asts@[file as int]));
            project_source_index_evidence(*source, *index);
            source.text_model_is_text();
        }
        let Some(forms) = &self.meta_asts[file] else { unreachable!() };
        check_indexed_meta_defn(source.text(), forms, items, item)
    }

    /// 本体の検査結果が、同じファイルの索引と構文木に対応することを表す。
    pub closed spec fn defn_body_matches_index(
        &self, file: usize, item: usize, result: Option<Result<DefnSignature<'a>, ExpressionCheckFailure<'a>>>,
    ) -> bool {
        if file >= self.indexes_model().len() {
            result.is_none()
        } else {
            let source = self.sources_model()[file as int].text_model();
            match self.indexes_model()[file as int] {
                ProjectSourceIndex::Functional(items) => self.meta_asts@[file as int] matches Some(forms)
                    && meta_ast_matches(source, forms@, items@)
                    && meta_file_matches(source, Ok(items))
                    && meta_defn_check_matches(source, forms@, items@, item, result),
                ProjectSourceIndex::Circuit(_) => result.is_none(),
            }
        }
    }

    /// 索引の補助関数の有無と本体の検査結果が対応することを示す。
    pub proof fn indexed_body_check_origin(
        &self, file: usize, item: usize, result: Option<Result<DefnSignature<'a>, ExpressionCheckFailure<'a>>>,
    )
        requires self.defn_body_matches_index(file, item, result),
        ensures result.is_some() == self.indexed_defn(file, item).is_some(),
            result matches Some(Ok(signature)) ==>
                self.defn_signature_matches_index(file, item, Some(signature)),
    {
        if file < self.indexes_model().len() {
            if let ProjectSourceIndex::Functional(items) = self.indexes_model()[file as int] {
                let forms = self.meta_asts@[file as int]->Some_0;
                let source = self.sources_model()[file as int].text_model();
                meta_defn_check_origin(source, forms@, items@, item, result);
            }
        }
    }

    /// ファイルが単独の補助関数宣言なら、索引を使う検査と単独宣言の検査が一致することを示す。
    pub proof fn indexed_body_agrees_with_standalone(
        &self, file: usize, indexed: Option<Result<DefnSignature<'a>, ExpressionCheckFailure<'a>>>,
        standalone: Result<DefnSignature<'a>, DefnBodyError<'a>>,
    )
        requires
            file < self.indexes_model().len(),
            self.indexes_model()[file as int] is Functional,
            self.defn_body_matches_index(file, 0, indexed),
            defn_body_matches(self.sources_model()[file as int].text_model(), standalone),
            !(standalone matches Err(DefnBodyError::Header(_))),
        ensures indexed matches Some(result) && same_defn_body_outcome(result, standalone),
    {
        let source = self.sources_model()[file as int].text_model();
        let items = self.indexes_model()[file as int]->Functional_0;
        let forms = self.meta_asts@[file as int]->Some_0;
        indexed_meta_body_agrees_with_standalone(source, forms@, items, indexed, standalone);
    }

    /// 指定された索引項目と、型検査で使う署名が対応することを表す。
    pub closed spec fn defn_signature_matches_index(
        &self, file: usize, item: usize, result: Option<DefnSignature<'a>>,
    ) -> bool {
        match self.indexed_defn(file, item) {
            Some(header) => result matches Some(signature)
                && signature_matches_header(self.sources_model()[file as int].text_model(), header, signature),
            None => result.is_none(),
        }
    }

    /// 指定された索引項目の補助関数ヘッダーを表す。
    pub closed spec fn indexed_defn(&self, file: usize, item: usize) -> Option<crate::ncg2m::defn::DefnHeader> {
        if file >= self.indexes_model().len() {
            None
        } else {
            match self.indexes_model()[file as int] {
                ProjectSourceIndex::Functional(items) if item < items@.len() => match items@[item as int].kind {
                    MetaItemKind::Defn(header) => Some(header),
                    _ => None,
                },
                _ => None,
            }
        }
    }

    pub(super) proof fn indexed_defn_presence(&self, file: usize, item: usize)
        ensures self.indexed_defn(file, item).is_some() <==> {
            &&& file < self.indexes_model().len()
            &&& self.indexes_model()[file as int] matches ProjectSourceIndex::Functional(items)
            && item < items@.len() && items@[item as int].kind is Defn
        },
    {}

    pub(super) proof fn indexed_defn_kind(&self, file: usize, item: usize)
        requires file < self.indexes_model().len(),
            self.indexes_model()[file as int] matches ProjectSourceIndex::Functional(items)
                && item < items@.len() && items@[item as int].kind is Defn,
        ensures self.indexed_defn(file, item).is_some(),
    {}

    /// 索引から取り出した署名が補助関数宣言に対応することを示す。
    pub proof fn indexed_defn_signature_origin(
        &self, file: usize, item: usize, result: Option<DefnSignature<'a>>,
    )
        requires self.defn_signature_matches_index(file, item, result),
        ensures
            result.is_some() == self.indexed_defn(file, item).is_some(),
            result matches Some(signature) ==> file < self.indexes_model().len()
                && (self.indexed_defn(file, item) matches Some(header)
                    && signature_matches_header(self.sources_model()[file as int].text_model(), header, signature)),
    {}

    /// 正規化済みのソース列を表す。
    pub closed spec fn sources_model(&self) -> Seq<ProjectSource<'a>> {
        self.sources@
    }

    /// ソース列に対応する索引列を表す。
    pub closed spec fn indexes_model(&self) -> Seq<ProjectSourceIndex<'a>> {
        self.indexes@
    }

    /// 正規化されたソースと、それぞれの言語の索引が同じ位置で対応することを表す。
    pub open spec fn has_source_indexes(&self) -> bool {
        let sources = self.sources_model();
        let indexes = self.indexes_model();
        &&& source_ids_unique(sources)
        &&& sources.len() == indexes.len()
        &&& forall|i: int| 0 <= i < sources.len() ==>
            #[trigger] project_source_index_matches(sources[i], indexes[i])
    }

    #[verifier::type_invariant]
    spec fn indexes_correspond(&self) -> bool {
        &&& self.has_source_indexes()
        &&& self.meta_asts@.len() == self.indexes@.len()
        &&& forall|i: int| 0 <= i < self.indexes@.len() ==>
            #[trigger] retained_ast_matches(self.sources@[i], self.indexes@[i], self.meta_asts@[i])
    }

    /// 入力と正規化したソースが対応し、同じ位置に各言語の索引があることを表す。
    pub open spec fn matches(&self, inputs: Seq<SourceSnapshot>) -> bool {
        project_sources_match(inputs, self.sources_model()) && self.has_source_indexes()
    }
}

spec fn retained_ast_matches(source: ProjectSource, index: ProjectSourceIndex, ast: Option<Vec<Form>>) -> bool {
    match index {
        ProjectSourceIndex::Circuit(_) => ast.is_none(),
        ProjectSourceIndex::Functional(items) => ast matches Some(forms) && meta_ast_matches(source.text, forms@, items@),
    }
}

/// ファイルの索引が、その拡張子で指定した言語の厳格な索引に対応することを表す。
pub closed spec fn project_source_index_matches(source: ProjectSource, index: ProjectSourceIndex) -> bool {
    match index {
        ProjectSourceIndex::Circuit(parsed) => source.kind is Circuit && circuit_source_matches(source.text)
            && parsed_circuit_matches(source, parsed),
        ProjectSourceIndex::Functional(items) => source.kind is Functional && valid_meta_file(source.text)
            && meta_file_matches(source.text, Ok(items)) && meta_binding_spans_valid(source.text, items@),
    }
}

pub(super) proof fn project_source_index_evidence(source: ProjectSource, index: ProjectSourceIndex)
    requires project_source_index_matches(source, index),
    ensures match index {
        ProjectSourceIndex::Circuit(parsed) => parsed_circuit_matches(source, parsed),
        ProjectSourceIndex::Functional(items) => meta_binding_spans_valid(source.text, items@),
    },
{}

spec fn valid_file_text(kind: SourceKind, text: &str) -> bool {
    match kind {
        SourceKind::Circuit => circuit_source_matches(text),
        SourceKind::Functional => valid_meta_file(text),
    }
}

spec fn input_text_matches_language(source: SourceSnapshot) -> bool {
    normalized_path(source.path) matches Ok(id)
        && (source_kind_of(id) matches Some(kind) && valid_file_text(kind, source.text))
}

spec fn inputs_parsed_before(inputs: Seq<SourceSnapshot>, stop: int) -> bool {
    forall|i: int| i < stop && #[trigger] first_source_input(inputs, i) ==> input_text_matches_language(inputs[i])
}

/// ソースの収集に成功し、各ファイルがその言語の構文に従うことを表す。
pub closed spec fn project_source_set_accepts(inputs: Seq<SourceSnapshot>) -> bool {
    valid_source_snapshots(inputs) && inputs_parsed_before(inputs, inputs.len() as int)
}

spec fn syntax_error_matches(kind: SourceKind, text: &str, error: ProjectFileSyntaxError) -> bool {
    &&& !valid_file_text(kind, text)
    &&& match error {
        ProjectFileSyntaxError::Circuit(error) => kind is Circuit && circuit_source_error(text, error),
        ProjectFileSyntaxError::Functional(error) => kind is Functional && meta_file_matches(text, Err(error)),
    }
}

/// 最初の収集エラー、または初出順で最初の構文エラーが元の入力に対応することを表す。
///
/// 構文エラーには、同じ入力から得られる正規化済み識別子、版、言語と、その本文の診断が対応する。
pub closed spec fn project_source_parse_error(inputs: Seq<SourceSnapshot>, error: ProjectSourceParseError) -> bool {
    match error {
        ProjectSourceParseError::Collection(error) => !valid_source_snapshots(inputs) && first_source_set_error(inputs, error),
        ProjectSourceParseError::File { input, id, revision, error } => {
            let text = inputs[input as int].text;
            &&& valid_source_snapshots(inputs)
            &&& first_source_input(inputs, input as int)
            &&& inputs_parsed_before(inputs, input as int)
            &&& normalized_path(inputs[input as int].path) == Ok(id.components_model())
            &&& revision == inputs[input as int].revision
            &&& (source_kind_of(id.components_model()) matches Some(kind) && syntax_error_matches(kind, text, error))
        },
    }
}


/// ファイルの診断が、指定された入力の本文・ファイル識別子・文書バージョンに対応することを示す。
pub proof fn project_file_diagnostic_origin(
    inputs: Seq<SourceSnapshot>, input: usize, id: VirtualPath, revision: u64, error: ProjectFileSyntaxError,
)
    requires project_source_parse_error(inputs, ProjectSourceParseError::File { input, id, revision, error }),
    ensures
        input < inputs.len(),
        normalized_path(inputs[input as int].path) == Ok(id.components_model()),
        revision == inputs[input as int].revision,
        match error {
            ProjectFileSyntaxError::Circuit(error) =>
                source_kind_of(id.components_model()) == Some(SourceKind::Circuit)
                    && circuit_source_error(inputs[input as int].text, error),
            ProjectFileSyntaxError::Functional(error) =>
                source_kind_of(id.components_model()) == Some(SourceKind::Functional)
                    && meta_file_matches(inputs[input as int].text, Err(error)),
        },
{}

/// 最初の失敗は、収集エラー全体またはファイル識別子・文書バージョン・構文診断の組として一意に定まる。
pub proof fn project_source_parse_errors_agree(
    inputs: Seq<SourceSnapshot>, left: ProjectSourceParseError, right: ProjectSourceParseError,
)
    requires project_source_parse_error(inputs, left), project_source_parse_error(inputs, right),
    ensures match (left, right) {
        (ProjectSourceParseError::Collection(a), ProjectSourceParseError::Collection(b)) => a == b,
        (ProjectSourceParseError::File { input: a, id: aid, revision: ar, error: ae },
            ProjectSourceParseError::File { input: b, id: bid, revision: br, error: be }) =>
            a == b && aid.components_model() == bid.components_model() && ar == br && ae == be,
        _ => false,
    },
{
    match (left, right) {
        (ProjectSourceParseError::Collection(a), ProjectSourceParseError::Collection(b)) =>
            source_set_errors_agree(inputs, a, b),
        (ProjectSourceParseError::File { input: a, id: aid, revision: ar, error: ae },
            ProjectSourceParseError::File { input: b, id: bid, revision: br, error: be }) => {
            if a < b { assert(input_text_matches_language(inputs[a as int])); }
            if b < a { assert(input_text_matches_language(inputs[b as int])); }
            assert(a == b);
            let text = inputs[a as int].text;
            match (ae, be) {
                (ProjectFileSyntaxError::Circuit(x), ProjectFileSyntaxError::Circuit(y)) =>
                    circuit_source_errors_agree(text, x, y),
                (ProjectFileSyntaxError::Functional(x), ProjectFileSyntaxError::Functional(y)) =>
                    meta_file_results_agree(text, Err(x), Err(y)),
                _ => {},
            }
        }
        _ => {},
    }
}

proof fn indexed_input_prefix(
    inputs: Seq<SourceSnapshot>, sources: Seq<ProjectSource>, indexes: Seq<ProjectSourceIndex>, stop: int,
)
    requires
        project_sources_match(inputs, sources),
        indexes.len() <= sources.len(),
        (indexes.len() == sources.len() && stop == inputs.len())
            || (indexes.len() < sources.len() && stop == sources[indexes.len() as int].first_input),
        forall|i: int| 0 <= i < indexes.len() ==> #[trigger] project_source_index_matches(sources[i], indexes[i]),
    ensures inputs_parsed_before(inputs, stop),
{
    assert forall|i: int| i < stop && #[trigger] first_source_input(inputs, i)
        implies input_text_matches_language(inputs[i]) by {
        collected_source_for_input(inputs, sources, i);
        let at = choose|at: int| 0 <= at < sources.len() && #[trigger] snapshot_matches(inputs[i], sources[at])
            && sources[at].first_input == i && sources[at].text == inputs[i].text;
        if indexes.len() < sources.len() {
            collected_sources_follow_input_order(inputs, sources, at, indexes.len() as int);
        }
        assert(project_source_index_matches(sources[at], indexes[at]));
    };
}

fn parse_source_file<'a>(source: &ProjectSource<'a>)
    -> (result: Result<(ProjectSourceIndex<'a>, Option<Vec<Form>>), ProjectFileSyntaxError>)
    ensures match result {
        Ok((index, ast)) => project_source_index_matches(*source, index) && retained_ast_matches(*source, index, ast),
        Err(error) => syntax_error_matches(source.kind, source.text, error),
    },
{
    match source.kind {
        SourceKind::Circuit => match index_project_circuit(source) {
            Ok(index) => Ok((ProjectSourceIndex::Circuit(index), None)),
            Err(error) => Err(ProjectFileSyntaxError::Circuit(error)),
        },
        SourceKind::Functional => match index_meta_with_forms(source.text) {
            Ok((index, forms)) => Ok((ProjectSourceIndex::Functional(index), Some(forms))),
            Err(error) => Err(ProjectFileSyntaxError::Functional(error)),
        },
    }
}

/// 回路ソースと NCG2M ソースを含む入力を収集し、各ファイルを拡張子に従って厳格に解析する。
///
/// 同じファイルを指す入力は、文書バージョンと本文が等しければ1件にまとめる。基底や宣言の衝突、名前解決は
/// 収集したソースと索引を使って後段で検査する。
///
/// # Errors
///
/// ソース集合の検査を先に行い、収集できた場合は、ファイルを入力での初出順に検査する。
/// ファイルの診断には、初出の入力添字、正規化済み識別子、文書バージョンを添える。
///
/// # Examples
///
/// ```
/// use circuitgame2_core::project::{ProjectSourceIndex, SourceSnapshot, parse_project_sources};
///
/// let meta = "(defmacro invert () (list))";
/// let inputs = [
///     SourceSnapshot { path: "lib/logic.ncg2m", revision: 3, text: meta },
///     SourceSnapshot { path: "main.ncg2", revision: 5, text: "(using nor)" },
///     SourceSnapshot { path: "./lib/./logic.ncg2m", revision: 3, text: meta },
/// ];
/// let project = parse_project_sources(&inputs)?;
/// assert!(matches!(project.indexes(), [ProjectSourceIndex::Functional(_), ProjectSourceIndex::Circuit(_)]));
/// assert_eq!(project.sources()[0].id.components(), &["lib", "logic.ncg2m"]);
/// assert_eq!(project.sources()[1].input_index(), 1);
/// # Ok::<(), circuitgame2_core::project::ProjectSourceParseError<'_>>(())
/// ```

pub fn parse_project_sources<'a>(inputs: &[SourceSnapshot<'a>])
    -> (result: Result<ParsedProjectSources<'a>, ProjectSourceParseError<'a>>)
    ensures
        result.is_ok() == project_source_set_accepts(inputs@),
        match result {
            Ok(project) => project.matches(inputs@),
            Err(error) => project_source_parse_error(inputs@, error),
        },
{
    let sources = match collect_sources(inputs) {
        Ok(sources) => sources,
        Err(error) => return Err(ProjectSourceParseError::Collection(error)),
    };
    let mut indexes: Vec<ProjectSourceIndex> = Vec::new();
    let mut meta_asts: Vec<Option<Vec<Form>>> = Vec::with_capacity(sources.len());
    let mut file = 0;
    while file < sources.len()
        invariant
            project_sources_match(inputs@, sources@),
            valid_source_snapshots(inputs@),
            file == indexes@.len() == meta_asts@.len() <= sources@.len(),
            forall|i: int| 0 <= i < file ==> #[trigger] project_source_index_matches(sources@[i], indexes@[i]),
            forall|i: int| 0 <= i < file ==>
                #[trigger] retained_ast_matches(sources@[i], indexes@[i], meta_asts@[i]),
        decreases sources@.len() - file,
    {
        let source = &sources[file];
        match parse_source_file(source) {
            Ok((index, ast)) => {
                indexes.push(index);
                meta_asts.push(ast);
            },
            Err(error) => {
                let input = source.first_input;
                let id = source.id.copy_for_diagnostic();
                proof {
                    collected_source_origin(inputs@, sources@, file as int);
                    indexed_input_prefix(inputs@, sources@, indexes@, input as int);
                }
                assert(!project_source_set_accepts(inputs@));
                return Err(ProjectSourceParseError::File { input, id, revision: source.revision, error });
            }
        }
        file += 1;
    }
    proof {
        indexed_input_prefix(inputs@, sources@, indexes@, inputs@.len() as int);
        collected_source_ids_unique(inputs@, sources@);
    }
    Ok(ParsedProjectSources { sources, indexes, meta_asts })
}

}
