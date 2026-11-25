//! 正規化済みのソースを検査し、回復した宣言をファイル順に検索する。

use super::{CircuitEditorFile, PositionedBinding, RecoveredDeclarationQuery, inspect_circuit_file};
#[cfg(verus_only)]
use super::circuit_editor_source;
use crate::project::{NameKey, ProjectSource};
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// 同じプロジェクトのソースを借りて保持する、エディタ向けの回復結果。
pub struct CircuitEditorProject<'p, 'a> {
    sources: &'p [ProjectSource<'a>],
    files: Vec<Option<CircuitEditorFile<'p, 'a>>>,
}

/// 回復で確認でき、名前の検索条件に合う宣言の候補。
///
/// 名前解決や可視性を確定する前の結果。未確認の断片に宣言が残っている場合がある。
pub struct PartialCircuitDeclarations<'p, 'a> {
    /// ソースの並びに対応する候補列。各列は元ファイル内の順に並ぶ。
    pub files: Vec<Vec<PositionedBinding<'p, 'a>>>,
}

spec fn editor_file_matches(source: &ProjectSource, file: Option<CircuitEditorFile>) -> bool {
    match file {
        Some(file) => file.valid() && file.source_model() == source,
        None => !circuit_editor_source(source),
    }
}

impl<'p, 'a> CircuitEditorProject<'p, 'a> {
    /// 解析に用いたソースの列を表す。
    pub closed spec fn sources_model(&self) -> &'p [ProjectSource<'a>] {
        self.sources
    }

    /// 解析に使ったファイル識別子、文書バージョン、本文を入力順で返す。
    pub fn sources(&self) -> (sources: &'p [ProjectSource<'a>])
        ensures sources == self.sources_model(),
    {
        self.sources
    }

    /// ソースと同じ順に並ぶ各ファイルの回復結果を表す。
    pub closed spec fn files_model(&self) -> Seq<Option<CircuitEditorFile<'p, 'a>>> {
        self.files@
    }

    /// 各回復結果が、その位置のソースに対応することを表す。
    pub closed spec fn matches_sources(&self, sources: &'p [ProjectSource<'a>]) -> bool {
        &&& self.sources == sources
        &&& self.files@.len() == sources@.len()
        &&& forall|i: int| 0 <= i < sources@.len()
            ==> editor_file_matches(&sources@[i], #[trigger] self.files@[i])
    }

    #[verifier::type_invariant]
    spec fn file_sources_correspond(&self) -> bool {
        self.matches_sources(self.sources)
    }

    /// ソースの並びと同じ順で、ファイルごとの回復結果を返す。
    ///
    /// NCG2M など回路の回復解析の対象外に当たるファイルは `None`。
    pub fn files(&self) -> (files: &[Option<CircuitEditorFile<'p, 'a>>])
        ensures files@ == self.files_model(), self.matches_sources(self.sources_model()),
    {
        proof { use_type_invariant(self); }
        self.files.as_slice()
    }

    /// ファイル位置から、回復結果が使った元のソースを特定する。
    pub proof fn file_source_evidence(&self, index: int)
        requires self.matches_sources(self.sources_model()), 0 <= index < self.files_model().len(),
        ensures
            index < self.sources_model()@.len(),
            self.files_model()[index] matches Some(file) ==> file.valid()
                && file.source_model() == &self.sources_model()@[index],
    {
        assert(editor_file_matches(&self.sources_model()@[index], self.files_model()[index]));
    }


    /// プロジェクト内の各ファイルについて、回復で確認でき、検索条件に合う宣言の列であることを表す。
    pub open spec fn query_matches(
        &self, query: RecoveredDeclarationQuery, result: Seq<Vec<PositionedBinding<'p, 'a>>>,
    ) -> bool {
        let files = self.files_model();
        &&& result.len() == files.len()
        &&& forall|i: int| 0 <= i < files.len() ==> match files[i] {
            Some(file) => file.file_query_matches(query, (#[trigger] result[i])@),
            None => (#[trigger] result[i])@.len() == 0,
        }
    }

    /// 候補が照会時のファイルと、そのファイルの検査項目を指すことを示す。
    pub proof fn query_candidate_origin(
        &self, query: RecoveredDeclarationQuery, result: Seq<Vec<PositionedBinding<'p, 'a>>>, index: int, row: int,
    ) -> (position: (usize, usize))
        requires
            self.matches_sources(self.sources_model()),
            self.query_matches(query, result),
            0 <= index < result.len(),
            0 <= row < result[index]@.len(),
        ensures
            self.files_model()[index] matches Some(file) && {
                let names = file.recovered_names_model();
                let entry = result[index]@[row];
                &&& position.0 < names.position_group_count_model()
                &&& position.1 < names.position_count_model(position.0)
                &&& names.position_model(position.0, position.1) == Some(entry.0)
                &&& file.binding_matches(entry.0, Some(entry.1))
                &&& entry.1.location.source == &self.sources_model()@[index]
                &&& entry.1.matches_declaration_query(query)
            },
    {
        self.file_source_evidence(index);
        assert(self.files_model()[index] is Some);
        let file = self.files_model()[index]->Some_0;
        let rows = result[index]@;
        let position = file.file_query_origin(query, rows, row);
        file.observed_binding_origin(rows[row].0, rows[row].1);
        position
    }


    /// プロジェクトの回復結果から検索条件に合う宣言を集める。
    ///
    /// 条件に合う宣言が複数あればすべて返す。未確認の断片に宣言が残っている場合がある。
    pub fn query_declarations(&self, query: RecoveredDeclarationQuery) -> (result: PartialCircuitDeclarations<'p, 'a>)
        ensures self.query_matches(query, result.files@),
    {
        let files = self.files();
        let mut result: Vec<Vec<PositionedBinding<'p, 'a>>> = Vec::new();
        let mut i = 0usize;
        while i < files.len()
            invariant
                files@ == self.files_model(),
                i <= files@.len(),
                result@.len() == i,
                forall|j: int| 0 <= j < i ==> match files@[j] {
                    Some(file) => file.file_query_matches(query, (#[trigger] result@[j])@),
                    None => (#[trigger] result@[j])@.len() == 0,
                },
            decreases files@.len() - i,
        {
            let rows = match &files[i] {
                Some(file) => file.query_declarations(query),
                None => Vec::new(),
            };
            result.push(rows);
            i += 1;
        }
        PartialCircuitDeclarations { files: result }
    }
    /// プロジェクト内の各ファイルにある同名宣言と候補列の対応を表す。
    pub open spec fn candidates_match(
        &self, key: NameKey, result: Seq<Vec<PositionedBinding<'p, 'a>>>,
    ) -> bool {
        self.query_matches(RecoveredDeclarationQuery::Exact(key), result)
    }

    /// 同名宣言の候補が現れたファイル内の検査項目を特定する。
    pub proof fn candidate_origin(
        &self, key: NameKey, result: Seq<Vec<PositionedBinding<'p, 'a>>>, index: int, row: int,
    ) -> (position: (usize, usize))
        requires
            self.matches_sources(self.sources_model()),
            self.candidates_match(key, result),
            0 <= index < result.len(),
            0 <= row < result[index]@.len(),
        ensures
            self.files_model()[index] matches Some(file) && {
                let names = file.recovered_names_model();
                let entry = result[index]@[row];
                &&& position.0 < names.position_group_count_model()
                &&& position.1 < names.position_count_model(position.0)
                &&& names.position_model(position.0, position.1) == Some(entry.0)
                &&& file.binding_matches(entry.0, Some(entry.1))
                &&& entry.1.location.source == &self.sources_model()@[index]
                &&& entry.1.has_declaration_key(key)
            },
    {
        self.query_candidate_origin(RecoveredDeclarationQuery::Exact(key), result, index, row)
    }

    /// プロジェクトの回復結果から同じ完全修飾名の宣言を集める。
    ///
    /// 同名の宣言はすべて返す。未確認の断片に宣言があるかどうかは結果から判断できない。
    pub fn declaration_candidates(&self, key: NameKey) -> (result: PartialCircuitDeclarations<'p, 'a>)
        ensures self.candidates_match(key, result.files@),
    {
        self.query_declarations(RecoveredDeclarationQuery::Exact(key))
    }
}

/// 収集済みのソースを順に回復解析し、エディタで繰り返し照会できる状態にする。
///
/// ファイル識別子の重複を解消するには先に [`crate::project::collect_sources`] を使う。
/// 入力から確認できた候補は回復結果に残り、ファイルごとの構文診断と修復記録も参照できる。
pub fn inspect_circuit_project<'p, 'a>(sources: &'p [ProjectSource<'a>])
    -> (project: CircuitEditorProject<'p, 'a>)
    ensures project.matches_sources(sources),
{
    let mut files = Vec::new();
    let mut i = 0usize;
    while i < sources.len()
        invariant
            i <= sources@.len(),
            files@.len() == i,
            forall|j: int| 0 <= j < i ==> editor_file_matches(&sources@[j], #[trigger] files@[j]),
        decreases sources@.len() - i,
    {
        let file = inspect_circuit_file(&sources[i]);
        assert(editor_file_matches(&sources@[i as int], file));
        files.push(file);
        i += 1;
    }
    CircuitEditorProject { sources, files }
}

} // verus!
