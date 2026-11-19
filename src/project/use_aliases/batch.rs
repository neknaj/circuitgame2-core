//! 構文索引の全定義参照をファイルと元ソースの順序で解決する。

use super::{
    DefinitionReferenceError, DefinitionReferenceReason, DefinitionReferenceSite,
    ResolvedDefinitionReference, UseAliases,
};
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// 構文済みプロジェクトで一つの `def` の参照を指す添字。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DefinitionPosition {
    /// 正規化済みソース一覧の添字。
    pub file: usize,
    /// ファイルの厳格索引の添字。
    pub entry: usize,
    /// 索引項目に属する定義の添字。
    pub definition: usize,
    /// 定義の右辺に含まれる参照の添字。
    pub reference: usize,
}

/// 元の索引位置と、解決した回路名または型名。
#[derive(Debug)]
pub struct IndexedDefinitionBinding<'p, 'a> {
    /// 元の参照を構文木上でたどるための位置。
    pub position: DefinitionPosition,
    /// 名前を使った位置と、その解決結果。
    pub resolved: ResolvedDefinitionReference<'p, 'a>,
}

/// 全定義の参照を調べた際に最初に見つかった診断。
#[derive(Debug)]
pub struct DefinitionBatchError<'p, 'a> {
    /// 元の参照を構文木上でたどるための位置。
    pub position: DefinitionPosition,
    /// 診断の主範囲を含む参照元。
    pub site: DefinitionReferenceSite<'p, 'a>,
    /// 解決できなかった理由と関連箇所。
    pub reason: DefinitionReferenceReason<'p, 'a>,
}

spec fn before(a: DefinitionPosition, b: DefinitionPosition) -> bool {
    a.file < b.file || (a.file == b.file && (
        a.entry < b.entry || (a.entry == b.entry && (
            a.definition < b.definition || (a.definition == b.definition && a.reference < b.reference)
        ))
    ))
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn valid_reference(&self, at: DefinitionPosition) -> bool {
        self.position_exists(at.file, at.entry, at.definition, at.reference)
    }

    spec fn resolution_at(
        &self, at: DefinitionPosition, result: Result<ResolvedDefinitionReference, DefinitionReferenceError>,
    ) -> bool {
        self.definition_resolution_evidence(at.file, at.entry, at.definition, at.reference, result)
    }

    #[verifier::opaque]
    spec fn resolutions_before(
        &self, stop: DefinitionPosition, found: Seq<IndexedDefinitionBinding>,
    ) -> bool {
        &&& forall|i: int| 0 <= i < found.len() ==> {
            let item = #[trigger] found[i];
            &&& self.valid_reference(item.position)
            &&& before(item.position, stop)
            &&& self.resolution_at(item.position, Ok(item.resolved))
        }
        &&& forall|at: DefinitionPosition| #[trigger] self.valid_reference(at) && before(at, stop)
            ==> exists|i: int| 0 <= i < found.len() && (#[trigger] found[i]).position == at
        &&& forall|i: int, j: int| 0 <= i < j < found.len()
            ==> before((#[trigger] found[i]).position, (#[trigger] found[j]).position)
    }

    proof fn advance_empty(
        &self, at: DefinitionPosition, next: DefinitionPosition, found: Seq<IndexedDefinitionBinding>,
    )
        requires
            self.resolutions_before(at, found),
            before(at, next),
            forall|p: DefinitionPosition| #[trigger] self.valid_reference(p) && before(p, next) ==> before(p, at),
        ensures self.resolutions_before(next, found),
    {
        reveal(UseAliases::resolutions_before);
    }

    proof fn record(
        &self, at: DefinitionPosition, next: DefinitionPosition, found: Seq<IndexedDefinitionBinding>,
        item: IndexedDefinitionBinding,
    )
        requires
            self.resolutions_before(at, found),
            self.valid_reference(at),
            item.position == at,
            self.resolution_at(at, Ok(item.resolved)),
            next == (DefinitionPosition { reference: (at.reference + 1) as usize, ..at }),
            at.reference < usize::MAX,
        ensures self.resolutions_before(next, found.push(item)),
    {
        reveal(UseAliases::resolutions_before);
        let extended = found.push(item);
        assert forall|p: DefinitionPosition| #[trigger] self.valid_reference(p) && before(p, next)
            implies exists|i: int| 0 <= i < extended.len() && (#[trigger] extended[i]).position == p by {
            if before(p, at) {
                let i = choose|i: int| 0 <= i < found.len() && (#[trigger] found[i]).position == p;
                assert(extended[i] == found[i]);
            } else {
                assert(p == at);
                assert(extended[found.len() as int].position == p);
            }
        };
    }

    /// 解決結果が、構文済みプロジェクトの全定義参照に元ソース順で対応することを表す。
    pub closed spec fn definition_bindings_match(&self, found: Seq<IndexedDefinitionBinding>) -> bool {
        let file = self.targets.project_model().circuits_model().len() as usize;
        self.resolutions_before(DefinitionPosition { file, entry: 0, definition: 0, reference: 0 }, found)
    }

    /// 診断が、先行する参照をすべて解決した後の最初の違反に対応することを表す。
    pub closed spec fn definition_batch_error_evidence(&self, error: DefinitionBatchError) -> bool {
        &&& self.valid_reference(error.position)
        &&& self.resolution_at(error.position, Err(DefinitionReferenceError::Rejected { site: error.site, reason: error.reason }))
        &&& exists|prefix: Seq<IndexedDefinitionBinding>| #[trigger] self.resolutions_before(error.position, prefix)
    }

    /// 構文済みプロジェクトの全 `def` の右辺にある回路名と型名を解決する。
    ///
    /// 正規化済みソース一覧と各ファイルの元ソース順で解決する。別名検査で得た警告はこの処理の後も参照できる。
    ///
    /// # Errors
    ///
    /// 解決や用途の検査に失敗した最初の参照について、元ソースの範囲と理由を返す。
    pub fn resolve_definitions(&self)
        -> (result: Result<Vec<IndexedDefinitionBinding<'p, 'a>>, DefinitionBatchError<'p, 'a>>)
        requires self.can_resolve(),
        ensures match result {
            Ok(found) => self.definition_bindings_match(found@),
            Err(error) => self.definition_batch_error_evidence(error),
        },
    {
        let circuits = self.targets.project().circuits();
        let mut found = Vec::new();
        let mut at = DefinitionPosition { file: 0, entry: 0, definition: 0, reference: 0 };
        assert(self.resolutions_before(at, found@)) by { reveal(UseAliases::resolutions_before); }
        while at.file < circuits.len()
            invariant
                self.can_resolve(),
                circuits@ == self.targets.project_model().circuits_model(),
                at.file <= circuits@.len(),
                at.file == circuits@.len() ==> at.entry == 0 && at.definition == 0 && at.reference == 0,
                self.resolutions_before(at, found@),
            decreases
                circuits@.len() - at.file,
                if at.file < circuits@.len() { circuits@[at.file as int].definitions_by_entry@.len() - at.entry } else { 0 },
                if at.file < circuits@.len() && at.entry < circuits@[at.file as int].definitions_by_entry@.len() {
                    circuits@[at.file as int].definitions_by_entry@[at.entry as int]@.len() - at.definition
                } else { 0 },
                if self.valid_reference(at) {
                    circuits@[at.file as int].definitions_by_entry@[at.entry as int]@[at.definition as int].references@.len() - at.reference
                } else { 0 },
        {
            let rows = &circuits[at.file].definitions_by_entry;
            if at.entry >= rows.len() {
                let next = DefinitionPosition { file: at.file + 1, entry: 0, definition: 0, reference: 0 };
                proof { self.advance_empty(at, next, found@); }
                at = next;
                continue;
            }
            let definitions = &rows[at.entry];
            if at.definition >= definitions.len() {
                let next = DefinitionPosition { entry: at.entry + 1, definition: 0, reference: 0, ..at };
                proof { self.advance_empty(at, next, found@); }
                at = next;
                continue;
            }
            let references = &definitions[at.definition].references;
            if at.reference >= references.len() {
                let next = DefinitionPosition { definition: at.definition + 1, reference: 0, ..at };
                proof { self.advance_empty(at, next, found@); }
                at = next;
                continue;
            }
            assert(self.valid_reference(at));
            let result = self.resolve_definition_reference(at.file, at.entry, at.definition, at.reference);
            let resolved = match result {
                Ok(resolved) => resolved,
                Err(DefinitionReferenceError::Rejected { site, reason }) => {
                    let error = DefinitionBatchError { position: at, site, reason };
                    assert(self.definition_batch_error_evidence(error));
                    return Err(error);
                },
                Err(DefinitionReferenceError::UnknownPosition) => {
                    proof { self.valid_position_is_not_unknown(at.file, at.entry, at.definition, at.reference); }
                    unreachable!();
                },
            };
            let next = DefinitionPosition { reference: at.reference + 1, ..at };
            let item = IndexedDefinitionBinding { position: at, resolved };
            proof { self.record(at, next, found@, item); }
            found.push(item);
            at = next;
        }
        Ok(found)
    }
}

} // verus!
