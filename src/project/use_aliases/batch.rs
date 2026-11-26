//! 構文索引の全定義参照をファイルと元ソースの順序で解決する。

#[cfg(verus_only)]
use super::{definition_position_before as before, definition_position_progress, definition_position_remaining};
use super::DefinitionPositionStep;

use super::{
    DefinitionReferenceError, DefinitionReferenceReason, DefinitionReferenceSite,
    ResolvedDefinitionReference, UseAliases,
};
use alloc::vec::Vec;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

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

/// 定義内の参照を解決できなかった理由と位置。
#[derive(Debug)]
pub struct DefinitionBatchError<'p, 'a> {
    /// 元の参照を構文木上でたどるための位置。
    pub position: DefinitionPosition,
    /// 診断の主範囲を含む参照元。
    pub site: DefinitionReferenceSite<'p, 'a>,
    /// 解決できなかった理由と関連箇所。
    pub reason: DefinitionReferenceReason<'p, 'a>,
}

/// 構文が確定したプロジェクトの定義参照を調べた結果。
#[derive(Debug)]
pub struct DefinitionReferences<'p, 'a> {
    /// 解決できた参照。正規化済みソース一覧と各ファイルの元ソース順。
    pub bindings: Vec<IndexedDefinitionBinding<'p, 'a>>,
    /// 解決できなかった参照の診断。解決できた参照と同じ基準で並べる。
    pub diagnostics: Vec<DefinitionBatchError<'p, 'a>>,
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

    spec fn rejection_at(&self, item: DefinitionBatchError) -> bool {
        self.resolution_at(item.position, Err(DefinitionReferenceError::Rejected { site: item.site, reason: item.reason }))
    }

    #[verifier::opaque]
    spec fn resolutions_before(
        &self, stop: DefinitionPosition, found: Seq<IndexedDefinitionBinding>, errors: Seq<DefinitionBatchError>,
    ) -> bool {
        &&& forall|i: int| 0 <= i < found.len() ==> {
            let item = #[trigger] found[i];
            &&& self.valid_reference(item.position)
            &&& before(item.position, stop)
            &&& self.resolution_at(item.position, Ok(item.resolved))
        }
        &&& forall|i: int| 0 <= i < errors.len() ==> {
            let item = #[trigger] errors[i];
            &&& self.valid_reference(item.position)
            &&& before(item.position, stop)
            &&& self.rejection_at(item)
        }
        &&& forall|at: DefinitionPosition| #[trigger] self.valid_reference(at) && before(at, stop) ==> (
            (exists|i: int| 0 <= i < found.len() && (#[trigger] found[i]).position == at)
            || (exists|i: int| 0 <= i < errors.len() && (#[trigger] errors[i]).position == at)
        )
        &&& forall|i: int, j: int| 0 <= i < j < found.len()
            ==> before((#[trigger] found[i]).position, (#[trigger] found[j]).position)
        &&& forall|i: int, j: int| 0 <= i < j < errors.len()
            ==> before((#[trigger] errors[i]).position, (#[trigger] errors[j]).position)
        &&& forall|i: int, j: int| 0 <= i < found.len() && 0 <= j < errors.len()
            ==> (#[trigger] found[i]).position != (#[trigger] errors[j]).position
    }

    proof fn advance_empty(
        &self, at: DefinitionPosition, next: DefinitionPosition,
        found: Seq<IndexedDefinitionBinding>, errors: Seq<DefinitionBatchError>,
    )
        requires
            self.resolutions_before(at, found, errors),
            before(at, next),
            forall|p: DefinitionPosition| #[trigger] self.valid_reference(p) && before(p, next) ==> before(p, at),
        ensures self.resolutions_before(next, found, errors),
    {
        reveal(UseAliases::resolutions_before);
    }

    proof fn record(
        &self, at: DefinitionPosition, next: DefinitionPosition, found: Seq<IndexedDefinitionBinding>,
        errors: Seq<DefinitionBatchError>, item: IndexedDefinitionBinding,
    )
        requires
            self.resolutions_before(at, found, errors),
            self.valid_reference(at),
            item.position == at,
            self.resolution_at(at, Ok(item.resolved)),
            next == (DefinitionPosition { reference: (at.reference + 1) as usize, ..at }),
            at.reference < usize::MAX,
        ensures self.resolutions_before(next, found.push(item), errors),
    {
        reveal(UseAliases::resolutions_before);
        let extended = found.push(item);
        assert forall|p: DefinitionPosition| #[trigger] self.valid_reference(p) && before(p, next)
            implies (exists|i: int| 0 <= i < extended.len() && (#[trigger] extended[i]).position == p)
                || (exists|i: int| 0 <= i < errors.len() && (#[trigger] errors[i]).position == p) by {
            if before(p, at) {
                if exists|i: int| 0 <= i < found.len() && (#[trigger] found[i]).position == p {
                    let i = choose|i: int| 0 <= i < found.len() && (#[trigger] found[i]).position == p;
                    assert(extended[i] == found[i]);
                }
            } else {
                assert(p == at);
                assert(extended[found.len() as int].position == p);
            }
        };
    }

    proof fn record_rejection(
        &self, at: DefinitionPosition, next: DefinitionPosition, found: Seq<IndexedDefinitionBinding>,
        errors: Seq<DefinitionBatchError>, item: DefinitionBatchError,
    )
        requires
            self.resolutions_before(at, found, errors),
            self.valid_reference(at),
            item.position == at,
            self.rejection_at(item),
            next == (DefinitionPosition { reference: (at.reference + 1) as usize, ..at }),
            at.reference < usize::MAX,
        ensures self.resolutions_before(next, found, errors.push(item)),
    {
        reveal(UseAliases::resolutions_before);
        let extended = errors.push(item);
        assert forall|p: DefinitionPosition| #[trigger] self.valid_reference(p) && before(p, next)
            implies (exists|i: int| 0 <= i < found.len() && (#[trigger] found[i]).position == p)
                || (exists|i: int| 0 <= i < extended.len() && (#[trigger] extended[i]).position == p) by {
            if before(p, at) {
                if exists|i: int| 0 <= i < errors.len() && (#[trigger] errors[i]).position == p {
                    let i = choose|i: int| 0 <= i < errors.len() && (#[trigger] errors[i]).position == p;
                    assert(extended[i] == errors[i]);
                }
            } else {
                assert(p == at);
                assert(extended[errors.len() as int].position == p);
            }
        };
    }

    /// 解決結果が、構文済みプロジェクトの全定義参照に元ソース順で対応することを表す。
    pub closed spec fn definition_bindings_match(&self, found: Seq<IndexedDefinitionBinding>) -> bool {
        let file = self.targets.project_model().circuits_model().len() as usize;
        self.resolutions_before(DefinitionPosition { file, entry: 0, definition: 0, reference: 0 }, found, Seq::empty())
    }

    pub(super) proof fn definition_binding_at(&self, found: Seq<IndexedDefinitionBinding>, i: int)
        requires self.definition_bindings_match(found), 0 <= i < found.len(),
        ensures ({
            let item = found[i];
            let at = item.position;
            self.definition_resolution_evidence(at.file, at.entry, at.definition, at.reference, Ok(item.resolved))
        }),
    {
        reveal(UseAliases::resolutions_before);
    }

    pub(super) proof fn definition_binding_index(&self, found: Seq<IndexedDefinitionBinding>, at: DefinitionPosition)
        -> (i: int)
        requires
            self.definition_bindings_match(found),
            self.position_exists(at.file, at.entry, at.definition, at.reference),
        ensures 0 <= i < found.len(), found[i].position == at,
    {
        reveal(UseAliases::resolutions_before);
        let project = self.targets.project_model();
        project.circuit_count_fits();
        let stop = DefinitionPosition { file: project.circuits_model().len() as usize, entry: 0, definition: 0, reference: 0 };
        assert(self.valid_reference(at) && before(at, stop));
        choose|i: int| 0 <= i < found.len() && (#[trigger] found[i]).position == at
    }

    /// 診断が、先行する参照をすべて解決した後の最初の違反に対応することを表す。
    pub closed spec fn definition_batch_error_evidence(&self, error: DefinitionBatchError) -> bool {
        &&& self.valid_reference(error.position)
        &&& self.rejection_at(error)
        &&& exists|prefix: Seq<IndexedDefinitionBinding>| #[trigger] self.resolutions_before(error.position, prefix, Seq::empty())
    }

    /// 全参照がソース順の解決結果または根拠付きの診断に一度ずつ現れることを表す。
    pub closed spec fn definition_references_match(&self, result: DefinitionReferences) -> bool {
        let file = self.targets.project_model().circuits_model().len() as usize;
        self.resolutions_before(
            DefinitionPosition { file, entry: 0, definition: 0, reference: 0 },
            result.bindings@, result.diagnostics@,
        )
    }

    /// 診断の根拠と、主範囲が解析時のファイルと版に属することを示す。
    pub proof fn definition_reference_diagnostic_at(
        &self, project: &crate::project::CircuitProject, targets: &super::UseTargets,
        result: DefinitionReferences, index: int,
    )
        requires
            crate::project::use_targets_match(project, *targets),
            super::use_aliases_match(targets, *self),
            self.definition_references_match(result),
            0 <= index < result.diagnostics@.len(),
        ensures ({
            let item = result.diagnostics@[index];
            let at = item.position;
            let span = item.site.name.span;
            let text = item.site.source.text_model().spec_bytes();
            &&& self.definition_resolution_evidence(at.file, at.entry, at.definition, at.reference,
                Err(DefinitionReferenceError::Rejected { site: item.site, reason: item.reason }))
            &&& at.file < project.sources_model().len()
            &&& *item.site.source == project.sources_model()[at.file as int]
            &&& span.start < span.end <= text.len()
            &&& vstd::utf8::is_char_boundary(text, span.start as int)
            &&& vstd::utf8::is_char_boundary(text, span.end as int)
        }),
    {
        reveal(UseAliases::resolutions_before);
        let item = result.diagnostics@[index];
        targets.matched_project(project);
        self.rejected_reference_location(item.position, item.site, item.reason);
        item.site.source.text_model_is_text();
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
        match self.scan_definitions(false) {
            Ok(result) => Ok(result.bindings),
            Err(error) => Err(error),
        }
    }

    /// 構文が確定したプロジェクトの各定義参照を解決する。
    ///
    /// 一つの参照を解決できなくても後続を調べる。返す診断の主範囲と関連箇所は
    /// 解析に使ったソースの版を指す。[`crate::project::check_use_aliases`]
    /// が返した別名表を使う。
    pub fn resolve_definitions_with_diagnostics(&self) -> (result: DefinitionReferences<'p, 'a>)
        requires self.can_resolve(),
        ensures self.definition_references_match(result),
    {
        match self.scan_definitions(true) {
            Ok(result) => result,
            Err(_) => unreachable!(),
        }
    }

    fn scan_definitions(&self, keep_going: bool)
        -> (result: Result<DefinitionReferences<'p, 'a>, DefinitionBatchError<'p, 'a>>)
        requires self.can_resolve(),
        ensures match result {
            Ok(result) => self.definition_references_match(result)
                && (!keep_going ==> self.definition_bindings_match(result.bindings@)),
            Err(error) => !keep_going && self.definition_batch_error_evidence(error),
        },
    {
        let project = self.targets.project();
        let circuits = project.circuits();
        let mut found = Vec::new();
        let mut errors = Vec::new();
        let mut positions = project.definition_positions();
        let mut at = positions.position();
        assert(self.resolutions_before(at, found@, errors@)) by { reveal(UseAliases::resolutions_before); }
        while at.file < circuits.len()
            invariant
                self.can_resolve(),
                circuits@ == self.targets.project_model().circuits_model(),
                *project == self.targets.project_model(),
                positions.valid(), positions.project_model() == project, at == positions.position_model(),
                !keep_going ==> errors@ == Seq::<DefinitionBatchError>::empty(),
                self.resolutions_before(at, found@, errors@),
            decreases
                definition_position_remaining(project, at).0, definition_position_remaining(project, at).1,
                definition_position_remaining(project, at).2, definition_position_remaining(project, at).3,
        {
            let step = positions.step();
            let next = positions.position();
            assert(step !is Finished ==> definition_position_progress(project, at, next));
            match step {
                DefinitionPositionStep::Finished => {
                    proof { assert(false); }
                    unreachable!();
                },
                DefinitionPositionStep::Advanced => {
                    proof { self.advance_empty(at, next, found@, errors@); }
                    at = next;
                    continue;
                },
                DefinitionPositionStep::Reference(_reference) => {
                    assert(_reference == at);
                },
            }
            let result = self.resolve_definition_reference(at.file, at.entry, at.definition, at.reference);
            match result {
                Ok(resolved) => {
                    let item = IndexedDefinitionBinding { position: at, resolved };
                    proof { self.record(at, next, found@, errors@, item); }
                    found.push(item);
                },
                Err(DefinitionReferenceError::Rejected { site, reason }) => {
                    let error = DefinitionBatchError { position: at, site, reason };
                    if !keep_going {
                        assert(self.definition_batch_error_evidence(error)) by {
                            assert(self.rejection_at(error));
                            assert(self.resolutions_before(at, found@, Seq::empty()));
                        };
                        return Err(error);
                    }
                    proof { self.record_rejection(at, next, found@, errors@, error); }
                    errors.push(error);
                },
                Err(DefinitionReferenceError::UnknownPosition) => {
                    proof { self.valid_position_is_not_unknown(at.file, at.entry, at.definition, at.reference); }
                    unreachable!();
                },
            }
            at = next;
        }
        Ok(DefinitionReferences { bindings: found, diagnostics: errors })
    }
}

} // verus!
