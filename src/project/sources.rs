//! メモリ上の入力を仮想ファイル識別子でまとめる。

use super::{PathError, SourceKind, VirtualPath, normalize_path};
#[cfg(verus_only)]
use super::{normalized_path, source_kind_of};
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// ホストから受け取ったソースのスナップショット。
#[derive(Debug)]
pub struct SourceSnapshot<'a> {
    /// プロジェクトルートを基準とする仮想パス。
    pub path: &'a str,
    /// ホストが付けた文書バージョン。
    pub revision: u64,
    /// 指定された文書バージョンの UTF-8 テキスト。
    pub text: &'a str,
}

/// 一意なファイル識別子と、それに対応するソースのバージョンと本文。
#[derive(Debug)]
pub struct ProjectSource<'a> {
    /// 正規化済みのファイル識別子。
    pub id: VirtualPath<'a>,
    /// 最終成分の拡張子で決まる言語。
    pub kind: SourceKind,
    /// この本文に対応する文書バージョン。
    pub revision: u64,
    /// 指定された文書バージョンの UTF-8 テキスト。
    pub text: &'a str,
    pub(super) first_input: usize,
}

/// ソースをファイル識別子で整理できなかった理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SourceSetError {
    /// 仮想パスを正規化できなかった。
    Path {
        /// 入力スナップショットの添字。
        input: usize,
        /// パスに違反した理由。
        error: PathError,
    },
    /// 拡張子が対応するソース言語を表していない。
    UnsupportedExtension {
        /// 入力スナップショットの添字。
        input: usize,
    },
    /// 同じファイル識別子にバージョンまたは本文が異なる入力がある。
    ConflictingSnapshot {
        /// 最初に現れた入力スナップショットの添字。
        first: usize,
        /// 異なるバージョンまたは本文を持つ入力スナップショットの添字。
        input: usize,
    },
}

pub(super) open spec fn snapshot_matches(input: SourceSnapshot, source: ProjectSource) -> bool {
    &&& normalized_path(input.path) == Ok(source.id.components_model())
    &&& source_kind_of(source.id.components_model()) == Some(source.kind)
    &&& input.revision == source.revision && input.text@ == source.text@
}

spec fn input_is_represented(input: SourceSnapshot, sources: Seq<ProjectSource>) -> bool {
    exists|at: int| 0 <= at < sources.len() && #[trigger] snapshot_matches(input, sources[at])
}

pub open spec fn first_source_input(inputs: Seq<SourceSnapshot>, index: int) -> bool {
    &&& 0 <= index < inputs.len()
    &&& forall|previous: int| 0 <= previous < index ==>
        normalized_path((#[trigger] inputs[previous]).path) != normalized_path(inputs[index].path)
}

spec fn source_origin(inputs: Seq<SourceSnapshot>, source: ProjectSource, count: int) -> bool {
    &&& source.first_input < count <= inputs.len()
    &&& snapshot_matches(inputs[source.first_input as int], source)
    &&& inputs[source.first_input as int].text == source.text
    &&& first_source_input(inputs, source.first_input as int)
}

#[verifier::opaque]
spec fn source_prefix_matches(inputs: Seq<SourceSnapshot>, sources: Seq<ProjectSource>, count: int) -> bool {
    &&& 0 <= count <= inputs.len()
    &&& forall|i: int| 0 <= i < sources.len() ==> #[trigger] source_origin(inputs, sources[i], count)
    &&& forall|i: int| 0 <= i < count ==> #[trigger] input_is_represented(inputs[i], sources)
    &&& forall|i: int, j: int| 0 <= i < j < sources.len() ==> {
        let left = #[trigger] sources[i];
        let right = #[trigger] sources[j];
        left.id.components_model() != right.id.components_model() && left.first_input < right.first_input
    }
}

/// 各仮想ファイル識別子がちょうど一件あり、バージョン、本文、言語が入力に対応することを表す。
pub closed spec fn project_sources_match(inputs: Seq<SourceSnapshot>, sources: Seq<ProjectSource>) -> bool {
    source_prefix_matches(inputs, sources, inputs.len() as int)
}

/// ソース列に同じ正規化済みファイル識別子が二度現れないことを表す。
pub closed spec fn source_ids_unique(sources: Seq<ProjectSource>) -> bool {
    forall|i: int, j: int| 0 <= i < j < sources.len() ==>
        (#[trigger] sources[i]).id.components_model() != (#[trigger] sources[j]).id.components_model()
}

/// 収集済みのソース列では、正規化済みファイル識別子が一意に定まる。
pub(super) proof fn collected_source_ids_unique(inputs: Seq<SourceSnapshot>, sources: Seq<ProjectSource>)
    requires project_sources_match(inputs, sources),
    ensures source_ids_unique(sources),
{
    reveal(source_prefix_matches);
}

/// 同じソース列の二つの位置で、ファイル識別子が一致するのは添字が等しいときに限る。
pub(super) proof fn source_ordinals_agree(sources: Seq<ProjectSource>, left: int, right: int)
    requires source_ids_unique(sources), 0 <= left < sources.len(), 0 <= right < sources.len(),
    ensures left == right
        <==> sources[left].id.components_model() == sources[right].id.components_model(),
{
}

pub(super) proof fn collected_source_origin(
    inputs: Seq<SourceSnapshot>, sources: Seq<ProjectSource>, index: int,
)
    requires
        project_sources_match(inputs, sources),
        0 <= index < sources.len(),
    ensures
        sources[index].first_input < inputs.len(),
        snapshot_matches(inputs[sources[index].first_input as int], sources[index]),
        inputs[sources[index].first_input as int].text == sources[index].text,
        first_source_input(inputs, sources[index].first_input as int),
{
    reveal(source_prefix_matches);
    assert(source_origin(inputs, sources[index], inputs.len() as int));
}

pub(super) proof fn collected_source_for_input(
    inputs: Seq<SourceSnapshot>, sources: Seq<ProjectSource>, index: int,
)
    requires
        project_sources_match(inputs, sources),
        first_source_input(inputs, index),
    ensures exists|file: int| 0 <= file < sources.len()
        && #[trigger] snapshot_matches(inputs[index], sources[file])
        && sources[file].first_input == index && sources[file].text == inputs[index].text,
{
    reveal(source_prefix_matches);
    assert(input_is_represented(inputs[index], sources));
    let file = choose|file: int| 0 <= file < sources.len() && #[trigger] snapshot_matches(inputs[index], sources[file]);
    let source = sources[file];
    assert(source_origin(inputs, source, inputs.len() as int));
    assert(source.first_input == index);
}

pub(super) proof fn collected_sources_follow_input_order(
    inputs: Seq<SourceSnapshot>, sources: Seq<ProjectSource>, earlier: int, later: int,
)
    requires
        project_sources_match(inputs, sources),
        0 <= earlier < sources.len(),
        0 <= later < sources.len(),
        sources[earlier].first_input < sources[later].first_input,
    ensures earlier < later,
{
    reveal(source_prefix_matches);
    if later < earlier {
        assert(sources[later].first_input < sources[earlier].first_input);
    }
}

/// 全入力が対応するソースを指し、同じ識別子の入力は同じバージョンと本文を持つことを表す。
pub open spec fn valid_source_snapshots(inputs: Seq<SourceSnapshot>) -> bool {
    &&& forall|i: int| 0 <= i < inputs.len() ==> {
        let input = #[trigger] inputs[i];
        normalized_path(input.path) matches Ok(id) && source_kind_of(id) is Some
    }
    &&& forall|i: int, j: int| 0 <= i < j < inputs.len()
        && normalized_path((#[trigger] inputs[i]).path).is_ok()
        && normalized_path(inputs[i].path) == normalized_path((#[trigger] inputs[j]).path) ==>
            inputs[i].revision == inputs[j].revision && inputs[i].text@ == inputs[j].text@
}

/// パス、拡張子、または同じファイルを指す二つの入力の違反を表す。
pub open spec fn source_set_error(inputs: Seq<SourceSnapshot>, error: SourceSetError) -> bool {
    match error {
        SourceSetError::Path { input, error } => input < inputs.len()
            && normalized_path(inputs[input as int].path) == Err(error),
        SourceSetError::UnsupportedExtension { input } => input < inputs.len()
            && (normalized_path(inputs[input as int].path) matches Ok(id) && source_kind_of(id) is None),
        SourceSetError::ConflictingSnapshot { first, input } => first < input < inputs.len()
            && normalized_path(inputs[first as int].path).is_ok()
            && normalized_path(inputs[first as int].path) == normalized_path(inputs[input as int].path)
            && (inputs[first as int].revision != inputs[input as int].revision
                || inputs[first as int].text@ != inputs[input as int].text@)
            && (forall|previous: int| 0 <= previous < first ==>
                normalized_path((#[trigger] inputs[previous]).path) != normalized_path(inputs[first as int].path)),
    }
}

fn find_source(sources: &[ProjectSource], id: &VirtualPath) -> (result: Option<usize>)
    ensures
        forall|i: int| 0 <= i < sources@.len() ==>
            ((#[trigger] sources@[i]).id.components_model() == id.components_model() ==> result.is_some()),
        result matches Some(index) ==> index < sources@.len()
            && sources@[index as int].id.components_model() == id.components_model(),
{
    let mut index = 0;
    while index < sources.len()
        invariant
            index <= sources@.len(),
            forall|i: int| 0 <= i < index ==>
                (#[trigger] sources@[i]).id.components_model() != id.components_model(),
        decreases sources@.len() - index,
    {
        if id.same_file(&sources[index].id) {
            return Some(index);
        }
        index += 1;
    }
    None
}

proof fn record_input(
    inputs: Seq<SourceSnapshot>, sources: Seq<ProjectSource>, count: int, found: int,
)
    requires
        source_prefix_matches(inputs, sources, count),
        0 <= count < inputs.len(),
        0 <= found < sources.len(),
        snapshot_matches(inputs[count], sources[found]),
    ensures source_prefix_matches(inputs, sources, count + 1),
{
    reveal(source_prefix_matches);
    assert forall|i: int| 0 <= i < sources.len() implies #[trigger] source_origin(inputs, sources[i], count + 1) by {
        assert(source_origin(inputs, sources[i], count));
    };
    assert forall|i: int| 0 <= i < count + 1 implies #[trigger] input_is_represented(inputs[i], sources) by {
        if i == count {
            assert(snapshot_matches(inputs[i], sources[found]));
        } else {
            assert(input_is_represented(inputs[i], sources));
        }
    };
}

proof fn append_source(
    inputs: Seq<SourceSnapshot>, sources: Seq<ProjectSource>, count: int, source: ProjectSource,
)
    requires
        source_prefix_matches(inputs, sources, count),
        0 <= count < inputs.len(),
        source.first_input == count,
        snapshot_matches(inputs[count], source),
        inputs[count].text == source.text,
        forall|i: int| 0 <= i < sources.len() ==>
            (#[trigger] sources[i]).id.components_model() != source.id.components_model(),
    ensures source_prefix_matches(inputs, sources.push(source), count + 1),
{
    reveal(source_prefix_matches);
    let extended = sources.push(source);
    assert forall|prior: int| 0 <= prior < count implies
        normalized_path((#[trigger] inputs[prior]).path) != Ok(source.id.components_model()) by {
        assert(input_is_represented(inputs[prior], sources));
        let at = choose|at: int| 0 <= at < sources.len() && #[trigger] snapshot_matches(inputs[prior], sources[at]);
        assert(normalized_path(inputs[prior].path) == Ok(sources[at].id.components_model()));
    };
    assert forall|i: int| 0 <= i < extended.len() implies #[trigger] source_origin(inputs, extended[i], count + 1) by {
        if i < sources.len() {
            assert(extended[i] == sources[i]);
            assert(source_origin(inputs, sources[i], count));
        } else {
            assert(extended[i] == source);
        }
    };
    assert forall|i: int, j: int| 0 <= i < j < extended.len() implies {
        let left = #[trigger] extended[i];
        let right = #[trigger] extended[j];
        left.id.components_model() != right.id.components_model() && left.first_input < right.first_input
    } by {
        assert(extended[i] == sources[i]);
        if j < sources.len() {
            assert(extended[j] == sources[j]);
            assert(sources[i].first_input < sources[j].first_input);
            assert(sources[i].id.components_model() != sources[j].id.components_model());
        } else {
            assert(extended[j] == source);
            assert(source_origin(inputs, sources[i], count));
            assert(sources[i].id.components_model() != source.id.components_model());
        }
    };
    assert forall|i: int| 0 <= i < count + 1 implies #[trigger] input_is_represented(inputs[i], extended) by {
        if i == count {
            assert(extended[sources.len() as int] == source);
            assert(snapshot_matches(inputs[i], extended[sources.len() as int]));
        } else {
            assert(input_is_represented(inputs[i], sources));
            let at = choose|at: int| 0 <= at < sources.len() && #[trigger] snapshot_matches(inputs[i], sources[at]);
            assert(extended[at] == sources[at]);
            assert(snapshot_matches(inputs[i], extended[at]));
        }
    };
}

proof fn source_set_is_consistent(inputs: Seq<SourceSnapshot>, sources: Seq<ProjectSource>)
    requires project_sources_match(inputs, sources),
    ensures valid_source_snapshots(inputs),
{
    reveal(source_prefix_matches);
    assert forall|i: int| 0 <= i < inputs.len() implies {
        let input = #[trigger] inputs[i];
        normalized_path(input.path) matches Ok(id) && source_kind_of(id) is Some
    } by {
        assert(input_is_represented(inputs[i], sources));
        let at = choose|at: int| 0 <= at < sources.len() && #[trigger] snapshot_matches(inputs[i], sources[at]);
        assert(source_kind_of(sources[at].id.components_model()) == Some(sources[at].kind));
    };
    assert forall|i: int, j: int| 0 <= i < j < inputs.len()
        && normalized_path((#[trigger] inputs[i]).path).is_ok()
        && normalized_path(inputs[i].path) == normalized_path((#[trigger] inputs[j]).path) implies
            inputs[i].revision == inputs[j].revision && inputs[i].text@ == inputs[j].text@ by {
        assert(input_is_represented(inputs[i], sources));
        assert(input_is_represented(inputs[j], sources));
        let left = choose|at: int| 0 <= at < sources.len() && #[trigger] snapshot_matches(inputs[i], sources[at]);
        let right = choose|at: int| 0 <= at < sources.len() && #[trigger] snapshot_matches(inputs[j], sources[at]);
        assert(sources[left].id.components_model() == sources[right].id.components_model());
        assert(left == right);
    };
}

/// 仮想パスを正規化し、同じファイルの同じバージョンと本文を一件にまとめる。
///
/// 返すソースは、それぞれが入力に最初に現れた順に並ぶ。ファイルの同一性は正規化した成分で決まる。
///
/// # Errors
///
/// パスまたは拡張子の違反、同じ識別子に異なるバージョンや本文がある場合の衝突を報告する。
pub fn collect_sources<'a>(inputs: &[SourceSnapshot<'a>]) -> (result: Result<Vec<ProjectSource<'a>>, SourceSetError>)
    ensures
        result.is_ok() <==> valid_source_snapshots(inputs@),
        match result {
            Ok(sources) => project_sources_match(inputs@, sources@),
            Err(error) => source_set_error(inputs@, error),
        },
{
    let mut sources: Vec<ProjectSource> = Vec::new();
    let mut index = 0;
    assert(source_prefix_matches(inputs@, sources@, 0)) by { reveal(source_prefix_matches); }
    while index < inputs.len()
        invariant
            index <= inputs@.len(),
            source_prefix_matches(inputs@, sources@, index as int),
        decreases inputs@.len() - index,
    {
        let input = &inputs[index];
        let id = match normalize_path(input.path) {
            Ok(id) => id,
            Err(error) => {
                assert(!valid_source_snapshots(inputs@));
                return Err(SourceSetError::Path { input: index, error });
            }
        };
        let Some(kind) = id.source_kind() else {
            assert(!valid_source_snapshots(inputs@));
            return Err(SourceSetError::UnsupportedExtension { input: index });
        };
        if let Some(found) = find_source(&sources, &id) {
            let existing = &sources[found];
            if input.revision != existing.revision || input.text != existing.text {
                proof {
                    reveal(source_prefix_matches);
                    assert(source_origin(inputs@, *existing, index as int));
                    assert(snapshot_matches(inputs@[existing.first_input as int], *existing));
                    assert(!valid_source_snapshots(inputs@));
                }
                return Err(SourceSetError::ConflictingSnapshot { first: existing.first_input, input: index });
            }
            proof {
                reveal(source_prefix_matches);
                assert(source_origin(inputs@, *existing, index as int));
                assert(snapshot_matches(inputs@[existing.first_input as int], *existing));
                assert(snapshot_matches(inputs@[index as int], *existing));
                record_input(inputs@, sources@, index as int, found as int);
            }
        } else {
            let source = ProjectSource {
                id, kind, revision: input.revision, text: input.text, first_input: index,
            };
            proof { append_source(inputs@, sources@, index as int, source); }
            sources.push(source);
        }
        index += 1;
    }
    proof { source_set_is_consistent(inputs@, sources@); }
    Ok(sources)
}

} // verus!
