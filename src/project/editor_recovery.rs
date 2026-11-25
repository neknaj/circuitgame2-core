//! 回復後も確認できる宣言と名前空間を、元のソースに結び付ける。

use alloc::vec::Vec;
use super::declarations::defines_binding;
#[cfg(verus_only)]
use super::name_keys::key_bytes;
#[cfg(verus_only)]
use super::declarations::named_binding;
use super::{LocatedName, NameKey, ProjectSource, SourceKind};
#[cfg(verus_only)]
use super::source_kind_of;
use crate::syntax::circuit::{Head, RecoveredNamePosition, RecoveredNames, recover_circuit_names};
#[cfg(verus_only)]
use crate::syntax::circuit::RecoveredName;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(verus_only)]
use vstd::utf8::is_char_boundary;

verus! {

/// 元の回路フォームで確認できた宣言または名前空間。
#[derive(Debug)]
pub struct ObservedCircuitBinding<'p, 'a> {
    /// 宣言名または名前空間パスが現れたファイルとバイト範囲。
    pub location: LocatedName<'p, 'a>,
    /// 宣言の照合キー、または名前空間のパス。
    pub kind: ObservedCircuitBindingKind<'a>,
}

/// 回復解析で確認できた名前の種類。
#[derive(Debug)]
pub enum ObservedCircuitBindingKind<'a> {
    /// 独立した回路宣言。
    Declaration {
        /// 元のフォームの種別。
        head: Head,
        /// 所属する名前空間と宣言名。
        key: NameKey<'a>,
    },
    /// 元のフォームに書かれた名前空間。パスはルートからの全成分を含む。
    Namespace(&'a str),
}

/// 回路ソースと、そのファイルから回復した名前。
pub struct CircuitEditorFile<'p, 'a> {
    source: &'p ProjectSource<'a>,
    names: RecoveredNames<'a>,
}

spec fn observed_binding<'p, 'a>(
    source: &'p ProjectSource<'a>, name: RecoveredName<'a>,
) -> Option<ObservedCircuitBinding<'p, 'a>> {
    if !named_binding(name.head) {
        None
    } else {
        Some(ObservedCircuitBinding {
            location: LocatedName { source, span: name.name.span },
            kind: if name.head is Namespace {
                ObservedCircuitBindingKind::Namespace(name.name.word)
            } else {
                let parent = match name.namespace {
                    Some(site) => Some(site.word),
                    None => None,
                };
                ObservedCircuitBindingKind::Declaration {
                    head: name.head,
                    key: NameKey { parent, name: name.name.word },
                }
            },
        })
    }
}

impl<'p, 'a> CircuitEditorFile<'p, 'a> {
    /// 解析に用いたファイルを表す。
    pub closed spec fn source_model(&self) -> &'p ProjectSource<'a> {
        self.source
    }

    /// ファイルの本文と名前の回復結果が対応することを表す。
    pub closed spec fn valid(&self) -> bool {
        circuit_editor_source(self.source) && self.names.valid()
            && self.names.source_model() == self.source.text_model()
    }

    #[verifier::type_invariant]
    spec fn source_matches_names(&self) -> bool {
        self.valid()
    }

    /// 解析に用いたファイル識別子、文書バージョン、本文を返す。
    pub fn source(&self) -> (source: &'p ProjectSource<'a>)
        ensures source == self.source_model(),
    {
        self.source
    }

    /// 元の本文から得た構文の回復結果を表す。
    pub closed spec fn recovered_names_model(&self) -> &RecoveredNames<'a> {
        &self.names
    }

    /// 元のフォームの名前を選び、診断と修復記録を参照するための回復結果を返す。
    pub fn recovered_names(&self) -> (names: &RecoveredNames<'a>)
        ensures
            names == self.recovered_names_model(),
            names.valid(), names.source_model() == self.source_model().text_model(),
    {
        proof { use_type_invariant(self); }
        &self.names
    }

    /// 選んだフォームの名前と、回復後に確認できる宣言または名前空間との対応を表す。
    pub closed spec fn binding_matches(
        &self, position: RecoveredNamePosition, binding: Option<ObservedCircuitBinding<'p, 'a>>,
    ) -> bool {
        exists|name: Option<RecoveredName<'a>>| #[trigger] self.names.name_matches(position, name)
            && binding == match name {
                Some(name) => observed_binding(self.source, name),
                None => None,
            }
    }

    /// 回復後に確認できた宣言の元フォームを、名前の回復結果から特定する。
    pub proof fn observed_binding_origin(
        &self, position: RecoveredNamePosition, binding: ObservedCircuitBinding<'p, 'a>,
    )
        requires self.binding_matches(position, Some(binding)),
        ensures exists|name: RecoveredName<'a>|
            #[trigger] self.recovered_names_model().name_matches(position, Some(name))
            && binding.location.source == self.source_model()
            && binding.location.span == name.name.span
            && match binding.kind {
                ObservedCircuitBindingKind::Declaration { head, key } => head == name.head
                    && key.name == name.name.word
                    && key.parent == match name.namespace {
                        Some(parent) => Some(parent.word),
                        None => None,
                    },
                ObservedCircuitBindingKind::Namespace(path) => name.head is Namespace && path == name.name.word,
            },
    {
        let candidate = choose|name: Option<RecoveredName<'a>>| #[trigger] self.names.name_matches(position, name)
            && Some(binding) == match name {
                Some(name) => observed_binding(self.source, name),
                None => None,
            };
        assert(candidate.is_some());
        let name = candidate->Some_0;
        assert(candidate == Some(name));
        assert(self.recovered_names_model().name_matches(position, Some(name)));
        assert(Some(binding) == observed_binding(self.source, name));
    }

    /// 選んだ元フォームの宣言または名前空間を返す。
    ///
    /// 対象外の位置やフォームでは `None` を返す。`module-part` の対象名は独立宣言に含めない。
    /// この結果から確認できるのはフォームの出現であり、名前の一意性や可視性の判定には全体の名前解決が必要。
    pub fn observed_binding_at(
        &self, position: RecoveredNamePosition,
    ) -> (binding: Option<ObservedCircuitBinding<'p, 'a>>)
        ensures
            self.binding_matches(position, binding),
            binding matches Some(binding) ==> {
                let bytes = self.source_model().text_model().spec_bytes();
                let span = binding.location.span;
                let word = match binding.kind {
                    ObservedCircuitBindingKind::Declaration { key, .. } => key.name,
                    ObservedCircuitBindingKind::Namespace(path) => path,
                };
                &&& binding.location.source == self.source_model()
                &&& span.start < span.end <= bytes.len()
                &&& is_char_boundary(bytes, span.start as int) && is_char_boundary(bytes, span.end as int)
                &&& word.spec_bytes() == bytes[span.start as int..span.end as int]
            },
    {
        proof { use_type_invariant(self); }
        let result = self.names.name_at(position);
        let Some(name) = result else {
            return None;
        };
        if !defines_binding(name.head) {
            return None;
        }
        proof { self.names.name_uses_source_ranges(position, name); }
        let kind = if matches!(name.head, Head::Namespace) {
            ObservedCircuitBindingKind::Namespace(name.name.word)
        } else {
            let parent = match name.namespace {
                Some(site) => Some(site.word),
                None => None,
            };
            ObservedCircuitBindingKind::Declaration {
                head: name.head,
                key: NameKey { parent, name: name.name.word },
            }
        };
        Some(ObservedCircuitBinding {
            location: LocatedName { source: self.source, span: name.name.span },
            kind,
        })
    }
}

type PositionedBinding<'p, 'a> = (RecoveredNamePosition, ObservedCircuitBinding<'p, 'a>);

impl ObservedCircuitBinding<'_, '_> {
    /// 独立宣言が指定した完全修飾名を持つことを表す。
    pub open spec fn has_declaration_key(&self, key: NameKey) -> bool {
        match self.kind {
            ObservedCircuitBindingKind::Declaration { key: candidate, .. } => key_bytes(candidate) == key_bytes(key),
            ObservedCircuitBindingKind::Namespace(_) => false,
        }
    }
}

spec fn is_candidate_result(binding: Option<ObservedCircuitBinding>, key: NameKey) -> bool {
    binding matches Some(binding) && binding.has_declaration_key(key)
}

proof fn candidates_agree(
    file: &CircuitEditorFile, position: RecoveredNamePosition, key: NameKey,
    left: Option<ObservedCircuitBinding>, right: Option<ObservedCircuitBinding>,
)
    requires file.binding_matches(position, left), file.binding_matches(position, right),
    ensures is_candidate_result(left, key) == is_candidate_result(right, key),
{
    reveal(CircuitEditorFile::binding_matches);
    let names = file.recovered_names_model();
    let source = file.source_model();
    let a = choose|name: Option<RecoveredName>| #[trigger] names.name_matches(position, name)
        && left == match name {
            Some(name) => observed_binding(source, name),
            None => None,
        };
    let b = choose|name: Option<RecoveredName>| #[trigger] names.name_matches(position, name)
        && right == match name {
            Some(name) => observed_binding(source, name),
            None => None,
        };
    names.names_agree_at(position, a, b);
}

proof fn exclude_candidate(
    file: &CircuitEditorFile, position: RecoveredNamePosition, key: NameKey,
    result: Option<ObservedCircuitBinding>,
)
    requires file.binding_matches(position, result), !is_candidate_result(result, key),
    ensures forall|binding: ObservedCircuitBinding|
        #[trigger] file.binding_matches(position, Some(binding)) ==> !binding.has_declaration_key(key),
{
    assert forall|binding: ObservedCircuitBinding|
        #[trigger] file.binding_matches(position, Some(binding)) implies !binding.has_declaration_key(key) by {
        candidates_agree(file, position, key, result, Some(binding));
    };
}


spec fn observes_candidate(
    file: &CircuitEditorFile, key: NameKey, group: usize, item: usize, row: Option<PositionedBinding>,
) -> bool {
    match file.recovered_names_model().position_model(group, item) {
        None => row.is_none(),
        Some(position) => match row {
            Some((at, binding)) => at == position
                && file.binding_matches(position, Some(binding)) && binding.has_declaration_key(key),
            None => forall|binding: ObservedCircuitBinding|
                #[trigger] file.binding_matches(position, Some(binding)) ==> !binding.has_declaration_key(key),
        },
    }
}

#[verifier::opaque]
spec fn candidate_group_prefix(
    file: &CircuitEditorFile, key: NameKey, group: usize, rows: Seq<PositionedBinding>, rank: Seq<nat>,
) -> bool {
    &&& rank.len() > 0
    &&& forall|i: int| 0 <= i < rank.len() - 1 ==> {
        let first = #[trigger] rank[i];
        let next = rank[i + 1];
        &&& first <= next <= rows.len()
        &&& next <= first + 1
        &&& observes_candidate(file, key, group, i as usize,
            if first == next { None } else { Some(rows[first as int]) })
    }
}

proof fn item_for_candidate(rank: Seq<nat>, row: int, from: int, end: int) -> (item: int)
    requires
        0 <= from < end < rank.len(),
        rank[from] <= row < rank[end],
        forall|i: int| from <= i < end ==> #[trigger] rank[i + 1] <= rank[i] + 1,
    ensures from <= item < end, rank[item] == row, rank[item + 1] == row + 1,
    decreases end - from,
{
    if row < rank[from + 1] {
        from
    } else {
        item_for_candidate(rank, row, from + 1, end)
    }
}


proof fn candidate_group_extend(
    file: &CircuitEditorFile, key: NameKey, group: usize,
    before: Seq<PositionedBinding>, after: Seq<PositionedBinding>, rank: Seq<nat>,
)
    requires
        candidate_group_prefix(file, key, group, before, rank),
        rank.last() == before.len(),
        before.len() <= after.len() <= before.len() + 1,
        after.take(before.len() as int) == before,
        rank.len() - 1 <= usize::MAX,
        observes_candidate(file, key, group, (rank.len() - 1) as usize,
            if before.len() == after.len() { None } else { Some(after.last()) }),
    ensures candidate_group_prefix(file, key, group, after, rank.push(after.len())),
{
    reveal(candidate_group_prefix);
    let extended = rank.push(after.len());
    assert forall|i: int| 0 <= i < extended.len() - 1 implies {
        let first = #[trigger] extended[i];
        let next = extended[i + 1];
        &&& first <= next <= after.len()
        &&& next <= first + 1
        &&& observes_candidate(file, key, group, i as usize,
            if first == next { None } else { Some(after[first as int]) })
    } by {
        if i + 1 < rank.len() {
            assert(extended[i] == rank[i]);
            assert(extended[i + 1] == rank[i + 1]);
            if rank[i] < rank[i + 1] {
                assert(after[rank[i] as int] == before[rank[i] as int]);
            }
        } else {
            assert(extended[i] == rank.last());
            assert(extended[i + 1] == after.len());
            if before.len() < after.len() {
                assert(after[before.len() as int] == after.last());
            }
        }
    };
}

impl<'p, 'a> CircuitEditorFile<'p, 'a> {
    /// フォーム群の各項目と候補列との対応を表す。候補の順番は検査項目の順番に従う。
    pub closed spec fn group_candidates_match(
        &self, key: NameKey, group: usize, rows: Seq<PositionedBinding<'p, 'a>>,
    ) -> bool {
        &&& self.recovered_names_model().position_count_model(group) <= usize::MAX
        &&& exists|rank: Seq<nat>| #[trigger] candidate_group_prefix(self, key, group, rows, rank)
            && rank.len() == self.recovered_names_model().position_count_model(group) + 1
            && rank.first() == 0 && rank.last() == rows.len()
    }

    /// 候補列の行に対応するフォーム群内の項目を特定する。
    pub proof fn group_candidate_origin(
        &self, key: NameKey, group: usize, rows: Seq<PositionedBinding<'p, 'a>>, row: int,
    ) -> (item: usize)
        requires self.group_candidates_match(key, group, rows), 0 <= row < rows.len(),
        ensures
            item < self.recovered_names_model().position_count_model(group),
            self.recovered_names_model().position_model(group, item) == Some(rows[row].0),
            self.binding_matches(rows[row].0, Some(rows[row].1)),
            rows[row].1.has_declaration_key(key),
    {
        let rank = choose|rank: Seq<nat>| #[trigger] candidate_group_prefix(self, key, group, rows, rank)
            && rank.len() == self.recovered_names_model().position_count_model(group) + 1
            && rank.first() == 0 && rank.last() == rows.len();
        reveal(candidate_group_prefix);
        let end = rank.len() - 1;
        assert forall|i: int| 0 <= i < end implies #[trigger] rank[i + 1] <= rank[i] + 1 by {
            assert(rank[i] <= rank[i + 1]);
        };
        let item = item_for_candidate(rank, row, 0, end);
        assert(observes_candidate(self, key, group, item as usize, Some(rows[row])));
        item as usize
    }


    fn declaration_candidate_at(&self, key: NameKey, group: usize, item: usize)
        -> (candidate: Option<PositionedBinding<'p, 'a>>)
        ensures observes_candidate(self, key, group, item, candidate),
    {
        let names = self.recovered_names();
        let position = names.position(group, item)?;
        let found = self.observed_binding_at(position);
        if let Some(binding) = found {
            if let ObservedCircuitBindingKind::Declaration { key: candidate, .. } = &binding.kind {
                if candidate.same_name(key) {
                    return Some((position, binding));
                }
            }
        }
        proof { exclude_candidate(self, position, key, found); }
        None
    }


    /// 同じ完全修飾名の宣言を、指定したフォーム群から元ソース順に集める。
    ///
    /// 回復から確認できた宣言を対象とする。空の結果はプロジェクト内に宣言がないことを意味しない。
    pub fn declaration_candidates_in_group(&self, key: NameKey, group: usize)
        -> (rows: Vec<PositionedBinding<'p, 'a>>)
        ensures
            self.group_candidates_match(key, group, rows@),
            group >= self.recovered_names_model().position_group_count_model() ==> rows@.len() == 0,
    {
        let names = self.recovered_names();
        let count = names.position_count(group);
        let mut rows = Vec::new();
        let mut item = 0usize;
        let ghost mut rank = seq![0nat];
        proof { reveal(candidate_group_prefix); }
        while item < count
            invariant
                names == self.recovered_names_model(),
                count == names.position_count_model(group),
                item <= count,
                rank.len() == item + 1,
                rank.first() == 0,
                rank.last() == rows@.len(),
                candidate_group_prefix(self, key, group, rows@, rank),
            decreases count - item,
        {
            let ghost before = rows@;
            if let Some(candidate) = self.declaration_candidate_at(key, group, item) {
                rows.push(candidate);
            }
            proof {
                assert(rows@.take(before.len() as int) =~= before);
                candidate_group_extend(self, key, group, before, rows@, rank);
                rank = rank.push(rows@.len());
                assert(rank.last() == rows@.len());
            }
            item += 1;
        }
        rows
    }
}


/// 元のソーススナップショットに回路フォームの回復結果を結び付ける。
///
/// 回路言語のファイルを解析する。NCG2M のファイルでは `None` を返す。
pub fn inspect_circuit_file<'p, 'a>(
    source: &'p ProjectSource<'a>,
) -> (file: Option<CircuitEditorFile<'p, 'a>>)
    ensures
        file.is_some() <==> circuit_editor_source(source),
        file matches Some(file) ==> file.valid() && file.source_model() == source,
{
    if !matches!(source.kind, SourceKind::Circuit)
        || !matches!(source.id.source_kind(), Some(SourceKind::Circuit))
    {
        return None;
    }
    let names = recover_circuit_names(source.text());
    Some(CircuitEditorFile { source, names })
}

/// 回路フォームの回復解析を適用する言語を表す。
pub closed spec fn circuit_editor_source(source: &ProjectSource) -> bool {
    source.kind is Circuit && source_kind_of(source.id.components_model()) is Some &&
        source_kind_of(source.id.components_model())->Some_0 is Circuit
}

} // verus!
