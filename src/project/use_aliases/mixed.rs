//! 混在プロジェクトで、ファイルと名前空間ブロックごとの別名を検査する。

use super::{AliasConflict, AliasDisposition, AliasIndex};
use crate::project::{MixedAbsoluteTarget, MixedUseTargets, MixedResolvedUse, NameKey};
#[cfg(verus_only)]
use crate::project::{
    mixed_use_targets_match, same_mixed_target,
    resolution::{mixed_direct_target_matches, mixed_direct_targets_agree},
};
use alloc::vec::Vec;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 混在プロジェクトの同じスコープにある別名の衝突。
pub type MixedUseAliasConflict<'t, 'p, 'a> =
    AliasConflict<&'t MixedResolvedUse<'p, 'a>, MixedAbsoluteTarget<'p, 'a, 'a>>;

/// ファイルと名前空間ブロックごとに検査した、混在プロジェクトの別名。
pub struct MixedUseAliases<'t, 'p, 'a> {
    targets: &'t MixedUseTargets<'p, 'a>,
    dispositions: Vec<AliasDisposition>,
    index: Option<AliasIndex>,
}

#[cfg(verus_only)]
type AliasKey = ((usize, Option<usize>), Seq<u8>);

spec fn alias_key(row: MixedResolvedUse) -> AliasKey {
    ((row.file, row.site.block), row.site.alias.word.spec_bytes())
}

spec fn first_for(
    rows: Seq<MixedResolvedUse>, key: AliasKey, limit: int, first: Option<usize>,
) -> bool {
    match first {
        Some(i) => 0 <= i < limit <= rows.len()
            && alias_key(rows[i as int]) == key
            && forall|j: int| 0 <= j < i ==> alias_key(#[trigger] rows[j]) != key,
        None => forall|j: int| 0 <= j < limit ==> alias_key(#[trigger] rows[j]) != key,
    }
}

spec fn indexed_first(bindings: Map<AliasKey, usize>, key: AliasKey) -> Option<usize> {
    if bindings.contains_key(key) { Some(bindings[key]) } else { None }
}

spec fn matches_index(bindings: Map<AliasKey, usize>, rows: Seq<MixedResolvedUse>, length: int) -> bool {
    forall|key: AliasKey| #[trigger] first_for(rows, key, length, indexed_first(bindings, key))
}

proof fn check_added_key(
    rows: Seq<MixedResolvedUse>, length: usize, prior: Map<AliasKey, usize>, next: Map<AliasKey, usize>,
)
    requires
        length < rows.len(), matches_index(prior, rows, length as int),
        {
            let key = alias_key(rows[length as int]);
            next == if prior.contains_key(key) { prior } else { prior.insert(key, length) }
        },
    ensures matches_index(next, rows, length + 1),
{
    let added = alias_key(rows[length as int]);
    assert forall|key: AliasKey| #[trigger] first_for(rows, key, length + 1, indexed_first(next, key)) by {
        let previous = indexed_first(prior, key);
        assert(first_for(rows, key, length as int, previous));
        if key == added && previous.is_none() {
            assert(indexed_first(next, key) == Some(length));
            assert(first_for(rows, key, length + 1, Some(length)));
        } else {
            assert(indexed_first(next, key) == previous);
            if previous.is_none() {
                assert(key != added);
                assert forall|j: int| 0 <= j < length + 1 implies alias_key(#[trigger] rows[j]) != key by {
                    if j < length { assert(alias_key(rows[j]) != key); }
                    else { assert(j == length); }
                };
            }
        }
    };
}

fn first_linear(
    rows: &[MixedResolvedUse], length: usize, file: usize, block: Option<usize>, word: &str,
) -> (first: Option<usize>)
    requires length <= rows@.len(),
    ensures first_for(rows@, ((file, block), word.spec_bytes()), length as int, first),
{
    let mut i = 0;
    while i < length
        invariant length <= rows@.len(), i <= length,
            forall|j: int| 0 <= j < i ==> alias_key(#[trigger] rows@[j]) != ((file, block), word.spec_bytes()),
        decreases length - i,
    {
        let row = &rows[i];
        if row.file == file && row.site.block == block
            && (NameKey { parent: None, name: row.site.alias.word }).same_name(NameKey { parent: None, name: word })
        {
            return Some(i);
        }
        i += 1;
    }
    None
}

spec fn direct_key<'a>(row: MixedResolvedUse<'_, 'a>) -> NameKey<'a> {
    NameKey { parent: row.site.namespace, name: row.site.alias.word }
}

spec fn accepts_direct(targets: &MixedUseTargets, row: MixedResolvedUse) -> bool {
    forall|existing: MixedAbsoluteTarget| #[trigger]
        mixed_direct_target_matches(&targets.exports_model(), direct_key(row), Some(existing))
        ==> same_mixed_target(existing, row.target)
}

spec fn bound_at(rows: Seq<MixedResolvedUse>, at: int, disposition: AliasDisposition) -> bool {
    match disposition {
        AliasDisposition::Binding => first_for(rows, alias_key(rows[at]), at, None),
        AliasDisposition::Duplicate { first } => first_for(rows, alias_key(rows[at]), at, Some(first))
            && same_mixed_target(rows[first as int].target, rows[at].target),
    }
}

#[verifier::opaque]
spec fn accepted_prefix(targets: &MixedUseTargets, dispositions: Seq<AliasDisposition>) -> bool {
    let rows = targets.directives_model();
    &&& dispositions.len() <= rows.len()
    &&& forall|i: int| 0 <= i < dispositions.len() ==> {
        let row = #[trigger] rows[i];
        accepts_direct(targets, row) && bound_at(rows, i, dispositions[i])
    }
}

spec fn accepts_before(targets: &MixedUseTargets, at: int) -> bool {
    let rows = targets.directives_model();
    &&& 0 <= at <= rows.len()
    &&& forall|i: int| 0 <= i < at ==> {
        let row = #[trigger] rows[i];
        &&& accepts_direct(targets, row)
        &&& forall|j: int| 0 <= j < i && alias_key(#[trigger] rows[j]) == alias_key(row)
            ==> same_mixed_target(rows[j].target, row.target)
    }
}

proof fn transitive_targets(left: MixedAbsoluteTarget, middle: MixedAbsoluteTarget, right: MixedAbsoluteTarget)
    requires same_mixed_target(left, middle), same_mixed_target(middle, right),
    ensures same_mixed_target(left, right),
{}

proof fn prefix_allows(targets: &MixedUseTargets, dispositions: Seq<AliasDisposition>)
    requires accepted_prefix(targets, dispositions),
    ensures accepts_before(targets, dispositions.len() as int),
{
    reveal(accepted_prefix);
    let rows = targets.directives_model();
    assert forall|i: int| 0 <= i < dispositions.len() implies {
        let row = #[trigger] rows[i];
        &&& accepts_direct(targets, row)
        &&& forall|j: int| 0 <= j < i && alias_key(#[trigger] rows[j]) == alias_key(row)
            ==> same_mixed_target(rows[j].target, row.target)
    } by {
        match dispositions[i] {
            AliasDisposition::Duplicate { first } => {
                let selected = rows[first as int];
                assert(alias_key(selected) == alias_key(rows[i]));
                assert forall|j: int| 0 <= j < i && alias_key(#[trigger] rows[j]) == alias_key(rows[i])
                    implies same_mixed_target(rows[j].target, rows[i].target) by {
                    if j != first {
                        assert(first < j);
                        assert(bound_at(rows, j, dispositions[j]));
                        match dispositions[j] {
                            AliasDisposition::Duplicate { first: other } => {
                                if other < first { assert(alias_key(rows[other as int]) != alias_key(rows[i])); }
                                if first < other { assert(alias_key(selected) != alias_key(rows[j])); }
                                transitive_targets(rows[j].target, selected.target, rows[i].target);
                            }
                            AliasDisposition::Binding => assert(false),
                        }
                    }
                };
            }
            AliasDisposition::Binding => (),
        }
    };
}

/// 同じスコープの別名と、その名前空間直下の宣言に衝突がないことを表す。
pub closed spec fn mixed_use_aliases_acceptable(targets: &MixedUseTargets) -> bool {
    accepts_before(targets, targets.directives_model().len() as int)
}

spec fn conflict_at(targets: &MixedUseTargets, at: int, error: MixedUseAliasConflict) -> bool {
    let rows = targets.directives_model();
    let row = rows[at];
    match error {
        AliasConflict::Direct { directive, existing } =>
            *directive == row && mixed_direct_target_matches(&targets.exports_model(), direct_key(row), Some(existing))
                && !same_mixed_target(existing, row.target),
        AliasConflict::BetweenUses { later, first } =>
            *later == row && accepts_direct(targets, row)
                && exists|i: usize| #[trigger] first_for(rows, alias_key(row), at, Some(i))
                    && *first == rows[i as int] && !same_mixed_target(first.target, row.target),
    }
}

/// 衝突の種別と二つの箇所が、元の指定順で選ばれる最初の衝突に対応することを表す。
pub closed spec fn mixed_alias_conflict_evidence(targets: &MixedUseTargets, error: MixedUseAliasConflict) -> bool {
    exists|at: int| 0 <= at < targets.directives_model().len() && accepts_before(targets, at)
        && #[trigger] conflict_at(targets, at, error)
}

proof fn first_alias_ranks_agree(
    rows: Seq<MixedResolvedUse>, key: AliasKey, limit: int, first: Option<usize>, other: Option<usize>,
)
    requires first_for(rows, key, limit, first), first_for(rows, key, limit, other),
    ensures first == other,
{
    if let Some(i) = first {
        assert(alias_key(rows[i as int]) == key);
        assert(other is Some);
        let j = other->Some_0;
        assert(alias_key(rows[j as int]) == key);
        if i < j { assert(alias_key(rows[i as int]) != key); }
        if j < i { assert(alias_key(rows[j as int]) != key); }
    } else if let Some(j) = other {
        assert(alias_key(rows[j as int]) == key);
        assert(alias_key(rows[j as int]) != key);
    }
}

proof fn earlier_conflict_invalidates_prefix(
    targets: &MixedUseTargets, at: int, limit: int, error: MixedUseAliasConflict,
)
    requires 0 <= at < limit, accepts_before(targets, limit), conflict_at(targets, at, error),
    ensures false,
{
    let rows = targets.directives_model();
    let row = rows[at];
    match error {
        AliasConflict::Direct { existing, .. } => {
            assert(accepts_direct(targets, row));
            assert(mixed_direct_target_matches(&targets.exports_model(), direct_key(row), Some(existing)));
        }
        AliasConflict::BetweenUses { first, .. } => {
            let i = choose|i: usize| #[trigger] first_for(rows, alias_key(row), at, Some(i))
                && *first == rows[i as int] && !same_mixed_target(first.target, row.target);
            assert(alias_key(rows[i as int]) == alias_key(row));
            assert(same_mixed_target(rows[i as int].target, row.target));
        }
    }
}

/// 同じ別名指定から得られる最初の衝突は、出現箇所と参照先を含めて一致することを示す。
pub proof fn mixed_alias_conflicts_agree(
    targets: &MixedUseTargets, a: MixedUseAliasConflict, b: MixedUseAliasConflict,
)
    requires mixed_use_targets_match(&targets.project_model(), *targets),
        mixed_alias_conflict_evidence(targets, a), mixed_alias_conflict_evidence(targets, b),
    ensures a == b,
{
    let rows = targets.directives_model();
    let i = choose|at: int| 0 <= at < rows.len() && accepts_before(targets, at) && #[trigger] conflict_at(targets, at, a);
    let j = choose|at: int| 0 <= at < rows.len() && accepts_before(targets, at) && #[trigger] conflict_at(targets, at, b);
    if i < j { earlier_conflict_invalidates_prefix(targets, i, j, a); }
    if j < i { earlier_conflict_invalidates_prefix(targets, j, i, b); }
    let row = rows[i];
    match (a, b) {
        (AliasConflict::Direct { existing: left, .. }, AliasConflict::Direct { existing: right, .. }) => {
            let project = targets.project_model();
            targets.mixed_use_exports_match(&project);
            mixed_direct_targets_agree(&project, &targets.exports_model(), direct_key(row), Some(left), Some(right));
        }
        (AliasConflict::BetweenUses { first: left, .. }, AliasConflict::BetweenUses { first: right, .. }) => {
            let key = alias_key(row);
            let left_rank = choose|n: usize| #[trigger] first_for(rows, key, i, Some(n))
                && *left == rows[n as int] && !same_mixed_target(left.target, row.target);
            let right_rank = choose|n: usize| #[trigger] first_for(rows, key, i, Some(n))
                && *right == rows[n as int] && !same_mixed_target(right.target, row.target);
            first_alias_ranks_agree(rows, key, i, Some(left_rank), Some(right_rank));
        }
        (AliasConflict::Direct { existing, .. }, AliasConflict::BetweenUses { .. }) |
        (AliasConflict::BetweenUses { .. }, AliasConflict::Direct { existing, .. }) => {
            assert(accepts_direct(targets, row));
            assert(mixed_direct_target_matches(&targets.exports_model(), direct_key(row), Some(existing)));
            assert(false);
        }
    }
}

/// 解決済みの別名指定と、それぞれの束縛・重複の判定が対応することを表す。
pub closed spec fn mixed_use_aliases_match(targets: &MixedUseTargets, aliases: MixedUseAliases) -> bool {
    *aliases.targets == *targets
        && accepted_prefix(targets, aliases.dispositions@)
        && aliases.dispositions@.len() == targets.directives_model().len()
}

impl<'t, 'p, 'a> MixedUseAliases<'t, 'p, 'a> {
    #[verifier::type_invariant]
    spec fn index_keeps_order(&self) -> bool {
        &&& accepted_prefix(self.targets, self.dispositions@)
        &&& self.dispositions@.len() == self.targets.directives_model().len()
        &&& self.index matches Some(index) ==> index.valid()
            && matches_index(index.bindings(), self.targets.directives_model(), self.dispositions@.len() as int)
    }

    /// 検査した別名指定と、それらの参照先を返す。
    pub fn targets(&self) -> (targets: &'t MixedUseTargets<'p, 'a>)
        ensures *targets == self.targets_model(),
    {
        self.targets
    }

    /// 検査した別名指定と参照先を表す。
    pub closed spec fn targets_model(&self) -> MixedUseTargets<'p, 'a> {
        *self.targets
    }

    /// 同じファイル・ブロックの最初の別名指定であることを表す。
    pub closed spec fn first_alias_matches(
        &self, file: usize, block: Option<usize>, word: &str, rank: Option<usize>,
    ) -> bool {
        let rows = self.targets.directives_model();
        first_for(rows, ((file, block), word.spec_bytes()), rows.len() as int, rank)
    }

    /// 検索結果が、指定したファイル・ブロック・綴りの最初の行を指すことを示す。
    pub proof fn first_alias_origin(
        &self, file: usize, block: Option<usize>, word: &str, rank: Option<usize>,
    )
        requires self.first_alias_matches(file, block, word, rank),
        ensures {
            let rows = self.targets_model().directives_model();
            match rank {
                Some(i) => 0 <= i < rows.len()
                    && rows[i as int].file == file
                    && rows[i as int].site.block == block
                    && rows[i as int].site.alias.word.spec_bytes() == word.spec_bytes()
                    && forall|j: int| 0 <= j < i ==> (#[trigger] rows[j]).file != file
                        || rows[j].site.block != block || rows[j].site.alias.word.spec_bytes() != word.spec_bytes(),
                None => forall|j: int| 0 <= j < rows.len() ==> (#[trigger] rows[j]).file != file
                    || rows[j].site.block != block || rows[j].site.alias.word.spec_bytes() != word.spec_bytes(),
            }
        },
    {}

    /// ファイルと名前空間ブロックを指定して、別名を最初に定義した指示の添字を返す。
    ///
    /// ファイルの直下にある別名は `block = None` で引く。添字は
    /// [`MixedUseTargets::directives`] の同じ位置を指す。
    pub fn first_alias(&self, file: usize, block: Option<usize>, word: &str) -> (rank: Option<usize>)
        ensures self.first_alias_matches(file, block, word, rank),
    {
        proof { use_type_invariant(self); }
        let rows = self.targets.directives();
        if let Some(index) = self.index.as_ref() {
            let found = index.lookup((file, block), word);
            assert(found == indexed_first(index.bindings(), ((file, block), word.spec_bytes())));
            found
        } else {
            first_linear(rows, rows.len(), file, block, word)
        }
    }

    /// 各 `use` が最初の指定か重複指定かを、元の指定順で返す。
    pub fn dispositions(&self) -> (dispositions: &[AliasDisposition])
        ensures dispositions@ == self.dispositions_model(),
    {
        self.dispositions.as_slice()
    }

    /// 判定が最初の指定、またはその指定を参照する重複に対応することを示す。
    pub proof fn disposition_origin(&self, rank: int)
        requires mixed_use_aliases_match(&self.targets_model(), *self), 0 <= rank < self.dispositions_model().len(),
        ensures {
            let rows = self.targets_model().directives_model();
            let row = rows[rank];
            &&& rank < rows.len()
            &&& match self.dispositions_model()[rank] {
                AliasDisposition::Binding => forall|j: int| 0 <= j < rank ==> (#[trigger] rows[j]).file != row.file
                    || rows[j].site.block != row.site.block
                    || rows[j].site.alias.word.spec_bytes() != row.site.alias.word.spec_bytes(),
                AliasDisposition::Duplicate { first } => {
                    let previous = rows[first as int];
                    &&& first < rank
                    &&& previous.file == row.file
                    &&& previous.site.block == row.site.block
                    &&& previous.site.alias.word.spec_bytes() == row.site.alias.word.spec_bytes()
                    &&& same_mixed_target(previous.target, row.target)
                    &&& forall|j: int| 0 <= j < first ==> (#[trigger] rows[j]).file != row.file
                        || rows[j].site.block != row.site.block
                        || rows[j].site.alias.word.spec_bytes() != row.site.alias.word.spec_bytes()
                },
            }
        },
    {
        reveal(accepted_prefix);
    }

    /// 元の指定順の別名の判定を表す。
    pub closed spec fn dispositions_model(&self) -> Seq<AliasDisposition> {
        self.dispositions@
    }
}

/// 同じ解決済み指定から作った索引では、束縛・重複の判定列が一致することを示す。
pub proof fn mixed_alias_dispositions_agree(
    targets: &MixedUseTargets, a: MixedUseAliases, b: MixedUseAliases,
)
    requires mixed_use_aliases_match(targets, a), mixed_use_aliases_match(targets, b),
    ensures a.dispositions_model() == b.dispositions_model(),
{
    reveal(accepted_prefix);
    let rows = targets.directives_model();
    assert(a.dispositions_model() =~= b.dispositions_model()) by {
        assert forall|i: int| 0 <= i < rows.len()
            implies #[trigger] a.dispositions_model()[i] == b.dispositions_model()[i] by {
            let left = a.dispositions_model()[i];
            let right = b.dispositions_model()[i];
            assert(bound_at(rows, i, left));
            assert(bound_at(rows, i, right));
            let first = match left { AliasDisposition::Binding => None, AliasDisposition::Duplicate { first } => Some(first) };
            let other = match right { AliasDisposition::Binding => None, AliasDisposition::Duplicate { first } => Some(first) };
            first_alias_ranks_agree(rows, alias_key(rows[i]), i, first, other);
        };
    };
}

/// 両言語の別名と直接宣言の衝突を調べ、同じ対象への重複指定を記録する。
///
/// # Errors
///
/// 別名の指定順で最初の衝突を返す。一つの別名で複数の衝突が起きる場合は、
/// 直接宣言または子名前空間との衝突を先に返す。
///
/// # Examples
///
/// 同じブロックで同じ対象に別名を付け直すと、先行する指定を参照する重複判定を返す。
///
/// ```
/// use circuitgame2_core::project::{
///     AliasDisposition, SourceSnapshot, check_mixed_use_aliases, index_mixed_use_targets, parse_project_sources,
/// };
///
/// let sources = [
///     SourceSnapshot { path: "api.ncg2m", revision: 1,
///         text: "(namespace api (defn ready (as-type (Fn () Bool) (fn () true))) (export ready))" },
///     SourceSnapshot { path: "app.ncg2m", revision: 2,
///         text: "(use ::api::ready ok) (use ::api::ready ok)" },
/// ];
/// let project = parse_project_sources(&sources).unwrap();
/// let targets = index_mixed_use_targets(&project).unwrap();
/// let aliases = check_mixed_use_aliases(&targets).unwrap();
/// assert_eq!(aliases.first_alias(1, None, "ok"), Some(0));
/// assert_eq!(aliases.dispositions(), &[AliasDisposition::Binding, AliasDisposition::Duplicate { first: 0 }]);
/// ```
pub fn check_mixed_use_aliases<'t, 'p, 'a>(targets: &'t MixedUseTargets<'p, 'a>)
    -> (result: Result<MixedUseAliases<'t, 'p, 'a>, MixedUseAliasConflict<'t, 'p, 'a>>)
    requires mixed_use_targets_match(&targets.project_model(), *targets),
    ensures result.is_ok() == mixed_use_aliases_acceptable(targets),
        match result {
            Ok(aliases) => mixed_use_aliases_match(targets, aliases),
            Err(error) => mixed_alias_conflict_evidence(targets, error),
        },
{
    let rows = targets.directives();
    let _project = targets.project();
    let exports = targets.exports();
    let mut dispositions = Vec::new();
    let mut index = Some(AliasIndex::new());
    let mut at = 0;
    assert(accepted_prefix(targets, dispositions@)) by { reveal(accepted_prefix); }
    while at < rows.len()
        invariant
            *_project == targets.project_model(), *exports == targets.exports_model(),
            mixed_use_targets_match(_project, *targets),
            rows@ == targets.directives_model(), at == dispositions@.len(),
            accepted_prefix(targets, dispositions@),
            index matches Some(bindings) ==> bindings.valid() && matches_index(bindings.bindings(), rows@, at as int),
        decreases rows@.len() - at,
    {
        let row = &rows[at];
        let key = NameKey { parent: row.site.namespace, name: row.site.alias.word };
        let direct = exports.mixed_direct_target(key);
        let ghost direct_model = direct;
        if let Some(found) = direct {
            if !found.is_same_target(&row.target) {
                let error = AliasConflict::Direct { directive: row, existing: found };
                proof { prefix_allows(targets, dispositions@); }
                assert(conflict_at(targets, at as int, error));
                assert(!accepts_direct(targets, *row));
                assert(!mixed_use_aliases_acceptable(targets));
                return Err(error);
            }
        }
        assert(accepts_direct(targets, *row)) by {
            targets.mixed_use_exports_match(_project);
            assert forall|existing: MixedAbsoluteTarget| #[trigger]
                mixed_direct_target_matches(exports, key, Some(existing)) implies same_mixed_target(existing, row.target) by {
                mixed_direct_targets_agree(_project, exports, key, direct_model, Some(existing));
                assert(direct_model == Some(existing));
            };
        };
        let mut indexed = None;
        if let Some(ref mut bindings) = index {
            let ghost old = bindings.bindings();
            indexed = bindings.insert_if_absent((row.file, row.site.block), row.site.alias.word, at);
            proof {
                if let Some(previous) = indexed {
                    let key = alias_key(*row);
                    assert(previous == indexed_first(old, key));
                    assert(first_for(rows@, key, at as int, previous));
                    check_added_key(rows@, at, old, bindings.bindings());
                }
            }
        }
        let first = match indexed {
            Some(previous) => previous,
            None => {
                // 節点の添字を確保できない場合は、欠けた索引を使わず元の順序で検索する。
                index = None;
                first_linear(rows, at, row.file, row.site.block, row.site.alias.word)
            }
        };
        assert(first_for(rows@, alias_key(*row), at as int, first));
        let disposition = if let Some(i) = first {
            let previous = &rows[i];
            if !previous.target.is_same_target(&row.target) {
                let error = AliasConflict::BetweenUses { later: row, first: previous };
                assert(conflict_at(targets, at as int, error));
                proof { prefix_allows(targets, dispositions@); }
                assert(!mixed_use_aliases_acceptable(targets));
                return Err(error);
            }
            AliasDisposition::Duplicate { first: i }
        } else {
            AliasDisposition::Binding
        };
        proof { reveal(accepted_prefix); }
        assert(bound_at(rows@, at as int, disposition));
        dispositions.push(disposition);
        at += 1;
    }
    proof { prefix_allows(targets, dispositions@); }
    Ok(MixedUseAliases { targets, dispositions, index })
}

}

impl core::fmt::Debug for MixedUseAliases<'_, '_, '_> {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.debug_struct("MixedUseAliases")
            .field("targets", &self.targets)
            .field("dispositions", &self.dispositions)
            .finish()
    }
}
