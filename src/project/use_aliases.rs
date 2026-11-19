//! 解決済みの `use` をスコープごとに照合し、別名の束縛と重複警告を求める。

#[cfg(verus_only)]
use super::name_keys::key_bytes;
#[cfg(verus_only)]
use super::resolution::direct_targets_agree;
use super::{AbsoluteTarget, NameKey, ResolvedUse, UseTargets};
#[cfg(verus_only)]
use super::{DeclarationTable, direct_target_matches, same_target};
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// 一つの `use` が作る束縛、またはその重複警告。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AliasDisposition {
    /// このスコープと別名で最初の指定。直下の同一対象とも束縛を共有できる。
    Binding,
    /// 同じスコープで同じ別名と対象を指定した。
    Duplicate {
        /// 最初の指定を解決済み一覧で指す添字。警告の関連位置に使う。
        first: usize,
    },
}

/// 別名に異なる対象を割り当てたときの診断。
#[derive(Debug)]
pub enum UseAliasConflict<'t, 'p, 'a> {
    /// 同じスコープの二つの `use` が、同じ別名で異なる対象を指す。
    BetweenUses {
        /// 後から別名を指定した箇所と、その参照先。
        later: &'t ResolvedUse<'p, 'a>,
        /// 同じ別名を最初に指定した箇所と、その参照先。
        first: &'t ResolvedUse<'p, 'a>,
    },
    /// 別名と同じ名前の直接宣言または子名前空間が、異なる対象を指す。
    Direct {
        /// 衝突を起こした別名の指定と、その参照先。
        directive: &'t ResolvedUse<'p, 'a>,
        /// 元から存在した宣言または子名前空間と、その位置。
        existing: AbsoluteTarget<'p, 'a, 'a>,
    },
}

/// 解決済みの各 `use` に対応する別名の束縛と警告。
#[derive(Debug)]
pub struct UseAliases<'t, 'p, 'a> {
    targets: &'t UseTargets<'p, 'a>,
    dispositions: Vec<AliasDisposition>,
}

spec fn alias_key<'a>(item: ResolvedUse<'_, 'a>) -> NameKey<'a> {
    NameKey { parent: item.site.namespace, name: item.site.alias.word }
}

spec fn same_alias(left: ResolvedUse, right: ResolvedUse) -> bool {
    left.site.source.id.components_model() == right.site.source.id.components_model()
        && left.site.block == right.site.block
        && key_bytes(NameKey { parent: None, name: left.site.alias.word })
            == key_bytes(NameKey { parent: None, name: right.site.alias.word })
}

fn scope_and_alias_match(left: &ResolvedUse, right: &ResolvedUse) -> (same: bool)
    ensures same == same_alias(*left, *right),
{
    left.site.block == right.site.block
        && NameKey { parent: None, name: left.site.alias.word }
            .same_name(NameKey { parent: None, name: right.site.alias.word })
        && left.site.source.id.same_file(&right.site.source.id)
}

spec fn first_alias(items: Seq<ResolvedUse>, at: int, first: int) -> bool {
    &&& 0 <= first < at < items.len()
    &&& same_alias(items[first], items[at])
    &&& forall|i: int| 0 <= i < first ==> !same_alias(#[trigger] items[i], items[at])
}

fn find_first(items: &[ResolvedUse], at: usize) -> (first: Option<usize>)
    requires at < items@.len(),
    ensures match first {
        Some(first) => first_alias(items@, at as int, first as int),
        None => forall|i: int| 0 <= i < at ==> !same_alias(#[trigger] items@[i], items@[at as int]),
    },
{
    let mut i = 0;
    while i < at
        invariant
            i <= at < items@.len(),
            forall|j: int| 0 <= j < i ==> !same_alias(#[trigger] items@[j], items@[at as int]),
        decreases at - i,
    {
        if scope_and_alias_match(&items[i], &items[at]) {
            return Some(i);
        }
        i += 1;
    }
    None
}

spec fn allows_direct(table: &DeclarationTable, item: ResolvedUse) -> bool {
    forall|existing: AbsoluteTarget| #[trigger] direct_target_matches(table, alias_key(item), Some(existing))
        ==> same_target(existing, item.target)
}

spec fn disposition_matches(items: Seq<ResolvedUse>, at: int, disposition: AliasDisposition) -> bool {
    &&& 0 <= at < items.len()
    &&& match disposition {
        AliasDisposition::Binding =>
            forall|i: int| 0 <= i < at ==> !same_alias(#[trigger] items[i], items[at]),
        AliasDisposition::Duplicate { first } =>
            first_alias(items, at, first as int) && same_target(items[first as int].target, items[at].target),
    }
}

spec fn checked_prefix(
    table: &DeclarationTable, items: Seq<ResolvedUse>, dispositions: Seq<AliasDisposition>,
) -> bool {
    &&& dispositions.len() <= items.len()
    &&& forall|i: int| 0 <= i < dispositions.len() ==>
        disposition_matches(items, i, #[trigger] dispositions[i]) && allows_direct(table, items[i])
}

/// 同じスコープと別名の指定が同じ対象を指し、直接宣言と子名前空間にも衝突しないことを表す。
pub closed spec fn use_aliases_acceptable(targets: &UseTargets) -> bool {
    let items = targets.directives_model();
    let table = targets.exports_model().declarations_model();
    &&& forall|i: int| 0 <= i < items.len() ==> allows_direct(&table, #[trigger] items[i])
    &&& forall|i: int, j: int| 0 <= i < j < items.len()
        && #[trigger] same_alias(items[i], items[j])
        ==> same_target(items[i].target, items[j].target)
}

proof fn compatible_pair(items: Seq<ResolvedUse>, decisions: Seq<AliasDisposition>, i: int, j: int)
    requires
        0 <= i < j < decisions.len() <= items.len(),
        same_alias(items[i], items[j]),
        disposition_matches(items, i, decisions[i]),
        disposition_matches(items, j, decisions[j]),
    ensures same_target(items[i].target, items[j].target),
{
    assert(decisions[j] is Duplicate);
    let f = decisions[j]->Duplicate_first;
    assert(f <= i);
    if f < i {
        assert(same_alias(items[f as int], items[i]));
        assert(decisions[i] is Duplicate);
        let g = decisions[i]->Duplicate_first;
        assert(g <= f);
        assert(same_alias(items[g as int], items[j]));
        assert(f <= g);
    }
}

/// 各指定に対して、衝突しない束縛または最初の指定を指す重複警告があることを表す。
pub closed spec fn use_aliases_match(targets: &UseTargets, aliases: UseAliases) -> bool {
    &&& *aliases.targets == *targets
    &&& aliases.dispositions@.len() == targets.directives_model().len()
    &&& checked_prefix(&targets.exports_model().declarations_model(), targets.directives_model(), aliases.dispositions@)
}

/// 診断が、異なる対象を同じ別名に割り当てた指定を指すことを表す。
pub closed spec fn alias_conflict_evidence(targets: &UseTargets, error: UseAliasConflict) -> bool {
    let items = targets.directives_model();
    let table = targets.exports_model().declarations_model();
    match error {
        UseAliasConflict::BetweenUses { later, first } =>
            exists|i: int, j: int| #[trigger] first_alias(items, i, j)
                && items[i] == *later && items[j] == *first
                && !same_target(first.target, later.target),
        UseAliasConflict::Direct { directive, existing } =>
            exists|i: int| 0 <= i < items.len() && #[trigger] items[i] == *directive
                && direct_target_matches(&table, alias_key(*directive), Some(existing))
                && !same_target(existing, directive.target),
    }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// 元の指定、参照先、診断の範囲を含む解決済み一覧を返す。
    pub fn directives(&self) -> (directives: &'t [ResolvedUse<'p, 'a>])
        ensures directives@ == self.directives_model(),
    {
        self.targets.directives()
    }

    /// 解決済み一覧の論理上の列を返す。
    pub closed spec fn directives_model(&self) -> Seq<ResolvedUse<'p, 'a>> {
        self.targets.directives_model()
    }

    /// 解決済み一覧と同じ順で、各指定の束縛または重複警告を返す。
    pub fn dispositions(&self) -> (dispositions: &[AliasDisposition])
        ensures dispositions@ == self.dispositions_model(),
    {
        self.dispositions.as_slice()
    }

    /// 束縛と重複警告の論理上の列を返す。
    pub closed spec fn dispositions_model(&self) -> Seq<AliasDisposition> {
        self.dispositions@
    }
}

/// 解決済みの `use` を照合し、別名の束縛と重複警告を返す。
///
/// [`index_use_targets`](super::index_use_targets) で得た指定を渡す。
/// 同じファイルとブロックで、同じ対象を同じ別名に割り当てた後続の指定には警告を出す。
/// 警告の関連位置は最初の指定を指す。名前空間内の直接宣言と子名前空間も照合する。
///
/// # Errors
///
/// 異なる対象が同じ別名を取り合う場合、衝突を起こした指定と相手の位置を返す。
/// 一つの指定で両方の衝突が起きた場合は、直接宣言または子名前空間との衝突を返す。
pub fn check_use_aliases<'t, 'p, 'a>(targets: &'t UseTargets<'p, 'a>)
    -> (result: Result<UseAliases<'t, 'p, 'a>, UseAliasConflict<'t, 'p, 'a>>)
    requires targets.exports_model().declarations_model().well_formed(),
    ensures
        result.is_ok() <==> use_aliases_acceptable(targets),
        match result {
            Ok(aliases) => use_aliases_match(targets, aliases),
            Err(error) => alias_conflict_evidence(targets, error),
        },
{
    let items = targets.directives();
    let table = targets.exports().declarations();
    let mut dispositions = Vec::new();
    let mut at = 0;
    while at < items.len()
        invariant
            items@ == targets.directives_model(),
            *table == targets.exports_model().declarations_model(),
            table.well_formed(),
            at == dispositions@.len(),
            checked_prefix(table, items@, dispositions@),
        decreases items@.len() - at,
    {
        let directive = &items[at];
        let direct = table.direct_target(NameKey { parent: directive.site.namespace, name: directive.site.alias.word });
        let ghost direct_model = direct;
        if let Some(existing) = direct {
            if !existing.is_same_target(&directive.target) {
                let error = UseAliasConflict::Direct { directive, existing };
                assert(alias_conflict_evidence(targets, error));
                assert(!allows_direct(table, *directive));
                assert(!use_aliases_acceptable(targets));
                return Err(error);
            }
        }
        assert(allows_direct(table, *directive)) by {
            assert forall|existing: AbsoluteTarget|
                #[trigger] direct_target_matches(table, alias_key(*directive), Some(existing))
                implies same_target(existing, directive.target) by {
                direct_targets_agree(table, alias_key(*directive), direct_model, Some(existing));
            };
        }
        let disposition = if let Some(first) = find_first(items, at) {
            let previous = &items[first];
            if !previous.target.is_same_target(&directive.target) {
                let error = UseAliasConflict::BetweenUses { later: directive, first: previous };
                assert(alias_conflict_evidence(targets, error));
                assert(same_alias(*previous, *directive));
                assert(!use_aliases_acceptable(targets));
                return Err(error);
            }
            AliasDisposition::Duplicate { first }
        } else {
            AliasDisposition::Binding
        };
        assert(disposition_matches(items@, at as int, disposition));
        dispositions.push(disposition);
        at += 1;
    }
    proof {
        assert forall|i: int| 0 <= i < items@.len()
            implies allows_direct(table, #[trigger] items@[i]) by {
            assert(disposition_matches(items@, i, dispositions@[i]));
        };
        assert forall|i: int, j: int| 0 <= i < j < items@.len()
            && #[trigger] same_alias(items@[i], items@[j])
            implies same_target(items@[i].target, items@[j].target) by {
            compatible_pair(items@, dispositions@, i, j);
        };
    }
    Ok(UseAliases { targets, dispositions })
}

} // verus!
