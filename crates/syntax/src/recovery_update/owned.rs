//! 文書が所有する回復キャッシュから、現在の本文の解析結果を得る。

use alloc::string::String;
#[cfg(verus_only)]
use core::ops::Range;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::{string::StringSliceAdditionalSpecFns, utf8::{encode_utf8, encode_utf8_valid_utf8, is_char_boundary_iff_not_is_continuation_byte}};

use super::{ReparsedRecovery, remember_edges_at, reparse_edges, split_source};
#[cfg(verus_only)]
use super::{clean_prefix, parsed_from};
use crate::{Recovered, parse_recovering};
#[cfg(verus_only)]
use crate::{recovered_replay_matches, recovered_replays_agree};
#[cfg(verus_only)]
use crate::recovery_replay::{retained_original_lists_agree};

verus! {

/// 一つの文書の旧本文と、その接頭部・接尾部の回復結果を所有する。
///
/// 開いている文書ごとに保持する。呼び出し側が文書 ID と公開時に使う版を管理する。
/// バイト位置は UTF-8 の `usize`、文書版はプロジェクトのスナップショットと同じ `u64`。
pub struct OwnedRecoveryCache {
    text: String,
    revision: u64,
    start: usize,
    join: usize,
    head: Recovered,
    tail: Recovered,
}

/// 文書バージョンと本文を結び付けて返す、一回の問い合わせの結果。
///
/// 局所解析の結果はキャッシュと現在の本文を借りる。両方の借用が終わるまで参照できる。
pub struct RecoverySnapshot<'cache, 'text> {
    revision: u64,
    source: &'text str,
    recovery: SnapshotRecovery<'cache, 'text>,
}

/// 現在の本文について得た回復解析の結果。
pub enum SnapshotRecovery<'cache, 'text> {
    /// 前後の解析結果を借り、編集後の中間だけを解析した結果。
    Local(ReparsedRecovery<'cache, 'text>),
    /// 局所再解析を使えない場合に、現在の本文全体を解析した結果。
    Full(Recovered),
}

impl OwnedRecoveryCache {
    #[verifier::type_invariant]
    spec fn valid(&self) -> bool {
        self.stored_edges_match()
    }

    /// 保存した前後の構文が、旧本文の区間と対応することを表す。
    pub closed spec fn stored_edges_match(&self) -> bool {
        cached_edges_match(self.text@, self.start, self.join, self.head, self.tail)
    }

    /// キャッシュを作った文書版を表す。
    pub closed spec fn revision_model(&self) -> u64 { self.revision }

    /// キャッシュが所有する旧本文を表す。
    pub closed spec fn text_model(&self) -> Seq<char> { self.text@ }

    /// 接頭部の解析結果を表す。
    pub closed spec fn head_model(&self) -> Recovered { self.head }

    /// 接尾部の解析結果を表す。
    pub closed spec fn tail_model(&self) -> Recovered { self.tail }

    /// 旧本文の再利用する接頭部の終了位置。
    pub closed spec fn head_end_model(&self) -> usize { self.start }

    /// 旧本文の再利用する接尾部の開始位置。
    pub closed spec fn tail_start_model(&self) -> usize { self.join }

    /// 現在の接頭部・接尾部のバイト列が、旧本文の対応区間と等しいことを表す。
    pub open spec fn reuses_edge_bytes(&self, update: &ReparsedRecovery) -> bool {
        let old = encode_utf8(self.text_model());
        let current = update.source_model().spec_bytes();
        &&& self.stored_edges_match()
        &&& update.valid()
        &&& self.head_end_model() <= self.tail_start_model() <= old.len()
        &&& update.section_model(1).byte_base <= update.section_model(2).byte_base <= current.len()
        &&& old[..self.head_end_model() as int] == current[..update.section_model(1).byte_base as int]
        &&& old[self.tail_start_model() as int..] == current[update.section_model(2).byte_base as int..]
    }

    /// 旧本文を引き取り、変更予定の区間の前後を一度だけ解析する。
    ///
    /// `start` と `join` は旧本文の UTF-8 バイト位置。
    /// 接頭部は空か、修復を挟まず元の閉じ括弧で終わる必要がある。
    ///
    /// # Errors
    ///
    /// 区間の指定が本文の文字境界にない場合や、再利用できる接頭部が得られない場合は、
    /// 受け取った本文をエラーとして返す。
    pub fn remember(text: String, revision: u64, start: usize, join: usize) -> (result: Result<Self, String>)
        ensures
            result matches Ok(cache) ==> cache.text_model() == text@ && cache.revision_model() == revision
                && cache.head_end_model() == start && cache.tail_start_model() == join,
            result matches Err(unchanged) ==> unchanged@ == text@,
    {
        let source = text.as_str();
        let Some(edges) = remember_edges_at(source, start, join) else { return Err(text); };
        let ghost prefix = edges.prefix;
        let ghost suffix = edges.suffix;
        let head = edges.head;
        let tail = edges.tail;
        proof {
            let bytes = encode_utf8(text@);
            assert(source.spec_bytes() == bytes);
            assert(start <= join <= bytes.len());
            assert(edges_from(bytes, start, join, (prefix, suffix), head, tail));
            assert(exists|parts: (&str, &str)|
                #[trigger] edges_from(bytes, start, join, parts, head, tail));
            assert(cached_edges_match(text@, start, join, head, tail));
        }
        Ok(Self { text, revision, start, join, head, tail })
    }

    /// キャッシュを構築した文書バージョンを返す。
    pub fn revision(&self) -> (revision: u64)
        ensures revision == self.revision_model(),
    {
        self.revision
    }

    /// キャッシュが所有する旧本文を借りる。
    pub fn text(&self) -> (source: &str)
        ensures source@ == self.text_model(),
    {
        self.text.as_str()
    }

    /// 現在の本文の変更区間だけを回復解析し、問い合わせの文書バージョンを添える。
    ///
    /// 変更区間を切り出せない場合や、指定されたバージョンと本文がキャッシュの条件を満たさない場合は、
    /// `None` を返す。呼び出し側はそのとき用途に合う全文解析を実行できる。
    pub fn try_snapshot<'p, 's>(&'p self, source: &'s str, revision: u64)
        -> (result: Option<RecoverySnapshot<'p, 's>>)
        ensures result matches Some(snapshot) ==> {
            &&& snapshot.revision_model() == revision
            &&& snapshot.source_model() == source
            &&& snapshot.matches_source()
            &&& snapshot.recovery_model() matches SnapshotRecovery::Local(update)
            &&& self.revision_model() <= revision
            &&& (revision == self.revision_model() ==> source@ == self.text_model())
            &&& *update.section_model(0).recovered == self.head_model()
            &&& *update.section_model(2).recovered == self.tail_model()
            &&& self.reuses_edge_bytes(&update)
        },
    {
        let recovery = SnapshotRecovery::Local(self.try_reparse(source, revision)?);
        Some(RecoverySnapshot { revision, source, recovery })
    }

    /// 再利用する接頭部または接尾部で、旧本文の範囲に対応する現在の範囲を求める。
    ///
    /// `section` は接頭部なら0、接尾部なら2。`try_snapshot` が局所解析を返せば、
    /// 前後の本文が等しい条件を満たす。旧範囲は指定した区間内に収まるものを渡す。
    pub proof fn reused_range_in_current(
        &self, old: &str, update: &ReparsedRecovery, old_span: Range<usize>, section: int,
    ) -> (new_span: Range<usize>)
        requires
            old@ == self.text_model(), self.reuses_edge_bytes(update),
            crate::located_span(old, old_span),
            section == 0 && old_span.end <= self.head_end_model()
                || section == 2 && self.tail_start_model() <= old_span.start,
        ensures
            crate::located_span(update.source_model(), new_span),
            old.spec_bytes()[old_span.start as int..old_span.end as int]
                == update.source_model().spec_bytes()[new_span.start as int..new_span.end as int],
            section == 0 ==> new_span == old_span,
            section == 2 ==> {
                let old_base = self.tail_start_model();
                let current_base = update.section_model(2).byte_base;
                &&& new_span.start as int == old_span.start - old_base + current_base
                &&& new_span.end as int == old_span.end - old_base + current_base
            },
    {
        reveal(ReparsedRecovery::valid);
        let current = update.source_model();
        let a = old.spec_bytes();
        let b = current.spec_bytes();
        encode_utf8_valid_utf8(current@);
        crate::is_char_boundary_start_end_of_seq(b);
        let (old_base, old_limit, current_base, current_limit) = if section == 0 {
            (0int, self.head_end_model() as int, 0int, update.section_model(1).byte_base as int)
        } else {
            (self.tail_start_model() as int, a.len() as int,
                update.section_model(2).byte_base as int, b.len() as int)
        };
        let shared = a[old_base..old_limit];
        assert(shared == b[current_base..current_limit]);
        let first = old_span.start - old_base;
        let last = old_span.end - old_base;
        let start = current_base + first;
        let end = current_base + last;
        assert(0 <= start < end <= current_limit <= b.len() <= usize::MAX);
        assert(a[old_span.start as int..old_span.end as int] =~= shared[first..last]);
        assert(b[start..end] =~= shared[first..last]);
        edge_range_boundary(old, current, old_base, old_limit, current_base, current_limit, first);
        edge_range_boundary(old, current, old_base, old_limit, current_base, current_limit, last);
        start as usize..end as usize
    }

    /// 旧全文の連続した前後の元リストが、現在の局所解析の前後の区間を過不足なく覆うことを示す。
    ///
    /// `head_count` 件目で接頭部が終わり、`first_tail` 件目を閉じた位置から接尾部が始まる。
    /// 件数が0なら本文の先頭を境界とする。旧本文はこのキャッシュの解析に使ったものを渡す。
    pub proof fn reused_original_lists_cover(
        &self, old: &str, whole: &Recovered, update: &ReparsedRecovery, head_count: nat, first_tail: nat,
    )
        requires
            old@ == self.text_model(),
            3 * old.spec_bytes().len() + 1 < usize::MAX,
            recovered_replay_matches(old, whole.forms@, whole.repairs@, whole.original_lists@),
            head_count <= first_tail <= whole.original_lists@.len(),
            self.head_end_model() == if head_count == 0 { 0 } else { whole.original_lists@[head_count - 1].end },
            self.tail_start_model() == if first_tail == 0 { 0 } else { whole.original_lists@[first_tail - 1].end },
            self.reuses_edge_bytes(update),
            *update.section_model(0).recovered == self.head_model(),
            *update.section_model(2).recovered == self.tail_model(),
        ensures
            update.section_model(0).recovered.original_lists@ == whole.original_lists@.take(head_count as int),
            whole.original_lists@.skip(first_tail as int)
                == update.section_model(2).recovered.original_lists@.map_values(
                    |span: Range<usize>| (self.tail_start_model() + span.start) as usize..(self.tail_start_model() + span.end) as usize),
    {
        let bytes = old.spec_bytes();
        let pair = choose|pair: (&str, &str)| #[trigger]
            edges_from(bytes, self.start, self.join, pair, self.head, self.tail);
        let (head_text, tail_text) = pair;
        retained_original_lists_agree(old, whole, head_text, &self.head, tail_text, &self.tail, head_count, first_tail);
    }

    fn try_reparse<'p, 's>(&'p self, source: &'s str, revision: u64)
        -> (result: Option<ReparsedRecovery<'p, 's>>)
        ensures result matches Some(update) ==> {
            &&& update.valid() && update.source_model() == source
            &&& self.revision_model() <= revision
            &&& (revision == self.revision_model() ==> source@ == self.text_model())
            &&& *update.section_model(0).recovered == self.head_model()
            &&& *update.section_model(2).recovered == self.tail_model()
            &&& self.reuses_edge_bytes(&update)
        },
    {
        if revision < self.revision {
            return None;
        }
        let old = self.text();
        if revision == self.revision && source != old {
            return None;
        }
        proof { use_type_invariant(self); }
        let (prefix, _, suffix) = split_source(old, self.start, self.join)?;
        proof {
            let bytes = encode_utf8(self.text@);
            let pair = choose|pair: (&str, &str)|
                #[trigger] edges_from(bytes, self.start, self.join, pair, self.head, self.tail);
            let (previous_prefix, previous_suffix) = pair;
            assert(previous_prefix.spec_bytes() == prefix.spec_bytes());
            assert(previous_suffix.spec_bytes() == suffix.spec_bytes());
            parsed_from_transfers_on_bytes(previous_prefix, prefix, &self.head);
            parsed_from_transfers_on_bytes(previous_suffix, suffix, &self.tail);
            crate::recovery_boundary::settled_boundary_transfers_on_bytes(
                previous_prefix, prefix, prefix.spec_bytes().len() as usize,
            );
        }
        reparse_edges(source, prefix, suffix, &self.head, &self.tail)
    }
}

// 末尾以外の位置は、保存したバイトが UTF-8 の継続バイトかどうかで決まる。
proof fn edge_range_boundary(
    old: &str, current: &str, old_base: int, old_limit: int, current_base: int, current_limit: int, offset: int,
)
    requires
        0 <= old_base <= old_limit <= old.spec_bytes().len(),
        0 <= current_base <= current_limit <= current.spec_bytes().len(),
        old.spec_bytes()[old_base..old_limit] == current.spec_bytes()[current_base..current_limit],
        0 <= offset <= old_limit - old_base,
        crate::is_char_boundary(old.spec_bytes(), old_base + offset),
        crate::is_char_boundary(current.spec_bytes(), current_limit),
    ensures crate::is_char_boundary(current.spec_bytes(), current_base + offset),
{
    let a = old.spec_bytes();
    let b = current.spec_bytes();
    let shared = a[old_base..old_limit];
    let reused = b[current_base..current_limit];
    assert(shared == reused);
    assert(shared.len() == old_limit - old_base);
    assert(reused.len() == current_limit - current_base);
    if offset < shared.len() {
        encode_utf8_valid_utf8(old@);
        encode_utf8_valid_utf8(current@);
        is_char_boundary_iff_not_is_continuation_byte(a, old_base + offset);
        is_char_boundary_iff_not_is_continuation_byte(b, current_base + offset);
        assert(a[old_base + offset] == shared[offset]);
        assert(b[current_base + offset] == shared[offset]);
    }
}

spec fn cached_edges_match(chars: Seq<char>, start: usize, join: usize, head: Recovered, tail: Recovered) -> bool {
    let bytes = encode_utf8(chars);
    &&& start <= join <= bytes.len()
    &&& exists|parts: (&str, &str)| #[trigger] edges_from(bytes, start, join, parts, head, tail)
}

spec fn edges_from(
    bytes: Seq<u8>, start: usize, join: usize, parts: (&str, &str), head: Recovered, tail: Recovered,
) -> bool {
    let (prefix, suffix) = parts;
    &&& prefix.spec_bytes() == bytes[..start as int]
    &&& suffix.spec_bytes() == bytes[join as int..]
    &&& clean_prefix(prefix, &head)
    &&& parsed_from(suffix, &tail)
}

proof fn parsed_from_transfers_on_bytes(left: &str, right: &str, result: &Recovered)
    requires left.spec_bytes() == right.spec_bytes(), parsed_from(left, result),
    ensures parsed_from(right, result),
{
    crate::recovery_replay::recovery_replay_transfers_on_bytes(left, right, result);
    reveal(crate::form_spans_valid);
    reveal(crate::original_list_ranges);
}

/// 現在の本文を回復解析する。前後の本文と回復の境界が一致すれば、その結果を再利用する。
///
/// キャッシュがない場合、問い合わせの文書バージョンがキャッシュより古い場合、同じ文書バージョンで本文が異なる場合、
/// または変更区間を独立に読めない場合は、現在の本文を全文解析する。
/// 結果は問い合わせで渡した文書バージョンと本文に対応する。
/// ホストは公開直前に、文書 ID と文書バージョンを最新のスナップショットと照合する。
pub fn recover_snapshot<'p, 's>(
    cache: Option<&'p OwnedRecoveryCache>, source: &'s str, revision: u64,
) -> (snapshot: RecoverySnapshot<'p, 's>)
    ensures
        snapshot.revision_model() == revision,
        snapshot.source_model() == source,
        snapshot.matches_source(),
        snapshot.recovery_model() matches SnapshotRecovery::Local(update) ==> {
            &&& cache matches Some(saved)
            &&& saved.revision_model() <= revision
            &&& (revision == saved.revision_model() ==> source@ == saved.text_model())
            &&& *update.section_model(0).recovered == saved.head_model()
            &&& *update.section_model(2).recovered == saved.tail_model()
            &&& saved.reuses_edge_bytes(&update)
        },
{
    if let Some(cache) = cache {
        if let Some(snapshot) = cache.try_snapshot(source, revision) {
            return snapshot;
        }
    }
    let recovery = SnapshotRecovery::Full(parse_recovering(source));
    RecoverySnapshot { revision, source, recovery }
}

impl<'p, 's> RecoverySnapshot<'p, 's> {
    #[verifier::type_invariant]
    spec fn consistent(&self) -> bool { self.matches_source() }

    /// 問い合わせで渡された文書版を表す。
    pub closed spec fn revision_model(&self) -> u64 { self.revision }

    /// この解析に使った本文を表す。
    pub closed spec fn source_model(&self) -> &'s str { self.source }

    /// この解析で得た結果を表す。
    pub closed spec fn recovery_model(&self) -> &SnapshotRecovery<'p, 's> { &self.recovery }

    /// 問い合わせで渡された文書版を返す。最新版かどうかは公開時に確認する。
    pub fn revision(&self) -> (revision: u64)
        ensures revision == self.revision_model(),
    {
        self.revision
    }

    /// 診断範囲と構文木の添字の基準となる UTF-8 本文を返す。
    pub fn source(&self) -> (source: &'s str)
        ensures source == self.source_model(),
    {
        self.source
    }

    /// 問い合わせの文書バージョンと本文に対応する回復解析結果を借りる。
    pub fn recovery(&self) -> (result: &SnapshotRecovery<'p, 's>)
        ensures result == self.recovery_model(), self.matches_source(),
    {
        proof { use_type_invariant(self); }
        &self.recovery
    }

    /// 解析結果が問い合わせ時の本文に対応することを表す。
    pub open spec fn matches_source(&self) -> bool {
        match self.recovery_model() {
            SnapshotRecovery::Local(local) => local.valid() && local.source_model() == self.source_model(),
            SnapshotRecovery::Full(full) =>
                recovered_replay_matches(self.source_model(), full.forms@, full.repairs@, full.original_lists@),
        }
    }

    /// 位置と添字を現在の本文に揃えると、参照する全文回復解析と一致することを表す。
    pub open spec fn agrees_with(&self, whole: &Recovered) -> bool {
        match self.recovery_model() {
            SnapshotRecovery::Local(local) => local.agrees_with(whole),
            SnapshotRecovery::Full(full) =>
                full.forms@ == whole.forms@ && full.repairs@ == whole.repairs@
                && full.original_lists@ == whole.original_lists@,
        }
    }

    /// 局所再解析と全文解析のどちらでも、同じ本文の参照結果と一致することを示す。
    pub proof fn agrees_with_full(&self, whole: &Recovered)
        requires
            self.matches_source(),
            recovered_replay_matches(self.source_model(), whole.forms@, whole.repairs@, whole.original_lists@),
        ensures self.agrees_with(whole),
    {
        match self.recovery_model() {
            SnapshotRecovery::Local(local) => local.agrees_with_full(whole),
            SnapshotRecovery::Full(full) => recovered_replays_agree(self.source, self.source, full, whole),
        }
    }
}

} // verus!
