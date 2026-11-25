//! 文書が所有する回復キャッシュから、現在の本文の解析結果を得る。

use alloc::string::String;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::{string::StringSliceAdditionalSpecFns, utf8::encode_utf8};

use super::{ReparsedRecovery, remember_edges_at, reparse_edges, split_source};
#[cfg(verus_only)]
use super::{clean_prefix, parsed_from};
use crate::{Recovered, parse_recovering};
#[cfg(verus_only)]
use crate::{recovered_replay_matches, recovered_replays_agree};

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
            result matches Ok(cache) ==> cache.text_model() == text@ && cache.revision_model() == revision,
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

    fn try_reparse<'p, 's>(&'p self, source: &'s str, revision: u64)
        -> (result: Option<ReparsedRecovery<'p, 's>>)
        ensures result matches Some(update) ==> {
            &&& update.valid() && update.source_model() == source
            &&& self.revision_model() <= revision
            &&& (revision == self.revision_model() ==> source@ == self.text_model())
            &&& *update.section_model(0).recovered == self.head_model()
            &&& *update.section_model(2).recovered == self.tail_model()
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
        },
{
    let recovery = if let Some(cache) = cache {
        cache.try_reparse(source, revision)
    } else {
        None
    };
    let recovery = match recovery {
        Some(local) => SnapshotRecovery::Local(local),
        None => SnapshotRecovery::Full(parse_recovering(source)),
    };
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
