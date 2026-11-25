//! S 式の変更区間だけを回復解析し、共通部分の結果を再利用する。

use crate::{Recovered, parse_recovering, recovery_boundary_at};
#[cfg(verus_only)]
use crate::{form_spans_valid, original_list_ranges, original_list_roots, recovered_replay_matches, settled_recovery_boundary};
#[cfg(verus_only)]
use crate::recovery_replay::{clean_prefix_form_count, recovered_three_parts_agree, recovery_three_parts_projection};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::{
    string::StringSliceAdditionalSpecFns,
    utf8::{encode_utf8_decode_utf8, encode_utf8_valid_utf8, is_char_boundary,
        is_char_boundary_iff_not_is_continuation_byte, is_char_boundary_start_end_of_seq},
};

mod observe;
mod owned;
pub use owned::{OwnedRecoveryCache, RecoverySnapshot, SnapshotRecovery, recover_snapshot};
pub use observe::RecoveryFormLocation;
#[cfg(verus_only)]
pub use observe::{located_span, original_list_form};

verus! {

/// 編集区間の前後にある本文と、それぞれを単独で読んだ回復結果。
pub struct RecoveryEdges<'a> {
    prefix: &'a str,
    suffix: &'a str,
    head: Recovered,
    tail: Recovered,
}

/// 現在の文書に含まれる一つの区間と、その区間を起点とした回復結果。
pub struct RecoverySection<'a> {
    /// 現在の文書の先頭から区間までの UTF-8 バイト数。
    pub byte_base: usize,
    /// 区間より前にある構文木の要素数。
    pub form_base: usize,
    /// バイト位置と構文木の添字を、区間の先頭から数えた回復結果。
    pub recovered: &'a Recovered,
}

/// 変更区間を読み直した結果と、現在の本文に対応する前後の解析結果。
pub struct ReparsedRecovery<'p, 's> {
    source: &'s str,
    _pieces: Ghost<(&'p str, &'s str, &'p str)>,
    start: usize,
    join: usize,
    head: &'p Recovered,
    changed: Recovered,
    tail: &'p Recovered,
}

spec fn parsed_from(source: &str, parsed: &Recovered) -> bool {
    &&& recovered_replay_matches(source, parsed.forms@, parsed.repairs@, parsed.original_lists@)
    &&& form_spans_valid(source, parsed.forms@, source.spec_bytes().len() as int)
    &&& original_list_ranges(source, parsed.original_lists@, parsed.repairs@, source.spec_bytes().len() as int)
    &&& original_list_roots(parsed.forms@, parsed.original_lists@)
}

spec fn clean_prefix(source: &str, parsed: &Recovered) -> bool {
    &&& source.spec_bytes().len() <= usize::MAX
    &&& settled_recovery_boundary(source, source.spec_bytes().len() as usize)
    &&& parsed.repairs@.len() == 0
    &&& parsed_from(source, parsed)
}

impl<'a> RecoveryEdges<'a> {
    #[verifier::type_invariant]
    spec fn valid(&self) -> bool {
        clean_prefix(self.prefix, &self.head) && parsed_from(self.suffix, &self.tail)
    }

    /// 接頭部と接尾部の本文をバイト単位で照合し、変更区間だけを回復解析する。
    ///
    /// 変更区間は空か、修復を挟まず元の閉じ括弧で終わる必要がある。
    /// この条件を満たさない場合、前後の本文が異なる場合、区切りが UTF-8 の文字境界にない場合、
    /// または位置や添字の計算が表現できる本文長の上限を超えた場合は `None` を返す。
    /// 呼び出し側は `None` の場合に現在の本文を全文解析できる。
    pub fn reparse<'p, 's>(&'p self, source: &'s str) -> (result: Option<ReparsedRecovery<'p, 's>>)
        ensures result matches Some(update) ==> update.source_model() == source && update.valid(),
    {
        proof { use_type_invariant(self); }
        reparse_edges(source, self.prefix, self.suffix, &self.head, &self.tail)
    }
}

fn reparse_edges<'p, 's>(
    source: &'s str, old_prefix: &'p str, old_suffix: &'p str, head: &'p Recovered, tail: &'p Recovered,
) -> (result: Option<ReparsedRecovery<'p, 's>>)
    requires clean_prefix(old_prefix, head), parsed_from(old_suffix, tail),
    ensures result matches Some(update) ==> {
        &&& update.source_model() == source
        &&& update.valid()
        &&& update.section_model(0).recovered == head
        &&& update.section_model(2).recovered == tail
    },
{
    let length = source.as_bytes().len();
    let suffix_len = old_suffix.as_bytes().len();
    if length > (usize::MAX - 2) / 3 || suffix_len > length {
        return None;
    }
    let start = old_prefix.as_bytes().len();
    let join = length - suffix_len;
    let (prefix, middle, suffix) = split_source(source, start, join)?;
    proof {
        encode_utf8_decode_utf8(prefix@);
        encode_utf8_decode_utf8(suffix@);
        encode_utf8_decode_utf8(old_prefix@);
        encode_utf8_decode_utf8(old_suffix@);
    }
    if prefix != old_prefix || suffix != old_suffix {
        return None;
    }
    let changed = analyze_closed(middle)?;
    Some(ReparsedRecovery {
        source, _pieces: Ghost((old_prefix, middle, old_suffix)), start, join,
        head, changed, tail,
    })
}

impl<'p, 's> ReparsedRecovery<'p, 's> {
    /// 解析結果が対応する現在の本文を表す。
    pub closed spec fn source_model(&self) -> &'s str { self.source }

    /// 各区間の結果が、その区間の本文に対応することを表す。
    pub closed spec fn valid(&self) -> bool {
        let bytes = self.source.spec_bytes();
        let (prefix, middle, suffix) = self._pieces@;
        &&& 3 * bytes.len() + 1 < usize::MAX
        &&& self.start <= self.join <= bytes.len()
        &&& is_char_boundary(bytes, self.start as int)
        &&& is_char_boundary(bytes, self.join as int)
        &&& prefix.spec_bytes() == bytes[..self.start as int]
        &&& middle.spec_bytes() == bytes[self.start as int..self.join as int]
        &&& suffix.spec_bytes() == bytes[self.join as int..]
        &&& clean_prefix(prefix, self.head)
        &&& clean_prefix(middle, &self.changed)
        &&& parsed_from(suffix, self.tail)
    }

    #[verifier::type_invariant]
    spec fn sections_are_valid(&self) -> bool { self.valid() }

    /// 解析結果が対応する現在の本文を返す。
    pub fn source(&self) -> (source: &'s str)
        ensures source == self.source_model(),
    {
        self.source
    }

    /// 区間ごとの結果と加算する値を、接頭部、変更区間、接尾部の順に返す。
    ///
    /// 絶対位置を得るには、範囲の両端に `byte_base` を、構文木の添字に `form_base` を加える。
    pub fn sections(&self) -> (sections: [RecoverySection<'_>; 3])
        ensures self.sections_match(sections), self.valid(),
    {
        proof {
            use_type_invariant(self);
            let (prefix, middle, _) = self._pieces@;
            clean_prefix_form_count(prefix, self.head, self.start);
            clean_prefix_form_count(middle, &self.changed, (self.join - self.start) as usize);
        }
        let head_count = self.head.forms.len();
        let middle_count = self.changed.forms.len();
        [
            RecoverySection { byte_base: 0, form_base: 0, recovered: self.head },
            RecoverySection { byte_base: self.start, form_base: head_count, recovered: &self.changed },
            RecoverySection { byte_base: self.join, form_base: head_count + middle_count, recovered: self.tail },
        ]
    }

    /// 指定した区間の回復結果と、絶対位置への変換に使う基準値。
    pub closed spec fn section_model(&self, index: int) -> RecoverySection<'_> {
        if index == 0 {
            RecoverySection { byte_base: 0, form_base: 0, recovered: self.head }
        } else if index == 1 {
            RecoverySection { byte_base: self.start, form_base: self.head.forms@.len() as usize,
                recovered: &self.changed }
        } else {
            RecoverySection { byte_base: self.join,
                form_base: (self.head.forms@.len() + self.changed.forms@.len()) as usize,
                recovered: self.tail }
        }
    }

    /// 区間列がこの解析結果の位置と内容を保持することを表す。
    pub open spec fn sections_match(&self, sections: [RecoverySection; 3]) -> bool {
        &&& sections@[0] == self.section_model(0)
        &&& sections@[1] == self.section_model(1)
        &&& sections@[2] == self.section_model(2)
    }

    /// 区間ごとの結果を位置と添字で揃えたものが、参照する全文解析と一致することを表す。
    pub closed spec fn agrees_with(&self, whole: &Recovered) -> bool {
        recovery_three_parts_projection(whole, self.head, &self.changed, self.tail, self.start, self.join)
    }

    /// 現在の本文を全文解析した場合にも、同じ構文木、修復、元リストが得られることを示す。
    pub proof fn agrees_with_full(&self, whole: &Recovered)
        requires self.valid(), recovered_replay_matches(self.source_model(), whole.forms@, whole.repairs@, whole.original_lists@),
        ensures self.agrees_with(whole),
    {
        let (prefix, middle, suffix) = self._pieces@;
        recovered_three_parts_agree(self.source, prefix, middle, suffix,
            self.start, self.join, whole, self.head, &self.changed, self.tail);
    }
}

/// 選んだ変更区間の前後を別々に読み、次の編集で使えるよう保持する。
///
/// `start` と `join` は変更前の本文における UTF-8 のバイト位置。
/// 接頭部は空か、修復を挟まず元の閉じ括弧で終わる必要がある。
/// 接尾部は単独で回復解析し、変更後の合流点から同じ本文が続く場合に再利用する。
pub fn remember_recovery_edges(source: &str, start: usize, join: usize) -> Option<RecoveryEdges<'_>> {
    remember_edges_at(source, start, join)
}

fn remember_edges_at(source: &str, start: usize, join: usize) -> (result: Option<RecoveryEdges<'_>>)
    ensures result matches Some(edges) ==> {
        let bytes = source.spec_bytes();
        &&& start <= join <= bytes.len()
        &&& edges.prefix.spec_bytes() == bytes[..start as int]
        &&& edges.suffix.spec_bytes() == bytes[join as int..]
        &&& clean_prefix(edges.prefix, &edges.head)
        &&& parsed_from(edges.suffix, &edges.tail)
    },
{
    let (prefix, _, suffix) = split_source(source, start, join)?;
    let head = analyze_closed(prefix)?;
    let tail = parse_recovering(suffix);
    Some(RecoveryEdges { prefix, suffix, head, tail })
}

fn analyze_closed(source: &str) -> (result: Option<Recovered>)
    ensures result matches Some(parsed) ==> clean_prefix(source, &parsed),
{
    let length = source.as_bytes().len();
    let parsed = parse_recovering(source);
    if !parsed.repairs.is_empty() || recovery_boundary_at(source, length).is_none() {
        return None;
    }
    Some(parsed)
}

fn split_source(source: &str, start: usize, join: usize) -> (result: Option<(&str, &str, &str)>)
    ensures result matches Some((prefix, middle, suffix)) ==> {
        let bytes = source.spec_bytes();
        &&& start <= join <= bytes.len()
        &&& is_char_boundary(bytes, start as int)
        &&& is_char_boundary(bytes, join as int)
        &&& prefix.spec_bytes() == bytes[..start as int]
        &&& middle.spec_bytes() == bytes[start as int..join as int]
        &&& suffix.spec_bytes() == bytes[join as int..]
    },
{
    if start > join || !source.is_char_boundary(start) || !source.is_char_boundary(join) {
        return None;
    }
    proof { encode_utf8_valid_utf8(source@); }
    let (before, suffix) = source.split_at(join);
    proof {
        encode_utf8_valid_utf8(before@);
        if start < join {
            assert(before.spec_bytes()[start as int] == source.spec_bytes()[start as int]);
            is_char_boundary_iff_not_is_continuation_byte(source.spec_bytes(), start as int);
            is_char_boundary_iff_not_is_continuation_byte(before.spec_bytes(), start as int);
        } else {
            is_char_boundary_start_end_of_seq(before.spec_bytes());
        }
        assert(is_char_boundary(before.spec_bytes(), start as int));
    }
    let (prefix, middle) = before.split_at(start);
    assert(prefix.spec_bytes() =~= source.spec_bytes()[..start as int]);
    assert(middle.spec_bytes() =~= source.spec_bytes()[start as int..join as int]);
    Some((prefix, middle, suffix))
}

} // verus!
