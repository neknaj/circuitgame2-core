//! NCG2M の厳格索引と、編集中の元入力から確認できた断片を返す。

mod provisional;

pub use provisional::{ProvisionalMetaDeclaration, recover_meta_file_with_provisional};
#[cfg(verus_only)]
pub use provisional::provisional_meta_matches;

use alloc::vec::Vec;
use core::ops::Range;

use crate::project::read_source_span;
use crate::syntax::{Recovered, parse_recovering};
#[cfg(verus_only)]
use crate::syntax::{
    inserted_closes_match, located_span, original_list_ranges, original_list_roots, original_list_source_bounds,
    recovered_replay_matches,
};
use super::{MetaFileError, MetaItem, index_meta_file};
#[cfg(verus_only)]
use super::super::defn::usable_forms;
#[cfg(verus_only)]
use super::{meta_binding_spans_valid, meta_file_matches, meta_file_results_agree, same_meta_item, valid_meta_file};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 元の括弧で閉じたトップレベルのリストと、その範囲内での厳格索引。
#[derive(Debug)]
pub struct OriginalMetaList {
    /// 文書全体を基準にした UTF-8 半開バイト範囲。
    pub span: Range<usize>,
    /// リスト先頭を基準にした索引または最初の構文違反。
    pub index: Result<Vec<MetaItem>, MetaFileError>,
}

/// NCG2M の文書の構文を検査した結果。
#[derive(Debug)]
pub enum MetaFileRecovery {
    /// 文書全体の厳格索引。各位置は文書先頭を基準にする。
    Complete(Vec<MetaItem>),
    /// 文書を厳格に読めなかったため、確定したリストを個別に検査した。
    Incomplete {
        /// 文書全体を厳格に読んだときに最初に見つけた違反。
        first: MetaFileError,
        /// 共通 S 式の構文木と、補完や読み飛ばしの記録。
        syntax: Recovered,
        /// 元のトップレベルのリストごとの結果。文書上の順に並ぶ。
        lists: Vec<OriginalMetaList>,
    },
}

/// 断片の索引が、その範囲から切り出した元入力の厳格索引と一致することを表す。
pub open spec fn original_meta_list_matches(source: &str, list: OriginalMetaList) -> bool {
    &&& located_span(source, list.span)
    &&& exists|fragment: &str| {
        &&& #[trigger] fragment.spec_bytes() == source.spec_bytes()[list.span.start as int..list.span.end as int]
        &&& meta_file_matches(fragment, list.index)
        &&& (list.index.is_ok() == valid_meta_file(fragment))
        &&& (list.index matches Ok(items) ==> meta_binding_spans_valid(fragment, items@))
    }
}

spec fn completed_lists_match(source: &str, spans: Seq<Range<usize>>, lists: Seq<OriginalMetaList>) -> bool {
    &&& lists.len() <= spans.len()
    &&& forall|i: int| 0 <= i < lists.len() ==> {
        let list = #[trigger] lists[i];
        list.span == spans[i] && original_meta_list_matches(source, list)
    }
}

/// 回復結果が文書の厳格索引、または元入力の確定したリストの列に対応することを表す。
pub closed spec fn meta_file_recovery_matches(source: &str, recovery: MetaFileRecovery) -> bool {
    match recovery {
        MetaFileRecovery::Complete(items) =>
            valid_meta_file(source) && meta_file_matches(source, Ok(items))
                && meta_binding_spans_valid(source, items@),
        MetaFileRecovery::Incomplete { first, syntax, lists } =>
            !valid_meta_file(source) && meta_file_matches(source, Err(first))
                && recovered_replay_matches(source, syntax.forms@, syntax.repairs@, syntax.original_lists@)
                && usable_forms(source, syntax.forms@)
                && inserted_closes_match(source, syntax.forms@, syntax.repairs@)
                && original_list_ranges(source, syntax.original_lists@, syntax.repairs@,
                    source.spec_bytes().len() as int)
                && original_list_roots(syntax.forms@, syntax.original_lists@)
                && lists@.len() == syntax.original_lists@.len()
                && completed_lists_match(source, syntax.original_lists@, lists@),
    }
}

/// 全文の解析に成功した回復結果は、同じ入力の厳格索引と各項目の位置・内容が一致する。
pub proof fn complete_meta_recovery_agrees(
    source: &str, recovery: MetaFileRecovery, strict: Vec<MetaItem>,
)
    requires
        meta_file_recovery_matches(source, recovery),
        recovery is Complete,
        meta_file_matches(source, Ok(strict)),
    ensures
        recovery->Complete_0@.len() == strict@.len(),
        forall|i: int| 0 <= i < strict@.len() ==>
            #[trigger] same_meta_item(recovery->Complete_0@[i], strict@[i]),
{
    let items = recovery->Complete_0;
    meta_file_results_agree(source, Ok(items), Ok(strict));
}

/// 断片の位置と索引を、回復で確定した元のトップレベルのリストに結び付ける。
pub proof fn recovered_meta_list_has_origin(
    source: &str, recovery: MetaFileRecovery, slot: int,
)
    requires
        meta_file_recovery_matches(source, recovery),
        recovery is Incomplete,
        0 <= slot < recovery->Incomplete_lists@.len(),
    ensures
        recovery->Incomplete_lists@[slot].span == recovery->Incomplete_syntax.original_lists@[slot],
        original_meta_list_matches(source, recovery->Incomplete_lists@[slot]),
{
    let lists = recovery->Incomplete_lists@;
    let spans = recovery->Incomplete_syntax.original_lists@;
    assert(completed_lists_match(source, spans, lists));
}

/// 文書全体を厳格に検査し、失敗時は確定したリストを個別に検査する。
///
/// 共通 S 式の回復が元入力の括弧で閉じたと確認したトップレベルのリストだけを使う。
/// 同じリスト内に違反があれば、そのリストには厳格な違反を保持する。
/// 文書全体と断片の違反は、それぞれ文書先頭と断片先頭を基準とする。
///
/// # Examples
///
/// ```
/// use circuitgame2_core::ncg2m::file::recovery::{MetaFileRecovery, recover_meta_file};
///
/// let source = ") (defmacro saved () (quote value)) (defn broken";
/// let MetaFileRecovery::Incomplete { lists, .. } = recover_meta_file(source) else { panic!() };
/// assert_eq!(lists.len(), 1);
/// assert_eq!(&source[lists[0].span.clone()], "(defmacro saved () (quote value))");
/// assert!(lists[0].index.is_ok());
/// ```
pub fn recover_meta_file(source: &str) -> (recovery: MetaFileRecovery)
    ensures
        meta_file_recovery_matches(source, recovery),
        recovery is Complete <==> valid_meta_file(source),
{
    let first = match index_meta_file(source) {
        Ok(items) => return MetaFileRecovery::Complete(items),
        Err(error) => error,
    };
    let syntax = parse_recovering(source);
    let mut lists: Vec<OriginalMetaList> = Vec::new();
    let mut at = 0;
    while at < syntax.original_lists.len()
        invariant
            at == lists@.len(),
            completed_lists_match(source, syntax.original_lists@, lists@),
            original_list_ranges(source, syntax.original_lists@, syntax.repairs@,
                source.spec_bytes().len() as int),
        decreases syntax.original_lists@.len() - at,
    {
        let span = &syntax.original_lists[at];
        proof { original_list_source_bounds(source, syntax.original_lists@, syntax.repairs@, at as int); }
        let fragment = read_source_span(source, span.start, span.end);
        let index = index_meta_file(fragment);
        let list = OriginalMetaList { span: span.start..span.end, index };
        assert(original_meta_list_matches(source, list)) by {
            assert(fragment.spec_bytes() == source.spec_bytes()[list.span.start as int..list.span.end as int]);
        };
        let ghost prior = lists@;
        let ghost next = list;
        lists.push(list);
        assert forall|i: int| 0 <= i < lists@.len() implies {
            let list = #[trigger] lists@[i];
            list.span == syntax.original_lists@[i] && original_meta_list_matches(source, list)
        } by {
            if i < at {
                assert(lists@[i] == prior[i]);
            } else {
                assert(lists@[i] == next);
            }
        };
        at += 1;
    }
    MetaFileRecovery::Incomplete { first, syntax, lists }
}

}
