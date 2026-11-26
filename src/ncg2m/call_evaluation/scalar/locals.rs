//! スカラーの局所束縛列を元の環境に結び、最も内側の名前を検索する。

use super::*;
use crate::ncg2m::forms::is_spelling;

verus! {

/// 評価済みの局所名とその値。
#[derive(Clone, Copy)]
pub(super) struct ScalarLocal<'a> {
    pub(super) name: &'a str,
    pub(super) value: ScalarValue,
}

#[verifier::opaque]
spec fn lookup_group(group: Seq<ScalarLocal>, limit: nat, name: Seq<u8>) -> Option<ScalarValue>
    decreases limit,
{
    if limit == 0 {
        None
    } else {
        let row = group[(limit - 1) as int];
        if row.name.spec_bytes() == name { Some(row.value) }
        else { lookup_group(group, (limit - 1) as nat, name) }
    }
}

pub(super) closed spec fn lexical_value(group: Seq<ScalarLocal>, name: Seq<u8>) -> Option<ScalarValue> {
    lookup_group(group, group.len(), name)
}

/// 検査済みの局所束縛列から指定した名前の値を得る。
pub(super) fn local_value(group: &[ScalarLocal], name: &str) -> (value: Option<ScalarValue>)
    ensures value == lexical_value(group@, name.spec_bytes()),
{
    let mut limit = group.len();
    while limit > 0
        invariant
            limit <= group@.len(),
            lookup_group(group@, limit as nat, name.spec_bytes())
                == lookup_group(group@, group@.len(), name.spec_bytes()),
        decreases limit,
    {
        reveal(lookup_group);
        let row = group[limit - 1];
        if is_spelling(row.name, name) {
            return Some(row.value);
        }
        limit -= 1;
    }
    proof { reveal(lookup_group); }
    None
}

pub(super) proof fn empty_local_values(name: Seq<u8>)
    ensures lexical_value(Seq::empty(), name).is_none(),
{
    reveal(lookup_group);
}

}
