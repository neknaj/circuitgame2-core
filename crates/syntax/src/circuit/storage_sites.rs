//! 状態素子の宣言から幅と型の指定位置を取り出す。

use super::{CircuitForms, FieldTypeSite, Form, Head};
#[cfg(verus_only)]
use super::{Clause, circuit_index_matches, header_arguments_match, natural_clause_matches, type_matches};
#[cfg(verus_only)]
use super::index::indexed_entry_evidence;
use vstd::prelude::*;

verus! {

/// 状態素子の宣言にある自然数と型指定のフォーム添字。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StorageSites {
    /// ラッチの幅指定。
    Latch {
        /// `width` の自然数の字句。
        width: usize,
    },
    /// RAM のアドレス幅とデータ型の指定。
    Memory {
        /// `address` の自然数の字句。
        address: usize,
        /// `data` の型指定。幅の字句、または構造体を参照する名前の字句を指す。
        data: FieldTypeSite,
    },
}

/// 状態素子の添字が、指定された宣言の幅と型を指すことを表す。
pub closed spec fn storage_sites_match(
    source: &str, syntax: &CircuitForms, entry: int, result: Option<StorageSites>,
) -> bool {
    if 0 <= entry < syntax.entries@.len() {
        let item = syntax.entries@[entry];
        let forms = syntax.forms@;
        let root = item.form as int;
        let end = forms[root]->List_end as int;
        match item.head {
            Head::Latch => {
                &&& root < forms.len() && forms[root] is List
                &&& natural_clause_matches(source, forms, root + 3, end, end, Clause::Width)
                &&& result matches Some(StorageSites::Latch { width }) && width == root + 5
            },
            Head::Memory => {
                let ty = root + 8;
                &&& root < forms.len() && forms[root] is List
                &&& natural_clause_matches(source, forms, root + 3, end, root + 6, Clause::Address)
                &&& super::named_clause_matches(source, forms, root + 6, end, end, Clause::Data)
                &&& type_matches(source, forms, ty, end, end)
                &&& result matches Some(StorageSites::Memory { address, data })
                    && address == root + 5
                    && match data {
                        FieldTypeSite::Bits { width } => forms[ty] is List && width == ty + 2,
                        FieldTypeSite::Named { form } => forms[ty] is Atom && form == ty,
                    }
            },
            _ => result.is_none(),
        }
    } else {
        result.is_none()
    }
}

/// 幅と型を指すフォームの種別を、数値化と名前解決に使える形で示す。
pub proof fn storage_site_evidence(source: &str, syntax: &CircuitForms, entry: int, sites: StorageSites)
    requires storage_sites_match(source, syntax, entry, Some(sites)),
    ensures ({
        let forms = syntax.forms@;
        &&& 0 <= entry < syntax.entries@.len()
        &&& match sites {
            StorageSites::Latch { width } => syntax.entries@[entry].head is Latch
                && super::natural_argument_at(forms, width as int, forms.len() as int),
            StorageSites::Memory { address, data } => {
                &&& syntax.entries@[entry].head is Memory
                &&& super::natural_argument_at(forms, address as int, forms.len() as int)
                &&& match data {
                    FieldTypeSite::Bits { width } =>
                        super::natural_argument_at(forms, width as int, forms.len() as int),
                    FieldTypeSite::Named { form } => form < forms.len()
                        && forms[form as int] is Atom && super::reference_atom(forms[form as int]->Atom_kind),
                }
            },
        }
    }),
{
}

/// 厳格索引から、ラッチまたは RAM の宣言の幅と型の指定位置を返す。
///
/// 索引を生成したソースを渡す。項目が範囲外か、状態素子の宣言以外なら `None` を返す。
/// 幅の数値化と型名の解決は後段で行う。
///
/// # Panics
///
/// 手で組み立てた構文木と索引でフォームの添字が不整合な場合は、パニックすることがある。
pub fn storage_sites(_source: &str, syntax: &CircuitForms, entry: usize) -> (result: Option<StorageSites>)
    requires circuit_index_matches(_source, syntax.forms@, syntax.entries@),
    ensures
        storage_sites_match(_source, syntax, entry as int, result),
        result.is_some() <==> (entry < syntax.entries@.len()
            && (syntax.entries@[entry as int].head is Latch || syntax.entries@[entry as int].head is Memory)),
{
    if entry >= syntax.entries.len() {
        return None;
    }
    let item = &syntax.entries[entry];
    let root = item.form;
    let ghost forms = syntax.forms@;
    proof {
        indexed_entry_evidence(_source, forms, syntax.entries@, entry as int);
        reveal(super::form_has_head);
        reveal(header_arguments_match);
    }
    match item.head {
        Head::Latch => Some(StorageSites::Latch { width: root + 5 }),
        Head::Memory => {
            proof {
                let end = forms[root as int]->List_end as int;
                let data = choose|data: int| #[trigger] natural_clause_matches(
                    _source, forms, root + 3, end, data, Clause::Address)
                    && super::named_clause_matches(_source, forms, data, end, end, Clause::Data)
                    && type_matches(_source, forms, data + 2, end, end);
                assert(data == root + 6);
            }
            let ty = root + 8;
            let data = match syntax.forms[ty] {
                Form::List { .. } => FieldTypeSite::Bits { width: ty + 2 },
                Form::Atom { .. } => FieldTypeSite::Named { form: ty },
            };
            Some(StorageSites::Memory { address: root + 5, data })
        },
        _ => None,
    }
}

} // verus!
