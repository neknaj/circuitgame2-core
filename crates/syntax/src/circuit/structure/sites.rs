//! 厳格索引の構造体宣言から、配置検査に使う構文位置を取り出す。

#[cfg(verus_only)]
use super::{field_matches, fields_match_before};
use crate::circuit::{CircuitForms, Head};
use crate::Form;
use alloc::vec::Vec;
use vstd::prelude::*;

#[cfg(verus_only)]
use crate::circuit::index::indexed_entry_evidence;
#[cfg(verus_only)]
use crate::circuit::{
    circuit_index_matches, direct_form_in_range, directive_word_at, following_direct_form,
    form_region_ends_at, header_arguments_match, natural_clause_matches, node_end_is_following_direct_form,
    reference_atom, type_matches, Clause, HeaderError,
};
#[cfg(verus_only)]
use crate::{complete_list_indices, nested_list_indices, AtomKind};

verus! {

/// 構造体のフィールドや RAM のデータ型を指定する構文位置。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FieldTypeSite {
    /// ビット列を指定する。
    Bits {
        /// 幅の自然数の字句を指すフォームの添字。
        width: usize,
    },
    /// 別の構造体型を参照する。
    Named {
        /// 型名の字句を指すフォームの添字。
        form: usize,
    },
}

/// 一つのフィールドを構成するフォームの添字。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FieldSite {
    /// フィールド宣言のリスト。
    pub form: usize,
    /// フィールド名の字句。
    pub name: usize,
    /// 宣言した型。
    pub ty: FieldTypeSite,
    /// `at` に渡した自然数の字句。
    pub offset: usize,
}

/// 構造体の総幅とフィールドを指す添字。
#[derive(Debug, Eq, PartialEq)]
pub struct StructureSites {
    /// `width` に渡した自然数の字句。
    pub width: usize,
    /// ソース上の宣言順に並ぶフィールド。
    pub fields: Vec<FieldSite>,
}

/// フィールドの名前、型、オフセットの添字が同じ構文上の宣言を参照することを表す。
pub open spec fn field_site_matches(source: &str, forms: Seq<Form>, site: FieldSite) -> bool {
    let root = site.form as int;
    let end = forms[root]->List_end as int;
    let ty = root + 2;
    let at = site.offset as int - 2;
    &&& 0 <= root < end <= forms.len()
    &&& forms[root] is List
    &&& site.name == root + 1
    &&& directive_word_at(source, forms, site.name as int, end, HeaderError::ExpectedName)
    &&& type_matches(source, forms, ty, end, at)
    &&& natural_clause_matches(source, forms, at, end, end, Clause::At)
    &&& match site.ty {
        FieldTypeSite::Bits { width } =>
            width == ty + 2 && natural_clause_matches(source, forms, ty, end, at, Clause::Bits),
        FieldTypeSite::Named { form } => form == ty && 0 <= ty < at
            && forms[ty] is Atom && reference_atom(forms[ty]->Atom_kind),
    }
}

spec fn field_sites_before(
    source: &str, forms: Seq<Form>, start: int, end: int, cursor: int, fields: Seq<FieldSite>,
) -> bool {
    &&& forall|i: int| 0 <= i < fields.len() ==> {
        let field = #[trigger] fields[i];
        &&& field_site_matches(source, forms, field)
        &&& direct_form_in_range(forms, start, end, field.form as int)
        &&& field.form < cursor
    }
    &&& forall|i: int, j: int| 0 <= i < j < fields.len() ==>
        (#[trigger] fields[i]).form < (#[trigger] fields[j]).form
    &&& forall|root: int| #[trigger] direct_form_in_range(forms, start, end, root) && root < cursor
        ==> exists|i: int| 0 <= i < fields.len() && (#[trigger] fields[i]).form == root
}

proof fn add_field_site(
    source: &str, forms: Seq<Form>, start: int, end: int, next: int, fields: Seq<FieldSite>, field: FieldSite,
)
    requires
        field_sites_before(source, forms, start, end, field.form as int, fields),
        field_site_matches(source, forms, field),
        direct_form_in_range(forms, start, end, field.form as int),
        following_direct_form(forms, field.form as int, next),
        form_region_ends_at(forms, start, end),
    ensures field_sites_before(source, forms, start, end, next, fields.push(field)),
{
    reveal(following_direct_form);
    let result = fields.push(field);
    assert forall|root: int| #[trigger] direct_form_in_range(forms, start, end, root) && root < next implies
        exists|i: int| 0 <= i < result.len() && (#[trigger] result[i]).form == root by {
        if root < field.form {
            let i = choose|i: int| 0 <= i < fields.len() && (#[trigger] fields[i]).form == root;
            assert(result[i] == fields[i]);
        } else {
            assert(root == field.form);
            assert(result[fields.len() as int] == field);
        }
    };
}

fn read_field_site(_source: &str, forms: &[Form], root: usize, limit: usize) -> (result: (FieldSite, usize))
    requires
        field_matches(_source, forms@, root as int, limit as int),
        complete_list_indices(forms@), nested_list_indices(forms@),
    ensures
        result.0.form == root,
        field_site_matches(_source, forms@, result.0),
        root < result.1 <= limit,
        following_direct_form(forms@, root as int, result.1 as int),
{
    let Form::List { end: last, .. } = forms[root] else { unreachable!() };
    assert!(root < last && last <= limit);
    let type_form = root + 2;
    proof {
        let at = choose|at: int| #[trigger] type_matches(_source, forms@, type_form as int, last as int, at)
            && natural_clause_matches(_source, forms@, at, last as int, last as int, Clause::At);
        assert(type_form < last);
    }
    let (ty, at) = match forms[type_form] {
        Form::List { end, .. } => (FieldTypeSite::Bits { width: type_form + 2 }, end),
        _ => (FieldTypeSite::Named { form: type_form }, type_form + 1),
    };
    proof { node_end_is_following_direct_form(forms@, root as int, last as int); }
    (FieldSite { form: root, name: root + 1, ty, offset: at + 2 }, last)
}

/// 総幅の位置と、直接フィールドすべての宣言順の位置を表す。
pub closed spec fn structure_sites_match(
    source: &str, syntax: &CircuitForms, entry: int, result: Option<StructureSites>,
) -> bool {
    let entries = syntax.entries@;
    let forms = syntax.forms@;
    if 0 <= entry < entries.len() && entries[entry].head is Struct {
        let root = entries[entry].form as int;
        let end = forms[root]->List_end as int;
        let width = root + 3;
        let start = width + 3;
        &&& 0 <= root < end <= forms.len()
        &&& forms[root] is List
        &&& natural_clause_matches(source, forms, width, end, start, Clause::Width)
        &&& result matches Some(sites) && sites.width == width + 2
            && field_sites_before(source, forms, start, end, end, sites.fields@)
    } else {
        result.is_none()
    }
}

proof fn field_site_prefix_agrees(
    source: &str, forms: Seq<Form>, start: int, end: int, left: Seq<FieldSite>, right: Seq<FieldSite>, count: nat,
)
    requires
        field_sites_before(source, forms, start, end, end, left),
        field_sites_before(source, forms, start, end, end, right),
        count <= left.len(),
    ensures
        count <= right.len(),
        forall|i: int| 0 <= i < count ==> (#[trigger] left[i]) == (#[trigger] right[i]),
    decreases count,
{
    if count > 0 {
        let i = (count - 1) as int;
        field_site_prefix_agrees(source, forms, start, end, left, right, i as nat);
        let a = left[i];
        assert(direct_form_in_range(forms, start, end, a.form as int));
        let k = choose|k: int| 0 <= k < right.len() && (#[trigger] right[k]).form == a.form;
        if k < i {
            assert(left[k] == right[k]);
            assert(left[k].form < a.form);
        }
        assert(i <= k < right.len());
        let b = right[i];
        if i < k {
            assert(b.form < a.form);
            assert(direct_form_in_range(forms, start, end, b.form as int));
            let j = choose|j: int| 0 <= j < left.len() && (#[trigger] left[j]).form == b.form;
            if j < i {
                assert(left[j] == right[j]);
                assert(right[j].form < b.form);
            } else if i < j {
                assert(a.form < left[j].form);
            }
        }
        assert(k == i);
        assert(field_site_matches(source, forms, a));
        assert(field_site_matches(source, forms, b));
        assert(a == b);
        assert forall|j: int| 0 <= j < count implies (#[trigger] left[j]) == (#[trigger] right[j]) by {
            if j < i { assert(left[j] == right[j]); }
        };
    }
}

/// 同じ構造体宣言から得た総幅とフィールドの構文位置は、宣言順に一致する。
pub proof fn structure_sites_agree(
    source: &str, syntax: &CircuitForms, entry: int, left: StructureSites, right: StructureSites,
)
    requires
        structure_sites_match(source, syntax, entry, Some(left)),
        structure_sites_match(source, syntax, entry, Some(right)),
    ensures left.width == right.width && left.fields@ == right.fields@,
{
    let root = syntax.entries@[entry].form as int;
    let forms = syntax.forms@;
    let start = root + 6;
    let end = forms[root]->List_end as int;
    field_site_prefix_agrees(source, forms, start, end, left.fields@, right.fields@, left.fields@.len());
    field_site_prefix_agrees(source, forms, start, end, right.fields@, left.fields@, right.fields@.len());
    assert(left.fields@ =~= right.fields@);
}

/// 総幅の添字が元の構文木の自然数の字句を指すことを示す。
pub proof fn structure_width_site_evidence(
    source: &str, syntax: &CircuitForms, entry: int, sites: StructureSites,
)
    requires structure_sites_match(source, syntax, entry, Some(sites)),
    ensures
        0 <= entry < syntax.entries@.len(),
        syntax.entries@[entry].head is Struct,
        sites.width < syntax.forms@.len(),
        syntax.forms@[sites.width as int] is Atom,
        syntax.forms@[sites.width as int]->Atom_kind is Natural,
{
    reveal(structure_sites_match);
}

/// フィールドの各添字が宣言内の名前、型、オフセットの字句に対応することを示す。
pub proof fn structure_field_site_evidence(
    source: &str, syntax: &CircuitForms, entry: int, sites: StructureSites, index: int,
)
    requires structure_sites_match(source, syntax, entry, Some(sites)), 0 <= index < sites.fields@.len(),
    ensures ({
        let site = sites.fields@[index];
        let forms = syntax.forms@;
        &&& field_site_matches(source, forms, site)
        &&& site.name < forms.len()
        &&& forms[site.name as int] is Atom && forms[site.name as int]->Atom_kind is Name
        &&& site.offset < forms.len()
        &&& forms[site.offset as int] is Atom && forms[site.offset as int]->Atom_kind is Natural
        &&& match site.ty {
            FieldTypeSite::Bits { width } => width < forms.len()
                && forms[width as int] is Atom && forms[width as int]->Atom_kind is Natural,
            FieldTypeSite::Named { form } => form < forms.len()
                && forms[form as int] is Atom && reference_atom(forms[form as int]->Atom_kind),
        }
    }),
{
    reveal(structure_sites_match);
    reveal(crate::circuit::directive_word_at);
    reveal(crate::circuit::directive_word_matches);
}

/// 直接フィールドが宣言順に並び、対応する添字を一度ずつ含むことを示す。
pub proof fn structure_field_sites_order(
    source: &str, syntax: &CircuitForms, entry: int, sites: StructureSites,
)
    requires structure_sites_match(source, syntax, entry, Some(sites)),
    ensures ({
        let root = syntax.entries@[entry].form as int;
        let forms = syntax.forms@;
        let fields = sites.fields@;
        let end = forms[root]->List_end as int;
        &&& forall|i: int| 0 <= i < fields.len() ==>
            direct_form_in_range(forms, root + 6, end, (#[trigger] fields[i]).form as int)
        &&& forall|i: int, j: int| 0 <= i < j < fields.len() ==>
            (#[trigger] fields[i]).form < (#[trigger] fields[j]).form
        &&& forall|field: int| #[trigger] direct_form_in_range(forms, root + 6, end, field)
            ==> exists|i: int| 0 <= i < fields.len() && (#[trigger] fields[i]).form == field
    }),
{
    reveal(structure_sites_match);
    reveal(direct_form_in_range);
}

/// 厳格索引の構造体から総幅と各フィールドの位置を取り出す。
///
/// 同じソースの厳格索引を渡す。項目が範囲外か構造体以外なら `None` を返す。
///
/// # Examples
///
/// フィールドは `at` の値にかかわらず、ソース上の宣言順に並ぶ。
///
/// ```
/// use circuitgame2_syntax::{
///     Form, circuit::{FieldTypeSite, index_headers, structure_sites},
/// };
/// let source = "(struct Empty (width 8))
///     (struct Pair (width 16) (high (bits 4) (at 12)) (inner Empty (at 0)))";
/// let syntax = index_headers(source).unwrap();
/// let atom = |index: usize| {
///     let Form::Atom { span, .. } = &syntax.forms[index] else { panic!("expected an atom") };
///     &source[span.clone()]
/// };
/// let empty = structure_sites(source, &syntax, 0).unwrap();
/// assert!(empty.fields.is_empty());
/// let pair = structure_sites(source, &syntax, 1).unwrap();
/// assert_eq!(atom(pair.width), "16");
/// let high = pair.fields[0];
/// let inner = pair.fields[1];
/// assert_eq!((atom(high.name), atom(high.offset)), ("high", "12"));
/// assert_eq!((atom(inner.name), atom(inner.offset)), ("inner", "0"));
/// let FieldTypeSite::Bits { width } = high.ty else { panic!("expected a bit width") };
/// let FieldTypeSite::Named { form } = inner.ty else { panic!("expected a type name") };
/// assert_eq!((atom(width), atom(form)), ("4", "Empty"));
/// ```
///
/// # Panics
///
/// 手で組み立てた構文木と索引の添字やリストの終端が不整合な場合は、パニックすることがある。
pub fn structure_sites(_source: &str, syntax: &CircuitForms, entry: usize) -> (result: Option<StructureSites>)
    requires
        circuit_index_matches(_source, syntax.forms@, syntax.entries@),
        complete_list_indices(syntax.forms@), nested_list_indices(syntax.forms@),
    ensures
        structure_sites_match(_source, syntax, entry as int, result),
        result.is_some() <==> (entry < syntax.entries@.len() && syntax.entries@[entry as int].head is Struct),
{
    if entry >= syntax.entries.len() { return None; }
    let item = &syntax.entries[entry];
    if !matches!(item.head, Head::Struct) { return None; }
    let forms = syntax.forms.as_slice();
    proof {
        indexed_entry_evidence(_source, forms@, syntax.entries@, entry as int);
        reveal(crate::circuit::form_has_head);
        reveal(header_arguments_match);
    }
    let Form::List { end: last, .. } = forms[item.form] else { unreachable!() };
    let width = item.form + 5;
    let start = item.form + 6;

    let mut fields = Vec::new();
    let mut cursor = start;
    proof {
        reveal(direct_form_in_range);
        assert(start < last ==> direct_form_in_range(forms@, start as int, last as int, cursor as int));
        assert(form_region_ends_at(forms@, start as int, last as int));
    }
    while cursor < last
        invariant
            start <= cursor <= last <= forms@.len(),
            complete_list_indices(forms@), nested_list_indices(forms@),
            form_region_ends_at(forms@, start as int, last as int),
            fields_match_before(_source, forms@, start as int, last as int, last as int),
            cursor < last ==> direct_form_in_range(forms@, start as int, last as int, cursor as int),
            field_sites_before(_source, forms@, start as int, last as int, cursor as int, fields@),
        decreases last - cursor,
    {
        assert(field_matches(_source, forms@, cursor as int, last as int)) by { reveal(fields_match_before); };
        let (field, next) = read_field_site(_source, forms, cursor, last);
        proof {
            add_field_site(_source, forms@, start as int, last as int, next as int, fields@, field);
            reveal(following_direct_form);
        }
        fields.push(field);
        cursor = next;
    }
    Some(StructureSites { width, fields })
}

} // verus!
