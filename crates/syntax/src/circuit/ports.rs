use super::clauses::{read_named_clause, read_type};
use super::{
    AtomKind, CircuitForms, Clause, Form, Head, HeaderError, check_directive_word, form_span_exec,
};
use alloc::vec::Vec;
use core::ops::Range;
use vstd::prelude::*;

#[cfg(verus_only)]
use super::clauses::{enclosing_region_bounds_form, natural_clause_matches, reference_atom};
#[cfg(verus_only)]
use super::index::indexed_entry_evidence;
#[cfg(verus_only)]
use super::{circuit_index_matches, header_arguments_match, header_matches};
#[cfg(verus_only)]
use super::{
    direct_form_in_range, directive_argument_error_span, directive_word_at, following_direct_form,
    form_region_ends_at, named_clause_error_span, named_clause_matches,
    node_end_is_following_direct_form, type_error_evidence, type_matches,
};
#[cfg(verus_only)]
use crate::{
    complete_list_indices, form_span, form_spans_valid, list_delimited, list_source_delimiters,
    nested_list_indices,
};
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// ポート宣言が指定した型の構文上の位置。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PortTypeSite {
    /// 型を省略した裸のポート名。1 ビットとして扱う。
    ImplicitBit,
    /// ビット幅を指定する型。
    Bits {
        /// 元の構文木で自然数の字句を指す添字。
        width: usize,
    },
    /// 名前で参照する型。
    Named {
        /// 元の構文木で型名の字句を指す添字。
        form: usize,
    },
}

/// 検査済みの署名にある一つのポートの構文位置。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PortSite {
    /// このポートの先頭を指す構文木の添字。
    pub form: usize,
    /// ポート名の字句を指す構文木の添字。
    pub name: usize,
    /// ポート型の指定。
    pub ty: PortTypeSite,
}

/// `func` または `module` の入力ポートと出力ポート。
#[derive(Debug, Eq, PartialEq)]
pub struct RoutinePorts {
    /// 宣言の `in` 節に並ぶポート。
    pub inputs: Vec<PortSite>,
    /// 宣言の `out` 節に並ぶポート。
    pub outputs: Vec<PortSite>,
}

spec fn port_site_matches(source: &str, forms: Seq<Form>, site: PortSite) -> bool {
    &&& site.form < forms.len()
    &&& site.name < forms.len()
    &&& forms[site.name as int] is Atom && forms[site.name as int]->Atom_kind is Name
    &&& match site.ty {
        PortTypeSite::ImplicitBit => site.name == site.form,
        PortTypeSite::Bits { width } => forms[site.form as int] is List && site.name == site.form + 1
            && width == site.form + 4 && width < forms.len()
            && forms[width as int] is Atom && forms[width as int]->Atom_kind is Natural
            && natural_clause_matches(source, forms, site.form + 2,
                forms[site.form as int]->List_end as int, forms[site.form as int]->List_end as int, Clause::Bits),
        PortTypeSite::Named { form } => forms[site.form as int] is List && site.name == site.form + 1
            && form == site.form + 2 && form < forms.len()
            && forms[form as int] is Atom && reference_atom(forms[form as int]->Atom_kind),
    }
}

/// 索引で取得したポート名と型指定が、元の構文木の字句を指すことを示す。
pub proof fn port_site_evidence(
    source: &str, syntax: &CircuitForms, entry: int, ports: RoutinePorts, input: bool, at: int,
)
    requires
        routine_ports_match(source, syntax, entry, Some(ports)),
        0 <= at < (if input { ports.inputs@.len() } else { ports.outputs@.len() }),
    ensures ({
        let site = if input { ports.inputs@[at] } else { ports.outputs@[at] };
        &&& site.name < syntax.forms@.len()
        &&& syntax.forms@[site.name as int] is Atom && syntax.forms@[site.name as int]->Atom_kind is Name
        &&& site.ty matches PortTypeSite::Bits { width } ==>
            width < syntax.forms@.len() && syntax.forms@[width as int] is Atom
                && syntax.forms@[width as int]->Atom_kind is Natural
        &&& site.ty matches PortTypeSite::Named { form } ==>
            form < syntax.forms@.len() && syntax.forms@[form as int] is Atom
                && reference_atom(syntax.forms@[form as int]->Atom_kind)
    }),
{
    reveal(routine_ports_match);
}

/// 無修飾名、または名前と型を並べたリストをポートとして認識する関係。
pub open spec fn port_matches(source: &str, forms: Seq<Form>, index: int, limit: int) -> bool {
    &&& 0 <= index < limit <= forms.len()
    &&& (if forms[index] is List {
        let end = forms[index]->List_end as int;
        &&& end <= limit
        &&& directive_word_at(source, forms, index + 1, end, HeaderError::ExpectedName)
        &&& type_matches(source, forms, index + 2, end, end)
    } else {
        directive_word_at(source, forms, index, limit, HeaderError::ExpectedName)
    })
}

/// ポートの形、名前、型、余分な要素の順で最初の違反を表す。
pub open spec fn port_error_evidence(
    source: &str, forms: Seq<Form>, index: int, limit: int,
    kind: HeaderError, span: Range<usize>,
) -> bool {
    &&& 0 <= index < limit <= forms.len()
    &&& {
        let form = forms[index];
        if form is List {
            let end = form->List_end as int;
            let close = (form_span(form).end - 1) as usize;
            let name = HeaderError::ExpectedName;
            &&& index < end <= limit
            &&& 0 < form_span(form).end <= source.spec_bytes().len()
            &&& source.spec_bytes()[close as int] == 41
            &&& (if directive_word_at(source, forms, index + 1, end, name) {
                type_error_evidence(source, forms, index + 2, end, close, kind, span)
                    || (kind == HeaderError::UnexpectedArgument && exists|after: int|
                        #[trigger] type_matches(source, forms, index + 2, end, after)
                        && after < end && span == form_span(forms[after]))
            } else {
                kind == name && directive_argument_error_span(forms, index + 1, end, close, span)
            })
        } else {
            kind == HeaderError::ExpectedPort
                && !directive_word_at(source, forms, index, limit, HeaderError::ExpectedName)
                && span == form_span(form)
        }
    }
}

fn read_port(source: &str, forms: &[Form], index: usize, _limit: usize)
    -> (result: Result<usize, (HeaderError, Range<usize>)>)
    requires
        index < _limit <= forms@.len(),
        form_region_ends_at(forms@, index as int, _limit as int),
        complete_list_indices(forms@),
        nested_list_indices(forms@),
        list_source_delimiters(source, forms@, false),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures
        result.is_ok() == port_matches(source, forms@, index as int, _limit as int),
        match result {
            Ok(after) => index < after <= _limit && following_direct_form(forms@, index as int, after as int),
            Err((kind, span)) => port_error_evidence(source, forms@, index as int, _limit as int, kind, span),
        },
{
    let form = &forms[index];
    let next = match form {
        Form::Atom { kind: AtomKind::Name, .. } => index + 1,
        Form::List { span: list_span, end: list_end } => {
            let end = *list_end;
            proof { enclosing_region_bounds_form(forms@, index as int, index as int, _limit as int); }
            assert(list_delimited(source.spec_bytes(), *form, false)) by {
                reveal(list_source_delimiters);
            };
            let close = list_span.end - 1;
            check_directive_word(source, forms, index + 1, end, close, HeaderError::ExpectedName)?;
            let value = index + 2;
            proof {
                assert(form_region_ends_at(forms@, value as int, end as int)) by {
                    assert(exists|parent: int| 0 <= parent < value
                        && #[trigger] forms@[parent] is List && forms@[parent]->List_end == end);
                };
                enclosing_region_bounds_form(forms@, value as int, value as int, end as int);
            }
            let after_type = read_type(source, forms, value, end, close)?;
            assert(type_matches(source, forms@, value as int, end as int, after_type as int));
            if after_type < end {
                return Err((HeaderError::UnexpectedArgument, form_span_exec(&forms[after_type])));
            }
            end
        }
        _ => return Err((HeaderError::ExpectedPort, form_span_exec(form))),
    };
    proof { node_end_is_following_direct_form(forms@, index as int, next as int); }
    Ok(next)
}

/// 走査済みの直接子がすべてポートであることを表す。
#[verifier::opaque]
pub open spec fn ports_match_before(
    source: &str, forms: Seq<Form>, start: int, limit: int, cursor: int,
) -> bool {
    forall|i: int| #[trigger] direct_form_in_range(forms, start, limit, i) && i < cursor
        ==> port_matches(source, forms, i, limit)
}

/// 入力節は空を許し、出力節はポートを1つ以上要求する。
pub open spec fn ports_clause_matches(
    source: &str, forms: Seq<Form>, index: int, limit: int, after: int, clause: Clause,
) -> bool {
    &&& (clause is In || clause is Out)
    &&& named_clause_matches(source, forms, index, limit, after, clause)
    &&& (clause is Out ==> index + 2 < after)
    &&& ports_match_before(source, forms, index + 2, after, after)
}

/// 節名の誤り、出力ポートの欠落、または最初の不正なポートの診断根拠を表す。
pub open spec fn ports_error_evidence(
    source: &str, forms: Seq<Form>, index: int, limit: int, closing: usize, clause: Clause,
    kind: HeaderError, span: Range<usize>,
) -> bool {
    (kind == HeaderError::ExpectedClause(clause)
        && named_clause_error_span(source, forms, index, limit, closing, clause, span))
    || (exists|end: int| #[trigger] named_clause_matches(source, forms, index, limit, end, clause)
        && ((clause is Out && index + 2 == end && kind == HeaderError::ExpectedPort
            && span.start + 1 == form_span(forms[index]).end && span.end == span.start
            && span.start < source.spec_bytes().len() && source.spec_bytes()[span.start as int] == 41)
        || (exists|i: int| #[trigger] direct_form_in_range(forms, index + 2, end, i)
            && ports_match_before(source, forms, index + 2, end, i)
            && port_error_evidence(source, forms, i, end, kind, span))))
}

proof fn record_port(
    source: &str, forms: Seq<Form>, start: int, index: int, next: int, limit: int,
)
    requires
        index < next <= limit,
        direct_form_in_range(forms, start, limit, index),
        following_direct_form(forms, index, next),
        form_region_ends_at(forms, start, limit),
        ports_match_before(source, forms, start, limit, index),
        port_matches(source, forms, index, limit),
    ensures
        next < limit ==> direct_form_in_range(forms, start, limit, next),
        ports_match_before(source, forms, start, limit, next),
{
    reveal(following_direct_form);
    reveal(ports_match_before);
    assert forall|i: int| #[trigger] direct_form_in_range(forms, start, limit, i) && i < next
        implies port_matches(source, forms, i, limit) by {
        if i > index {
            assert(!direct_form_in_range(forms, start, limit, i));
        }
    };
}

fn read_ports_clause(
    source: &str, forms: &[Form], index: usize, limit: usize, closing: usize, clause: Clause,
) -> (result: Result<usize, (HeaderError, Range<usize>)>)
    requires
        index <= limit <= forms@.len(),
        form_region_ends_at(forms@, index as int, limit as int),
        nested_list_indices(forms@),
        complete_list_indices(forms@),
        list_source_delimiters(source, forms@, false),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
        closing < source.spec_bytes().len() && source.spec_bytes()[closing as int] == 41,
        clause is In || clause is Out,
    ensures
        forall|after: int| #[trigger] ports_clause_matches(
            source, forms@, index as int, limit as int, after, clause)
            <==> (result matches Ok(next) && after == next),
        result matches Ok(after) ==> index + 2 <= after <= limit,
        result matches Err((kind, span)) ==> ports_error_evidence(
            source, forms@, index as int, limit as int, closing, clause, kind, span),
{
    proof { enclosing_region_bounds_form(forms@, index as int, index as int, limit as int); }
    let (end, close) = read_named_clause(source, forms, index, limit, closing, clause)?;
    assert(named_clause_matches(source, forms@, index as int, limit as int, end as int, clause));
    let start = index + 2;
    if matches!(clause, Clause::Out) && start == end {
        return Err((HeaderError::ExpectedPort, close..close));
    }
    let mut cursor = start;
    proof {
        reveal(direct_form_in_range);
        reveal(ports_match_before);
        assert(form_region_ends_at(forms@, start as int, end as int)) by {
            assert(exists|parent: int| 0 <= parent < start
                && #[trigger] forms@[parent] is List && forms@[parent]->List_end == end);
        };
        assert(cursor < end ==> direct_form_in_range(forms@, start as int, end as int, cursor as int));
        assert(ports_match_before(source, forms@, start as int, end as int, cursor as int));
    }
    while cursor < end
        invariant
            start == index + 2,
            start <= cursor <= end <= limit <= forms@.len(),
            clause is In || clause is Out,
            clause is Out ==> start < end,
            named_clause_matches(source, forms@, index as int, limit as int, end as int, clause),
            form_region_ends_at(forms@, start as int, end as int),
            nested_list_indices(forms@),
            complete_list_indices(forms@),
            list_source_delimiters(source, forms@, false),
            form_spans_valid(source, forms@, source.spec_bytes().len() as int),
            cursor < end ==> direct_form_in_range(forms@, start as int, end as int, cursor as int),
            ports_match_before(source, forms@, start as int, end as int, cursor as int),
        decreases end - cursor,
    {
        assert(form_region_ends_at(forms@, cursor as int, end as int));
        let next = match read_port(source, forms, cursor, end) {
            Ok(next) => next,
            Err(error) => {
                assert(!ports_match_before(source, forms@, start as int, end as int, end as int)) by {
                    reveal(ports_match_before);
                };
                return Err(error);
            },
        };
        proof { record_port(source, forms@, start as int, cursor as int, next as int, end as int); }
        cursor = next;
    }
    Ok(end)
}

/// 宣言名と入出力節を受理したとき、本体の開始添字を定める。
///
/// `module-part` では宣言名の直後から本体が始まる。
pub open spec fn routine_signature_matches(
    source: &str, forms: Seq<Form>, first: int, limit: int, head: Head, after: int,
) -> bool {
    &&& directive_word_at(source, forms, first, limit, HeaderError::ExpectedName)
    &&& match head {
        Head::ModulePart => after == first + 1,
        Head::Func | Head::Module => exists|out: int|
            #[trigger] ports_clause_matches(source, forms, first + 1, limit, out, Clause::In)
                && ports_clause_matches(source, forms, out, limit, after, Clause::Out),
        _ => false,
    }
}

/// 宣言名、入力節、出力節の順で最初に見つかった違反を表す。
pub open spec fn routine_signature_error_evidence(
    source: &str, forms: Seq<Form>, first: int, limit: int, closing: usize, head: Head,
    kind: HeaderError, span: Range<usize>,
) -> bool {
    let name = HeaderError::ExpectedName;
    if !directive_word_at(source, forms, first, limit, name) {
        kind == name && directive_argument_error_span(forms, first, limit, closing, span)
    } else {
        (head is Func || head is Module)
        && (ports_error_evidence(source, forms, first + 1, limit, closing, Clause::In, kind, span)
            || (exists|out: int| #[trigger] ports_clause_matches(source, forms, first + 1, limit, out, Clause::In)
                && ports_error_evidence(source, forms, out, limit, closing, Clause::Out, kind, span)))
    }
}

pub(super) fn read_routine_signature(
    source: &str, forms: &[Form], first: usize, limit: usize, closing: usize, head: Head,
) -> (result: Result<usize, (HeaderError, Range<usize>)>)
    requires
        first <= limit <= forms@.len(),
        form_region_ends_at(forms@, first as int, limit as int),
        nested_list_indices(forms@),
        complete_list_indices(forms@),
        list_source_delimiters(source, forms@, false),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
        closing < source.spec_bytes().len() && source.spec_bytes()[closing as int] == 41,
        head is Func || head is Module || head is ModulePart,
    ensures
        forall|after: int| #[trigger] routine_signature_matches(
            source, forms@, first as int, limit as int, head, after)
            <==> (result matches Ok(next) && after == next),
        result matches Ok(after) ==> first < after <= limit,
        result matches Err((kind, span)) ==> routine_signature_error_evidence(
            source, forms@, first as int, limit as int, closing, head, kind, span),
{
    check_directive_word(source, forms, first, limit, closing, HeaderError::ExpectedName)?;
    let next = first + 1;
    if matches!(head, Head::ModulePart) {
        return Ok(next);
    }
    let out = read_ports_clause(source, forms, next, limit, closing, Clause::In)?;
    assert(ports_clause_matches(source, forms@, next as int, limit as int, out as int, Clause::In));
    read_ports_clause(source, forms, out, limit, closing, Clause::Out)
}

spec fn port_sites_before(source: &str, forms: Seq<Form>, first: int, stop: int, at: int, sites: Seq<PortSite>) -> bool {
    &&& forall|i: int| 0 <= i < sites.len() ==> {
        let site = #[trigger] sites[i];
        &&& port_site_matches(source, forms, site)
        &&& site.form < at
        &&& direct_form_in_range(forms, first, stop, site.form as int)
    }
    &&& forall|i: int, j: int| 0 <= i < j < sites.len() ==> (#[trigger] sites[i]).form < (#[trigger] sites[j]).form
    &&& forall|index: int| #[trigger] direct_form_in_range(forms, first, stop, index) && index < at
        ==> exists|i: int| 0 <= i < sites.len() && (#[trigger] sites[i]).form == index
}

proof fn add_port_site(source: &str, forms: Seq<Form>, first: int, stop: int, sites: Seq<PortSite>, site: PortSite, next: int)
    requires
        port_sites_before(source, forms, first, stop, site.form as int, sites),
        port_site_matches(source, forms, site),
        direct_form_in_range(forms, first, stop, site.form as int),
        following_direct_form(forms, site.form as int, next),
        form_region_ends_at(forms, first, stop),
    ensures port_sites_before(source, forms, first, stop, next, sites.push(site)),
{
    reveal(following_direct_form);
    let all = sites.push(site);
    assert forall|index: int| #[trigger] direct_form_in_range(forms, first, stop, index) && index < next implies
        exists|i: int| 0 <= i < all.len() && (#[trigger] all[i]).form == index by {
        if index < site.form {
            let i = choose|i: int| 0 <= i < sites.len() && (#[trigger] sites[i]).form == index;
            assert(all[i] == sites[i]);
        } else {
            assert(index == site.form);
            assert(all[sites.len() as int] == site);
        }
    };
}

fn collect_port_sites(_source: &str, forms: &[Form], clause: usize, stop: usize, _limit: usize, _direction: Clause)
    -> (sites: Vec<PortSite>)
    requires
        ports_clause_matches(_source, forms@, clause as int, _limit as int, stop as int, _direction),
        complete_list_indices(forms@), nested_list_indices(forms@),
    ensures
        port_sites_before(_source, forms@, clause + 2, stop as int, stop as int, sites@),
        sites@.len() == super::call_shapes::argument_count(forms@, clause + 2, stop as int),
{
    let first = clause + 2;
    let mut at = first;
    let mut sites: Vec<PortSite> = Vec::new();
    proof {
        reveal(direct_form_in_range);
        assert(at < stop ==> direct_form_in_range(forms@, first as int, stop as int, at as int));
    }
    while at < stop
        invariant
            ports_clause_matches(_source, forms@, clause as int, _limit as int, stop as int, _direction),
            complete_list_indices(forms@), nested_list_indices(forms@),
            first == clause + 2 <= at <= stop,
            at < stop ==> direct_form_in_range(forms@, first as int, stop as int, at as int),
            port_sites_before(_source, forms@, first as int, stop as int, at as int, sites@),
            sites@.len() + super::call_shapes::argument_count(forms@, at as int, stop as int)
                == super::call_shapes::argument_count(forms@, first as int, stop as int),
        decreases stop - at,
    {
        proof {
            reveal(ports_match_before);
            assert(port_matches(_source, forms@, at as int, stop as int));
        }
        let (name, ty, next) = match &forms[at] {
            Form::List { end, .. } => {
                let type_form = at + 2;
                if matches!(forms[type_form], Form::List { .. }) {
                    assert(natural_clause_matches(_source, forms@, type_form as int, *end as int, *end as int, Clause::Bits));
                    (at + 1, PortTypeSite::Bits { width: at + 4 }, *end)
                } else {
                    (at + 1, PortTypeSite::Named { form: type_form }, *end)
                }
            },
            _ => (at, PortTypeSite::ImplicitBit, at + 1),
        };
        let site = PortSite { form: at, name, ty };
        proof {
            reveal(super::directive_word_at);
            reveal(super::directive_word_matches);
            node_end_is_following_direct_form(forms@, at as int, next as int);
            assert(form_region_ends_at(forms@, first as int, stop as int));
            add_port_site(_source, forms@, first as int, stop as int, sites@, site, next as int);
            reveal(following_direct_form);
            reveal_with_fuel(super::call_shapes::argument_count, 1);
        }
        sites.push(site);
        at = next;
    }
    proof { reveal_with_fuel(super::call_shapes::argument_count, 1); }
    sites
}

/// 入出力の一覧が、厳格索引の署名に現れるポートを順番どおりに含むことを表す。
pub closed spec fn routine_ports_match(
    source: &str, syntax: &CircuitForms, entry: int, ports: Option<RoutinePorts>,
) -> bool {
    if 0 <= entry < syntax.entries@.len()
        && (syntax.entries@[entry].head is Func || syntax.entries@[entry].head is Module) {
        let forms = syntax.forms@;
        let form = syntax.entries@[entry].form as int;
        let first = form + 3;
        let out = forms[first]->List_end as int;
        let end = forms[out]->List_end as int;
        ports matches Some(ports) && port_sites_before(source, forms, first + 2, out, out, ports.inputs@)
            && port_sites_before(source, forms, out + 2, end, end, ports.outputs@)
            && ports.inputs@.len() == super::call_shapes::argument_count(forms, first + 2, out)
            && ports.outputs@.len() == super::call_shapes::argument_count(forms, out + 2, end)
    } else {
        ports.is_none()
    }
}

pub(super) proof fn routine_port_list_counts(
    source: &str, syntax: &CircuitForms, entry: int, ports: RoutinePorts, layout: RoutineLayout,
)
    requires
        routine_ports_match(source, syntax, entry, Some(ports)),
        routine_layout_matches(source, syntax, entry, Some(layout)),
    ensures
        ports.inputs@.len() == super::call_shapes::argument_count(syntax.forms@, layout.input + 2, layout.output as int),
        ports.outputs@.len() == super::call_shapes::argument_count(syntax.forms@, layout.output + 2, layout.body as int),
{
}

/// 署名の有無が、厳格索引の項目の種別に対応することを示す。
pub proof fn routine_ports_availability(source: &str, syntax: &CircuitForms, entry: int, ports: Option<RoutinePorts>)
    requires routine_ports_match(source, syntax, entry, ports),
    ensures ports.is_some() <==> (0 <= entry < syntax.entries@.len()
        && (syntax.entries@[entry].head is Func || syntax.entries@[entry].head is Module)),
{
}

/// 厳格索引の一項目から `func` または `module` の署名を取り出す。
///
/// `syntax` には同じ `source` を厳格に解析して得た索引を渡す。
/// 一覧は宣言順に並ぶ。項目が対象外の種別または範囲外なら `None` を返す。
///
/// # Panics
///
/// 構文木と索引を手動で組み立て、互いに対応しない添字を渡すとパニックすることがある。
pub fn routine_ports(source: &str, syntax: &CircuitForms, entry: usize) -> (ports: Option<RoutinePorts>)
    requires circuit_index_matches(source, syntax.forms@, syntax.entries@),
        complete_list_indices(syntax.forms@), nested_list_indices(syntax.forms@),
    ensures routine_ports_match(source, syntax, entry as int, ports),
        ports.is_some() ==> entry < syntax.entries@.len(),
{
    let layout = routine_layout(source, syntax, entry)?;
    let forms = syntax.forms.as_slice();
    let inputs = collect_port_sites(source, forms, layout.input, layout.output, layout.end, Clause::In);
    let outputs = collect_port_sites(source, forms, layout.output, layout.body, layout.end, Clause::Out);
    Some(RoutinePorts { inputs, outputs })
}

pub(super) struct RoutineLayout {
    pub(super) input: usize,
    pub(super) output: usize,
    pub(super) body: usize,
    pub(super) end: usize,
}

pub(super) open spec fn routine_layout_matches(source: &str, syntax: &CircuitForms, entry: int, layout: Option<RoutineLayout>) -> bool {
    let entries = syntax.entries@;
    let forms = syntax.forms@;
    if 0 <= entry < entries.len() && (entries[entry].head is Func || entries[entry].head is Module) {
        let form = entries[entry].form as int;
        layout matches Some(layout) && 0 <= form < forms.len() && forms[form] is List
            && layout.end == forms[form]->List_end && layout.input == form + 3
            && ports_clause_matches(source, forms, layout.input as int, layout.end as int, layout.output as int, Clause::In)
            && ports_clause_matches(source, forms, layout.output as int, layout.end as int, layout.body as int, Clause::Out)
            && super::body::body_items_before(source, forms, layout.body as int, layout.end as int, layout.end as int)
    } else {
        layout.is_none()
    }
}

pub(super) fn routine_layout(_source: &str, syntax: &CircuitForms, entry: usize) -> (layout: Option<RoutineLayout>)
    requires circuit_index_matches(_source, syntax.forms@, syntax.entries@),
        complete_list_indices(syntax.forms@), nested_list_indices(syntax.forms@),
    ensures routine_layout_matches(_source, syntax, entry as int, layout),
{
    if entry >= syntax.entries.len() { return None; }
    let item = &syntax.entries[entry];
    if !matches!(item.head, Head::Func | Head::Module) { return None; }
    let forms = syntax.forms.as_slice();
    proof {
        indexed_entry_evidence(_source, forms@, syntax.entries@, entry as int);
        reveal(super::form_has_head);
        reveal(header_arguments_match);
    }
    let Form::List { end: last, .. } = &forms[item.form] else { proof { assert(false); } return None; };
    let first = item.form + 3;
    proof {
        let body = choose|body: int| #[trigger] routine_signature_matches(_source, forms@, item.form + 2, *last as int, item.head, body)
            && super::body::body_items_before(_source, forms@, body, *last as int, *last as int);
        let out = choose|out: int| #[trigger] ports_clause_matches(_source, forms@, first as int, *last as int, out, Clause::In)
            && ports_clause_matches(_source, forms@, out, *last as int, body, Clause::Out);
        assert(forms@[first as int] is List && forms@[out] is List);
    }
    let Form::List { end: out, .. } = &forms[first] else { proof { assert(false); } return None; };
    let Form::List { end: output_end, .. } = &forms[*out] else { proof { assert(false); } return None; };
    Some(RoutineLayout { input: first, output: *out, body: *output_end, end: *last })
}

} // verus!
