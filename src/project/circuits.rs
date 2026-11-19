//! 回路ソースの集合を構文木と名前索引に結び付ける。

#[cfg(verus_only)]
use super::sources::{
    collected_source_for_input, collected_source_ids_unique, collected_source_origin,
    collected_sources_follow_input_order, first_source_input, snapshot_matches, source_ids_unique,
};
use super::{
    LocatedName, ProjectSource, SourceKind, SourceSetError, SourceSnapshot, VirtualPath, collect_sources,
};
#[cfg(verus_only)]
use super::{
    location_in_source, normalized_path, project_sources_match, source_kind_of, source_set_error,
    valid_source_snapshots,
};
use crate::syntax::Form;
#[cfg(verus_only)]
use crate::syntax::circuit::NameSite;
use crate::syntax::circuit::{
    CircuitFormError, CircuitRecovery, NamedBuildCircuit, index_named_build_forms,
    recover_circuit_forms,
};
#[cfg(verus_only)]
use crate::syntax::circuit::{
    build_index_matches, circuit_index_matches, circuit_recovery_matches, circuit_source_error,
    circuit_source_matches, name_site_matches, named_form_matches, named_forms_match,
};
#[cfg(verus_only)]
use crate::syntax::{
    AtomKind, bare_atom_kind, complete_list_indices, form_span, form_spans_valid,
    nested_list_indices,
};
use alloc::vec::Vec;
use core::ops::Range;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(verus_only)]
use vstd::utf8::{
    encode_utf8_valid_utf8, is_char_boundary, is_char_boundary_iff_not_is_continuation_byte,
};

verus! {

/// 収集した各回路ソースと、その構文木と名前索引。
#[derive(Debug)]
pub struct CircuitProject<'a> {
    sources: Vec<ProjectSource<'a>>,
    circuits: Vec<NamedBuildCircuit<'a>>,
}

/// 回路プロジェクトの構文解析で失敗した理由。
#[derive(Debug)]
pub enum CircuitProjectError<'a> {
    /// 入力スナップショットの収集に失敗した。
    Sources(SourceSetError),
    /// 回路記述以外のソースが含まれている。
    UnsupportedLanguage {
        /// 正規化済みのファイル識別子。
        id: VirtualPath<'a>,
        /// 入力に付いていた文書バージョン。
        revision: u64,
        /// 拡張子で指定された言語。
        kind: SourceKind,
    },
    /// 回路ソースに字句または構文の誤りがある。
    Syntax {
        /// 正規化済みのファイル識別子。
        id: VirtualPath<'a>,
        /// 診断範囲が対応する文書バージョン。
        revision: u64,
        /// 元ソース上の範囲を持つ構文診断。
        error: CircuitFormError,
    },
}

/// 厳格なプロジェクト解析のエラーと、対象ファイルの回復結果。
#[derive(Debug)]
pub struct CircuitProjectFailure<'a> {
    /// 解析を打ち切った最初の違反。
    pub error: CircuitProjectError<'a>,
    /// 構文違反があったファイルの回復結果。ソース収集の失敗や未対応言語では `None`。
    pub recovery: Option<CircuitRecovery>,
}

/// 構文木と名前索引が、指定した回路ソースを解析した結果に対応することを表す。
pub closed spec fn parsed_circuit_matches(source: ProjectSource, parsed: NamedBuildCircuit) -> bool {
    &&& source.kind is Circuit
    &&& circuit_source_matches(source.text)
    &&& circuit_index_matches(source.text, parsed.syntax.forms@, parsed.syntax.entries@)
    &&& complete_list_indices(parsed.syntax.forms@) && nested_list_indices(parsed.syntax.forms@)
    &&& form_spans_valid(source.text, parsed.syntax.forms@, source.text.spec_bytes().len() as int)
    &&& named_forms_match(source.text, parsed.syntax.forms@, parsed.syntax.entries@,
        parsed.names@, parsed.syntax.entries@.len() as int)
    &&& build_index_matches(source.text, parsed.build_model())
    &&& parsed.entry_ranges@.len() == parsed.syntax.entries@.len()
}

spec fn circuit_inputs_before(inputs: Seq<SourceSnapshot>, stop: int) -> bool {
    forall|i: int| i < stop && #[trigger] first_source_input(inputs, i) ==> {
        let input = inputs[i];
        &&& (normalized_path(input.path) matches Ok(id)
            && source_kind_of(id) == Some(SourceKind::Circuit))
        &&& circuit_source_matches(input.text)
    }
}

/// 入力から回路ソースだけを収集でき、各本文が回路の文法に従うことを表す。
///
/// 同じ識別子の入力は本文も一致するため、解析の対象は最初に現れた入力で代表させる。
pub closed spec fn circuit_project_accepts(inputs: Seq<SourceSnapshot>) -> bool {
    valid_source_snapshots(inputs) && circuit_inputs_before(inputs, inputs.len() as int)
}

/// 診断の根拠を、入力スナップショットのファイル識別子とバージョンに結び付ける。
pub closed spec fn circuit_project_error(inputs: Seq<SourceSnapshot>, error: CircuitProjectError) -> bool {
    match error {
        CircuitProjectError::Sources(error) => !valid_source_snapshots(inputs) && source_set_error(inputs, error),
        CircuitProjectError::UnsupportedLanguage { id, revision, kind } =>
            valid_source_snapshots(inputs) && !(kind is Circuit) && source_kind_of(id.components_model()) == Some(kind)
                && (exists|i: int| first_source_input(inputs, i)
                    && normalized_path((#[trigger] inputs[i]).path) == Ok(id.components_model())
                    && circuit_inputs_before(inputs, i)
                    && inputs[i].revision == revision),
        CircuitProjectError::Syntax { id, revision, error } =>
            valid_source_snapshots(inputs) && source_kind_of(id.components_model()) == Some(SourceKind::Circuit)
                && (exists|i: int| first_source_input(inputs, i)
                    && normalized_path((#[trigger] inputs[i]).path) == Ok(id.components_model())
                    && circuit_inputs_before(inputs, i)
                    && inputs[i].revision == revision
                    && !circuit_source_matches(inputs[i].text)
                    && circuit_source_error(inputs[i].text, error)),
    }
}

/// 厳格解析の診断と回復結果が、一つのファイル識別子と文書バージョンに対応することを表す。
pub closed spec fn circuit_project_failure(
    inputs: Seq<SourceSnapshot>, failure: CircuitProjectFailure,
) -> bool {
    &&& circuit_project_error(inputs, failure.error)
    &&& match (failure.error, failure.recovery) {
        (CircuitProjectError::Syntax { id, revision, error }, Some(recovery)) =>
            (exists|i: int| first_source_input(inputs, i)
                && normalized_path((#[trigger] inputs[i]).path) == Ok(id.components_model())
                && circuit_inputs_before(inputs, i)
                && inputs[i].revision == revision
                && !circuit_source_matches(inputs[i].text)
                && circuit_source_error(inputs[i].text, error)
                && circuit_recovery_matches(inputs[i].text, recovery)) && !(recovery is Complete),
        (CircuitProjectError::Syntax { .. }, None) => false,
        (_, recovery) => recovery.is_none(),
    }
}

impl<'a> CircuitProject<'a> {
    /// ファイル識別子で整理したソースを初出順に返す。
    pub fn sources(&self) -> (sources: &[ProjectSource<'a>])
        ensures sources@ == self.sources_model(),
    {
        self.sources.as_slice()
    }

    /// `sources()` と同じ順に並ぶ構文木と名前索引を返す。
    pub fn circuits(&self) -> (circuits: &[NamedBuildCircuit<'a>])
        ensures circuits@ == self.circuits_model(),
    {
        self.circuits.as_slice()
    }

    /// ファイル識別子ごとに整理したソースの列を表す。
    pub closed spec fn sources_model(&self) -> Seq<ProjectSource<'a>> {
        self.sources@
    }

    /// ソースの列に対応する構文木と名前索引の列を表す。
    pub closed spec fn circuits_model(&self) -> Seq<NamedBuildCircuit<'a>> {
        self.circuits@
    }

    /// 正規化済みファイル識別子が一意で、各ソースとその解析結果が同じ位置で対応することを表す。
    pub open spec fn has_parsed_sources(&self) -> bool {
        let sources = self.sources_model();
        let circuits = self.circuits_model();
        &&& circuits.len() == sources.len()
        &&& source_ids_unique(sources)
        &&& forall|i: int| 0 <= i < sources.len() ==>
            #[trigger] parsed_circuit_matches(sources[i], circuits[i])
    }

    /// 各ソースに対応する構文木と名前索引が得られたことを表す。
    pub open spec fn matches(&self, inputs: Seq<SourceSnapshot>) -> bool {
        project_sources_match(inputs, self.sources_model()) && self.has_parsed_sources()
    }
}

pub(super) open spec fn is_form_location(source: &ProjectSource, form: Form, loc: LocatedName) -> bool {
    *loc.source == *source && loc.span == form_span(form) && location_in_source(loc)
}

pub(super) fn form_location<'p, 'a>(source: &'p ProjectSource<'a>, forms: &[Form], index: usize)
    -> (loc: LocatedName<'p, 'a>)
    requires
        index < forms@.len(),
        form_spans_valid(source.text, forms@, source.text.spec_bytes().len() as int),
    ensures is_form_location(source, forms@[index as int], loc),
{
    let source_span = match &forms[index] {
        Form::Atom { span: atom, .. } => atom,
        Form::List { span: list, .. } => list,
    };
    let loc = LocatedName { source, span: source_span.start..source_span.end };
    proof {
        reveal(form_spans_valid);
        assert(loc.span == form_span(forms@[index as int]));
        super::declarations::located_name_evidence(loc);
    }
    loc
}

pub(super) open spec fn name_in_source(text: &str, name: NameSite) -> bool {
    &&& name.span.start < name.span.end <= text.spec_bytes().len()
    &&& name.span.end == name.span.start + name.word.spec_bytes().len()
    &&& is_char_boundary(text.spec_bytes(), name.span.start as int)
    &&& is_char_boundary(text.spec_bytes(), name.span.end as int)
    &&& text.spec_bytes()[name.span.start as int..name.span.end as int] == name.word.spec_bytes()
}

/// 構文木のアトムに対応する原文と UTF-8 のバイト範囲を返す。
pub(super) fn read_indexed_atom<'a>(text: &'a str, forms: &[Form], index: usize) -> (out: (&'a str, Range<usize>))
    requires
        index < forms@.len(), forms@[index as int] is Atom,
        form_spans_valid(text, forms@, text.spec_bytes().len() as int),
    ensures
        out.1 == form_span(forms@[index as int]),
        out.0.spec_bytes() == text.spec_bytes()[out.1.start as int..out.1.end as int],
        out.1.start < out.1.end <= text.spec_bytes().len(),
        is_char_boundary(text.spec_bytes(), out.1.start as int),
        is_char_boundary(text.spec_bytes(), out.1.end as int),
        !(forms@[index as int]->Atom_kind is String) ==>
            bare_atom_kind(out.0.spec_bytes()) == Some(forms@[index as int]->Atom_kind),
{
    let Form::Atom { span: word_span, kind: _kind } = &forms[index] else {
        proof { assert(false); }
        return ("", 0..0);
    };
    let start = word_span.start;
    let end = word_span.end;
    proof {
        reveal(form_spans_valid);
        encode_utf8_valid_utf8(text@);
        assert(form_span(forms@[index as int]) == (start..end));
        assert(!(*_kind is String) ==>
            bare_atom_kind(text.spec_bytes()[start as int..end as int]) == Some(*_kind));
    }
    let (prefix, _) = text.split_at(end);
    proof {
        encode_utf8_valid_utf8(prefix@);
        assert(prefix.spec_bytes()[start as int] == text.spec_bytes()[start as int]);
        is_char_boundary_iff_not_is_continuation_byte(text.spec_bytes(), start as int);
        is_char_boundary_iff_not_is_continuation_byte(prefix.spec_bytes(), start as int);
    }
    let (_, word) = prefix.split_at(start);
    assert(word.spec_bytes() =~= text.spec_bytes()[start as int..end as int]);
    (word, start..end)
}

pub(super) proof fn parsed_index_evidence(source: ProjectSource, parsed: NamedBuildCircuit)
    requires parsed_circuit_matches(source, parsed),
    ensures
        circuit_index_matches(source.text, parsed.syntax.forms@, parsed.syntax.entries@),
        complete_list_indices(parsed.syntax.forms@), nested_list_indices(parsed.syntax.forms@),
        form_spans_valid(source.text, parsed.syntax.forms@, source.text.spec_bytes().len() as int),
        named_forms_match(source.text, parsed.syntax.forms@, parsed.syntax.entries@, parsed.names@,
            parsed.syntax.entries@.len() as int),
        build_index_matches(source.text, parsed.build_model()),
        parsed.entry_ranges@.len() == parsed.syntax.entries@.len(),
{
}

pub(super) proof fn parsed_name_span(
    source: ProjectSource, parsed: NamedBuildCircuit, index: int,
)
    requires
        parsed_circuit_matches(source, parsed),
        0 <= index < parsed.names@.len(),
    ensures
        name_in_source(source.text, parsed.names@[index].name),
        name_site_matches(source.text, parsed.syntax.forms@,
            parsed.names@[index].form + 2, parsed.names@[index].name),
{
    let named = parsed.names@[index];
    let forms = parsed.syntax.forms@;
    let entries = parsed.syntax.entries@;
    reveal(named_forms_match);
    let i = choose|i: int| 0 <= i < entries.len()
        && #[trigger] named_form_matches(source.text, forms, entries[i], named);
    reveal(named_form_matches);
    reveal(name_site_matches);
    assert(name_site_matches(source.text, forms, named.form + 2, named.name));
}

proof fn parsed_sources_cover_prefix(
    inputs: Seq<SourceSnapshot>, sources: Seq<ProjectSource>, circuits: Seq<NamedBuildCircuit>, count: int, stop: int,
)
    requires
        project_sources_match(inputs, sources),
        0 <= count == circuits.len() <= sources.len(),
        (count == sources.len() && stop == inputs.len())
            || (count < sources.len() && stop == sources[count].first_input),
        forall|i: int| 0 <= i < count ==> #[trigger] parsed_circuit_matches(sources[i], circuits[i]),
    ensures circuit_inputs_before(inputs, stop),
{
    assert forall|i: int| i < stop && #[trigger] first_source_input(inputs, i) implies {
        let input = inputs[i];
        &&& (normalized_path(input.path) matches Ok(id) && source_kind_of(id) == Some(SourceKind::Circuit))
        &&& circuit_source_matches(input.text)
    } by {
        collected_source_for_input(inputs, sources, i);
        let at = choose|at: int| 0 <= at < sources.len() && #[trigger] snapshot_matches(inputs[i], sources[at])
            && sources[at].first_input == i && sources[at].text == inputs[i].text;
        if count < sources.len() {
            collected_sources_follow_input_order(inputs, sources, at, count);
        }
        assert(parsed_circuit_matches(sources[at], circuits[at]));
    };
}

/// メモリ上のソースを収集し、回路ソースをファイルごとに一度ずつ解析する。
///
/// # Errors
///
/// ソース集合を先に検査する。収集後は各ファイルの言語と構文を初出順に検査し、最初の違反を返す。
/// 構文診断には、元入力を特定するファイル識別子と文書バージョンを添える。
/// 解析順が `.ncg2m` に達したときは、対象ファイルを示す未対応診断を返す。
pub fn parse_circuit_project<'a>(
    inputs: &[SourceSnapshot<'a>],
) -> (result: Result<CircuitProject<'a>, CircuitProjectError<'a>>)
    ensures
        result.is_ok() <==> circuit_project_accepts(inputs@),
        match result {
            Ok(project) => project.matches(inputs@),
            Err(error) => circuit_project_error(inputs@, error),
        },
{
    match parse_circuit_project_internal(inputs, false) {
        Ok(project) => Ok(project),
        Err(failure) => Err(failure.error),
    }
}

/// ビルド用の厳格解析を行い、構文違反で失敗したファイルだけを回復解析する。
///
/// # Errors
///
/// 最初の違反を返す。構文違反の場合は、診断が示すファイル識別子と文書バージョンに
/// 対応する回復結果を添える。ソース収集の失敗や未対応言語の場合は、違反だけを返す。
pub fn parse_circuit_project_with_recovery<'a>(
    inputs: &[SourceSnapshot<'a>],
) -> (result: Result<CircuitProject<'a>, CircuitProjectFailure<'a>>)
    ensures
        result.is_ok() <==> circuit_project_accepts(inputs@),
        match result {
            Ok(project) => project.matches(inputs@),
            Err(failure) => circuit_project_failure(inputs@, failure),
        },
{
    parse_circuit_project_internal(inputs, true)
}

fn parse_circuit_project_internal<'a>(
    inputs: &[SourceSnapshot<'a>],
    recover: bool,
) -> (result: Result<CircuitProject<'a>, CircuitProjectFailure<'a>>)
    ensures
        result.is_ok() <==> circuit_project_accepts(inputs@),
        match result {
            Ok(project) => project.matches(inputs@),
            Err(failure) => circuit_project_error(inputs@, failure.error)
                && (if recover { circuit_project_failure(inputs@, failure) }
                    else { failure.recovery.is_none() }),
        },
{
    let sources = match collect_sources(inputs) {
        Ok(sources) => sources,
        Err(error) => return Err(CircuitProjectFailure {
            error: CircuitProjectError::Sources(error),
            recovery: None,
        }),
    };
    let mut circuits: Vec<NamedBuildCircuit> = Vec::new();
    let mut index = 0;
    while index < sources.len()
        invariant
            project_sources_match(inputs@, sources@),
            valid_source_snapshots(inputs@),
            index == circuits@.len() <= sources@.len(),
            forall|i: int| 0 <= i < index ==> #[trigger] parsed_circuit_matches(sources@[i], circuits@[i]),
        decreases sources@.len() - index,
    {
        let source = &sources[index];
        proof { collected_source_origin(inputs@, sources@, index as int); }
        if !matches!(source.kind, SourceKind::Circuit) {
            let id = source.id.copy_for_diagnostic();
            proof { parsed_sources_cover_prefix(inputs@, sources@, circuits@, index as int, source.first_input as int); }
            assert(!circuit_project_accepts(inputs@));
            return Err(CircuitProjectFailure {
                error: CircuitProjectError::UnsupportedLanguage {
                    id, revision: source.revision, kind: source.kind,
                },
                recovery: None,
            });
        }
        let parsed = match index_named_build_forms(source.text) {
            Ok(parsed) => parsed,
            Err(error) => {
                let id = source.id.copy_for_diagnostic();
                proof { parsed_sources_cover_prefix(inputs@, sources@, circuits@, index as int, source.first_input as int); }
                assert(!circuit_project_accepts(inputs@));
                let recovery = if recover { Some(recover_circuit_forms(source.text)) } else { None };
                return Err(CircuitProjectFailure {
                    error: CircuitProjectError::Syntax { id, revision: source.revision, error },
                    recovery,
                });
            }
        };
        assert(parsed_circuit_matches(*source, parsed));
        circuits.push(parsed);
        index += 1;
    }
    proof {
        parsed_sources_cover_prefix(inputs@, sources@, circuits@, sources@.len() as int, inputs@.len() as int);
        collected_source_ids_unique(inputs@, sources@);
    }
    Ok(CircuitProject { sources, circuits })
}

} // verus!
