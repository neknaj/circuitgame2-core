//! 両言語の公開指定を混在プロジェクトの宣言表に適用する。

use super::{ExportError, is_published_in};
#[cfg(verus_only)]
use super::{before, published};
use crate::ncg2m::file::MetaItemKind;
#[cfg(verus_only)]
use crate::ncg2m::file::{meta_binding_span_evidence, meta_export_span_evidence};
use crate::project::circuits::{read_indexed_atom, read_source_span};
#[cfg(verus_only)]
use crate::project::circuits::parsed_index_evidence;
use crate::project::source_indexes::count_directive_entries;
use crate::project::{
    LocatedName, MixedDeclarationTable, NameKey, ParsedProjectSources, ProjectSourceIndex, index_mixed_declarations,
};
#[cfg(verus_only)]
use crate::project::{
    location_in_source, mixed_declaration_lookup_agrees, mixed_declaration_table_matches, mixed_name_conflict_evidence, mixed_name_conflicts_agree,
    mixed_project_declares, mixed_project_names_conflict,
    name_keys::{key_bytes, key_views_agree}, source_indexes::{directive_entry_count, project_source_index_evidence},
};
use crate::syntax::{Form, circuit::Head};
#[cfg(verus_only)]
use crate::syntax::{form_span, circuit::export_entry_evidence};
use alloc::vec::Vec;
#[cfg(verus_only)]
use core::ops::Range;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 混在プロジェクトの公開指定を適用できなかった理由。
pub type MixedExportError<'p, 'a> = ExportError<'p, 'a>;

/// 混在プロジェクトの宣言表と公開状態。
#[derive(Debug)]
pub struct MixedExportTable<'p, 'a> {
    declarations: MixedDeclarationTable<'p, 'a>,
    names: Vec<NameKey<'a>>,
}

spec fn arg_count(index: ProjectSourceIndex, item: int) -> nat {
    match index {
        ProjectSourceIndex::Circuit(circuit) => {
            let info = circuit.syntax.entries@[item];
            let root = info.form as int;
            if info.head is Export && circuit.syntax.forms@[root] is List {
                (circuit.syntax.forms@[root]->List_end - root - 2) as nat
            } else { 0 }
        },
        ProjectSourceIndex::Functional(items) => match items@[item].kind {
            MetaItemKind::Export { names } => names@.len(),
            _ => 0,
        },
    }
}

spec fn at(project: &ParsedProjectSources, file: int, item: int, arg: int) -> bool {
    &&& 0 <= file < project.indexes_model().len()
    &&& 0 <= item < directive_entry_count(project.indexes_model()[file])
    &&& 0 <= arg < arg_count(project.indexes_model()[file], item)
}

spec fn spans(index: ProjectSourceIndex, item: int, arg: int) -> (Option<Range<usize>>, Range<usize>) {
    match index {
        ProjectSourceIndex::Circuit(circuit) => {
            let info = circuit.syntax.entries@[item];
            let forms = circuit.syntax.forms@;
            let parent = match info.namespace {
                Some(root) => Some(form_span(forms[root + 2])),
                None => None,
            };
            (parent, form_span(forms[info.form + 2 + arg]))
        },
        ProjectSourceIndex::Functional(items) => {
            let info = items@[item];
            (info.namespace, info.kind->Export_names@[arg])
        },
    }
}

spec fn requested(project: &ParsedProjectSources, file: int, item: int, arg: int, key: NameKey) -> bool {
    &&& at(project, file, item, arg)
    &&& {
        let bytes = project.sources_model()[file].text.spec_bytes();
        let (parent, name) = spans(project.indexes_model()[file], item, arg);
        let parent_bytes = match parent {
            Some(span) => Some(bytes[span.start as int..span.end as int]),
            None => None,
        };
        key_bytes(key) == (parent_bytes, bytes[name.start as int..name.end as int])
    }
}

/// 指定された完全修飾名の公開指定が、いずれかの言語の元の索引にあることを表す。
pub closed spec fn mixed_publication_requested(project: &ParsedProjectSources, key: NameKey) -> bool {
    exists|f: int, i: int, a: int| #[trigger] requested(project, f, i, a, key)
}

fn count_args(project: &ParsedProjectSources, file: usize, item: usize) -> (len: usize)
    requires project.has_source_indexes(), file < project.indexes_model().len(),
        item < directive_entry_count(project.indexes_model()[file as int]),
    ensures len == arg_count(project.indexes_model()[file as int], item as int),
{
    let _source = &project.sources()[file];
    let index = &project.indexes()[file];
    proof { project_source_index_evidence(*_source, *index); }
    match index {
        ProjectSourceIndex::Circuit(circuit) => {
            let info = &circuit.syntax.entries[item];
            if !matches!(info.head, Head::Export) {
                return 0;
            }
            proof {
                parsed_index_evidence(*_source, *circuit);
                export_entry_evidence(_source.text, circuit.syntax.forms@, circuit.syntax.entries@, item as int);
            }
            match &circuit.syntax.forms[info.form] {
                Form::List { end, .. } => *end - info.form - 2,
                _ => unreachable!(),
            }
        },
        ProjectSourceIndex::Functional(items) => match &items[item].kind {
            MetaItemKind::Export { names } => names.len(),
            _ => 0,
        },
    }
}

fn read_export<'p, 'a>(
    project: &'p ParsedProjectSources<'a>, file: usize, item: usize, arg: usize,
) -> (export: (NameKey<'a>, LocatedName<'p, 'a>))
    requires project.has_source_indexes(), at(project, file as int, item as int, arg as int),
    ensures
        requested(project, file as int, item as int, arg as int, export.0),
        *export.1.source == project.sources_model()[file as int],
        export.1.span == spans(project.indexes_model()[file as int], item as int, arg as int).1,
        location_in_source(export.1),
{
    let source = &project.sources()[file];
    let index = &project.indexes()[file];
    proof { project_source_index_evidence(*source, *index); }
    let (parent, name, span) = match index {
        ProjectSourceIndex::Circuit(circuit) => {
            let info = &circuit.syntax.entries[item];
            let forms = &circuit.syntax.forms;
            proof {
                parsed_index_evidence(*source, *circuit);
                export_entry_evidence(source.text, forms@, circuit.syntax.entries@, item as int);
            }
            let parent = match info.namespace {
                Some(root) => {
                    assert(circuit.syntax.entries@[item as int].namespace == Some(root));
                    let _length = forms.len();
                    assert(root + 2 < _length);
                    Some(read_indexed_atom(source.text, forms, root + 2).0)
                },
                None => None,
            };
            let (name, span) = read_indexed_atom(source.text, forms, info.form + 2 + arg);
            (parent, name, span)
        },
        ProjectSourceIndex::Functional(items) => {
            let info = &items[item];
            let MetaItemKind::Export { names: name_spans } = &info.kind else { unreachable!() };
            proof {
                meta_binding_span_evidence(source.text, items@, item as int);
                meta_export_span_evidence(source.text, items@, item as int, arg as int);
            }
            let parent = match &info.namespace {
                Some(path) => Some(read_source_span(source.text, path.start, path.end)),
                None => None,
            };
            let word = &name_spans[arg];
            (parent, read_source_span(source.text, word.start, word.end), word.start..word.end)
        },
    };
    let location = LocatedName { source, span };
    proof { crate::project::declarations::located_name_evidence(location); }
    (NameKey { parent, name }, location)
}

#[verifier::opaque]
spec fn selected_before(project: &ParsedProjectSources, names: Seq<NameKey>, file: int, item: int, arg: int) -> bool {
    &&& forall|f: int, i: int, a: int, key: NameKey| #[trigger] requested(project, f, i, a, key)
        && before(f, i, a, file, item, arg) ==> mixed_project_declares(project, key) && published(names, key)
    &&& forall|n: int| 0 <= n < names.len() ==> #[trigger] mixed_publication_requested(project, names[n])
}

proof fn next_arg(
    project: &ParsedProjectSources, names: Seq<NameKey>, next: Seq<NameKey>,
    file: int, item: int, arg: int, key: NameKey,
)
    requires
        selected_before(project, names, file, item, arg),
        requested(project, file, item, arg, key), mixed_project_declares(project, key),
        next == names || next == names.push(key), published(next, key),
    ensures selected_before(project, next, file, item, arg + 1),
{
    reveal(selected_before);
    assert forall|f: int, i: int, a: int, word: NameKey| #[trigger] requested(project, f, i, a, word)
        && before(f, i, a, file, item, arg + 1)
        implies mixed_project_declares(project, word) && published(next, word) by {
        if before(f, i, a, file, item, arg) {
            assert(published(names, word));
            let n = choose|n: int| 0 <= n < names.len() && key_bytes(#[trigger] names[n]) == key_bytes(word);
            assert(next[n] == names[n]);
        } else {
            assert(f == file && i == item && a == arg);
            assert(key_bytes(word) == key_bytes(key));
            key_views_agree(word, key);
            super::super::declarations::mixed_project_name_equivalence(project, word, key);
            let n = choose|n: int| 0 <= n < next.len() && key_bytes(#[trigger] next[n]) == key_bytes(key);
            assert(key_bytes(next[n]) == key_bytes(word));
        }
    };
    assert forall|n: int| 0 <= n < next.len() implies #[trigger] mixed_publication_requested(project, next[n]) by {
        if n < names.len() { assert(next[n] == names[n]); }
        else { assert(next[n] == key); assert(mixed_publication_requested(project, key)); }
    };
}

proof fn next_item(project: &ParsedProjectSources, names: Seq<NameKey>, file: int, item: int, arg: int)
    requires selected_before(project, names, file, item, arg), arg == arg_count(project.indexes_model()[file], item),
    ensures selected_before(project, names, file, item + 1, 0),
{
    reveal(selected_before);
    assert forall|f: int, i: int, a: int, key: NameKey| #[trigger] requested(project, f, i, a, key)
        && before(f, i, a, file, item + 1, 0) implies before(f, i, a, file, item, arg) by {};
}

proof fn next_file(project: &ParsedProjectSources, names: Seq<NameKey>, file: int, item: int)
    requires selected_before(project, names, file, item, 0), item == directive_entry_count(project.indexes_model()[file]),
    ensures selected_before(project, names, file + 1, 0, 0),
{
    reveal(selected_before);
    assert forall|f: int, i: int, a: int, key: NameKey| #[trigger] requested(project, f, i, a, key)
        && before(f, i, a, file + 1, 0, 0) implies before(f, i, a, file, item, 0) by {};
}

/// 公開指定がすべて、指定元と同じ名前空間にある独立宣言を指すことを表す。
pub closed spec fn mixed_project_exports_valid(project: &ParsedProjectSources) -> bool {
    forall|key: NameKey| #[trigger] mixed_publication_requested(project, key) ==> mixed_project_declares(project, key)
}

/// エラーが宣言の衝突か、元の順序で最初の未解決の公開名に対応することを表す。
pub closed spec fn mixed_export_error_evidence(project: &ParsedProjectSources, error: MixedExportError) -> bool {
    match error {
        ExportError::Conflict(conflict) => mixed_project_names_conflict(project)
            && mixed_name_conflict_evidence(project, conflict),
        ExportError::MissingDeclaration(location) => !mixed_project_names_conflict(project)
            && location_in_source(location)
            && (exists|file: int, item: int, arg: int, key: NameKey|
                #[trigger] requested(project, file, item, arg, key)
                && !mixed_project_declares(project, key)
                && *location.source == project.sources_model()[file]
                && location.span == spans(project.indexes_model()[file], item, arg).1
                && forall|f: int, i: int, a: int, word: NameKey| #[trigger] requested(project, f, i, a, word)
                    && before(f, i, a, file, item, arg) ==> mixed_project_declares(project, word)),
    }
}

proof fn missing_export_position<'a>(project: &ParsedProjectSources<'a>, location: LocatedName)
    -> (position: (int, int, int, NameKey<'a>))
    requires mixed_export_error_evidence(project, ExportError::MissingDeclaration(location)),
    ensures
        requested(project, position.0, position.1, position.2, position.3),
        !mixed_project_declares(project, position.3),
        *location.source == project.sources_model()[position.0],
        location.span == spans(project.indexes_model()[position.0], position.1, position.2).1,
        forall|f: int, i: int, a: int, word: NameKey| #[trigger] requested(project, f, i, a, word)
            && before(f, i, a, position.0, position.1, position.2) ==> mixed_project_declares(project, word),
{
    let (file, item, arg, word) = choose|file: int, item: int, arg: int, word: NameKey|
        #[trigger] requested(project, file, item, arg, word)
        && !mixed_project_declares(project, word)
        && *location.source == project.sources_model()[file]
        && location.span == spans(project.indexes_model()[file], item, arg).1
        && (forall|f: int, i: int, a: int, key: NameKey| #[trigger] requested(project, f, i, a, key)
            && before(f, i, a, file, item, arg) ==> mixed_project_declares(project, key));
    (file, item, arg, word)
}

/// 同じソース集合から選ぶ公開指定のエラーは、種別と元ファイル・範囲まで一致する。
pub proof fn mixed_export_errors_agree(project: &ParsedProjectSources, a: MixedExportError, b: MixedExportError)
    requires mixed_export_error_evidence(project, a), mixed_export_error_evidence(project, b),
    ensures a == b,
{
    match (a, b) {
        (ExportError::Conflict(first), ExportError::Conflict(second)) => {
            mixed_name_conflicts_agree(project, first, second);
        },
        (ExportError::MissingDeclaration(first), ExportError::MissingDeclaration(second)) => {
            let (af, ai, aa, ak) = missing_export_position(project, first);
            let (bf, bi, ba, bk) = missing_export_position(project, second);
            if before(af, ai, aa, bf, bi, ba) {
                assert(mixed_project_declares(project, ak));
            }
            if before(bf, bi, ba, af, ai, aa) {
                assert(mixed_project_declares(project, bk));
            }
            assert(af == bf && ai == bi && aa == ba);
        },
        _ => assert(false),
    }
}

/// 宣言表と公開状態が、両言語の元の索引に対応することを表す。
pub closed spec fn mixed_export_table_matches(project: &ParsedProjectSources, table: MixedExportTable) -> bool {
    &&& mixed_declaration_table_matches(project, table.declarations)
    &&& !mixed_project_names_conflict(project)
    &&& mixed_project_exports_valid(project)
    &&& forall|key: NameKey| #[trigger] table.publishes(key) <==> mixed_publication_requested(project, key)
}

pub(in crate::project) proof fn mixed_exports_use_project_declarations(project: &ParsedProjectSources, table: &MixedExportTable)
    requires mixed_export_table_matches(project, *table),
    ensures mixed_declaration_table_matches(project, table.declarations_model()), !mixed_project_names_conflict(project),
{}

/// 公開状態と宣言表が、元の言語別索引に対応することを指定の名前について示す。
pub proof fn mixed_publication_agrees(
    project: &ParsedProjectSources, table: &MixedExportTable, key: NameKey,
)
    requires mixed_export_table_matches(project, *table),
    ensures
        table.publishes(key) == mixed_publication_requested(project, key),
        table.declarations_model().declares(key) == mixed_project_declares(project, key),
        table.publishes(key) ==> table.declarations_model().declares(key),
{
    mixed_declaration_lookup_agrees(project, &table.declarations, key);
}

impl<'p, 'a> MixedExportTable<'p, 'a> {
    /// 指定された完全修飾名に公開指定があることを表す。
    pub closed spec fn publishes(&self, key: NameKey) -> bool {
        published(self.names@, key)
    }

    /// 指定された完全修飾名の宣言が公開されているかを返す。
    pub fn is_public(&self, key: NameKey) -> (found: bool)
        ensures found == self.publishes(key),
    {
        is_published_in(&self.names, key)
    }

    /// 公開状態を適用した混在プロジェクトの宣言表を返す。
    pub fn declarations(&self) -> (table: &MixedDeclarationTable<'p, 'a>)
        ensures *table == self.declarations_model(),
    {
        &self.declarations
    }

    /// 公開状態を適用した宣言表を表す。
    pub closed spec fn declarations_model(&self) -> MixedDeclarationTable<'p, 'a> {
        self.declarations
    }
}

/// 両言語の公開指定を共有宣言表に適用する。同じ宣言への複数の指定は一件にまとめる。
///
/// # Errors
///
/// 宣言名の衝突を先に検査する。指定元と同じ名前空間に独立宣言がないときは、
/// その公開名の元ファイルとバイト範囲を返す。複数あるときは、ソースの初出順、
/// フォームの記述順、同じフォームの引数順で最初の公開名を選ぶ。
///
/// # Examples
///
/// 回路ファイルから、同じ名前空間にある NCG2M の補助関数を公開できる。
///
/// ```
/// use circuitgame2_core::project::{
///     MixedAbsoluteTarget, NameKey, SourceSnapshot, index_mixed_exports, parse_project_sources,
/// };
///
/// let sources = [
///     SourceSnapshot { path: "api.ncg2", revision: 1, text: "(namespace tools (export ready))" },
///     SourceSnapshot { path: "tools.ncg2m", revision: 2,
///         text: "(namespace tools (defn ready (as-type (Fn () Bool) (fn () true))))" },
/// ];
/// let project = parse_project_sources(&sources).unwrap();
/// let exports = index_mixed_exports(&project).unwrap();
/// assert!(exports.is_public(NameKey { parent: Some("tools"), name: "ready" }));
/// assert!(matches!(exports.resolve_absolute("::tools::ready", Some("app")),
///     Ok(MixedAbsoluteTarget::Declaration(_))));
/// ```
pub fn index_mixed_exports<'p, 'a>(project: &'p ParsedProjectSources<'a>)
    -> (result: Result<MixedExportTable<'p, 'a>, MixedExportError<'p, 'a>>)
    ensures result.is_ok() <==> !mixed_project_names_conflict(project) && mixed_project_exports_valid(project),
        match result {
            Ok(table) => mixed_export_table_matches(project, table),
            Err(error) => mixed_export_error_evidence(project, error),
        },
{
    let declarations = match index_mixed_declarations(project) {
        Ok(table) => table,
        Err(error) => return Err(ExportError::Conflict(error)),
    };
    let indexes = project.indexes();
    let mut names = Vec::new();
    let mut file = 0;
    assert(selected_before(project, names@, 0, 0, 0)) by { reveal(selected_before); }
    while file < indexes.len()
        invariant
            indexes@ == project.indexes_model(), project.has_source_indexes(), file <= indexes@.len(),
            !mixed_project_names_conflict(project), mixed_declaration_table_matches(project, declarations),
            selected_before(project, names@, file as int, 0, 0),
        decreases indexes@.len() - file,
    {
        let items = count_directive_entries(&indexes[file]);
        let mut item = 0;
        while item < items
            invariant
                indexes@ == project.indexes_model(), project.has_source_indexes(),
                file < indexes@.len(), item <= items == directive_entry_count(indexes@[file as int]),
                !mixed_project_names_conflict(project), mixed_declaration_table_matches(project, declarations),
                selected_before(project, names@, file as int, item as int, 0),
            decreases items - item,
        {
            let args = count_args(project, file, item);
            let mut arg = 0;
            while arg < args
                invariant
                    indexes@ == project.indexes_model(), project.has_source_indexes(),
                    file < indexes@.len(), item < directive_entry_count(indexes@[file as int]),
                    arg <= args == arg_count(indexes@[file as int], item as int),
                    !mixed_project_names_conflict(project), mixed_declaration_table_matches(project, declarations),
                    selected_before(project, names@, file as int, item as int, arg as int),
                decreases args - arg,
            {
                let (key, location) = read_export(project, file, item, arg);
                proof { mixed_declaration_lookup_agrees(project, &declarations, key); }
                if declarations.declaration(key).is_none() {
                    assert(mixed_publication_requested(project, key));
                    assert(!mixed_project_exports_valid(project));
                    proof { reveal(selected_before); }
                    return Err(ExportError::MissingDeclaration(location));
                }
                let ghost previous = names@;
                if !is_published_in(&names, key) {
                    names.push(key);
                    assert(names@[previous.len() as int] == key);
                }
                proof { next_arg(project, previous, names@, file as int, item as int, arg as int, key); }
                arg += 1;
            }
            proof { next_item(project, names@, file as int, item as int, arg as int); }
            item += 1;
        }
        proof { next_file(project, names@, file as int, item as int); }
        file += 1;
    }
    proof {
        reveal(selected_before);
        assert forall|key: NameKey| #[trigger] mixed_publication_requested(project, key)
            implies mixed_project_declares(project, key) && published(names@, key) by {
            let (f, i, a) = choose|f: int, i: int, a: int| #[trigger] requested(project, f, i, a, key);
            assert(before(f, i, a, file as int, 0, 0));
        };
        assert forall|key: NameKey| #[trigger] published(names@, key) implies mixed_publication_requested(project, key) by {
            let n = choose|n: int| 0 <= n < names@.len() && key_bytes(#[trigger] names@[n]) == key_bytes(key);
            assert(mixed_publication_requested(project, names@[n]));
            let (f, i, a) = choose|f: int, i: int, a: int| #[trigger] requested(project, f, i, a, names@[n]);
            assert(requested(project, f, i, a, key));
        };
    }
    let table = MixedExportTable { declarations, names };
    assert(mixed_export_table_matches(project, table));
    Ok(table)
}

}
