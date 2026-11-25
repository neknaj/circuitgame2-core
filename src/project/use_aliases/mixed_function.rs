//! 混在ソース集合の厳格索引から、関数の呼び出し位置を確定する。

use super::definitions::DefinitionReferenceSite;
use crate::project::circuits::read_indexed_atom;
#[cfg(verus_only)]
use crate::project::circuits::parsed_index_evidence;
#[cfg(verus_only)]
use crate::project::source_indexes::{project_source_index_evidence, project_source_index_matches};
use crate::project::{ParsedProjectSources, ProjectSourceIndex};
use crate::syntax::circuit::{ExpressionReferenceKind, Head, NameSite};
#[cfg(verus_only)]
use crate::syntax::circuit::{
    build_definition_scope_evidence, build_entry_ranges_evidence, expression_reference_in_source,
};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::{string::StringSliceAdditionalSpecFns, utf8::is_char_boundary};

verus! {

impl<'a> ParsedProjectSources<'a> {
    /// 指定した定義内参照が `func` 本体の呼び出し名であることを表す。
    pub open spec fn has_func_callee(&self, file: usize, entry: usize, definition: usize, reference: usize) -> bool {
        &&& file < self.sources_model().len()
        &&& file < self.indexes_model().len()
        &&& self.indexes_model()[file as int] matches ProjectSourceIndex::Circuit(parsed)
        &&& entry < parsed.syntax.entries@.len()
        &&& entry < parsed.entry_ranges@.len()
        &&& parsed.syntax.entries@[entry as int].head is Func
        &&& {
            let definitions = parsed.entry_ranges@[entry as int].definitions;
            let index = definitions.start + definition;
            &&& index < definitions.end
            &&& index < parsed.definitions@.len()
            &&& {
                let references = parsed.definitions@[index].references;
                let at = references.start + reference;
                &&& at < references.end
                &&& at < parsed.references@.len()
                &&& parsed.references@[at].kind is Callee
            }
        }
    }

    /// 混在ソース集合のファイル番号で、`func` 本体の呼び出し名を取り出す。
    ///
    /// `entry` はファイル内の構文項目、`definition` は項目内の定義、`reference` は定義内の参照を指す。
    /// 範囲外や別の種類の参照には `None` を返す。呼び出し名の解決は後段で行う。
    ///
    /// # Examples
    ///
    /// ```
    /// use circuitgame2_core::project::{ProjectSourceIndex, SourceSnapshot, parse_project_sources};
    /// use circuitgame2_core::syntax::circuit::Head;
    ///
    /// let circuit = "; 猫\n(namespace app (func gate (in a) (out z) (def z (nor a a))))";
    /// let project = parse_project_sources(&[
    ///     SourceSnapshot { path: "tools.ncg2m", revision: 1, text: "" },
    ///     SourceSnapshot { path: "board.ncg2", revision: 7, text: circuit },
    /// ]).unwrap();
    /// let ProjectSourceIndex::Circuit(index) = &project.indexes()[1] else { panic!() };
    /// let entry = index.syntax.entries.iter().position(|item| item.head == Head::Func).unwrap();
    /// let site = project.func_callee_site(1, entry, 0, 0).unwrap();
    /// assert_eq!(&circuit[site.name.span], "nor");
    /// assert_eq!(site.source.revision, 7);
    /// assert_eq!(site.block, Some(0));
    /// assert!(project.func_callee_site(0, entry, 0, 0).is_none());
    /// ```
    pub fn func_callee_site(&self, file: usize, entry: usize, definition: usize, reference: usize)
        -> (result: Option<DefinitionReferenceSite<'_, 'a>>)
        ensures
            result.is_some() <==> self.has_func_callee(file, entry, definition, reference),
            result matches Some(site) ==> {
                let parsed = self.indexes_model()[file as int]->Circuit_0;
                let item = parsed.syntax.entries@[entry as int];
                let def = parsed.entry_ranges@[entry as int].definitions.start + definition;
                let reference_at = parsed.definitions@[def].references.start + reference;
                let indexed = parsed.references@[reference_at];
                &&& *site.source == self.sources_model()[file as int]
                &&& site.owner is Func && site.role is Callee && site.block == item.namespace
                &&& site.name.span == indexed.span
                &&& {
                    let bytes = site.source.text_model().spec_bytes();
                    let start = site.name.span.start as int;
                    let end = site.name.span.end as int;
                    &&& 0 <= start < end <= bytes.len()
                    &&& is_char_boundary(bytes, start) && is_char_boundary(bytes, end)
                    &&& bytes[start..end] == site.name.word.spec_bytes()
                }
            },
    {
        let sources = self.sources();
        let indexes = self.indexes();
        if file >= sources.len() { return None; }
        let index = &indexes[file];
        let ProjectSourceIndex::Circuit(parsed) = index else { return None; };
        if entry >= parsed.syntax.entries.len() || entry >= parsed.entry_ranges.len() { return None; }
        let item = &parsed.syntax.entries[entry];
        if !matches!(item.head, Head::Func) { return None; }
        let source = &sources[file];
        let ghost model = parsed.build_model();
        proof {
            assert(project_source_index_matches(*source, *index));
            project_source_index_evidence(*source, *index);
            parsed_index_evidence(*source, *parsed);
            build_entry_ranges_evidence(source.text, &model, entry as int);
        }
        let definitions = &parsed.entry_ranges[entry].definitions;
        if definition >= definitions.end - definitions.start { return None; }
        let def = definitions.start + definition;
        let references = &parsed.definitions[def].references;
        proof { build_definition_scope_evidence(source.text, &model, entry as int, def as int); }
        if reference >= references.end - references.start { return None; }
        let indexed = &parsed.references[references.start + reference];
        if !matches!(indexed.kind, ExpressionReferenceKind::Callee) { return None; }
        proof {
            source.text_model_is_text();
            assert(expression_reference_in_source(source.text, parsed.syntax.forms@, *indexed));
        }
        let (word, span) = read_indexed_atom(source.text, &parsed.syntax.forms, indexed.form);
        Some(DefinitionReferenceSite {
            source,
            name: NameSite { word, span },
            role: indexed.kind,
            owner: item.head,
            block: item.namespace,
        })
    }
}

} // verus!
