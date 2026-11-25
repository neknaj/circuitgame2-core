//! 元のモジュール断片の対象名を、置換範囲と部分候補に結び付ける。

use super::{CircuitEditorFile, CircuitEditorProject, PartialCircuitDeclarations, RecoveredDeclarationQuery};
use crate::project::{LocatedName, read_source_span};
use crate::syntax::circuit::{Head, RecoveredName, RecoveredNamePosition, RecoveredNames};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::{string::StringSliceAdditionalSpecFns, utf8::{encode_utf8_valid_utf8, is_char_boundary}};

verus! {

/// 回復後も所属を確認できた断片の対象名と、観測済みモジュールの部分候補。
pub struct ModulePartCandidates<'p, 'a> {
    /// カーソルを含む元の対象名。置換範囲は解析に使った文書版を指す。
    pub replace: LocatedName<'p, 'a>,
    /// 対象名のうち、カーソルより前にある文字列。
    pub prefix: &'a str,
    /// 断片が属する名前空間。ルート直下の断片では `None`。
    pub namespace: Option<&'a str>,
    /// 同じ名前空間で接頭辞が一致したモジュールの元の宣言。未確認の断片は含まない。
    pub declarations: PartialCircuitDeclarations<'p, 'a>,
}

type PartName<'a> = (usize, usize, RecoveredNamePosition, RecoveredName<'a>);

spec fn contains_cursor(name: RecoveredName, offset: usize) -> bool {
    name.head is ModulePart && name.name.span.start <= offset <= name.name.span.end
}

spec fn part_name_at(names: &RecoveredNames, offset: usize, hit: PartName) -> bool {
    names.position_model(hit.0, hit.1) == Some(hit.2)
        && names.name_matches(hit.2, Some(hit.3))
        && contains_cursor(hit.3, offset)
}

spec fn no_part_at(names: &RecoveredNames, group: usize, item: usize, offset: usize) -> bool {
    forall|position: RecoveredNamePosition, name: RecoveredName|
        !(#[trigger] part_name_at(names, offset, (group, item, position, name)))
}

fn part_in_group<'a>(names: &RecoveredNames<'a>, group: usize, offset: usize) -> (result: Option<PartName<'a>>)
    requires names.valid(),
    ensures match result {
        Some(hit) => hit.0 == group && hit.1 < names.position_count_model(group)
            && part_name_at(names, offset, hit),
        None => forall|i: usize| i < names.position_count_model(group)
            ==> #[trigger] no_part_at(names, group, i, offset),
    },
{
    let count = names.position_count(group);
    let mut item = 0usize;
    while item < count
        invariant
            names.valid(),
            item <= count,
            count == names.position_count_model(group),
            forall|i: usize| i < item ==> #[trigger] no_part_at(names, group, i, offset),
        decreases count - item,
    {
        let Some(position) = names.position(group, item) else { unreachable!() };
        let observed = names.name_at(position);
        let ghost original = observed;
        if let Some(name) = observed {
            if matches!(name.head, Head::ModulePart) && name.name.span.start <= offset && offset <= name.name.span.end {
                let hit = (group, item, position, name);
                assert(part_name_at(names, offset, hit));
                return Some(hit);
            }
        }
        proof {
            assert forall|at: RecoveredNamePosition, name: RecoveredName|
                #[trigger] part_name_at(names, offset, (group, item, at, name)) implies false by {
                names.names_agree_at(position, original, Some(name));
            };
            assert(no_part_at(names, group, item, offset));
        }
        item += 1;
    }
    None
}

spec fn located_part(names: &RecoveredNames, offset: usize, result: Option<PartName>) -> bool {
    match result {
        Some(hit) => hit.0 < names.position_group_count_model()
            && hit.1 < names.position_count_model(hit.0)
            && part_name_at(names, offset, hit),
        None => forall|g: usize, i: usize|
            g < names.position_group_count_model() && i < names.position_count_model(g)
                ==> #[trigger] no_part_at(names, g, i, offset),
    }
}

fn part_name<'a>(names: &RecoveredNames<'a>, offset: usize) -> (result: Option<PartName<'a>>)
    requires names.valid(),
    ensures located_part(names, offset, result),
{
    let count = names.position_group_count();
    let mut group = 0usize;
    while group < count
        invariant
            names.valid(),
            group <= count,
            count == names.position_group_count_model(),
            forall|g: usize, i: usize| g < group && i < names.position_count_model(g)
                ==> #[trigger] no_part_at(names, g, i, offset),
        decreases count - group,
    {
        if let Some(hit) = part_in_group(names, group, offset) {
            return Some(hit);
        }
        group += 1;
    }
    None
}

impl<'p, 'a> CircuitEditorFile<'p, 'a> {
    spec fn context_matches(
        &self, offset: usize, replace: LocatedName<'p, 'a>, prefix: &'a str, namespace: Option<&'a str>,
    ) -> bool {
        let names = self.recovered_names_model();
        let bytes = self.source_model().text_model().spec_bytes();
        &&& replace.source == self.source_model()
        &&& is_char_boundary(bytes, offset as int)
        &&& is_char_boundary(bytes, replace.span.start as int)
        &&& is_char_boundary(bytes, replace.span.end as int)
        &&& replace.span.start <= offset <= replace.span.end <= bytes.len()
        &&& prefix.spec_bytes() == bytes[replace.span.start as int..offset as int]
        &&& exists|hit: PartName| {
            &&& #[trigger] located_part(names, offset, Some(hit))
            &&& replace.span == hit.3.name.span
            &&& namespace == match hit.3.namespace {
                Some(site) => Some(site.word),
                None => None,
            }
        }
    }

    spec fn no_context(&self, offset: usize) -> bool {
        !is_char_boundary(self.source_model().text_model().spec_bytes(), offset as int)
            || located_part(self.recovered_names_model(), offset, None)
    }

    fn part_context(&self, offset: usize)
        -> (result: Option<(LocatedName<'p, 'a>, &'a str, Option<&'a str>)>)
        ensures match result {
            Some((replace, prefix, namespace)) => self.context_matches(offset, replace, prefix, namespace),
            None => self.no_context(offset),
        },
    {
        let source = self.source();
        let text = source.text();
        if !text.is_char_boundary(offset) {
            return None;
        }
        let names = self.recovered_names();
        let Some(hit) = part_name(names, offset) else { return None; };
        let ghost chosen = hit;
        let (_, _, _position, name) = hit;
        let span = name.name.span.start..name.name.span.end;
        let namespace = match &name.namespace {
            Some(site) => Some(site.word),
            None => None,
        };
        proof {
            assert(located_part(names, offset, Some(chosen)));
            assert(part_name_at(names, offset, chosen));
            names.name_uses_source_ranges(_position, name);
        }
        let prefix = if span.start == offset {
            proof {
                reveal_strlit("");
                assert("".spec_bytes() =~= text.spec_bytes()[span.start as int..offset as int]);
            }
            ""
        } else {
            read_source_span(text, span.start, offset)
        };
        let replace = LocatedName { source, span };
        assert(self.context_matches(offset, replace, prefix, namespace)) by {
            encode_utf8_valid_utf8(text@);
            let bytes = self.source_model().text_model().spec_bytes();
            assert(replace.source == self.source_model());
            assert(is_char_boundary(bytes, offset as int));
            assert(is_char_boundary(bytes, replace.span.start as int));
            assert(is_char_boundary(bytes, replace.span.end as int));
            assert(replace.span.start <= offset <= replace.span.end <= bytes.len());
            assert(prefix.spec_bytes() == bytes[replace.span.start as int..offset as int]);
            assert(located_part(self.recovered_names_model(), offset, Some(chosen)));
            assert(exists|hit: PartName| {
                &&& #[trigger] located_part(names, offset, Some(hit))
                &&& replace.span == hit.3.name.span
                &&& namespace == match hit.3.namespace {
                    Some(site) => Some(site.word),
                    None => None,
                }
            });
        }
        Some((replace, prefix, namespace))
    }
}

impl<'p, 'a> CircuitEditorProject<'p, 'a> {
    /// 断片の置換範囲と接頭辞が元のフォームに由来し、宣言候補がその文脈の条件に合うことを表す。
    pub closed spec fn module_part_candidates_match(
        &self, file: usize, offset: usize, result: Option<ModulePartCandidates<'p, 'a>>,
    ) -> bool {
        let files = self.files_model();
        if file >= files.len() {
            result.is_none()
        } else if let Some(editor) = files[file as int] {
            match result {
                Some(hit) => editor.context_matches(offset, hit.replace, hit.prefix, hit.namespace)
                    && self.query_matches(RecoveredDeclarationQuery::Prefix {
                        parent: hit.namespace,
                        prefix: hit.prefix,
                        head: Some(Head::Module),
                    }, hit.declarations.files@),
                None => editor.no_context(offset),
            }
        } else {
            result.is_none()
        }
    }

    /// 候補を取得した元の文書と置換範囲を特定し、宣言の検索条件を取り出す。
    pub proof fn module_part_completion_evidence(
        &self, file: usize, offset: usize, hit: ModulePartCandidates<'p, 'a>,
    )
        requires
            self.matches_sources(self.sources_model()),
            self.module_part_candidates_match(file, offset, Some(hit)),
        ensures
            file < self.sources_model()@.len(),
            hit.replace.source == &self.sources_model()@[file as int],
            hit.replace.span.start <= offset <= hit.replace.span.end
                <= hit.replace.source.text_model().spec_bytes().len(),
            hit.prefix.spec_bytes() == hit.replace.source.text_model().spec_bytes()[hit.replace.span.start as int..offset as int],
            self.query_matches(RecoveredDeclarationQuery::Prefix {
                parent: hit.namespace, prefix: hit.prefix, head: Some(Head::Module),
            }, hit.declarations.files@),
    {
        self.file_source_evidence(file as int);
    }

    /// カーソルを含む元の断片名から、同じ名前空間にあるモジュール宣言の部分候補を返す。
    ///
    /// 空所が元の名前の範囲内または直後にある場合を対象とする。断片の所属を確認できない場合や、
    /// 名前以外の位置では `None`。候補には未確認の断片が含まれない。
    pub fn module_part_candidates(&self, file: usize, offset: usize)
        -> (result: Option<ModulePartCandidates<'p, 'a>>)
        ensures self.module_part_candidates_match(file, offset, result),
    {
        let Some(Some(editor)) = self.files().get(file) else { return None; };
        let (replace, prefix, namespace) = editor.part_context(offset)?;
        let declarations = self.query_declarations(RecoveredDeclarationQuery::Prefix {
            parent: namespace,
            prefix,
            head: Some(Head::Module),
        });
        Some(ModulePartCandidates { replace, prefix, namespace, declarations })
    }
}

} // verus!
