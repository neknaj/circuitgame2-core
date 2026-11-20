//! 解決済みの構造体を宣言位置で検索できるように集める。

mod layout;
pub use layout::{StructureLayout, StructureLayoutError, StructureLayoutField, StructureLayouts, StructurePlacementError};

use super::{ResolvedStructure, StructurePosition, StructureResolutionError, UseAliases};
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// プロジェクト内の宣言位置と、解決したフィールド型。
#[derive(Debug)]
pub struct ResolvedStructureEntry {
    /// 元の構造体宣言の位置。
    pub position: StructurePosition,
    /// 宣言幅とフィールドの解決結果。
    pub declaration: ResolvedStructure,
}

/// 元のファイル順と厳格索引順に並べた解決済み構造体。
#[derive(Debug)]
pub struct ResolvedStructures {
    entries: Vec<ResolvedStructureEntry>,
}

/// プロジェクト内の構造体を走査中に見つかった診断。
#[derive(Debug)]
pub struct StructureIndexError<'p, 'a> {
    /// 診断の対象になった構造体宣言。
    pub position: StructurePosition,
    /// 数値検査または型参照の診断。
    pub error: StructureResolutionError<'p, 'a>,
}

spec fn structure_before(left: StructurePosition, right: StructurePosition) -> bool {
    left.file < right.file || (left.file == right.file && left.entry < right.entry)
}

spec fn entries_in_order(entries: Seq<ResolvedStructureEntry>) -> bool {
    forall|a: int, b: int| 0 <= a < b < entries.len() ==>
        structure_before((#[trigger] entries[a]).position, (#[trigger] entries[b]).position)
}

impl ResolvedStructures {
    #[verifier::type_invariant]
    spec fn sorted(&self) -> bool {
        entries_in_order(self.entries@)
    }

    /// 解決済みの構造体宣言を走査順に返す。
    pub fn entries(&self) -> (entries: &[ResolvedStructureEntry])
        ensures entries@ == self.entries_model(),
    {
        self.entries.as_slice()
    }

    /// 構造体宣言の位置から解決結果を検索する。
    ///
    /// 構造体がその位置に存在しない場合は `None` を返す。
    pub fn get(&self, position: StructurePosition) -> (found: Option<&ResolvedStructure>)
        ensures self.lookup_matches(position, found),
    {
        proof { use_type_invariant(self); }
        let entries = self.entries.as_slice();
        let mut first = 0;
        let mut last = entries.len();
        while first < last
            invariant
                first <= last <= entries@.len(),
                entries@ == self.entries@,
                entries_in_order(entries@),
                forall|i: int| 0 <= i < first ==> structure_before((#[trigger] entries@[i]).position, position),
                forall|i: int| last <= i < entries@.len() ==> structure_before(position, (#[trigger] entries@[i]).position),
            decreases last - first,
        {
            let middle = first + (last - first) / 2;
            let item = &entries[middle];
            let at = item.position;
            if at.file < position.file || (at.file == position.file && at.entry < position.entry) {
                assert forall|i: int| 0 <= i <= middle implies
                    structure_before((#[trigger] entries@[i]).position, position) by {
                    if i < middle { assert(structure_before(entries@[i].position, item.position)); }
                };
                first = middle + 1;
            } else if position.file < at.file || (at.file == position.file && position.entry < at.entry) {
                assert forall|i: int| middle <= i < entries@.len() implies
                    structure_before(position, (#[trigger] entries@[i]).position) by {
                    if i > middle { assert(structure_before(item.position, entries@[i].position)); }
                };
                last = middle;
            } else {
                return Some(&item.declaration);
            }
        }
        None
    }

    /// 元の宣言位置と解決結果の列を表す。
    pub closed spec fn entries_model(&self) -> Seq<ResolvedStructureEntry> { self.entries@ }

    /// 検索結果が対応する宣言の解決結果であることを表す。
    pub closed spec fn lookup_matches(&self, position: StructurePosition, found: Option<&ResolvedStructure>) -> bool {
        match found {
            Some(declaration) => exists|i: int| 0 <= i < self.entries@.len()
                && (#[trigger] self.entries@[i]).position == position && self.entries@[i].declaration == *declaration,
            None => forall|i: int| 0 <= i < self.entries@.len() ==> (#[trigger] self.entries@[i]).position != position,
        }
    }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn is_structure_position(&self, position: StructurePosition) -> bool {
        let circuits = self.targets.project_model().circuits_model();
        &&& position.file < circuits.len()
        &&& position.entry < circuits[position.file as int].syntax.entries@.len()
        &&& circuits[position.file as int].syntax.entries@[position.entry as int].head is Struct
    }

    spec fn structure_prefix(
        &self, limit: u64, stop: StructurePosition, entries: Seq<ResolvedStructureEntry>,
    ) -> bool {
        &&& entries_in_order(entries)
        &&& forall|i: int| 0 <= i < entries.len() ==> {
            let row = #[trigger] entries[i];
            &&& self.is_structure_position(row.position)
            &&& structure_before(row.position, stop)
            &&& self.structure_resolution_matches(row.position.file, row.position.entry, limit, Ok(Some(row.declaration)))
        }
        &&& forall|position: StructurePosition| #[trigger] self.is_structure_position(position)
            && structure_before(position, stop) ==> exists|i: int| 0 <= i < entries.len()
                && (#[trigger] entries[i]).position == position
    }

    /// 索引が構造体宣言を一度ずつ含むこと、または最初の解決診断に対応することを表す。
    pub closed spec fn structure_index_matches(
        &self, limit: u64, result: Result<ResolvedStructures, StructureIndexError>,
    ) -> bool {
        match result {
            Ok(index) => self.structure_prefix(limit, StructurePosition {
                file: self.targets.project_model().circuits_model().len() as usize, entry: 0,
            }, index.entries@),
            Err(error) => self.is_structure_position(error.position)
                && self.structure_resolution_matches(error.position.file, error.position.entry, limit, Err(error.error))
                && (exists|prefix: Seq<ResolvedStructureEntry>|
                    #[trigger] self.structure_prefix(limit, error.position, prefix)),
        }
    }

    proof fn advance_structure_entry(
        &self, limit: u64, file: usize, entry: usize, entries: Seq<ResolvedStructureEntry>,
        row: Option<ResolvedStructureEntry>,
    )
        requires
            entry < usize::MAX,
            self.structure_prefix(limit, StructurePosition { file, entry }, entries),
            match row {
                Some(row) => row.position == (StructurePosition { file, entry })
                    && self.is_structure_position(row.position)
                    && self.structure_resolution_matches(file, entry, limit, Ok(Some(row.declaration))),
                None => !self.is_structure_position(StructurePosition { file, entry }),
            },
        ensures self.structure_prefix(limit, StructurePosition { file, entry: (entry + 1) as usize },
            if let Some(row) = row { entries.push(row) } else { entries }),
    {
        let position = StructurePosition { file, entry };
        let next = StructurePosition { file, entry: (entry + 1) as usize };
        let all = if let Some(row) = row { entries.push(row) } else { entries };
        assert forall|p: StructurePosition| #[trigger] self.is_structure_position(p) && structure_before(p, next)
            implies exists|i: int| 0 <= i < all.len() && (#[trigger] all[i]).position == p by {
            if p == position {
                assert(row.is_some());
                assert(all[entries.len() as int].position == p);
            } else {
                assert(structure_before(p, position));
                let i = choose|i: int| 0 <= i < entries.len() && (#[trigger] entries[i]).position == p;
                assert(all[i] == entries[i]);
            }
        };
    }

    proof fn advance_structure_file(
        &self, limit: u64, file: usize, count: usize, entries: Seq<ResolvedStructureEntry>,
    )
        requires
            file < self.targets.project_model().circuits_model().len(),
            file < usize::MAX,
            count == self.targets.project_model().circuits_model()[file as int].syntax.entries@.len(),
            self.structure_prefix(limit, StructurePosition { file, entry: count }, entries),
        ensures self.structure_prefix(limit, StructurePosition { file: (file + 1) as usize, entry: 0 }, entries),
    {
        let next = StructurePosition { file: (file + 1) as usize, entry: 0 };
        assert forall|p: StructurePosition| #[trigger] self.is_structure_position(p) && structure_before(p, next)
            implies exists|i: int| 0 <= i < entries.len() && (#[trigger] entries[i]).position == p by {
            assert(structure_before(p, StructurePosition { file, entry: count }));
        };
    }

    /// プロジェクトにある構造体のフィールド型をすべて解決する。
    ///
    /// ファイル順とファイル内の宣言順に走査する。配置と循環の検査は解決結果から行う。
    ///
    /// # Examples
    ///
    /// 検索にはファイルの厳格索引の添字を使う。
    ///
    /// ```
    /// use circuitgame2_core::project::{
    ///     SourceSnapshot, StructurePosition, check_use_aliases, index_use_targets, parse_circuit_project,
    /// };
    /// let project = parse_circuit_project(&[SourceSnapshot {
    ///     path: "layout.ncg2", revision: 1,
    ///     text: "(struct Base (width 8)) (func id (in x) (out x))
    ///         (struct Wrapper (width 16) (inner Base (at 8)))",
    /// }]).unwrap();
    /// let targets = index_use_targets(&project).unwrap();
    /// let aliases = check_use_aliases(&targets).unwrap();
    /// let structures = aliases.index_resolved_structures(16).unwrap();
    /// assert_eq!(structures.entries().len(), 2);
    /// assert!(structures.get(StructurePosition { file: 0, entry: 1 }).is_none());
    /// let wrapper = structures.get(StructurePosition { file: 0, entry: 2 }).unwrap();
    /// assert_eq!(wrapper.width, 16);
    /// ```
    ///
    /// # Errors
    ///
    /// 最初に数値検査または型名の解決で失敗した構造体と、その診断を返す。
    pub fn index_resolved_structures(&self, limit: u64)
        -> (result: Result<ResolvedStructures, StructureIndexError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.structure_index_matches(limit, result),
    {
        let circuits = self.targets.project().circuits();
        let mut entries = Vec::new();
        let mut file = 0;
        while file < circuits.len()
            invariant
                self.can_resolve(),
                circuits@ == self.targets.project_model().circuits_model(),
                file <= circuits@.len(),
                self.structure_prefix(limit, StructurePosition { file, entry: 0 }, entries@),
            decreases circuits@.len() - file,
        {
            let syntax = &circuits[file].syntax;
            let mut entry = 0;
            while entry < syntax.entries.len()
                invariant
                    self.can_resolve(),
                    circuits@ == self.targets.project_model().circuits_model(),
                    file < circuits@.len(),
                    *syntax == circuits@[file as int].syntax,
                    entry <= syntax.entries@.len(),
                    self.structure_prefix(limit, StructurePosition { file, entry }, entries@),
                decreases syntax.entries@.len() - entry,
            {
                let position = StructurePosition { file, entry };
                if matches!(syntax.entries[entry].head, crate::syntax::circuit::Head::Struct) {
                    let declaration = match self.resolve_structure_fields(file, entry, limit) {
                        Ok(Some(declaration)) => declaration,
                        Ok(None) => {
                            proof { self.resolution_keeps_structure_position(file, entry, limit); }
                            unreachable!()
                        },
                        Err(error) => return Err(StructureIndexError { position, error }),
                    };
                    let row = ResolvedStructureEntry { position, declaration };
                    proof { self.advance_structure_entry(limit, file, entry, entries@, Some(row)); }
                    entries.push(row);
                } else {
                    proof { self.advance_structure_entry(limit, file, entry, entries@, None); }
                }
                entry += 1;
            }
            proof { self.advance_structure_file(limit, file, entry, entries@); }
            file += 1;
        }
        Ok(ResolvedStructures { entries })
    }

    proof fn resolution_keeps_structure_position(&self, file: usize, entry: usize, limit: u64)
        requires
            self.is_structure_position(StructurePosition { file, entry }),
            self.structure_resolution_matches(file, entry, limit, Ok(None)),
        ensures false,
    {
        crate::project::structure_declarations::no_structure_declaration(
            &self.targets.project_model(), file as int, entry as int, limit);
    }
}

} // verus!
