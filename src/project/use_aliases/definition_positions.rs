//! 構文索引の定義参照を、名前を解決せず元ソース順に走査する。

use super::DefinitionPosition;
use crate::project::CircuitProject;
#[cfg(verus_only)]
use super::definitions::{definition_count, reference_count};
#[cfg(verus_only)]
use crate::project::circuits::parsed_index_evidence;
#[cfg(verus_only)]
use crate::syntax::circuit::{build_definition_scope_evidence, build_entry_ranges_evidence};
use vstd::prelude::*;

verus! {

/// 定義参照の走査を一単位進めた結果。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DefinitionPositionStep {
    /// 参照を一つ取り出した。
    Reference(DefinitionPosition),
    /// 今の区間が尽き、次の定義・索引項目・ファイルのいずれかへ進んだ。
    Advanced,
    /// 全ファイルの走査を終えた。
    Finished,
}

/// 確定済みの構文索引を借りて走査するカーソル。
///
/// 添字は借りているプロジェクトに属する。編集後のプロジェクトでは新しいカーソルを作る。
pub struct DefinitionPositions<'p, 'a> {
    project: &'p CircuitProject<'a>,
    at: DefinitionPosition,
}

/// 定義参照の走査順。正規化済みのファイル順と各ファイルの構文順に従う。
pub open spec fn definition_position_before(a: DefinitionPosition, b: DefinitionPosition) -> bool {
    a.file < b.file || (a.file == b.file && (
        a.entry < b.entry || (a.entry == b.entry && (
            a.definition < b.definition || (a.definition == b.definition && a.reference < b.reference)
        ))
    ))
}

/// 指定位置に、厳格索引に登録された定義参照があることを表す。
pub open spec fn definition_position_exists(project: &CircuitProject, at: DefinitionPosition) -> bool {
    let circuits = project.circuits_model();
    &&& at.file < circuits.len()
    &&& {
        let parsed = &circuits[at.file as int];
        &&& at.entry < parsed.entry_ranges@.len()
        &&& at.definition < definition_count(parsed, at.entry as int)
        &&& at.reference < reference_count(parsed, at.entry as int, at.definition as int)
    }
}

/// 走査の残りを、ファイル、索引項目、定義、参照の辞書式順で表す。
pub open spec fn definition_position_remaining(project: &CircuitProject, at: DefinitionPosition) -> (nat, nat, nat, nat) {
    let rows = project.circuits_model();
    let row = &rows[at.file as int];
    let has_entry = at.file < rows.len() && at.entry < row.entry_ranges@.len();
    (
        (rows.len() - at.file) as nat,
        if at.file < rows.len() { (row.entry_ranges@.len() - at.entry) as nat } else { 0 },
        if has_entry { (definition_count(row, at.entry as int) - at.definition) as nat } else { 0 },
        if definition_position_exists(project, at) {
            (reference_count(row, at.entry as int, at.definition as int) - at.reference) as nat
        } else { 0 },
    )
}

/// 走査の残りが辞書式順で減ったことを表す。
pub open spec fn definition_position_progress(project: &CircuitProject, at: DefinitionPosition, next: DefinitionPosition) -> bool {
    let a = definition_position_remaining(project, at);
    let b = definition_position_remaining(project, next);
    b.0 < a.0 || (b.0 == a.0 && (b.1 < a.1 || (b.1 == a.1 && (
        b.2 < a.2 || (b.2 == a.2 && b.3 < a.3)
    ))))
}

/// 参照を一つ取り出すか、参照を含まない区間を飛ばして走査が進むことを表す。
pub open spec fn definition_positions_advance(
    project: &CircuitProject, at: DefinitionPosition, next: DefinitionPosition, result: DefinitionPositionStep,
) -> bool {
    match result {
        DefinitionPositionStep::Finished => at.file == project.circuits_model().len() && next == at,
        DefinitionPositionStep::Advanced => definition_position_before(at, next)
            && (forall|reference: DefinitionPosition|
                #[trigger] definition_position_exists(project, reference) && definition_position_before(reference, next)
                    ==> definition_position_before(reference, at)),
        DefinitionPositionStep::Reference(reference) => reference == at && definition_position_exists(project, reference)
            && next == (DefinitionPosition { reference: (at.reference + 1) as usize, ..at }),
    }
}

impl<'p, 'a> DefinitionPositions<'p, 'a> {
    /// このカーソルが走査する構文済みのプロジェクト。
    pub closed spec fn project_model(&self) -> &'p CircuitProject<'a> { self.project }

    /// 次に調べる索引位置。走査を終えると末尾のファイル位置を指す。
    pub closed spec fn position_model(&self) -> DefinitionPosition { self.at }

    /// 走査位置が、借りている構文索引の先頭から末尾までの範囲にあることを表す。
    pub open spec fn valid(&self) -> bool {
        let at = self.position_model();
        let files = self.project_model().circuits_model();
        &&& self.project_model().has_parsed_sources()
        &&& at.file <= files.len()
        &&& at.file == files.len() ==> at.entry == 0 && at.definition == 0 && at.reference == 0
    }

    /// 次に調べる索引位置を返す。末尾でも同じ形式で取得できる。
    pub fn position(&self) -> (at: DefinitionPosition)
        ensures at == self.position_model(),
    {
        self.at
    }

    /// 定義参照を一つ返すか、次の定義・索引項目・ファイルまで進む。
    ///
    /// 呼び出し一回で参照または索引範囲一つを調べる。`Finished` を返した後は同じ位置を保つ。
    pub fn step(&mut self) -> (result: DefinitionPositionStep)
        requires old(self).valid(),
        ensures
            final(self).valid(), final(self).project_model() == old(self).project_model(),
            definition_positions_advance(old(self).project_model(), old(self).position_model(),
                final(self).position_model(), result),
            result !is Finished ==> definition_position_progress(old(self).project_model(),
                old(self).position_model(), final(self).position_model()),
    {
        let at = self.at;
        let circuits = self.project.circuits();
        if at.file >= circuits.len() {
            return DefinitionPositionStep::Finished;
        }
        let parsed = &circuits[at.file];
        if at.entry >= parsed.entry_ranges.len() {
            self.at = DefinitionPosition { file: at.file + 1, entry: 0, definition: 0, reference: 0 };
            return DefinitionPositionStep::Advanced;
        }
        let ghost source = self.project.sources_model()[at.file as int];
        proof {
            parsed_index_evidence(source, *parsed);
            build_entry_ranges_evidence(source.text, &parsed.build_model(), at.entry as int);
        }
        let definitions = &parsed.entry_ranges[at.entry].definitions;
        if at.definition >= definitions.end - definitions.start {
            self.at = DefinitionPosition { entry: at.entry + 1, definition: 0, reference: 0, ..at };
            return DefinitionPositionStep::Advanced;
        }
        let _definition_count = parsed.definitions.len();
        assert(definitions.start + at.definition < _definition_count);
        let position = definitions.start + at.definition;
        let references = &parsed.definitions[position].references;
        proof { build_definition_scope_evidence(source.text, &parsed.build_model(), at.entry as int, position as int); }
        if at.reference >= references.end - references.start {
            self.at = DefinitionPosition { definition: at.definition + 1, reference: 0, ..at };
            return DefinitionPositionStep::Advanced;
        }
        self.at = DefinitionPosition { reference: at.reference + 1, ..at };
        DefinitionPositionStep::Reference(at)
    }
}

impl<'a> CircuitProject<'a> {
    /// 名前を解決せずに、プロジェクトの全定義参照を走査する。
    pub fn definition_positions<'p>(&'p self) -> (cursor: DefinitionPositions<'p, 'a>)
        requires self.has_parsed_sources(),
        ensures cursor.valid(), cursor.project_model() == self,
            cursor.position_model() == (DefinitionPosition { file: 0, entry: 0, definition: 0, reference: 0 }),
    {
        DefinitionPositions { project: self, at: DefinitionPosition { file: 0, entry: 0, definition: 0, reference: 0 } }
    }
}

} // verus!
