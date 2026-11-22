//! モジュール断片の対象と、断片が元から属する位置を対応付ける。

mod body;
pub use body::{ModuleBody, ModuleDefinition};

use super::{AbsoluteTarget, LocatedName, ProjectSource, UseTargets, declarations::key_of};
use crate::syntax::circuit::{Head, NamedForm, named_build_entry};
#[cfg(verus_only)]
use super::{
    circuits::parsed_index_evidence, declarations::{declaration_key_evidence, form_key},
    parsed_circuit_matches, resolution::selected_direct_target_matches,
};
use vstd::prelude::*;
use alloc::vec::Vec;

verus! {

/// 解析済みプロジェクト内の回路本体の位置。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ModuleBodyPosition {
    /// プロジェクトのソース配列の添字。
    pub file: usize,
    /// そのファイルの厳格索引の添字。
    pub entry: usize,
}

/// モジュール断片と、その結線を受け取るモジュール。
#[derive(Debug)]
pub struct ModulePartBinding<'p, 'a> {
    /// 断片の別名を解決するときに使うファイル。
    pub part_source: &'p ProjectSource<'a>,
    /// 断片のフォームと、その別名スコープを特定する名前空間ブロック。
    pub part: &'p NamedForm<'a>,
    /// 断片の定義や参照を取り出すための厳格索引の位置。
    pub part_position: ModuleBodyPosition,
    /// 断片のファイル内の名前索引の添字。
    pub part_name: usize,
    /// ポートを宣言したモジュールのファイル。
    pub module_source: &'p ProjectSource<'a>,
    /// 結線を受け取るモジュールのフォーム。
    pub module: &'p NamedForm<'a>,
    /// モジュールのポートと本体を取り出すための厳格索引の位置。
    pub module_position: ModuleBodyPosition,
}

spec fn body_position_matches(
    project: &super::CircuitProject, position: ModuleBodyPosition, source: &ProjectSource, form: &NamedForm,
) -> bool {
    let circuits = project.circuits_model();
    let sources = project.sources_model();
    let entries = circuits[position.file as int].syntax.entries@;
    &&& position.file < sources.len() && position.file < circuits.len()
    &&& sources[position.file as int] == *source
    &&& position.entry < entries.len()
    &&& entries[position.entry as int].form == form.form && entries[position.entry as int].head == form.head
}

/// モジュール断片の対象を確定できなかった理由。
#[derive(Debug)]
pub enum ModulePartError<'p, 'a> {
    /// ファイル番号または名前索引の添字が範囲外。
    InvalidPosition,
    /// 指定位置がモジュール断片を指していない。
    ExpectedPart(LocatedName<'p, 'a>),
    /// 同じ名前空間に対象名の宣言も子名前空間もない。
    MissingModule(LocatedName<'p, 'a>),
    /// 対象名が別の種別の宣言または子名前空間を指す。
    WrongTarget {
        /// モジュール断片で指定した名前。
        part: LocatedName<'p, 'a>,
        /// 対象名の宣言または子名前空間の導入位置。
        target: LocatedName<'p, 'a>,
        /// 対象名が指した種別。
        head: Head,
    },
}

/// プロジェクト順で最初に所有先を確定できなかったモジュール断片。
#[derive(Debug)]
pub struct ModulePartsError<'p, 'a> {
    /// 断片があるファイルの添字。
    pub file: usize,
    /// そのファイルの名前索引で断片を指す添字。
    pub name: usize,
    /// 対象名に対する診断。
    pub diagnostic: ModulePartError<'p, 'a>,
}

spec fn before(file: int, name: int, limit_file: int, limit_name: int) -> bool {
    file < limit_file || file == limit_file && name < limit_name
}

impl<'p, 'a> UseTargets<'p, 'a> {
    /// 指定した索引位置から、断片と同じ名前空間にある対象を直接検索した結果を表す。
    pub closed spec fn module_part_resolution(
        &self, file: usize, index: usize, result: Result<ModulePartBinding<'p, 'a>, ModulePartError<'p, 'a>>,
    ) -> bool {
        let project = self.project_model();
        let sources = project.sources_model();
        let circuits = project.circuits_model();
        if file >= circuits.len() || file >= sources.len() || index >= circuits[file as int].names@.len() {
            result == Err(ModulePartError::InvalidPosition)
        } else {
            let part = &circuits[file as int].names@[index as int];
            let source = &sources[file as int];
            let site = LocatedName { source, span: part.name.span };
            if part.head != Head::ModulePart {
                result == Err(ModulePartError::ExpectedPart(site))
            } else {
                let key = form_key(*part);
                let declarations = self.exports_model().declarations_model();
                match result {
                    Ok(binding) => binding.part == part && binding.part_source == source
                        && binding.module.head == Head::Module
                        && binding.part_position.file == file
                        && binding.part_name == index
                        && body_position_matches(&project, binding.part_position, source, part)
                        && body_position_matches(&project, binding.module_position, binding.module_source, binding.module)
                        && selected_direct_target_matches(&declarations, key, Some(AbsoluteTarget::Declaration {
                            source: binding.module_source, form: binding.module,
                        })),
                    Err(ModulePartError::MissingModule(location)) => location == site
                        && selected_direct_target_matches(&declarations, key, None),
                    Err(ModulePartError::WrongTarget { part: location, target, head }) => location == site && {
                        if head == Head::Namespace {
                            selected_direct_target_matches(&declarations, key, Some(AbsoluteTarget::Namespace {
                                key, introduced_at: target,
                            }))
                        } else {
                            head != Head::Module && exists|form: &NamedForm| form.head == head
                                && form.name.span == target.span
                                && #[trigger] declarations.declaration_at(key, target.source, form)
                        }
                    },
                    _ => false,
                }
            }
        }
    }

    /// ファイル番号と名前索引の添字で断片を指定し、同じ名前空間のモジュールを探す。
    ///
    /// 断片の対象名は直接検索する。返した断片のファイルとブロックは本文の名前解決に使える。
    ///
    /// # Errors
    ///
    /// 位置が範囲外か、指定位置が断片を指さない場合に診断する。
    /// 対象名が未定義の場合や、別の種別の宣言または子名前空間を指す場合にも診断する。
    pub fn resolve_module_part(
        &self, file: usize, index: usize,
    ) -> (result: Result<ModulePartBinding<'p, 'a>, ModulePartError<'p, 'a>>)
        requires self.covers_project(),
        ensures self.module_part_resolution(file, index, result),
    {
        let project = self.project();
        let sources = project.sources();
        let circuits = project.circuits();
        if file >= circuits.len() || file >= sources.len() {
            return Err(ModulePartError::InvalidPosition);
        }
        let source = &sources[file];
        let names = &circuits[file].names;
        if index >= names.len() {
            return Err(ModulePartError::InvalidPosition);
        }
        let part = &names[index];
        let site = LocatedName { source, span: part.name.span.start..part.name.span.end };
        if !matches!(part.head, Head::ModulePart) {
            return Err(ModulePartError::ExpectedPart(site));
        }
        let declarations = self.exports().declarations();
        proof { self.declarations_cover_project(); }
        let key = key_of(part);
        match declarations.direct_target(key) {
            Some(AbsoluteTarget::Declaration { source: module_source, form: module }) => {
                if matches!(module.head, Head::Module) {
                    let (module_file, module_name) = declarations.selected_declaration_position(
                        key, Ghost(*project), Ghost(*module_source), Ghost(*module));
                    proof {
                        assert(parsed_circuit_matches(*source, circuits@[file as int]));
                        parsed_index_evidence(*source, circuits@[file as int]);
                        assert(parsed_circuit_matches(*module_source, circuits@[module_file as int]));
                        parsed_index_evidence(*module_source, circuits@[module_file as int]);
                    }
                    let part_entry = named_build_entry(source.text, &circuits[file], index);
                    let module_entry = named_build_entry(module_source.text, &circuits[module_file], module_name);
                    Ok(ModulePartBinding {
                        part_source: source, part, part_position: ModuleBodyPosition { file, entry: part_entry },
                        part_name: index,
                        module_source, module, module_position: ModuleBodyPosition { file: module_file, entry: module_entry },
                    })
                } else {
                    let target = LocatedName { source: module_source, span: module.name.span.start..module.name.span.end };
                    proof {
                        declaration_key_evidence(declarations, key, module_source, module);
                        assert(exists|form: &NamedForm| form.head == module.head
                            && form.name.span == target.span
                            && #[trigger] declarations.declaration_at(key, target.source, form));
                    }
                    Err(ModulePartError::WrongTarget { part: site, target, head: module.head })
                }
            },
            Some(AbsoluteTarget::Namespace { introduced_at, .. }) =>
                Err(ModulePartError::WrongTarget { part: site, target: introduced_at, head: Head::Namespace }),
            None => Err(ModulePartError::MissingModule(site)),
        }
    }

    spec fn has_part(&self, file: int, name: int) -> bool {
        let circuits = self.project_model().circuits_model();
        &&& 0 <= file < circuits.len()
        &&& 0 <= name < circuits[file].names@.len()
        &&& circuits[file].names@[name].head is ModulePart
    }

    #[verifier::opaque]
    spec fn bindings_before(&self, rows: Seq<ModulePartBinding>, file: int, name: int) -> bool {
        &&& forall|i: int| 0 <= i < rows.len() ==> {
            let row = #[trigger] rows[i];
            let f = row.part_position.file;
            let p = row.part_name;
            &&& self.has_part(f as int, p as int) && before(f as int, p as int, file, name)
            &&& self.module_part_resolution(f, p, Ok(row))
        }
        &&& forall|f: int, p: int| #[trigger] self.has_part(f, p) && before(f, p, file, name) ==>
            exists|i: int| 0 <= i < rows.len() && (#[trigger] rows[i]).part_position.file == f && rows[i].part_name == p
        &&& forall|i: int, j: int| 0 <= i < j < rows.len() ==> {
            let left = #[trigger] rows[i];
            let right = #[trigger] rows[j];
            before(left.part_position.file as int, left.part_name as int, right.part_position.file as int, right.part_name as int)
        }
    }

    proof fn extend_bindings(
        &self, old: Seq<ModulePartBinding>, file: usize, name: usize, row: Option<ModulePartBinding>,
    ) -> (next: Seq<ModulePartBinding>)
        requires
            self.bindings_before(old, file as int, name as int),
            row.is_some() == self.has_part(file as int, name as int),
            row matches Some(part) ==> part.part_position.file == file && part.part_name == name
                && self.module_part_resolution(file, name, Ok(part)),
        ensures
            next == match row { Some(part) => old.push(part), None => old },
            self.bindings_before(next, file as int, name + 1),
    {
        reveal(UseTargets::bindings_before);
        let next = match row { Some(part) => old.push(part), None => old };
        assert forall|i: int| 0 <= i < next.len() implies {
            let part = #[trigger] next[i];
            let f = part.part_position.file;
            let p = part.part_name;
            &&& self.has_part(f as int, p as int) && before(f as int, p as int, file as int, name + 1)
            &&& self.module_part_resolution(f, p, Ok(part))
        } by {
            if i < old.len() { assert(next[i] == old[i]); }
        };
        assert forall|f: int, p: int| #[trigger] self.has_part(f, p) && before(f, p, file as int, name + 1) implies
            exists|i: int| 0 <= i < next.len() && (#[trigger] next[i]).part_position.file == f && next[i].part_name == p by {
            if before(f, p, file as int, name as int) {
                let i = choose|i: int| 0 <= i < old.len() && (#[trigger] old[i]).part_position.file == f && old[i].part_name == p;
                assert(next[i] == old[i]);
            } else {
                assert(f == file && p == name);
                assert(next[old.len() as int] == row->Some_0);
            }
        };
        assert forall|i: int, j: int| 0 <= i < j < next.len() implies {
            let left = #[trigger] next[i];
            let right = #[trigger] next[j];
            before(left.part_position.file as int, left.part_name as int, right.part_position.file as int, right.part_name as int)
        } by {
            assert(next[i] == old[i]);
            if j < old.len() { assert(next[j] == old[j]); }
        };
        next
    }

    proof fn complete_bindings_file(&self, rows: Seq<ModulePartBinding>, file: usize, count: usize)
        requires
            file < self.project_model().circuits_model().len(),
            count == self.project_model().circuits_model()[file as int].names@.len(),
            self.bindings_before(rows, file as int, count as int),
        ensures self.bindings_before(rows, file + 1, 0),
    {
        reveal(UseTargets::bindings_before);
        assert forall|f: int, p: int| #[trigger] self.has_part(f, p) implies
            before(f, p, file as int, count as int) == before(f, p, file + 1, 0) by {};
    }

    /// 収集結果が全断片をソース順に含むか、最初に失敗した断片を示すことを表す。
    pub closed spec fn module_parts_result(
        &self, result: Result<Vec<ModulePartBinding<'p, 'a>>, ModulePartsError<'p, 'a>>,
    ) -> bool {
        match result {
            Ok(parts) => self.bindings_before(parts@, self.project_model().circuits_model().len() as int, 0),
            Err(error) => self.has_part(error.file as int, error.name as int)
                && self.module_part_resolution(error.file, error.name, Err(error.diagnostic))
                && (exists|prior: Seq<ModulePartBinding>| #[trigger] self.bindings_before(prior, error.file as int, error.name as int)),
        }
    }

    /// プロジェクト内の全断片を、その所有モジュールに対応付けてソース順に返す。
    ///
    /// # Errors
    ///
    /// 所有先が見つからないか種別が異なるときは、最初に見つかった断片の診断を返す。
    pub fn collect_module_parts(&self) -> (result: Result<Vec<ModulePartBinding<'p, 'a>>, ModulePartsError<'p, 'a>>)
        requires self.covers_project(),
        ensures self.module_parts_result(result),
    {
        let circuits = self.project().circuits();
        let mut rows = Vec::new();
        let mut file = 0;
        assert(self.bindings_before(rows@, 0, 0)) by { reveal(UseTargets::bindings_before); };
        while file < circuits.len()
            invariant
                self.covers_project(), circuits@ == self.project_model().circuits_model(),
                file <= circuits@.len(), self.bindings_before(rows@, file as int, 0),
            decreases circuits@.len() - file,
        {
            let names = circuits[file].names.as_slice();
            let mut name = 0;
            while name < names.len()
                invariant
                    self.covers_project(), circuits@ == self.project_model().circuits_model(), file < circuits@.len(),
                    names@ == circuits@[file as int].names@, name <= names@.len(),
                    self.bindings_before(rows@, file as int, name as int),
                decreases names@.len() - name,
            {
                let ghost old = rows@;
                if matches!(names[name].head, Head::ModulePart) {
                    let row = match self.resolve_module_part(file, name) {
                        Ok(row) => row,
                        Err(diagnostic) => return Err(ModulePartsError { file, name, diagnostic }),
                    };
                    proof {
                        reveal(UseTargets::module_part_resolution);
                        self.extend_bindings(old, file, name, Some(row));
                    }
                    rows.push(row);
                } else {
                    proof { self.extend_bindings(old, file, name, None); }
                }
                name += 1;
            }
            proof { self.complete_bindings_file(rows@, file, name); }
            file += 1;
        }
        Ok(rows)
    }
}

} // verus!
