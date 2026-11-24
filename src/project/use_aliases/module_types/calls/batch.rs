//! モジュールの全断片から、元の定義と参照の順に呼び出しを検査する。

use super::{DefinitionPosition, ModuleBodyPosition, ModuleCallInputs, ModuleCallInputsError, ModuleOutputTypes,
    ModuleOutputTypesError, UseAliases};
use crate::syntax::circuit::ExpressionReferenceKind;
#[cfg(verus_only)]
use crate::project::{ModuleBody, circuits::{parsed_circuit_matches, parsed_index_evidence}};
#[cfg(verus_only)]
use crate::syntax::circuit::{build_definition_scope_evidence, build_entry_ranges_evidence};
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// モジュール内の呼び出し位置と入力の照合結果。
#[derive(Debug)]
pub struct CheckedModuleCall<'p, 'a> {
    /// 照合に使ったモジュール本体または断片の添字。
    pub member: usize,
    /// 呼び出し名が現れた元のファイル、本体、定義、参照の添字。
    pub at: DefinitionPosition,
    /// 参照先の署名と入力ごとの照合結果。
    pub inputs: ModuleCallInputs<'p, 'a>,
}

/// モジュール全体の型表と、全断片の呼び出しの照合結果。
#[derive(Debug)]
pub struct ModuleCalls<'p, 'a> {
    /// 配線、式、出力の検査結果。全呼び出しでこの型表を共有する。
    pub module: ModuleOutputTypes<'p, 'a>,
    /// 本体、断片、定義、参照の順に並んだ呼び出し。
    pub calls: Vec<CheckedModuleCall<'p, 'a>>,
}

/// モジュールの組み立てから呼び出しの照合までに見つかった違反。
#[derive(Debug)]
pub enum ModuleCallsError<'p, 'a> {
    /// 配線、式または出力の違反。
    Module(ModuleOutputTypesError<'p, 'a>),
    /// モジュールの型表を得た後、最初に見つかった呼び出しの違反。
    Call {
        /// 違反のある呼び出し名の元の位置。
        at: DefinitionPosition,
        /// 参照先の署名、入出力数または入力型の違反。
        reason: ModuleCallInputsError<'p, 'a>,
    },
}

spec fn before(a: (int, int, int), b: (int, int, int)) -> bool {
    a.0 < b.0 || a.0 == b.0 && (a.1 < b.1 || a.1 == b.1 && a.2 < b.2)
}

spec fn row_cursor(row: CheckedModuleCall) -> (int, int, int) {
    (row.member as int, row.at.definition as int, row.at.reference as int)
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// 全件検査の成功結果から、モジュールの型表を取り出す。
    pub(in crate::project::use_aliases::module_types) proof fn module_calls_type_evidence(
        &self, owner: ModuleBodyPosition, limit: u64, checked: &ModuleCalls,
    )
        requires self.module_calls_result(owner, limit, Ok(Some(*checked))),
        ensures self.module_output_types_result(owner, limit, Ok(Some(checked.module))),
    {
    }

    /// 全件検査の項目を元の断片と、その場所で選んだ呼び出し計画に対応付ける。
    pub(in crate::project::use_aliases::module_types) proof fn module_calls_item_evidence(
        &self, owner: ModuleBodyPosition, limit: u64, checked: &ModuleCalls, index: int,
    )
        requires self.module_calls_result(owner, limit, Ok(Some(*checked))), 0 <= index < checked.calls@.len(),
        ensures ({
            let row = checked.calls@[index];
            let members = checked.module.expressions.typed.sources.roots.wiring.drivers.body.members@;
            &&& row.member < members.len()
            &&& members[row.member as int] == (ModuleBodyPosition { file: row.at.file, entry: row.at.entry })
            &&& self.module_call_ports_result(row.at, limit, Ok(Some(row.inputs.ports)))
            &&& (row.inputs.ports.signature.target is Nor ==> self.module_nor_literals_fit(row.at, limit, &row.inputs))
        }),
    {
        reveal(UseAliases::module_calls_before);
        let row = checked.calls@[index];
        self.inferred_module_call_plan(&checked.module, row.at, limit, row.inputs);
    }

    /// 全件検査から、指定した実引数の型と要求ポートの照合を取り出す。
    pub(in crate::project::use_aliases::module_types) proof fn module_call_leaf(
        &self, owner: ModuleBodyPosition, limit: u64, checked: &ModuleCalls, index: usize, arg: usize,
        port: crate::project::CallPortType, driver: Option<crate::project::OutputDriver>,
    )
        requires
            self.can_resolve(), self.module_calls_result(owner, limit, Ok(Some(*checked))),
            index < checked.calls@.len(),
            ({
                let row = checked.calls@[index as int];
                arg < row.inputs.ports.arguments@.len()
                    && row.inputs.ports.signature.target.port_matches(crate::project::PortDirection::Input, arg, Some(port))
            }),
            driver matches Some(driver) ==> self.module_argument_binding(checked, index as int, arg as int, driver),
        ensures ({
            let row = checked.calls@[index as int];
            let forms = self.targets.project_model().circuits_model()[row.at.file as int].syntax.forms@;
            let form = forms[row.inputs.ports.arguments@[arg as int] as int];
            let result = row.inputs.types@[arg as int];
            &&& (exists|known: Option<crate::project::SignalType>| #[trigger]
                super::leaf_result(row.inputs.ports.signature.source, form, &port, known, limit, Ok(result)))
            &&& (driver matches Some(driver) ==> {
                let expressions = checked.module.expressions;
                result == super::bound_type(&expressions.typed, expressions.types@, driver)
                    && (result matches Some(signal) ==> crate::project::port_types_equal(signal.ty, port.ty))
            })
        }),
    {
        reveal(UseAliases::module_calls_before);
        self.inferred_call_leaf(owner, limit, checked, index, arg, port, driver);
    }

    /// 同じモジュールを組み立てる呼び出しが、互いに異なるソース位置を持つことを示す。
    pub(in crate::project::use_aliases::module_types) proof fn module_call_sites_distinct(
        &self, owner: ModuleBodyPosition, limit: u64, checked: &ModuleCalls, i: int, j: int,
    )
        requires self.can_resolve(), self.module_calls_result(owner, limit, Ok(Some(*checked))),
            0 <= i < j < checked.calls@.len(),
        ensures checked.calls@[i].at != checked.calls@[j].at,
    {
        reveal(UseAliases::module_calls_before);
        let a = checked.calls@[i];
        let b = checked.calls@[j];
        assert(before(row_cursor(a), row_cursor(b)));
        if a.at == b.at {
            assert(a.member < b.member);
            self.module_calls_type_evidence(owner, limit, checked);
            self.module_output_types_evidence(owner, limit, checked.module);
            self.module_selections_evidence(owner, limit, checked.module.expressions);
            let drivers = checked.module.expressions.typed.sources.roots.wiring.drivers;
            self.checked_module_driver_body(owner, limit, drivers);
            self.targets.module_body_members_distinct(&drivers.body, a.member as int, b.member as int);
            assert(drivers.body.members@[a.member as int] == drivers.body.members@[b.member as int]);
        }
    }

    spec fn module_call_body(module: &ModuleOutputTypes) -> ModuleBody {
        module.expressions.typed.sources.roots.wiring.drivers.body
    }

    spec fn member_site(body: &ModuleBody, cursor: (int, int, int)) -> DefinitionPosition {
        let position = body.members@[cursor.0];
        DefinitionPosition { file: position.file, entry: position.entry,
            definition: cursor.1 as usize, reference: cursor.2 as usize }
    }

    spec fn member_call(&self, body: &ModuleBody, cursor: (int, int, int)) -> bool {
        &&& 0 <= cursor.0 < body.members@.len()
        &&& 0 <= cursor.1 <= usize::MAX && 0 <= cursor.2 <= usize::MAX
        &&& self.module_call_at(Self::member_site(body, cursor))
    }

    #[verifier::opaque]
    spec fn module_calls_before(&self, module: &ModuleOutputTypes, limit: u64,
        cursor: (int, int, int), rows: Seq<CheckedModuleCall>,
    ) -> bool {
        let body = Self::module_call_body(module);
        &&& forall|site: (int, int, int)| #[trigger] self.member_call(&body, site) && before(site, cursor)
            ==> exists|i: int| 0 <= i < rows.len() && #[trigger] row_cursor(rows[i]) == site
        &&& forall|i: int| 0 <= i < rows.len() ==> {
            let row = #[trigger] rows[i];
            let site = row_cursor(row);
            &&& before(site, cursor)
            &&& self.member_call(&body, site)
            &&& row.at == Self::member_site(&body, site)
            &&& self.inferred_call(module, row.at, limit, Ok(Some(row.inputs)))
        }
        &&& forall|i: int, j: int| #![trigger row_cursor(rows[i]), row_cursor(rows[j])]
            0 <= i < j < rows.len() ==> before(row_cursor(rows[i]), row_cursor(rows[j]))
    }

    proof fn advance_module_calls(&self, module: &ModuleOutputTypes, limit: u64, old: (int, int, int),
        next: (int, int, int), rows: Seq<CheckedModuleCall>, added: Option<CheckedModuleCall>,
    )
        requires
            self.module_calls_before(module, limit, old, rows),
            before(old, next),
            ({
                let body = Self::module_call_body(module);
                forall|site: (int, int, int)| #[trigger] self.member_call(&body, site)
                    && before(site, next) && !before(site, old) ==> added.is_some() && site == old
            }),
            added matches Some(row) ==> {
                let body = Self::module_call_body(module);
                &&& row_cursor(row) == old
                &&& self.member_call(&body, old)
                &&& row.at == Self::member_site(&body, old)
                &&& self.inferred_call(module, row.at, limit, Ok(Some(row.inputs)))
            },
        ensures self.module_calls_before(module, limit, next, match added { Some(row) => rows.push(row), None => rows }),
    {
        reveal(UseAliases::module_calls_before);
        let body = Self::module_call_body(module);
        let new_rows = match added { Some(row) => rows.push(row), None => rows };
        assert forall|site: (int, int, int)| #[trigger] self.member_call(&body, site) && before(site, next) implies
            exists|i: int| 0 <= i < new_rows.len() && #[trigger] row_cursor(new_rows[i]) == site by {
            if before(site, old) {
                let i = choose|i: int| 0 <= i < rows.len() && #[trigger] row_cursor(rows[i]) == site;
                assert(new_rows[i] == rows[i]);
            } else {
                assert(added.is_some() && site == old);
                assert(row_cursor(new_rows[rows.len() as int]) == site);
            }
        };
        assert forall|i: int| 0 <= i < new_rows.len() implies {
            let row = #[trigger] new_rows[i];
            let site = row_cursor(row);
            before(site, next) && self.member_call(&body, site) && row.at == Self::member_site(&body, site)
                && self.inferred_call(module, row.at, limit, Ok(Some(row.inputs)))
        } by {
            if i < rows.len() { assert(new_rows[i] == rows[i]); }
        };
        assert forall|i: int, j: int| #![trigger row_cursor(new_rows[i]), row_cursor(new_rows[j])]
            0 <= i < j < new_rows.len() implies before(row_cursor(new_rows[i]), row_cursor(new_rows[j])) by {
            assert(new_rows[i] == rows[i]);
            if j < rows.len() { assert(new_rows[j] == rows[j]); }
        };
    }

    /// 全呼び出しの網羅と順序、または先行する照合がすべて通った時点での診断を表す。
    pub closed spec fn module_calls_result(&self, owner: ModuleBodyPosition, limit: u64,
        result: Result<Option<ModuleCalls>, ModuleCallsError>,
    ) -> bool {
        match result {
            Ok(None) => self.module_output_types_result(owner, limit, Ok(None)),
            Ok(Some(checked)) => self.module_output_types_result(owner, limit, Ok(Some(checked.module)))
                && self.module_calls_before(&checked.module, limit,
                    (Self::module_call_body(&checked.module).members@.len() as int, 0, 0), checked.calls@),
            Err(ModuleCallsError::Module(error)) => self.module_output_types_result(owner, limit, Err(error)),
            Err(ModuleCallsError::Call { at, reason }) => exists|module: ModuleOutputTypes, member: int, rows: Seq<CheckedModuleCall>|
                #[trigger] self.module_calls_failure_evidence(owner, limit, &module, at, member, rows, reason),
        }
    }

    #[verifier::opaque]
    spec fn module_calls_failure_evidence(&self, owner: ModuleBodyPosition, limit: u64, module: &ModuleOutputTypes,
        at: DefinitionPosition, member: int, rows: Seq<CheckedModuleCall>, reason: ModuleCallInputsError,
    ) -> bool {
        let cursor = (member, at.definition as int, at.reference as int);
        let body = Self::module_call_body(module);
        &&& self.module_output_types_result(owner, limit, Ok(Some(*module)))
        &&& self.member_call(&body, cursor) && Self::member_site(&body, cursor) == at
        &&& self.module_calls_before(module, limit, cursor, rows)
        &&& self.inferred_call(module, at, limit, Err(reason))
    }

    proof fn module_calls_failure(&self, owner: ModuleBodyPosition, limit: u64, module: &ModuleOutputTypes,
        at: DefinitionPosition, member: int, rows: Seq<CheckedModuleCall>, reason: ModuleCallInputsError,
    )
        requires
            self.module_output_types_result(owner, limit, Ok(Some(*module))),
            ({
                let cursor = (member, at.definition as int, at.reference as int);
                let body = Self::module_call_body(module);
                &&& self.member_call(&body, cursor) && Self::member_site(&body, cursor) == at
                &&& self.module_calls_before(module, limit, cursor, rows)
            }),
            self.inferred_call(module, at, limit, Err(reason)),
        ensures self.module_calls_result(owner, limit, Err(ModuleCallsError::Call { at, reason })),
    {
        assert(self.module_calls_failure_evidence(owner, limit, &*module, at, member, rows, reason)) by {
            reveal(UseAliases::module_calls_failure_evidence);
        };
        assert(exists|snapshot: ModuleOutputTypes, i: int, prefix: Seq<CheckedModuleCall>|
            #[trigger] self.module_calls_failure_evidence(owner, limit, &snapshot, at, i, prefix, reason));
        reveal(UseAliases::module_calls_result);
        let result = Err::<Option<ModuleCalls>, ModuleCallsError>(ModuleCallsError::Call { at, reason });
        assert(result matches Err(ModuleCallsError::Call { at: site, reason: cause }) && site == at && cause == reason);
        assert(self.module_calls_result(owner, limit, result));
    }

    /// 型表を一度作り、モジュール本体と全断片にある呼び出しを照合する。
    ///
    /// 定義の右辺の中にある子の呼び出しも検査する。各呼び出しでは型が判明した信号と定数、
    /// 子の通常呼び出しの出力型を照合する。型が未確定の信号と子式は保留する。
    /// 子の署名や入出力数に違反があれば、その子を検査する順番で診断する。
    /// 位置がモジュールを指さなければ `None` を返す。
    ///
    /// # Errors
    ///
    /// 配線、式、出力の検査を先に行う。その後、本体、断片、定義、参照の順に最初の違反を返す。
    pub fn check_module_calls(&self, owner: ModuleBodyPosition, limit: u64)
        -> (result: Result<Option<ModuleCalls<'p, 'a>>, ModuleCallsError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.module_calls_result(owner, limit, result),
    {
        let module = match self.check_module_output_types(owner, limit) {
            Ok(Some(module)) => module,
            Ok(None) => return Ok(None),
            Err(error) => return Err(ModuleCallsError::Module(error)),
        };
        let drivers = &module.expressions.typed.sources.roots.wiring.drivers;
        let body = &drivers.body;
        proof {
            self.module_output_types_evidence(owner, limit, module);
            self.module_selections_evidence(owner, limit, module.expressions);
            self.checked_module_driver_body(owner, limit, *drivers);
        }
        let project = self.targets.project();
        let mut rows = Vec::new();
        let mut member = 0;
        assert(self.module_calls_before(&module, limit, (0, 0, 0), rows@)) by {
            reveal(UseAliases::module_calls_before);
        };
        while member < body.members.len()
            invariant
                self.can_resolve(), *project == self.targets.project_model(), project.has_parsed_sources(),
                self.module_output_types_result(owner, limit, Ok(Some(module))),
                *body == Self::module_call_body(&module), body.owner == owner,
                self.targets.module_body_result(owner, Ok(Some(*body))),
                member <= body.members@.len(),
                self.module_calls_before(&module, limit, (member as int, 0, 0), rows@),
            decreases body.members@.len() - member,
        {
            let position = body.members[member];
            proof { self.targets.module_body_member(body, member as int); }
            let parsed = &project.circuits()[position.file];
            let ghost source = project.sources_model()[position.file as int];
            let ghost model = parsed.build_model();
            proof {
                parsed_index_evidence(source, *parsed);
                build_entry_ranges_evidence(source.text, &model, position.entry as int);
            }
            let frame = &parsed.entry_ranges[position.entry];
            let mut definition = 0;
            while definition < frame.definitions.end - frame.definitions.start
                invariant
                    self.can_resolve(), *project == self.targets.project_model(),
                    self.module_output_types_result(owner, limit, Ok(Some(module))),
                    *body == Self::module_call_body(&module), body.owner == owner,
                    self.targets.module_body_result(owner, Ok(Some(*body))),
                    member < body.members@.len(), position == body.members@[member as int],
                    position.file < project.circuits_model().len(), position.file < project.sources_model().len(),
                    *parsed == project.circuits_model()[position.file as int], source == project.sources_model()[position.file as int],
                    model == parsed.build_model(), parsed_circuit_matches(source, *parsed),
                    position.entry < parsed.entry_ranges@.len(), position.entry < parsed.syntax.entries@.len(),
                    parsed.syntax.entries@[position.entry as int].head is Module
                        || parsed.syntax.entries@[position.entry as int].head is ModulePart,
                    *frame == parsed.entry_ranges@[position.entry as int],
                    frame.definitions.start <= frame.definitions.end <= parsed.definitions@.len(),
                    definition <= frame.definitions.end - frame.definitions.start,
                    self.module_calls_before(&module, limit, (member as int, definition as int, 0), rows@),
                decreases frame.definitions.end - frame.definitions.start - definition,
            {
                let index = frame.definitions.start + definition;
                proof {
                    parsed_index_evidence(source, *parsed);
                    build_definition_scope_evidence(source.text, &model, position.entry as int, index as int);
                }
                let row = &parsed.definitions[index];
                let mut reference = 0;
                while reference < row.references.end - row.references.start
                    invariant
                        self.can_resolve(), self.module_output_types_result(owner, limit, Ok(Some(module))),
                        *body == Self::module_call_body(&module), member < body.members@.len(),
                        position == body.members@[member as int],
                        position.file < self.targets.project_model().circuits_model().len(),
                        *parsed == self.targets.project_model().circuits_model()[position.file as int],
                        position.entry < parsed.entry_ranges@.len(), position.entry < parsed.syntax.entries@.len(),
                        parsed.syntax.entries@[position.entry as int].head is Module
                            || parsed.syntax.entries@[position.entry as int].head is ModulePart,
                        *frame == parsed.entry_ranges@[position.entry as int],
                        index == frame.definitions.start + definition,
                        frame.definitions.start <= index < frame.definitions.end <= parsed.definitions@.len(),
                        *row == parsed.definitions@[index as int],
                        row.references.start <= row.references.end <= parsed.references@.len(),
                        reference <= row.references.end - row.references.start,
                        self.module_calls_before(&module, limit, (member as int, definition as int, reference as int), rows@),
                    decreases row.references.end - row.references.start - reference,
                {
                    let at = DefinitionPosition { file: position.file, entry: position.entry, definition, reference };
                    let ghost cursor = (member as int, definition as int, reference as int);
                    let ghost next = (member as int, definition as int, reference + 1);
                    if matches!(parsed.references[row.references.start + reference].kind, ExpressionReferenceKind::Callee) {
                        assert(self.member_call(body, cursor));
                        let inputs = match self.check_inferred_call_in_member(owner, &module, member, at, limit) {
                            Ok(Some(inputs)) => inputs,
                            Ok(None) => {
                                proof { assert(false); }
                                unreachable!()
                            },
                            Err(reason) => {
                                assert(Self::member_site(body, cursor) == at);
                                proof { self.module_calls_failure(owner, limit, &module, at, member as int, rows@, reason); }
                                return Err(ModuleCallsError::Call { at, reason });
                            },
                        };
                        let call = CheckedModuleCall { member, at, inputs };
                        proof { self.advance_module_calls(&module, limit, cursor, next, rows@, Some(call)); }
                        rows.push(call);
                    } else {
                        proof { self.advance_module_calls(&module, limit, cursor, next, rows@, None); }
                    }
                    reference += 1;
                }
                proof {
                    self.advance_module_calls(&module, limit, (member as int, definition as int, reference as int),
                        (member as int, definition + 1, 0), rows@, None);
                }
                definition += 1;
            }
            proof {
                self.advance_module_calls(&module, limit, (member as int, definition as int, 0),
                    (member + 1, 0, 0), rows@, None);
            }
            member += 1;
        }
        Ok(Some(ModuleCalls { module, calls: rows }))
    }
}

} // verus!
