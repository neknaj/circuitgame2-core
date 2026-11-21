//! 通常呼び出しが返す型を、定義の左辺の名前順に対応付ける。

use super::{FuncArityError, FuncCallArity, FuncCallSignatureError, FuncCallTarget, UseAliases};
use super::typed::{cached_signature, signature_port};
#[cfg(verus_only)]
use super::typed::{cached_call_available, cached_call_model};
use super::super::signature_cache::SignatureCache;
#[cfg(verus_only)]
use super::{FuncCallSignature, TypedFuncCall};
use super::super::function_atoms::copy_location;
use super::super::function_drivers::name_location;
#[cfg(verus_only)]
use super::super::function_drivers::{expected_output_context, indexed_driver_site, same_definition_driver};
use super::super::function_literals::index_outputs;
#[cfg(verus_only)]
use super::super::function_literals::{output_indices, output_indices_agree};
use crate::project::{FuncWiring, FuncWiringResult, LocatedName, PortDirection, ProjectSource, SignalType};
use crate::project::circuits::form_location;
#[cfg(verus_only)]
use crate::project::{FuncDrivers, TypedPort, location_in_source, port_types_equal, ResolvedPortType, circuits::{
    is_form_location, parsed_circuit_matches, parsed_index_evidence,
}};
use crate::syntax::circuit::{NamedBuildCircuit, definition_root_is_call, definition_target_atoms};
#[cfg(verus_only)]
use crate::syntax::circuit::{
    build_definition_scope_evidence, build_entry_ranges_evidence, definition_target_range, indexed_call_arguments, ordinary_call_at,
};
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// 関数の配線と、通常呼び出しが直接駆動する信号の型。
#[derive(Debug)]
pub struct FuncCallOutputTypes<'p, 'a> {
    /// 前段の配線と入出力数の検査結果。対象外や展開待ちも保持する。
    pub wiring: FuncWiringResult<'p, 'a>,
    /// 駆動元の左辺一覧と同じ順に並ぶ型。
    /// 右辺全体が通常呼び出しである定義には出力型を置き、それ以外には `None` を置く。
    /// 対象外や展開待ちでは空になる。
    pub types: Vec<Option<SignalType<'p, 'a>>>,
}

/// 右辺全体を占める関数呼び出しと、その出力を受け取る左辺の位置。
#[derive(Debug)]
pub(in crate::project::use_aliases) struct RootFunctionCall {
    pub(in crate::project::use_aliases) definition: usize,
    pub(in crate::project::use_aliases) first_output: usize,
    pub(in crate::project::use_aliases) count: usize,
    pub(in crate::project::use_aliases) target_file: usize,
    pub(in crate::project::use_aliases) target_entry: usize,
}

/// 通常呼び出しの出力を左辺または出力ポートに対応付けられなかった理由。
#[derive(Debug)]
pub enum FuncCallOutputError<'p, 'a> {
    /// 呼び出し元の配線または入出力数の検査で見つかった違反。
    Caller(FuncArityError<'p, 'a>),
    /// 右辺全体を占める呼び出しの署名を解決できない。
    Signature(FuncCallSignatureError<'p, 'a>),
    /// 型付き署名を得た後の照合で、出力数と左辺の名前の数が一致しなかった。
    Count {
        /// 呼び出し式の元ソース範囲。
        call: LocatedName<'p, 'a>,
        /// 左辺が受け取る出力の数。
        targets: usize,
        /// 署名が返す出力の数。
        outputs: usize,
    },
    /// 左辺を通して駆動する出力ポートの宣言型と、呼び出しが返した型が異なる。
    OutputType {
        /// 型が一致しなかった左辺の名前。
        target: LocatedName<'p, 'a>,
        /// その値を返す呼び出し式。
        call: LocatedName<'p, 'a>,
        /// 呼び出し元が要求する型と、その注釈位置。
        expected: SignalType<'p, 'a>,
        /// 呼び出しが返す型と、その注釈位置。基底 NOR では呼び出し式を指す。
        actual: SignalType<'p, 'a>,
    },
}

spec fn call_output_type<'p, 'a>(
    call: &TypedFuncCall<'p, 'a>, expression: &LocatedName<'p, 'a>, index: int,
) -> SignalType<'p, 'a> {
    match call.signature {
        FuncCallSignature::Nor => SignalType { ty: ResolvedPortType::Bits(1), origin: *expression },
        FuncCallSignature::Function(signature) => {
            let port = signature.outputs@[index];
            SignalType { ty: port.ty, origin: port.annotation }
        },
    }
}

spec fn output_transfer(
    actual: SignalType, expected: Option<TypedPort>, target: LocatedName, call: LocatedName,
    result: Result<Option<SignalType>, FuncCallOutputError>,
) -> bool {
    if let Some(port) = expected {
        if !port_types_equal(actual.ty, port.ty) {
            result == Err(FuncCallOutputError::OutputType {
                target, call, expected: SignalType { ty: port.ty, origin: port.annotation }, actual,
            })
        } else { result == Ok(Some(actual)) }
    } else { result == Ok(Some(actual)) }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    #[verifier::opaque]
    spec fn is_function_call_start(
        &self, caller: (usize, usize, u64), drivers: &FuncDrivers, at: int,
    ) -> bool {
        let (file, entry, limit) = caller;
        let parsed = &self.targets.project_model().circuits_model()[file as int];
        let driver = drivers.definitions@[at];
        let local = (driver.definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
        &&& driver.result_index == 0
        &&& exists|call: TypedFuncCall|
            #[trigger] self.root_output_signature(file, entry, local, limit, Ok(Some(call)))
            && call.call.target is Function
    }

    #[verifier::opaque]
    spec fn root_function_call_matches(
        &self, caller: (usize, usize, u64), drivers: &FuncDrivers, row: RootFunctionCall,
    ) -> bool {
        let (file, entry, limit) = caller;
        let parsed = &self.targets.project_model().circuits_model()[file as int];
        let local = (row.definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
        &&& 0 < row.count && row.first_output + row.count <= drivers.definitions@.len()
        &&& forall|i: int| 0 <= i < row.count ==> {
            let driver = #[trigger] drivers.definitions@[row.first_output + i];
            driver.definition == row.definition && driver.result_index == i
        }
        &&& exists|call: TypedFuncCall|
            #[trigger] self.root_output_signature(file, entry, local, limit, Ok(Some(call)))
            && (call.call.target matches FuncCallTarget::Function { file: target_file, entry: target_entry, arity, .. }
                && target_file == row.target_file && target_entry == row.target_entry && arity.outputs == row.count)
    }

    pub(in crate::project::use_aliases) closed spec fn root_function_calls_match(
        &self, caller: (usize, usize, u64), drivers: &FuncDrivers, rows: Seq<RootFunctionCall>, processed: nat,
    ) -> bool {
        &&& processed <= drivers.definitions@.len()
        &&& forall|j: int| 0 <= j < rows.len() ==> {
            let row = #[trigger] rows[j];
            &&& row.first_output < processed
            &&& self.root_function_call_matches(caller, drivers, row)
        }
        &&& forall|a: int, b: int| 0 <= a < b < rows.len()
            ==> (#[trigger] rows[a]).first_output < (#[trigger] rows[b]).first_output
        &&& forall|i: int| 0 <= i < processed && #[trigger] self.is_function_call_start(caller, drivers, i)
            ==> exists|j: int| 0 <= j < rows.len() && (#[trigger] rows[j]).first_output == i
    }

    pub(in crate::project::use_aliases) open spec fn root_call_definitions_in_order(
        &self, file: usize, entry: usize, rows: Seq<RootFunctionCall>,
    ) -> bool {
        let parsed = &self.targets.project_model().circuits_model()[file as int];
        let definitions = parsed.entry_ranges@[entry as int].definitions;
        &&& forall|i: int| 0 <= i < rows.len() ==> {
            let call = #[trigger] rows[i];
            &&& definitions.start <= call.definition < definitions.end
            &&& parsed.definitions@[call.definition as int].references.start
                < parsed.definitions@[call.definition as int].references.end
        }
        &&& forall|i: int, j: int| 0 <= i < j < rows.len()
            ==> (#[trigger] rows[i]).definition < (#[trigger] rows[j]).definition
        &&& forall|i: int, j: int| 0 <= i < j < rows.len()
            ==> (#[trigger] rows[i]).first_output + rows[i].count <= (#[trigger] rows[j]).first_output
    }

    /// 保持した呼び出しが、参照を持つ定義の順に一度ずつ並ぶことを示す。
    pub(in crate::project::use_aliases) proof fn root_calls_follow_definition_order(
        &self, caller: (usize, usize, u64), wiring: &FuncWiring, rows: Seq<RootFunctionCall>,
    )
        requires
            self.can_resolve(),
            self.func_wiring_evidence(caller.0, caller.1, caller.2, Ok(FuncWiringResult::Checked(*wiring))),
            self.root_function_calls_match(caller, &wiring.drivers, rows, wiring.drivers.definitions@.len()),
        ensures self.root_call_definitions_in_order(caller.0, caller.1, rows),
    {
        let (file, entry, limit) = caller;
        self.checked_wiring_is_func(file, entry, limit, *wiring);
        let project = self.targets.project_model();
        let source = &project.sources_model()[file as int];
        let parsed = &project.circuits_model()[file as int];
        let definitions = parsed.entry_ranges@[entry as int].definitions;
        let drivers = wiring.drivers.definitions@;
        reveal(UseAliases::root_function_call_matches);
        reveal(UseAliases::root_output_signature);
        assert forall|i: int| 0 <= i < rows.len() implies {
            let row = #[trigger] rows[i];
            &&& 0 <= row.first_output < drivers.len()
            &&& drivers[row.first_output as int].definition == row.definition
            &&& drivers[row.first_output as int].result_index == 0
            &&& definitions.start <= row.definition < definitions.end
            &&& parsed.definitions@[row.definition as int].references.start
                < parsed.definitions@[row.definition as int].references.end
        } by {
            let row = rows[i];
            assert(self.root_function_call_matches(caller, &wiring.drivers, row));
            assert(row.count > 0);
            let first = drivers[row.first_output as int];
            assert(drivers[row.first_output as int + 0].definition == row.definition
                && drivers[row.first_output as int + 0].result_index == 0);
            assert(indexed_driver_site(source, parsed, entry as int, first));
            let local = (row.definition - definitions.start) as usize;
            assert(definitions.start + local == row.definition);
            let call = choose|call: TypedFuncCall|
                #[trigger] self.root_output_signature(file, entry, local, limit, Ok(Some(call)))
                && (call.call.target matches FuncCallTarget::Function { file: target_file, entry: target_entry, arity, .. }
                    && target_file == row.target_file && target_entry == row.target_entry && arity.outputs == row.count);
            self.typed_call_arguments_ready(file, entry, local, 0, limit, call);
        };
        assert forall|i: int, j: int| 0 <= i < j < rows.len()
            implies (#[trigger] rows[i]).definition < (#[trigger] rows[j]).definition by {
            let left = drivers[rows[i].first_output as int];
            let right = drivers[rows[j].first_output as int];
            assert(left.result_index == 0 && right.result_index == 0);
            assert(left.definition == rows[i].definition && right.definition == rows[j].definition);
        };
        assert forall|i: int, j: int| 0 <= i < j < rows.len()
            implies (#[trigger] rows[i]).first_output + rows[i].count <= (#[trigger] rows[j]).first_output by {
            let earlier = rows[i];
            let later = rows[j];
            if later.first_output < earlier.first_output + earlier.count {
                assert(self.root_function_call_matches(caller, &wiring.drivers, earlier));
                let offset = later.first_output - earlier.first_output;
                assert(0 <= offset < earlier.count);
                assert(drivers[earlier.first_output + offset].definition == earlier.definition);
                assert(drivers[later.first_output as int].definition == later.definition);
            }
        };
    }

    proof fn update_root_function_calls(
        &self, caller: (usize, usize, u64), drivers: &FuncDrivers, previous: Seq<RootFunctionCall>,
        at: nat, added: Option<RootFunctionCall>,
    )
        requires
            self.root_function_calls_match(caller, drivers, previous, at),
            at < drivers.definitions@.len(),
            added.is_some() <==> self.is_function_call_start(caller, drivers, at as int),
            added matches Some(row) ==> row.first_output == at && self.root_function_call_matches(caller, drivers, row),
        ensures self.root_function_calls_match(caller, drivers,
            if let Some(row) = added { previous.push(row) } else { previous }, at + 1),
    {
        let next = if let Some(row) = added { previous.push(row) } else { previous };
        assert forall|i: int| 0 <= i < at + 1 && #[trigger] self.is_function_call_start(caller, drivers, i)
            implies exists|j: int| 0 <= j < next.len() && (#[trigger] next[j]).first_output == i by {
            if i < at {
                let j = choose|j: int| 0 <= j < previous.len() && (#[trigger] previous[j]).first_output == i;
                assert(next[j] == previous[j]);
            } else {
                assert(next[previous.len() as int] == added->Some_0);
            }
        };
        assert forall|a: int, b: int| 0 <= a < b < next.len()
            implies (#[trigger] next[a]).first_output < (#[trigger] next[b]).first_output by {
            assert(next[a] == previous[a]);
            if b < previous.len() { assert(next[b] == previous[b]); }
        };
    }

    proof fn function_call_start_matches_signature(
        &self, caller: (usize, usize, u64), drivers: &FuncDrivers, at: int, call: Option<TypedFuncCall>,
    )
        requires
            self.can_resolve(),
            ({
                let (file, entry, limit) = caller;
                let parsed = &self.targets.project_model().circuits_model()[file as int];
                let driver = drivers.definitions@[at];
                let local = (driver.definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
                self.root_output_signature(file, entry, local, limit, Ok(call))
            }),
        ensures self.is_function_call_start(caller, drivers, at)
            <==> (drivers.definitions@[at].result_index == 0 && (call matches Some(typed) && typed.call.target is Function)),
    {
        reveal(UseAliases::is_function_call_start);
        reveal(UseAliases::root_output_signature);
        let (file, entry, limit) = caller;
        let parsed = &self.targets.project_model().circuits_model()[file as int];
        let local = (drivers.definitions@[at].definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
        if self.is_function_call_start(caller, drivers, at) {
            let witness = choose|typed: TypedFuncCall|
                #[trigger] self.root_output_signature(file, entry, local, limit, Ok(Some(typed)))
                && typed.call.target is Function;
            if let Some(actual) = call {
                if actual.call.target is Nor {
                    self.resolved_nor_call_agrees(file, entry, local, 0, limit, actual, Some(witness));
                }
            }
        }
    }

    fn record_root_function_call(
        &self, caller: (usize, usize, u64), index: usize, definition: usize, first: bool,
        signature: Option<&FuncCallArity<'p, 'a>>, cache: &SignatureCache<'p, 'a>,
        rows: &mut Vec<RootFunctionCall>, retain: bool, Ghost(wiring): Ghost<FuncWiring<'p, 'a>>,
    )
        requires
            self.can_resolve(),
            self.func_wiring_evidence(caller.0, caller.1, caller.2, Ok(FuncWiringResult::Checked(wiring))),
            index < wiring.drivers.definitions@.len(),
            definition == wiring.drivers.definitions@[index as int].definition,
            first <==> wiring.drivers.definitions@[index as int].result_index == 0,
            ({
                let (file, entry, limit) = caller;
                let circuits = self.targets.project_model().circuits_model();
                &&& file < circuits.len()
                &&& {
                    let parsed = &circuits[file as int];
                    &&& entry < parsed.entry_ranges@.len()
                    &&& {
                        let start = parsed.entry_ranges@[entry as int].definitions.start;
                        &&& start <= definition
                        &&& {
                            let local = (definition - start) as usize;
                            match signature {
                                Some(call) => cached_call_available(cache, *call) && self.root_output_signature(file, entry,
                                    local, limit, Ok(Some(cached_call_model(cache, *call)))),
                                None => self.root_output_signature(file, entry, local, limit, Ok(None)),
                            }
                        }
                    }
                }
            }),
            retain ==> self.root_function_calls_match(caller, &wiring.drivers, old(rows)@, index as nat),
            !retain ==> old(rows)@.len() == 0,
        ensures
            retain ==> self.root_function_calls_match(caller, &wiring.drivers, final(rows)@, (index + 1) as nat),
            !retain ==> final(rows)@.len() == 0,
    {
        if !retain { return; }
        let ghost previous = rows@;
        let ghost model = match signature { Some(call) => Some(cached_call_model(cache, *call)), None => None };
        proof {
            self.checked_wiring_is_func(caller.0, caller.1, caller.2, wiring);
            self.function_call_start_matches_signature(caller, &wiring.drivers, index as int, model);
        }
        if first {
            if let Some(call) = signature {
                if let FuncCallTarget::Function { file, entry, arity, .. } = &call.target {
                    let row = RootFunctionCall { definition, first_output: index, count: arity.outputs,
                        target_file: *file, target_entry: *entry };
                    proof {
                        let (source_file, source_entry, limit) = caller;
                        let project = self.targets.project_model();
                        let parsed = &project.circuits_model()[source_file as int];
                        let source = &project.sources_model()[source_file as int];
                        let driver = wiring.drivers.definitions@[index as int];
                        assert(indexed_driver_site(source, parsed, source_entry as int, driver));
                        let start = parsed.entry_ranges@[source_entry as int].definitions.start;
                        assert(start <= definition);
                        let local = (definition - start) as usize;
                        assert(start + local == definition);
                        let count = self.checked_wiring_output_group(source_file, source_entry, limit, wiring, index as int);
                        let typed = cached_call_model(cache, *call);
                        assert(model == Some(typed) && typed.call == *call);
                        assert(self.root_output_signature(source_file, source_entry, local, limit, Ok(Some(typed))));
                        reveal(UseAliases::root_output_signature);
                        assert(count == row.count);
                        assert(0 < row.count && row.first_output + row.count <= wiring.drivers.definitions@.len());
                        assert forall|i: int| 0 <= i < row.count implies {
                            let driver = #[trigger] wiring.drivers.definitions@[row.first_output + i];
                            driver.definition == row.definition && driver.result_index == i
                        } by {
                            assert(wiring.drivers.definitions@[row.first_output + i]
                                == wiring.drivers.definitions@[index as int + i]);
                        };
                        assert(typed.call.target matches FuncCallTarget::Function { file, entry, arity, .. }
                            && file == row.target_file && entry == row.target_entry && arity.outputs == row.count);
                        assert(row.definition == definition);
                        assert(self.root_function_call_matches(caller, &wiring.drivers, row)) by {
                            reveal(UseAliases::root_function_call_matches);
                            let definition = (row.definition - parsed.entry_ranges@[source_entry as int].definitions.start) as usize;
                            assert(definition == local);
                            assert(exists|candidate: TypedFuncCall|
                                #[trigger] self.root_output_signature(source_file, source_entry, definition, limit, Ok(Some(candidate)))
                                && (candidate.call.target matches FuncCallTarget::Function {
                                    file: target_file, entry: target_entry, arity, ..
                                } && target_file == row.target_file && target_entry == row.target_entry && arity.outputs == row.count));
                        };
                        self.update_root_function_calls(caller, &wiring.drivers, previous, index as nat, Some(row));
                    }
                    rows.push(row);
                    return;
                }
            }
        }
        proof { self.update_root_function_calls(caller, &wiring.drivers, previous, index as nat, None); }
    }

    #[verifier::opaque]
    spec fn root_output_signature(
        &self, file: usize, entry: usize, definition: usize, limit: u64,
        result: Result<Option<TypedFuncCall>, FuncCallOutputError>,
    ) -> bool {
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[file as int];
        let source = &project.sources_model()[file as int];
        let forms = parsed.syntax.forms@;
        let row = parsed.definitions@[parsed.entry_ranges@[entry as int].definitions.start + definition];
        let root = forms[row.expression.start as int];
        let (start, end) = definition_target_range(forms, row);
        let count = end - start;
        if !ordinary_call_at(source.text, forms, row.expression.start as int, row.expression.end as int) {
            result == Ok(None)
        } else {
            match result {
                Ok(Some(call)) => self.func_call_signature_evidence(file, entry, definition, 0, limit, Ok(Some(call)))
                    && call.call.target.port_counts().outputs == count,
                Err(FuncCallOutputError::Signature(error)) =>
                    self.func_call_signature_evidence(file, entry, definition, 0, limit, Err(error)),
                Err(FuncCallOutputError::Count { call, targets, outputs }) =>
                    is_form_location(source, root, call) && targets == count && outputs != targets
                        && exists|typed: TypedFuncCall| typed.call.target.port_counts().outputs == outputs
                            && #[trigger] self.func_call_signature_evidence(file, entry, definition, 0, limit, Ok(Some(typed))),
                _ => false,
            }
        }
    }

    fn read_root_output_signature(
        &self, file: usize, entry: usize, definition: usize, max_width: u64,
        source: &'p ProjectSource<'a>, parsed: &NamedBuildCircuit<'a>,
        cache: &mut SignatureCache<'p, 'a>,
    ) -> (result: Result<Option<FuncCallArity<'p, 'a>>, FuncCallOutputError<'p, 'a>>)
        requires
            self.can_resolve(),
            old(cache).matches(self, max_width),
            file < self.targets.project_model().circuits_model().len(),
            file < self.targets.project_model().sources_model().len(),
            *source == self.targets.project_model().sources_model()[file as int],
            *parsed == self.targets.project_model().circuits_model()[file as int],
            parsed_circuit_matches(*source, *parsed),
            entry < parsed.syntax.entries@.len(), entry < parsed.entry_ranges@.len(),
            parsed.syntax.entries@[entry as int].head is Func,
            definition < parsed.entry_ranges@[entry as int].definitions.end - parsed.entry_ranges@[entry as int].definitions.start,
        ensures
            final(cache).matches(self, max_width),
            match result {
                Ok(Some(call)) => cached_call_available(final(cache), call)
                    && self.root_output_signature(file, entry, definition, max_width,
                        Ok(Some(cached_call_model(final(cache), call)))),
                Ok(None) => self.root_output_signature(file, entry, definition, max_width, Ok(None)),
                Err(error) => self.root_output_signature(file, entry, definition, max_width, Err(error)),
            },
    {
        proof {
            reveal(UseAliases::root_output_signature);
            parsed_index_evidence(*source, *parsed);
            build_entry_ranges_evidence(source.text, &parsed.build_model(), entry as int);
            build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int,
                parsed.entry_ranges@[entry as int].definitions.start + definition);
        }
        let forms = parsed.syntax.forms.as_slice();
        let row = &parsed.definitions[parsed.entry_ranges[entry].definitions.start + definition];
        if !definition_root_is_call(source.text, forms, row, parsed.references.as_slice()) {
            return Ok(None);
        }
        let resolved = self.prepare_func_call_signature(file, entry, definition, 0, max_width, cache);
        let call = match resolved {
            Ok(Some(call)) => call,
            Ok(None) => {
                proof { self.call_has_signature_result(file, entry, definition, 0, max_width, Ok(None)); }
                unreachable!()
            },
            Err(error) => return Err(FuncCallOutputError::Signature(error)),
        };
        let targets = definition_target_atoms(forms, row);
        let expected = targets.end - targets.start;
        let actual = call.target.ports().outputs;
        if actual != expected {
            return Err(FuncCallOutputError::Count {
                call: form_location(source, forms, row.expression.start), targets: expected, outputs: actual,
            });
        }
        Ok(Some(call))
    }

    #[verifier::opaque]
    spec fn call_output_step(
        &self, file: usize, entry: usize, limit: u64, drivers: &FuncDrivers,
        outlets: Seq<Option<usize>>, i: int, result: Result<Option<SignalType>, FuncCallOutputError>,
    ) -> bool {
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[file as int];
        let source = &project.sources_model()[file as int];
        let driver = drivers.definitions@[i];
        let definition = (driver.definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
        let root = parsed.syntax.forms@[parsed.definitions@[driver.definition as int].expression.start as int];
        let target = LocatedName { source, span: driver.name.span };
        let expected = match outlets[i] {
            Some(output) => Some(drivers.signature.outputs@[output as int]),
            None => None,
        };
        match result {
            Err(error) if error is Signature || error is Count =>
                self.root_output_signature(file, entry, definition, limit, Err(error)),
            Ok(None) => self.root_output_signature(file, entry, definition, limit, Ok(None)),
            _ => exists|call: TypedFuncCall, expression: LocatedName|
                #[trigger] self.root_output_signature(file, entry, definition, limit, Ok(Some(call)))
                    && #[trigger] is_form_location(source, root, expression)
                    && driver.result_index < call.call.target.port_counts().outputs
                    && output_transfer(call_output_type(&call, &expression, driver.result_index as int),
                        expected, target, expression, result),
        }
    }

    #[verifier::opaque]
    spec fn call_output_prefix(
        &self, file: usize, entry: usize, limit: u64, drivers: &FuncDrivers,
        outlets: Seq<Option<usize>>, types: Seq<Option<SignalType>>,
    ) -> bool {
        forall|i: int| 0 <= i < types.len()
            ==> #[trigger] self.call_output_step(file, entry, limit, drivers, outlets, i, Ok(types[i]))
    }

    /// 結果型が右辺の呼び出しから得られ、出力注釈に適合するか、最初の違反に対応することを表す。
    pub closed spec fn func_call_outputs_evidence(
        &self, file: usize, entry: usize, limit: u64, result: Result<FuncCallOutputTypes, FuncCallOutputError>,
    ) -> bool {
        match result {
            Err(FuncCallOutputError::Caller(error)) => self.func_arity_evidence(file, entry, limit, Err(error)),
            Ok(result) => self.func_arity_evidence(file, entry, limit, Ok(result.wiring))
                && if let FuncWiringResult::Checked(wiring) = result.wiring {
                    result.types@.len() == wiring.drivers.definitions@.len()
                    && exists|outlets: Seq<Option<usize>>|
                        #[trigger] output_indices(&wiring.drivers, wiring.drivers.outputs@.len() as int, outlets)
                        && self.call_output_prefix(file, entry, limit, &wiring.drivers, outlets, result.types@)
                } else { result.types@.len() == 0 },
            Err(error) => exists|scope: FuncWiring|
                #[trigger] self.func_arity_evidence(file, entry, limit, Ok(FuncWiringResult::Checked(scope)))
                && self.call_output_failure(file, entry, limit, &scope.drivers, error),
        }
    }

    pub(in crate::project::use_aliases) closed spec fn call_output_failure(
        &self, file: usize, entry: usize, limit: u64, drivers: &FuncDrivers, error: FuncCallOutputError,
    ) -> bool {
        exists|map: Seq<Option<usize>>, prefix: Seq<Option<SignalType>>|
            #[trigger] output_indices(drivers, drivers.outputs@.len() as int, map)
            && #[trigger] self.call_output_prefix(file, entry, limit, drivers, map, prefix)
            && prefix.len() < drivers.definitions@.len()
            && self.call_output_step(file, entry, limit, drivers, map, prefix.len() as int, Err(error))
    }

    proof fn record_output_error(
        &self, file: usize, entry: usize, limit: u64, scope: &FuncWiring,
        outlets: Seq<Option<usize>>, prior: Seq<Option<SignalType>>, error: FuncCallOutputError,
    )
        requires
            self.func_arity_evidence(file, entry, limit, Ok(FuncWiringResult::Checked(*scope))),
            output_indices(&scope.drivers, scope.drivers.outputs@.len() as int, outlets),
            self.call_output_prefix(file, entry, limit, &scope.drivers, outlets, prior),
            prior.len() < scope.drivers.definitions@.len(),
            self.call_output_step(file, entry, limit, &scope.drivers, outlets, prior.len() as int, Err(error)),
            !(error is Caller),
        ensures self.func_call_outputs_evidence(file, entry, limit, Err(error)),
            self.call_output_failure(file, entry, limit, &scope.drivers, error),
    {
        assert(exists|map: Seq<Option<usize>>, prefix: Seq<Option<SignalType>>|
            #[trigger] output_indices(&scope.drivers, scope.drivers.outputs@.len() as int, map)
            && #[trigger] self.call_output_prefix(file, entry, limit, &scope.drivers, map, prefix)
            && prefix.len() < scope.drivers.definitions@.len()
            && self.call_output_step(file, entry, limit, &scope.drivers, map, prefix.len() as int, Err(error))) by {
            assert(output_indices(&scope.drivers, scope.drivers.outputs@.len() as int, outlets));
            assert(self.call_output_prefix(file, entry, limit, &scope.drivers, outlets, prior));
        };
        assert(self.call_output_failure(file, entry, limit, &scope.drivers, error));
        assert(exists|wiring: FuncWiring|
            #[trigger] self.func_arity_evidence(file, entry, limit, Ok(FuncWiringResult::Checked(wiring)))
            && self.call_output_failure(file, entry, limit, &wiring.drivers, error)) by {
            assert(self.func_arity_evidence(file, entry, limit, Ok(FuncWiringResult::Checked(*scope))));
        };
    }

    /// 右辺全体が通常呼び出しである定義について、左辺の信号の型を求める。
    ///
    /// 呼び出し先の出力を宣言順に割り当て、関数の出力ポートを駆動する名前は宣言型と照合する。
    /// 呼び出しが返した型を使う裸の信号参照や、別の呼び出しの引数への型の伝播は保留する。
    ///
    /// # Errors
    ///
    /// 配線と入出力数を先に検査する。その後は定義順に署名を解決し、出力数を再確認して、
    /// 左辺の名前順に出力型を照合する。最初の違反を返す。
    pub fn check_func_call_outputs(
        &self, file: usize, entry: usize, max_width: u64,
    ) -> (result: Result<FuncCallOutputTypes<'p, 'a>, FuncCallOutputError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.func_call_outputs_evidence(file, entry, max_width, result),
    {
        let wiring = match self.check_func_arity(file, entry, max_width) {
            Ok(wiring) => wiring,
            Err(error) => return Err(FuncCallOutputError::Caller(error)),
        };
        let mut signatures = SignatureCache::new();
        let mut rows = Vec::new();
        self.check_call_outputs_with_arity(file, entry, max_width, wiring, &mut signatures, &mut rows, false)
    }

    pub(in crate::project::use_aliases) fn check_call_outputs_with_arity(
        &self, file: usize, entry: usize, max_width: u64, wiring: FuncWiringResult<'p, 'a>,
        signatures: &mut SignatureCache<'p, 'a>, rows: &mut Vec<RootFunctionCall>, retain: bool,
    ) -> (result: Result<FuncCallOutputTypes<'p, 'a>, FuncCallOutputError<'p, 'a>>)
        requires self.can_resolve(), self.func_arity_evidence(file, entry, max_width, Ok(wiring)),
            old(signatures).matches(self, max_width),
            old(rows)@.len() == 0,
        ensures
            final(signatures).matches(self, max_width),
            self.func_call_outputs_evidence(file, entry, max_width, result),
            result matches Ok(outputs) ==> outputs.wiring == wiring,
            result matches Err(error) ==> !(error is Caller),
            result matches Err(error) ==> wiring matches FuncWiringResult::Checked(scope)
                && self.call_output_failure(file, entry, max_width, &scope.drivers, error),
            result matches Ok(outputs) ==> {
                &&& !retain ==> final(rows)@.len() == 0
                &&& if let FuncWiringResult::Checked(scope) = outputs.wiring {
                    retain ==> self.root_function_calls_match((file, entry, max_width), &scope.drivers,
                        final(rows)@, outputs.types@.len())
                } else { final(rows)@.len() == 0 }
            },
    {
        let FuncWiringResult::Checked(ref scope) = wiring else {
            return Ok(FuncCallOutputTypes { wiring, types: Vec::new() });
        };
        let project = self.targets.project();
        proof {
            self.arity_preserves_wiring(file, entry, max_width, wiring);
            self.checked_wiring_is_func(file, entry, max_width, *scope);
        }
        let parsed = &project.circuits()[file];
        let source = &project.sources()[file];
        let frame = &parsed.entry_ranges[entry].definitions;
        let drivers = &scope.drivers;
        let outlets = index_outputs(drivers);
        let mut types = Vec::new();
        let mut index = 0;
        let mut cached: Option<(usize, Option<FuncCallArity>)> = None;
        proof { reveal(UseAliases::call_output_prefix); }
        while index < drivers.definitions.len()
            invariant
                self.can_resolve(), *project == self.targets.project_model(),
                file < project.circuits_model().len(), file < project.sources_model().len(),
                *source == project.sources_model()[file as int], *parsed == project.circuits_model()[file as int],
                parsed_circuit_matches(*source, *parsed), entry < parsed.syntax.entries@.len(),
                parsed.syntax.entries@[entry as int].head is Func,
                self.func_arity_evidence(file, entry, max_width, Ok(wiring)),
                self.func_wiring_evidence(file, entry, max_width, Ok(wiring)),
                wiring == FuncWiringResult::Checked(*scope), *drivers == scope.drivers,
                expected_output_context(source, parsed, entry as int, *drivers),
                *frame == parsed.entry_ranges@[entry as int].definitions,
                forall|i: int| 0 <= i < drivers.definitions@.len()
                    ==> indexed_driver_site(source, parsed, entry as int, #[trigger] drivers.definitions@[i]),
                output_indices(drivers, drivers.outputs@.len() as int, outlets@),
                index == types@.len() <= drivers.definitions@.len(),
                retain ==> self.root_function_calls_match((file, entry, max_width), drivers, rows@, index as nat),
                !retain ==> rows@.len() == 0,
                self.call_output_prefix(file, entry, max_width, drivers, outlets@, types@),
                signatures.matches(self, max_width),
                cached matches Some((definition, signature))
                    ==> match signature {
                        Some(call) => cached_call_available(signatures, call)
                            && self.root_output_signature(file, entry, definition, max_width,
                                Ok(Some(cached_call_model(signatures, call)))),
                        None => self.root_output_signature(file, entry, definition, max_width, Ok(None)),
                    },
            decreases drivers.definitions@.len() - index,
        {
            let driver = &drivers.definitions[index];
            let definition = driver.definition - frame.start;
            proof {
                reveal(UseAliases::root_output_signature);
                reveal(UseAliases::call_output_step);
                reveal(output_indices);
                parsed_index_evidence(*source, *parsed);
                build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, driver.definition as int);
            }
            // 同じ左辺に並ぶ名前には、同じ呼び出し先の署名を使う。
            if !matches!(cached, Some((previous, _)) if previous == definition) {
                match self.read_root_output_signature(file, entry, definition, max_width, source, parsed, signatures) {
                    Ok(signature) => cached = Some((definition, signature)),
                    Err(error) => {
                        proof {
                            reveal(UseAliases::root_output_signature);
                            assert(self.call_output_step(file, entry, max_width, drivers, outlets@, index as int, Err(error)));
                            self.record_output_error(file, entry, max_width, scope, outlets@, types@, error);
                        }
                        return Err(error);
                    }
                }
            }
            let Some((_, signature)) = &cached else {
                proof { assert(false); }
                unreachable!()
            };
            let result = if let Some(call) = signature {
                let ghost model = cached_call_model(signatures, *call);
                proof { self.typed_call_arguments_ready(file, entry, definition, 0, max_width, model); }
                let signature = cached_signature(signatures, call);
                let Some(port) = signature_port(signature, PortDirection::Output, driver.result_index) else {
                    proof { assert(false); }
                    unreachable!()
                };
                let forms = parsed.syntax.forms.as_slice();
                let expression = form_location(source, forms, parsed.definitions[driver.definition].expression.start);
                let origin = match port.annotation {
                    Some(site) => copy_location(site),
                    None => copy_location(&expression),
                };
                let actual = SignalType { ty: port.ty, origin };
                assert(actual == call_output_type(&model, &expression, driver.result_index as int));
                if let Some(output) = outlets[index] {
                    let expected = &drivers.signature.outputs[output];
                    if !actual.ty.is_same_type(&expected.ty) {
                        let error = FuncCallOutputError::OutputType {
                            target: name_location(source, &driver.name), call: expression,
                            expected: SignalType { ty: expected.ty, origin: copy_location(&expected.annotation) },
                            actual,
                        };
                        proof {
                            assert(self.call_output_step(file, entry, max_width, drivers, outlets@, index as int, Err(error)));
                            self.record_output_error(file, entry, max_width, scope, outlets@, types@, error);
                        }
                        return Err(error);
                    }
                }
                assert(self.call_output_step(file, entry, max_width, drivers, outlets@, index as int, Ok(Some(actual))));
                Some(actual)
            } else {
                assert(self.call_output_step(file, entry, max_width, drivers, outlets@, index as int, Ok(None)));
                None
            };
            self.record_root_function_call((file, entry, max_width), index, driver.definition,
                driver.result_index == 0, signature.as_ref(), signatures, rows, retain, Ghost(*scope));
            let ghost before = types@;
            types.push(result);
            proof {
                reveal(UseAliases::call_output_prefix);
                assert forall|i: int| 0 <= i < types@.len()
                    implies #[trigger] self.call_output_step(file, entry, max_width, drivers, outlets@, i, Ok(types@[i])) by {
                    if i < before.len() { assert(types@[i] == before[i]); }
                };
            }
            index += 1;
        }
        Ok(FuncCallOutputTypes { wiring, types })
    }

    /// 同じ関数の呼び出し出力の型を二度求めると、定義ごとの型と注釈位置が一致する。
    pub(in crate::project::use_aliases) proof fn checked_call_output_types_agree(
        &self, file: usize, entry: usize, limit: u64, left: FuncCallOutputTypes, right: FuncCallOutputTypes,
    )
        requires
            self.can_resolve(),
            left.wiring is Checked,
            right.wiring is Checked,
            self.func_call_outputs_evidence(file, entry, limit, Ok(left)),
            self.func_call_outputs_evidence(file, entry, limit, Ok(right)),
        ensures left.types@ == right.types@,
    {
        let l = left.wiring->Checked_0;
        let r = right.wiring->Checked_0;
        self.arity_preserves_wiring(file, entry, limit, left.wiring);
        self.arity_preserves_wiring(file, entry, limit, right.wiring);
        self.checked_func_wiring_agrees(file, entry, limit, l, r);
        let a = self.checked_call_output_map(file, entry, limit, &left, &l);
        let b = self.checked_call_output_map(file, entry, limit, &right, &r);
        output_indices_agree(&l.drivers, &r.drivers, a, b);
        self.checked_wiring_is_func(file, entry, limit, l);
        self.checked_wiring_is_func(file, entry, limit, r);
        self.targets.parsed_project_model();
        let project = self.targets.project_model();
        let source = &project.sources_model()[file as int];
        let parsed = &project.circuits_model()[file as int];
        parsed_index_evidence(*source, *parsed);
        reveal(output_indices);
        reveal(UseAliases::call_output_prefix);
        assert forall|i: int| 0 <= i < left.types@.len() implies
            (#[trigger] left.types@[i]) == (#[trigger] right.types@[i]) by {
            assert(same_definition_driver(l.drivers.definitions@[i], r.drivers.definitions@[i]));
            assert(indexed_driver_site(source, parsed, entry as int, l.drivers.definitions@[i]));
            assert(indexed_driver_site(source, parsed, entry as int, r.drivers.definitions@[i]));
            build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int,
                l.drivers.definitions@[i].definition as int);
            self.call_output_steps_agree(file, entry, limit, &l.drivers, &r.drivers, a, b, i,
                left.types@[i], right.types@[i]);
        };
        assert(left.types@ =~= right.types@);
    }

    proof fn checked_call_output_map(
        &self, file: usize, entry: usize, limit: u64, outputs: &FuncCallOutputTypes, wiring: &FuncWiring,
    ) -> (map: Seq<Option<usize>>)
        requires
            outputs.wiring == FuncWiringResult::Checked(*wiring),
            self.func_call_outputs_evidence(file, entry, limit, Ok(*outputs)),
        ensures
            self.func_arity_evidence(file, entry, limit, Ok(outputs.wiring)),
            outputs.types@.len() == wiring.drivers.definitions@.len(),
            output_indices(&wiring.drivers, wiring.drivers.outputs@.len() as int, map),
            self.call_output_prefix(file, entry, limit, &wiring.drivers, map, outputs.types@),
    {
        choose|outlets: Seq<Option<usize>>|
            #[trigger] output_indices(&wiring.drivers, wiring.drivers.outputs@.len() as int, outlets)
            && self.call_output_prefix(file, entry, limit, &wiring.drivers, outlets, outputs.types@)
    }

    /// 保持した呼び出しの各出力を、同じ署名のポート型と注釈位置に対応付ける。
    pub(in crate::project::use_aliases) proof fn checked_root_function_call(
        &self, caller: (usize, usize, u64), outputs: &FuncCallOutputTypes, wiring: &FuncWiring,
        rows: Seq<RootFunctionCall>, position: int,
    ) -> (call: TypedFuncCall<'p, 'a>)
        requires
            self.can_resolve(),
            self.func_call_outputs_evidence(caller.0, caller.1, caller.2, Ok(*outputs)),
            outputs.wiring == FuncWiringResult::Checked(*wiring),
            self.root_function_calls_match(caller, &wiring.drivers, rows, outputs.types@.len()),
            0 <= position < rows.len(),
        ensures ({
            let row = rows[position];
            let (file, entry, limit) = caller;
            let parsed = self.targets.project_model().circuits_model()[file as int];
            let start = parsed.entry_ranges@[entry as int].definitions.start;
            let local = (row.definition - start) as usize;
            let expression = parsed.definitions@[row.definition as int].expression;
            let source = &self.targets.project_model().sources_model()[file as int];
            &&& start <= row.definition < parsed.definitions@.len()
            &&& self.func_call_signature_evidence(file, entry, local, 0, limit, Ok(Some(call)))
            &&& ordinary_call_at(source.text, parsed.syntax.forms@, expression.start as int, expression.end as int)
            &&& call.call.target matches FuncCallTarget::Function { file: target_file, entry: target_entry, .. }
            &&& target_file == row.target_file && target_entry == row.target_entry
            &&& call.signature matches FuncCallSignature::Function(signature)
            &&& 0 < row.count == signature.outputs@.len()
            &&& row.first_output + row.count <= outputs.types@.len()
            &&& forall|offset: int| #![trigger outputs.types@[row.first_output + offset]]
                0 <= offset < row.count ==> {
                let index = row.first_output + offset;
                let driver = wiring.drivers.definitions@[index];
                let ty = signature.outputs@[offset].ty;
                let origin = signature.outputs@[offset].annotation;
                &&& driver.definition == row.definition && driver.result_index == offset
                &&& outputs.types@[index] == Some(SignalType { ty, origin })
            }
        }),
    {
        let (file, entry, limit) = caller;
        let drivers = &wiring.drivers;
        let map = self.checked_call_output_map(file, entry, limit, outputs, wiring);
        self.arity_preserves_wiring(file, entry, limit, outputs.wiring);
        self.checked_wiring_is_func(file, entry, limit, *wiring);
        reveal(UseAliases::root_function_call_matches);
        reveal(UseAliases::root_output_signature);
        reveal(UseAliases::call_output_prefix);
        reveal(output_indices);
        let row = rows[position];
        self.targets.parsed_project_model();
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[file as int];
        let source = &project.sources_model()[file as int];
        parsed_index_evidence(*source, *parsed);
        assert(self.root_function_call_matches(caller, drivers, row));
        assert(row.count > 0);
        assert(drivers.definitions@[row.first_output as int + 0].definition == row.definition);
        assert(indexed_driver_site(source, parsed, entry as int, drivers.definitions@[row.first_output as int]));
        let start = parsed.entry_ranges@[entry as int].definitions.start;
        assert(start <= row.definition);
        let local = (row.definition - start) as usize;
        assert(start + local == row.definition);
        let typed = choose|call: TypedFuncCall|
            #[trigger] self.root_output_signature(file, entry, local, limit, Ok(Some(call)))
            && (call.call.target matches FuncCallTarget::Function { file: target_file, entry: target_entry, arity, .. }
                && target_file == row.target_file && target_entry == row.target_entry && arity.outputs == row.count);
        self.typed_call_arguments_ready(file, entry, local, 0, limit, typed);
        let expression = parsed.definitions@[row.definition as int].expression;
        assert(self.root_output_signature(file, entry, local, limit, Ok(Some(typed))));
        assert(ordinary_call_at(source.text, parsed.syntax.forms@, expression.start as int, expression.end as int));
        let ports = typed.signature->Function_0.outputs@;
        assert forall|offset: int| 0 <= offset < row.count implies
            #[trigger] outputs.types@[row.first_output + offset]
                == Some(SignalType { ty: ports[offset].ty, origin: ports[offset].annotation }) by {
            let index = row.first_output + offset;
            let port = ports[offset];
            let driver = drivers.definitions@[index];
            assert(indexed_driver_site(source, parsed, entry as int, driver));
            build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, driver.definition as int);
            assert(self.call_output_step(file, entry, limit, drivers, map, index, Ok(outputs.types@[index])));
            let item = self.checked_root_output(file, entry, limit, drivers, map, index, outputs.types@[index]);
            assert(item.is_some());
            let (other, expression) = item->Some_0;
            self.successful_call_signatures_agree(file, entry, local, 0, limit, typed, other);
            assert(call_output_type(&other, &expression, offset) == SignalType { ty: port.ty, origin: port.annotation });
        };
        assert forall|offset: int| #![trigger outputs.types@[row.first_output + offset]] 0 <= offset < row.count
            implies wiring.drivers.definitions@[row.first_output + offset].definition == row.definition
                && wiring.drivers.definitions@[row.first_output + offset].result_index == offset by {
            let at = row.first_output + offset;
            assert(drivers.definitions@[at].definition == row.definition);
        };
        typed
    }

    spec fn valid_call_output_step(
        &self, file: usize, entry: usize, drivers: &FuncDrivers, outlets: Seq<Option<usize>>, i: int,
    ) -> bool {
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[file as int];
        let source = &project.sources_model()[file as int];
        &&& file < project.circuits_model().len() && file < project.sources_model().len()
        &&& entry < parsed.entry_ranges@.len()
        &&& 0 <= i < drivers.definitions@.len() && i < outlets.len()
        &&& indexed_driver_site(source, parsed, entry as int, drivers.definitions@[i])
        &&& parsed.definitions@[drivers.definitions@[i].definition as int].expression.start < parsed.syntax.forms@.len()
        &&& (outlets[i] matches Some(port) ==> port < drivers.signature.outputs@.len())
    }

    proof fn call_output_steps_agree(
        &self, file: usize, entry: usize, limit: u64, left: &FuncDrivers, right: &FuncDrivers,
        a: Seq<Option<usize>>, b: Seq<Option<usize>>, i: int,
        first: Option<SignalType>, second: Option<SignalType>,
    )
        requires
            self.can_resolve(),
            self.valid_call_output_step(file, entry, left, a, i),
            self.valid_call_output_step(file, entry, right, b, i),
            same_definition_driver(left.definitions@[i], right.definitions@[i]),
            self.call_output_step(file, entry, limit, left, a, i, Ok(first)),
            self.call_output_step(file, entry, limit, right, b, i, Ok(second)),
        ensures first == second,
    {
        let x = self.checked_root_output(file, entry, limit, left, a, i, first);
        let y = self.checked_root_output(file, entry, limit, right, b, i, second);
        if let (Some((call_a, site_a)), Some((call_b, site_b))) = (x, y) {
            let project = self.targets.project_model();
            let parsed = &project.circuits_model()[file as int];
            let driver = left.definitions@[i];
            let local = (driver.definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
            assert(site_a == site_b);
            self.successful_call_signatures_agree(file, entry, local, 0, limit, call_a, call_b);
        }
    }

    proof fn checked_root_output(
        &self, file: usize, entry: usize, limit: u64, drivers: &FuncDrivers, outlets: Seq<Option<usize>>,
        i: int, value: Option<SignalType>,
    ) -> (found: Option<(TypedFuncCall<'p, 'a>, LocatedName<'p, 'a>)>)
        requires
            self.valid_call_output_step(file, entry, drivers, outlets, i),
            self.call_output_step(file, entry, limit, drivers, outlets, i, Ok(value)),
        ensures ({
            let project = self.targets.project_model();
            let parsed = &project.circuits_model()[file as int];
            let source = &project.sources_model()[file as int];
            let driver = drivers.definitions@[i];
            let row = parsed.definitions@[driver.definition as int];
            let local = (driver.definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
            let root = row.expression.start as int;
            &&& found.is_some() <==> ordinary_call_at(source.text, parsed.syntax.forms@, root, row.expression.end as int)
            &&& match found {
                Some((call, expression)) =>
                    self.func_call_signature_evidence(file, entry, local, 0, limit, Ok(Some(call)))
                    && is_form_location(source, parsed.syntax.forms@[root], expression)
                    && value == Some(call_output_type(&call, &expression, driver.result_index as int)),
                None => value.is_none(),
            }
        }),
    {
        reveal(UseAliases::call_output_step);
        reveal(UseAliases::root_output_signature);
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[file as int];
        let source = &project.sources_model()[file as int];
        let driver = drivers.definitions@[i];
        let local = (driver.definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
        let row = parsed.definitions@[driver.definition as int];
        let root = parsed.syntax.forms@[row.expression.start as int];
        let target = LocatedName { source, span: driver.name.span };
        let expected = match outlets[i] { Some(port) => Some(drivers.signature.outputs@[port as int]), None => None };
        if value.is_some() {
            let witness = choose|call: TypedFuncCall, expression: LocatedName|
                #[trigger] self.root_output_signature(file, entry, local, limit, Ok(Some(call)))
                && #[trigger] is_form_location(source, root, expression)
                && driver.result_index < call.call.target.port_counts().outputs
                && output_transfer(call_output_type(&call, &expression, driver.result_index as int),
                    expected, target, expression, Ok(value));
            assert(ordinary_call_at(source.text, parsed.syntax.forms@, row.expression.start as int, row.expression.end as int));
            Some(witness)
        } else {
            assert(!ordinary_call_at(source.text, parsed.syntax.forms@, row.expression.start as int, row.expression.end as int));
            None
        }
    }

    /// 解決済みの基底 NOR と同じ呼び出しから、出力型が1ビットであることを導く。
    pub(in crate::project::use_aliases) proof fn nor_root_output_type(
        &self, file: usize, entry: usize, limit: u64, outputs: &FuncCallOutputTypes, wiring: &FuncWiring,
        index: int, builtin: TypedFuncCall,
    )
        requires
            self.can_resolve(),
            self.func_call_outputs_evidence(file, entry, limit, Ok(*outputs)),
            outputs.wiring == FuncWiringResult::Checked(*wiring),
            0 <= index < wiring.drivers.definitions@.len(),
            builtin.call.target is Nor,
            ({
                let project = self.targets.project_model();
                let parsed = &project.circuits_model()[file as int];
                let source = &project.sources_model()[file as int];
                let driver = wiring.drivers.definitions@[index];
                let local = (driver.definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
                &&& indexed_driver_site(source, parsed, entry as int, driver)
                &&& builtin.call.call.form == parsed.definitions@[driver.definition as int].expression.start
                &&& self.func_call_signature_evidence(file, entry, local, 0, limit, Ok(Some(builtin)))
            }),
        ensures
            outputs.types@[index] matches Some(ty) && ty.ty == ResolvedPortType::Bits(1),
            ({
                let project = self.targets.project_model();
                let parsed = &project.circuits_model()[file as int];
                let row = parsed.definitions@[wiring.drivers.definitions@[index].definition as int];
                ordinary_call_at(project.sources_model()[file as int].text, parsed.syntax.forms@,
                    row.expression.start as int, row.expression.end as int)
            }),
    {
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[file as int];
        let source = &project.sources_model()[file as int];
        let forms = parsed.syntax.forms@;
        let drivers = &wiring.drivers;
        let driver = drivers.definitions@[index];
        let row = parsed.definitions@[driver.definition as int];
        let local = (driver.definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
        self.typed_call_arguments_ready(file, entry, local, 0, limit, builtin);
        indexed_call_arguments(source.text, forms, row, parsed.references@[row.references.start as int], builtin.call.call);
        let outlets = self.checked_call_output_map(file, entry, limit, outputs, wiring);
        reveal(UseAliases::call_output_prefix);
        assert(self.call_output_step(file, entry, limit, drivers, outlets, index, Ok(outputs.types@[index])));
        reveal(UseAliases::call_output_step);
        reveal(UseAliases::root_output_signature);
        let root = forms[row.expression.start as int];
        let target = LocatedName { source, span: driver.name.span };
        let expected = if let Some(output) = outlets[index] { Some(drivers.signature.outputs@[output as int]) } else { None };
        let (call, expression) = choose|call: TypedFuncCall, expression: LocatedName|
            #[trigger] self.root_output_signature(file, entry, local, limit, Ok(Some(call)))
            && #[trigger] is_form_location(source, root, expression)
            && driver.result_index < call.call.target.port_counts().outputs
            && output_transfer(call_output_type(&call, &expression, driver.result_index as int),
                expected, target, expression, Ok(outputs.types@[index]));
        self.resolved_nor_call_agrees(file, entry, local, 0, limit, builtin, Some(call));
        self.typed_call_arguments_ready(file, entry, local, 0, limit, call);
    }

    pub(in crate::project::use_aliases) proof fn call_outputs_fit_wiring(
        &self, file: usize, entry: usize, limit: u64, outputs: &FuncCallOutputTypes, wiring: &FuncWiring,
    )
        requires self.func_call_outputs_evidence(file, entry, limit, Ok(*outputs)),
            outputs.wiring == FuncWiringResult::Checked(*wiring),
        ensures
            outputs.types@.len() == wiring.drivers.definitions@.len(),
            forall|i: int| 0 <= i < outputs.types@.len() && (#[trigger] outputs.types@[i]).is_some()
                ==> location_in_source(outputs.types@[i]->Some_0.origin)
                    && self.declared_port_type(outputs.types@[i]->Some_0.ty),
    {
        let outlets = self.checked_call_output_map(file, entry, limit, outputs, wiring);
        reveal(UseAliases::call_output_prefix);
        assert forall|i: int| 0 <= i < outputs.types@.len() && (#[trigger] outputs.types@[i]).is_some()
            implies location_in_source(outputs.types@[i]->Some_0.origin)
                && self.declared_port_type(outputs.types@[i]->Some_0.ty) by {
            reveal(UseAliases::call_output_step);
            let drivers = &wiring.drivers;
            assert(self.call_output_step(file, entry, limit, drivers, outlets, i, Ok(outputs.types@[i])));
            let project = self.targets.project_model();
            let parsed = &project.circuits_model()[file as int];
            let source = &project.sources_model()[file as int];
            let driver = drivers.definitions@[i];
            let definition = (driver.definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
            let root = parsed.syntax.forms@[parsed.definitions@[driver.definition as int].expression.start as int];
            let target = LocatedName { source, span: driver.name.span };
            let expected = if let Some(output) = outlets[i] {
                Some(drivers.signature.outputs@[output as int])
            } else { None };
            let (call, expression) = choose|call: TypedFuncCall, expression: LocatedName|
                #[trigger] self.root_output_signature(file, entry, definition, limit, Ok(Some(call)))
                && #[trigger] is_form_location(source, root, expression)
                && driver.result_index < call.call.target.port_counts().outputs
                && output_transfer(call_output_type(&call, &expression, driver.result_index as int),
                    expected, target, expression, Ok(outputs.types@[i]));
            if call.signature is Function {
                reveal(UseAliases::root_output_signature);
                self.call_output_annotation_in_source(file, entry, definition, 0, limit, call, driver.result_index as int);
            }
        };
    }
}

} // verus!
