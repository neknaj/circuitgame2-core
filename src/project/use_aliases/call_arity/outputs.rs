//! 通常呼び出しが返す型を、定義の左辺の名前順に対応付ける。

use super::{FuncArityError, FuncCallSignatureError, TypedFuncCall, UseAliases};
#[cfg(verus_only)]
use super::FuncCallSignature;
use super::super::function_atoms::copy_location;
use super::super::function_drivers::name_location;
#[cfg(verus_only)]
use super::super::function_drivers::{expected_output_context, indexed_driver_site};
use super::super::function_literals::index_outputs;
#[cfg(verus_only)]
use super::super::function_literals::output_indices;
use crate::project::{FuncWiringResult, LocatedName, PortDirection, ProjectSource, SignalType};
use crate::project::circuits::form_location;
#[cfg(verus_only)]
use crate::project::{FuncDrivers, FuncWiring, TypedPort, port_types_equal, ResolvedPortType, circuits::{
    is_form_location, parsed_circuit_matches, parsed_index_evidence,
}};
use crate::syntax::circuit::{NamedBuildCircuit, definition_root_is_call, definition_target_atoms};
#[cfg(verus_only)]
use crate::syntax::circuit::{
    build_definition_scope_evidence, build_entry_ranges_evidence, definition_target_range, ordinary_call_at,
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
    ) -> (result: Result<Option<TypedFuncCall<'p, 'a>>, FuncCallOutputError<'p, 'a>>)
        requires
            self.can_resolve(),
            file < self.targets.project_model().circuits_model().len(),
            file < self.targets.project_model().sources_model().len(),
            *source == self.targets.project_model().sources_model()[file as int],
            *parsed == self.targets.project_model().circuits_model()[file as int],
            parsed_circuit_matches(*source, *parsed),
            entry < parsed.syntax.entries@.len(), entry < parsed.entry_ranges@.len(),
            parsed.syntax.entries@[entry as int].head is Func,
            definition < parsed.entry_ranges@[entry as int].definitions.end - parsed.entry_ranges@[entry as int].definitions.start,
        ensures self.root_output_signature(file, entry, definition, max_width, result),
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
        let resolved = self.resolve_func_call_signature(file, entry, definition, 0, max_width);
        let call = match resolved {
            Ok(Some(call)) => call,
            Ok(None) => {
                proof { self.call_has_signature_result(file, entry, definition, 0, max_width, resolved); }
                unreachable!()
            },
            Err(error) => return Err(FuncCallOutputError::Signature(error)),
        };
        let targets = definition_target_atoms(forms, row);
        let expected = targets.end - targets.start;
        let actual = call.call.target.ports().outputs;
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
        self.check_call_outputs_with_arity(file, entry, max_width, wiring)
    }

    pub(in crate::project::use_aliases) fn check_call_outputs_with_arity(
        &self, file: usize, entry: usize, max_width: u64, wiring: FuncWiringResult<'p, 'a>,
    ) -> (result: Result<FuncCallOutputTypes<'p, 'a>, FuncCallOutputError<'p, 'a>>)
        requires self.can_resolve(), self.func_arity_evidence(file, entry, max_width, Ok(wiring)),
        ensures
            self.func_call_outputs_evidence(file, entry, max_width, result),
            result matches Ok(outputs) ==> outputs.wiring == wiring,
            result matches Err(error) ==> !(error is Caller),
            result matches Err(error) ==> wiring matches FuncWiringResult::Checked(scope)
                && self.call_output_failure(file, entry, max_width, &scope.drivers, error),
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
        let mut cached: Option<(usize, Option<TypedFuncCall>)> = None;
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
                self.call_output_prefix(file, entry, max_width, drivers, outlets@, types@),
                cached matches Some((definition, signature))
                    ==> self.root_output_signature(file, entry, definition, max_width, Ok(signature)),
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
                match self.read_root_output_signature(file, entry, definition, max_width, source, parsed) {
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
                proof { self.typed_call_arguments_ready(file, entry, definition, 0, max_width, *call); }
                let Some(port) = call.signature.port(PortDirection::Output, driver.result_index) else {
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
                assert(actual == call_output_type(call, &expression, driver.result_index as int));
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

    pub(in crate::project::use_aliases) proof fn call_outputs_fit_wiring(
        &self, file: usize, entry: usize, limit: u64, outputs: &FuncCallOutputTypes, wiring: &FuncWiring,
    )
        requires self.func_call_outputs_evidence(file, entry, limit, Ok(*outputs)),
            outputs.wiring == FuncWiringResult::Checked(*wiring),
        ensures outputs.types@.len() == wiring.drivers.definitions@.len(),
    {}
}

} // verus!
