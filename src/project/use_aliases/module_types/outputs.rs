//! 出力ポートの宣言型を、全断片から解決した駆動元の型と照合する。

use super::{ModuleSelections, ModuleSelectionsError, UseAliases, selections::read_bound_type};
use crate::project::{ModuleBodyPosition, SignalType};
use crate::project::use_aliases::function_atoms::copy_location;
#[cfg(verus_only)]
use crate::project::{location_in_source, port_types_equal};
#[cfg(verus_only)]
use super::selections::bound_type;
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// 型が判明した出力の照合結果。
#[derive(Debug)]
pub struct ModuleOutputTypes<'p, 'a> {
    /// 全断片の配線、型表、および式の検査結果。
    pub expressions: ModuleSelections<'p, 'a>,
    /// 出力宣言順の駆動元の型。まだ型が分からない駆動元は `None`。
    pub outputs: Vec<Option<SignalType<'p, 'a>>>,
}

/// 出力を照合するまでに見つかった違反。
#[derive(Debug)]
pub enum ModuleOutputTypesError<'p, 'a> {
    /// 配線や式に見つかった違反。
    Expressions(ModuleSelectionsError<'p, 'a>),
    /// 出力ポートの宣言型と駆動元の型が異なる。
    Mismatch {
        /// 出力ポートの宣言順の添字。先頭は0。
        index: usize,
        /// 出力宣言の型と、その注釈のソース範囲。
        expected: SignalType<'p, 'a>,
        /// 駆動元の型と、その型を決めたソース範囲。
        actual: SignalType<'p, 'a>,
    },
}

spec fn output_type_at(expressions: &ModuleSelections, index: int, ty: Option<SignalType>) -> bool {
    let drivers = expressions.typed.sources.roots.wiring.drivers;
    let declared = drivers.signature.outputs@[index];
    &&& ty == bound_type(&expressions.typed, expressions.types@, drivers.outputs@[index])
    &&& (ty matches Some(actual) ==> port_types_equal(actual.ty, declared.ty))
}

#[verifier::opaque]
spec fn outputs_before(expressions: &ModuleSelections, types: Seq<Option<SignalType>>) -> bool {
    &&& types.len() <= expressions.typed.sources.roots.wiring.drivers.outputs@.len()
    &&& forall|i: int| 0 <= i < types.len() ==> output_type_at(expressions, i, #[trigger] types[i])
}

spec fn mismatch_at(expressions: &ModuleSelections, index: usize, expected: SignalType, actual: SignalType) -> bool {
    let drivers = expressions.typed.sources.roots.wiring.drivers;
    let port = drivers.signature.outputs@[index as int];
    &&& index < drivers.outputs@.len() && index < drivers.signature.outputs@.len()
    &&& expected == SignalType { ty: port.ty, origin: port.annotation }
    &&& bound_type(&expressions.typed, expressions.types@, drivers.outputs@[index as int]) == Some(actual)
    &&& !port_types_equal(actual.ty, expected.ty)
    &&& location_in_source(expected.origin) && location_in_source(actual.origin)
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// 出力検査の結果から、実引数の照合に使う式の検査結果を取り出す。
    pub(super) proof fn module_output_types_evidence(&self, owner: ModuleBodyPosition, limit: u64, checked: ModuleOutputTypes)
        requires self.module_output_types_result(owner, limit, Ok(Some(checked))),
        ensures self.module_selections_result(owner, limit, Ok(Some(checked.expressions))),
    {
    }
    /// 出力の照合結果と、宣言順で最初に見つかる不一致を定める。
    pub closed spec fn module_output_types_result(&self, owner: ModuleBodyPosition, limit: u64,
        result: Result<Option<ModuleOutputTypes>, ModuleOutputTypesError>) -> bool {
        match result {
            Ok(None) => self.module_selections_result(owner, limit, Ok(None)),
            Err(ModuleOutputTypesError::Expressions(error)) => self.module_selections_result(owner, limit, Err(error)),
            Ok(Some(checked)) => self.module_selections_result(owner, limit, Ok(Some(checked.expressions)))
                && checked.outputs@.len() == checked.expressions.typed.sources.roots.wiring.drivers.outputs@.len()
                && outputs_before(&checked.expressions, checked.outputs@),
            Err(ModuleOutputTypesError::Mismatch { index, expected, actual }) => exists|expressions: ModuleSelections, prior: Seq<Option<SignalType>>|
                #[trigger] self.module_selections_result(owner, limit, Ok(Some(expressions)))
                && #[trigger] outputs_before(&expressions, prior) && prior.len() == index
                && mismatch_at(&expressions, index, expected, actual),
        }
    }

    /// モジュールの出力宣言を、入力からの直結や各断片の定義が持つ型と照合する。
    ///
    /// ビット列は幅が一致する必要がある。構造体は同じ型宣言を指す必要がある。
    /// 駆動元がまだ型の判明していない式なら、その出力の照合を保留する。
    ///
    /// # Errors
    ///
    /// 配線と式の違反を先に返す。その後、出力宣言順で最初に見つけた型の不一致を返す。
    pub fn check_module_output_types(&self, owner: ModuleBodyPosition, limit: u64)
        -> (result: Result<Option<ModuleOutputTypes<'p, 'a>>, ModuleOutputTypesError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.module_output_types_result(owner, limit, result),
    {
        let expressions = match self.check_module_selections(owner, limit) {
            Ok(Some(expressions)) => expressions,
            Ok(None) => return Ok(None),
            Err(error) => return Err(ModuleOutputTypesError::Expressions(error)),
        };
        let drivers = &expressions.typed.sources.roots.wiring.drivers;
        let count = drivers.outputs.len();
        let mut outputs = Vec::new();
        let mut index = 0;
        assert(outputs_before(&expressions, outputs@)) by { reveal(outputs_before); };
        while index < count
            invariant
                self.module_selections_result(owner, limit, Ok(Some(expressions))),
                *drivers == expressions.typed.sources.roots.wiring.drivers,
                index == outputs@.len() <= count == drivers.outputs@.len(),
                outputs_before(&expressions, outputs@),
            decreases count - index,
        {
            proof {
                self.module_selections_evidence(owner, limit, expressions);
                self.module_output_driver(owner, limit, *drivers, index as int);
                self.module_input_sites(owner, limit, *drivers);
            }
            let driver = drivers.outputs[index];
            let declared = &drivers.signature.outputs[index];
            let ty = read_bound_type(&expressions.typed, expressions.types.as_slice(), driver);
            let ty = match ty {
                Some(actual) => {
                    if !actual.ty.is_same_type(&declared.ty) {
                        let expected = SignalType { ty: declared.ty, origin: copy_location(&declared.annotation) };
                        assert(mismatch_at(&expressions, index, expected, actual));
                        return Err(ModuleOutputTypesError::Mismatch { index, expected, actual });
                    }
                    Some(actual)
                },
                None => None,
            };
            assert(output_type_at(&expressions, index as int, ty));
            let ghost prior = outputs@;
            outputs.push(ty);
            assert(outputs_before(&expressions, outputs@)) by {
                reveal(outputs_before);
                assert forall|i: int| 0 <= i < outputs@.len() implies output_type_at(&expressions, i, #[trigger] outputs@[i]) by {
                    if i < index { assert(outputs@[i] == prior[i]); }
                };
            };
            index += 1;
        }
        Ok(Some(ModuleOutputTypes { expressions, outputs }))
    }
}

} // verus!
