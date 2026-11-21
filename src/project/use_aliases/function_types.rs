//! 通常呼び出しの出力型を信号参照に伝え、後続の呼び出しの入力型と照合する。

use super::{
    FuncAtomTypeError, FuncCallInputsError, FuncCallOutputError, FuncCallOutputTypes,
    FuncLiteralError, FuncLiteralWidths, FuncWiringResult, SignalType, StructureExpressionTypeError,
    StructureTypeError, UseAliases,
};
#[cfg(verus_only)]
use super::{DefinitionPosition, FuncWiring, FunctionExpansionOrder,
    ResolvedPortType, TypedFuncCall, call_arity::RootFunctionCall, function_atoms::{
    atoms_match, structure_projection_matches, structure_projection_required, structure_projections_in_order,
    signal_type_at,
}};
#[cfg(verus_only)]
use crate::syntax::{AtomKind, circuit::BitSelectionShape};
#[cfg(verus_only)]
use super::selection_arguments::{
    CheckedBitSelection, nested_named_selection_matches, nested_named_selection_root, selection_arguments_match,
    selection_chain_arguments_match,
};
#[cfg(verus_only)]
use super::function_atoms::named_selection_matches;
#[cfg(verus_only)]
use super::function_drivers::indexed_driver_site;
use alloc::vec::Vec;
use super::signature_cache::SignatureCache;
use super::call_arity::CallArgumentProjections;
use super::function_atoms::FuncProjections;
#[cfg(verus_only)]
use super::function_atoms::{ConcatProjection, StructureProjection, concat_projections_complete, concat_projections_match};
use super::selection_arguments::SelectionArgumentError;
use crate::project::ConcatResultWidthError;
use crate::project::LocatedName;
use vstd::prelude::*;

verus! {

/// 関数の配線、定数幅、および信号ごとに判明した型。
#[derive(Debug)]
pub struct FuncSignalTypes<'p, 'a> {
    /// 配線と定数の右辺の検査結果。対象外や展開待ちも保持する。
    pub literals: FuncLiteralWidths<'p, 'a>,
    /// 左辺の駆動元と同じ順に並ぶ型。未確定の型は `None`。
    /// 対象外や展開待ちでは空になる。
    pub types: Vec<Option<SignalType<'p, 'a>>>,
}

/// 関数内の信号型と呼び出しを検査したときの最初の違反。
#[derive(Debug)]
pub enum FuncSignalTypeError<'p, 'a> {
    /// 配線、入出力数、または定数の幅に関する診断。
    Literal(FuncLiteralError<'p, 'a>),
    /// 右辺全体を占める通常呼び出しの署名または出力に関する診断。
    CallOutput(FuncCallOutputError<'p, 'a>),
    /// 信号参照やビット選択式の型と、駆動先の出力宣言型の不一致。
    Signal(FuncAtomTypeError<'p, 'a>),
    /// ビット選択の入力がビット列型に合わない。
    SelectionInputType {
        /// 入力に指定した信号名の範囲。
        reference: LocatedName<'p, 'a>,
        /// 入力の型と、その型を決めた元ソースの位置。
        actual: SignalType<'p, 'a>,
    },
    /// ビット選択の数値引数または選択範囲の違反。
    SelectionArgument(SelectionArgumentError<'p, 'a>),
    /// 連接の引数がビット列型に合わない。
    ConcatInputType {
        /// 連接の引数のソース範囲。
        reference: LocatedName<'p, 'a>,
        /// 引数の型と、その型を決めた位置。
        actual: SignalType<'p, 'a>,
    },
    /// 連接の合計幅を表せないか、設定上限を超えた。
    ConcatWidth {
        /// 連接式全体のソース範囲。
        expression: LocatedName<'p, 'a>,
        /// 幅の検査で見つかった違反。
        reason: ConcatResultWidthError,
    },
    /// 配置表を準備した際に見つかった構造体の宣言違反。
    StructureLayout(StructureTypeError<'p, 'a>),
    /// 構造体式の型名、入力型、幅、またはフィールドの違反。
    StructureExpression(StructureExpressionTypeError<'p, 'a>),
    /// 直接の引数を検査した呼び出しの位置と、署名または引数に関する診断。
    CallInput(FuncCallInputsError<'p, 'a>),
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    pub(super) proof fn checked_types_keep_wiring(
        &self, file: usize, entry: usize, limit: u64, typed: FuncSignalTypes, wiring: FuncWiring,
    )
        requires
            self.func_signal_types_evidence(file, entry, limit, Ok(typed)),
            typed.literals.wiring == FuncWiringResult::Checked(wiring),
        ensures
            self.func_literal_evidence(file, entry, limit, Ok(typed.literals)),
            self.func_wiring_evidence(file, entry, limit, Ok(FuncWiringResult::Checked(wiring))),
    {
        self.literals_preserve_arity(file, entry, limit, typed.literals);
        self.arity_preserves_wiring(file, entry, limit, typed.literals.wiring);
    }

    proof fn successful_type_roots(
        &self, file: usize, entry: usize, limit: u64, typed: FuncSignalTypes, wiring: FuncWiring,
    ) -> (roots: FuncCallOutputTypes)
        requires
            self.func_signal_types_evidence(file, entry, limit, Ok(typed)),
            typed.literals.wiring == FuncWiringResult::Checked(wiring),
        ensures
            self.signal_type_sources(file, entry, limit, typed.literals, &wiring, roots),
            self.propagated_types_match(file, entry, limit, &wiring, typed.literals, roots, Ok(typed.types)),
    {
        choose|roots: FuncCallOutputTypes|
            #[trigger] self.signal_type_sources(file, entry, limit, typed.literals, &wiring, roots)
            && self.propagated_types_match(file, entry, limit, &wiring, typed.literals, roots, Ok(typed.types))
            && self.prepared_call_inputs_match(file, entry, limit, typed.types@, &wiring, Ok(()))
    }

    /// 同じ関数の型検査に成功すると、定義順の型とその決定位置が一致する。
    pub(super) proof fn checked_function_signal_types_agree(
        &self, file: usize, entry: usize, limit: u64, left: FuncSignalTypes, right: FuncSignalTypes,
    )
        requires
            self.can_resolve(),
            left.literals.wiring is Checked,
            right.literals.wiring is Checked,
            self.func_signal_types_evidence(file, entry, limit, Ok(left)),
            self.func_signal_types_evidence(file, entry, limit, Ok(right)),
        ensures left.types@ == right.types@,
    {
        let l = left.literals.wiring->Checked_0;
        let r = right.literals.wiring->Checked_0;
        let a = self.successful_type_roots(file, entry, limit, left, l);
        let b = self.successful_type_roots(file, entry, limit, right, r);
        self.checked_types_keep_wiring(file, entry, limit, left, l);
        self.checked_types_keep_wiring(file, entry, limit, right, r);
        self.checked_func_wiring_agrees(file, entry, limit, l, r);
        self.checked_literal_widths_agree(file, entry, limit, left.literals, right.literals);
        self.checked_call_output_types_agree(file, entry, limit, a, b);
        let project = self.targets.project_model();
        self.checked_function_atom_types_agree(file, entry, limit,
            &project.sources_model()[file as int], &project.circuits_model()[file as int], &l, &r,
            left.literals.widths@, a.types@, left.types, right.types);
    }

    #[verifier::opaque]
    pub(super) open spec fn root_call_result_types_match(
        &self, typed: FuncSignalTypes, wiring: FuncWiring, row: RootFunctionCall, call: TypedFuncCall,
    ) -> bool {
        let ports = call.signature->Function_0.outputs@;
        forall|offset: int| #![trigger typed.types@[row.first_output + offset]] 0 <= offset < row.count ==> {
            let at = row.first_output + offset;
            let port = ports[offset];
            &&& wiring.drivers.definitions@[at].definition == row.definition
            &&& wiring.drivers.definitions@[at].result_index == offset
            &&& typed.types@[at] == Some(SignalType { ty: port.ty, origin: port.annotation })
        }
    }

    /// 型検査済みの呼び出しから、宣言順の出力型と展開順の添字を取り出す。
    pub(super) proof fn checked_root_call_for_expansion(
        &self, plan: FunctionExpansionOrder, caller: (usize, usize, u64),
        typed: FuncSignalTypes, wiring: FuncWiring, rows: Seq<RootFunctionCall>, index: int,
    ) -> (selection: (TypedFuncCall<'p, 'a>, (int, int)))
        requires
            self.can_resolve(),
            self.function_expansion_evidence(Ok(plan)),
            self.func_signal_types_evidence(caller.0, caller.1, caller.2, Ok(typed)),
            typed.literals.wiring == FuncWiringResult::Checked(wiring),
            typed.types@.len() == wiring.drivers.definitions@.len(),
            self.root_function_calls_match(caller, &wiring.drivers, rows, typed.types@.len()),
            0 <= index < rows.len(),
        ensures
            ({
                let parsed = self.targets.project_model().circuits_model()[caller.0 as int];
                let start = parsed.entry_ranges@[caller.1 as int].definitions.start;
                &&& start <= rows[index].definition
                &&& self.func_call_signature_evidence(caller.0, caller.1, (rows[index].definition - start) as usize,
                    0, caller.2, Ok(Some(selection.0)))
                &&& crate::syntax::circuit::ordinary_call_at(
                    self.targets.project_model().sources_model()[caller.0 as int].text, parsed.syntax.forms@,
                    parsed.definitions@[rows[index].definition as int].expression.start as int,
                    parsed.definitions@[rows[index].definition as int].expression.end as int)
            }),
            selection.0.call.target is Function,
            selection.0.call.target->Function_file == rows[index].target_file,
            selection.0.call.target->Function_entry == rows[index].target_entry,
            0 <= selection.1.0 < selection.1.1 < plan.order_model().len(),
            plan.position_model(selection.1.0) == Some((rows[index].target_file, rows[index].target_entry)),
            plan.position_model(selection.1.1) == Some((caller.0, caller.1)),
            selection.0.signature is Function,
            0 < rows[index].count == selection.0.signature->Function_0.outputs@.len(),
            rows[index].first_output + rows[index].count <= typed.types@.len(),
            self.root_call_result_types_match(typed, wiring, rows[index], selection.0),
    {
        let (file, entry, limit) = caller;
        self.checked_types_keep_wiring(file, entry, limit, typed, wiring);
        let roots = self.successful_type_roots(file, entry, limit, typed, wiring);
        self.call_outputs_fit_wiring(file, entry, limit, &roots, &wiring);
        let call = self.checked_root_function_call(caller, &roots, &wiring, rows, index);
        let row = rows[index];
        let project = self.targets.project_model();
        self.checked_wiring_is_func(file, entry, limit, wiring);
        let parsed = &project.circuits_model()[file as int];
        let source = &project.sources_model()[file as int];
        let start = parsed.entry_ranges@[entry as int].definitions.start;
        assert(start <= row.definition);
        let local = (row.definition - start) as usize;
        self.typed_call_arguments_ready(file, entry, local, 0, limit, call);
        let site = self.expansion_site_for_call(DefinitionPosition { file, entry, definition: local, reference: 0 }, call.call);
        let order = self.function_expansion_callee_precedes(plan, site);
        assert(call.call.target->Function_file == row.target_file && call.call.target->Function_entry == row.target_entry);
        assert(0 <= order.0 < order.1 < plan.order_model().len());
        assert(site.target == (row.target_file, row.target_entry));
        assert(plan.position_model(order.0) == Some((row.target_file, row.target_entry)));
        assert(plan.position_model(order.1) == Some((file, entry)));
        let outputs = call.signature->Function_0.outputs@;
        let expression = parsed.definitions@[row.definition as int].expression;
        crate::syntax::circuit::ordinary_call_excludes_special_forms(
            source.text, parsed.syntax.forms@, expression.start as int, expression.end as int);
        assert forall|offset: int| #![trigger typed.types@[row.first_output + offset]] 0 <= offset < row.count implies {
            let at = row.first_output + offset;
            let port = outputs[offset];
            &&& wiring.drivers.definitions@[at].definition == row.definition
            &&& wiring.drivers.definitions@[at].result_index == offset
            &&& typed.types@[at] == Some(SignalType { ty: port.ty, origin: port.annotation })
        } by {
            let at = row.first_output + offset;
            assert(roots.types@[at] == Some(SignalType { ty: outputs[offset].ty, origin: outputs[offset].annotation }));
            assert(wiring.drivers.definitions@[at].definition == row.definition);
            self.nonliteral_definition_has_no_literal_width(file, entry, limit, &typed.literals, &wiring, at);
            self.atom_call_inherits_output_type(file, entry, limit, source, parsed, &wiring,
                typed.literals.widths@, roots.types@, typed.types, at);
        };
        assert(call.signature is Function && outputs.len() == row.count);
        assert(row.first_output + row.count <= typed.types@.len());
        assert(self.func_call_signature_evidence(caller.0, caller.1, local, 0, caller.2, Ok(Some(call))));
        assert(self.root_call_result_types_match(typed, wiring, row, call)) by {
            reveal(UseAliases::root_call_result_types_match);
        };
        (call, order)
    }

    pub(super) proof fn checked_literal_type(
        &self, file: usize, entry: usize, limit: u64, typed: FuncSignalTypes, wiring: FuncWiring,
        target: int, width: u64,
    )
        requires
            self.func_signal_types_evidence(file, entry, limit, Ok(typed)),
            typed.literals.wiring == FuncWiringResult::Checked(wiring),
            0 <= target < typed.types@.len(),
            typed.literals.widths@[target] == Some(width),
        ensures typed.types@[target] matches Some(ty) && ty.ty == ResolvedPortType::Bits(width),
    {
        let roots = self.successful_type_roots(file, entry, limit, typed, wiring);
        let project = self.targets.project_model();
        self.atom_literal_type(file, entry, limit, &project.sources_model()[file as int],
            &project.circuits_model()[file as int], &wiring, typed.literals.widths@,
            roots.types@, typed.types, target, width);
    }

    pub(super) proof fn checked_bare_rhs_inherits(
        &self, file: usize, entry: usize, limit: u64, typed: FuncSignalTypes, wiring: FuncWiring, target: int,
    )
        requires
            self.func_signal_types_evidence(file, entry, limit, Ok(typed)),
            typed.literals.wiring == FuncWiringResult::Checked(wiring),
            0 <= target < typed.types@.len(),
            target < wiring.drivers.definitions@.len(),
            ({
                let parsed = self.targets.project_model().circuits_model()[file as int];
                let driver = wiring.drivers.definitions@[target];
                let row = parsed.definitions@[driver.definition as int];
                let root = parsed.syntax.forms@[row.expression.start as int];
                driver.result_index == 0 && root is Atom && root->Atom_kind is Name
            }),
        ensures ({
            let parsed = self.targets.project_model().circuits_model()[file as int];
            let row = parsed.definitions@[wiring.drivers.definitions@[target].definition as int];
            let first = row.signals.start - parsed.entry_ranges@[entry as int].signals.start;
            &&& 0 <= first < wiring.signals@.len()
            &&& typed.types@[target] == signal_type_at(&wiring, typed.types@.take(target), wiring.signals@[first].driver)
        }),
    {
        let roots = self.successful_type_roots(file, entry, limit, typed, wiring);
        let project = self.targets.project_model();
        let source = &project.sources_model()[file as int];
        let parsed = &project.circuits_model()[file as int];
        self.nonliteral_definition_has_no_literal_width(file, entry, limit, &typed.literals, &wiring, target);
        self.atom_bare_rhs_inherits(file, entry, limit, source, parsed, &wiring,
            typed.literals.widths@, roots.types@, typed.types, target);
    }

    pub(super) proof fn checked_nor_type(
        &self, file: usize, entry: usize, limit: u64, typed: FuncSignalTypes, wiring: FuncWiring,
        index: int, builtin: TypedFuncCall,
    )
        requires
            self.can_resolve(),
            self.func_signal_types_evidence(file, entry, limit, Ok(typed)),
            typed.literals.wiring == FuncWiringResult::Checked(wiring),
            0 <= index < typed.types@.len() && index < wiring.drivers.definitions@.len(),
            builtin.call.target is Nor,
            ({
                let project = self.targets.project_model();
                let parsed = &project.circuits_model()[file as int];
                let driver = wiring.drivers.definitions@[index];
                let local = (driver.definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
                &&& indexed_driver_site(&project.sources_model()[file as int], parsed, entry as int, driver)
                &&& builtin.call.call.form == parsed.definitions@[driver.definition as int].expression.start
                &&& self.func_call_signature_evidence(file, entry, local, 0, limit, Ok(Some(builtin)))
            }),
        ensures
            typed.types@[index] matches Some(ty) && ty.ty == ResolvedPortType::Bits(1),
            wiring.drivers.definitions@[index].result_index == 0,
    {
        let roots = self.successful_type_roots(file, entry, limit, typed, wiring);
        self.call_outputs_fit_wiring(file, entry, limit, &roots, &wiring);
        self.nor_root_output_type(file, entry, limit, &roots, &wiring, index, builtin);
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[file as int];
        let source = &project.sources_model()[file as int];
        let row = parsed.definitions@[wiring.drivers.definitions@[index].definition as int];
        crate::syntax::circuit::ordinary_call_excludes_special_forms(
            source.text, parsed.syntax.forms@, row.expression.start as int, row.expression.end as int,
        );
        self.nonliteral_definition_has_no_literal_width(file, entry, limit, &typed.literals, &wiring, index);
        self.atom_call_inherits_output_type(file, entry, limit, source, parsed, &wiring,
            typed.literals.widths@, roots.types@, typed.types, index);
    }

    pub(super) proof fn checked_selection_type(
        &self, file: usize, entry: usize, limit: u64, typed: FuncSignalTypes, wiring: FuncWiring,
        index: int, shape: BitSelectionShape, input: SignalType, width: u64,
        origin: LocatedName, selection: CheckedBitSelection,
    )
        requires
            self.func_signal_types_evidence(file, entry, limit, Ok(typed)),
            typed.literals.wiring == FuncWiringResult::Checked(wiring),
            0 <= index < typed.types@.len() && index < wiring.drivers.definitions@.len(),
            ({
                let project = self.targets.project_model();
                let parsed = &project.circuits_model()[file as int];
                let source = &project.sources_model()[file as int];
                let driver = wiring.drivers.definitions@[index];
                let row = parsed.definitions@[driver.definition as int];
                let first = row.signals.start - parsed.entry_ranges@[entry as int].signals.start;
                &&& driver.result_index == 0
                &&& named_selection_matches(source.text, parsed.syntax.forms@, row.expression.start as int, shape)
                &&& signal_type_at(&wiring, typed.types@.take(index), wiring.signals@[first].driver) == Some(input)
                &&& selection_arguments_match(source, parsed.syntax.forms@, &shape, width, &origin, Ok(selection))
            }),
        ensures typed.types@[index] matches Some(ty) && ty.ty == ResolvedPortType::Bits(selection.count),
    {
        let roots = self.successful_type_roots(file, entry, limit, typed, wiring);
        self.call_outputs_fit_wiring(file, entry, limit, &roots, &wiring);
        let project = self.targets.project_model();
        let source = &project.sources_model()[file as int];
        let parsed = &project.circuits_model()[file as int];
        crate::syntax::circuit::bit_selection_shape_positions(
            source.text, parsed.syntax.forms@,
            parsed.definitions@[wiring.drivers.definitions@[index].definition as int].expression.start as int,
            shape,
        );
        self.nonliteral_definition_has_no_literal_width(file, entry, limit, &typed.literals, &wiring, index);
        self.successful_selection_type(file, entry, limit, source, parsed, &wiring, typed.literals.widths@,
            roots.types@, typed.types, index, shape, input, width, origin, selection);
    }

    /// 関数の型検査から、ネストした選択の入力幅と選択範囲の根拠を取り出す。
    pub(super) proof fn checked_nested_selection_type(
        &self, file: usize, entry: usize, limit: u64, typed: FuncSignalTypes, wiring: FuncWiring,
        index: int, steps: Seq<BitSelectionShape>, leaf: usize,
    ) -> (evidence: (u64, LocatedName<'p, 'a>, CheckedBitSelection))
        requires
            self.func_signal_types_evidence(file, entry, limit, Ok(typed)),
            typed.literals.wiring == FuncWiringResult::Checked(wiring),
            0 <= index < typed.types@.len() && index < wiring.drivers.definitions@.len(),
            ({
                let project = self.targets.project_model();
                let parsed = &project.circuits_model()[file as int];
                let source = &project.sources_model()[file as int];
                let driver = wiring.drivers.definitions@[index];
                let row = parsed.definitions@[driver.definition as int];
                let first = row.signals.start - parsed.entry_ranges@[entry as int].signals.start;
                &&& driver.result_index == 0
                &&& nested_named_selection_matches(source.text, parsed.syntax.forms@, row.expression.start, steps, leaf)
                &&& signal_type_at(&wiring, typed.types@.take(index), wiring.signals@[first].driver).is_some()
            }),
        ensures ({
            let project = self.targets.project_model();
            let parsed = &project.circuits_model()[file as int];
            let source = &project.sources_model()[file as int];
            let row = parsed.definitions@[wiring.drivers.definitions@[index].definition as int];
            let first = row.signals.start - parsed.entry_ranges@[entry as int].signals.start;
            let (width, origin, selection) = evidence;
            &&& signal_type_at(&wiring, typed.types@.take(index), wiring.signals@[first].driver)
                == Some(SignalType { ty: ResolvedPortType::Bits(width), origin })
            &&& selection_chain_arguments_match(source, parsed.syntax.forms@, steps, width, origin, Ok(selection))
            &&& typed.types@[index] matches Some(ty) && ty.ty == ResolvedPortType::Bits(selection.count)
        }),
    {
        let roots = self.successful_type_roots(file, entry, limit, typed, wiring);
        self.call_outputs_fit_wiring(file, entry, limit, &roots, &wiring);
        let project = self.targets.project_model();
        let source = &project.sources_model()[file as int];
        let parsed = &project.circuits_model()[file as int];
        let row = parsed.definitions@[wiring.drivers.definitions@[index].definition as int];
        nested_named_selection_root(source.text, parsed.syntax.forms@, row.expression.start, steps, leaf);
        self.nonliteral_definition_has_no_literal_width(file, entry, limit, &typed.literals, &wiring, index);
        self.successful_nested_selection_type(file, entry, limit, source, parsed, &wiring, typed.literals.widths@,
            roots.types@, typed.types, index, steps, leaf)
    }

    pub(super) closed spec fn signal_type_sources(
        &self, file: usize, entry: usize, limit: u64, literals: FuncLiteralWidths, wiring: &FuncWiring,
        roots: FuncCallOutputTypes,
    ) -> bool {
        &&& literals.wiring == FuncWiringResult::Checked(*wiring)
        &&& roots.wiring == literals.wiring
        &&& self.func_literal_evidence(file, entry, limit, Ok(literals))
        &&& self.func_call_outputs_evidence(file, entry, limit, Ok(roots))
    }

    spec fn propagated_types_match(
        &self, file: usize, entry: usize, limit: u64, wiring: &FuncWiring, literals: FuncLiteralWidths,
        roots: FuncCallOutputTypes, result: Result<Vec<Option<SignalType>>, FuncSignalTypeError>,
    ) -> bool {
        let project = self.targets.project_model();
        atoms_match(self, file, limit, &project.sources_model()[file as int], &project.circuits_model()[file as int],
            entry as int, wiring, literals.widths@, roots.types@, result)
    }

    /// 定数と通常呼び出しの型、信号の束縛、直接の引数の検査が結果に対応することを表す。
    pub closed spec fn func_signal_types_evidence(
        &self, file: usize, entry: usize, limit: u64, result: Result<FuncSignalTypes, FuncSignalTypeError>,
    ) -> bool {
        match result {
            Err(FuncSignalTypeError::Literal(error)) => self.func_literal_evidence(file, entry, limit, Err(error)),
            Err(FuncSignalTypeError::CallOutput(error)) => !(error is Caller)
                && self.func_call_outputs_evidence(file, entry, limit, Err(error))
                && exists|literals: FuncLiteralWidths| literals.wiring matches FuncWiringResult::Checked(scope)
                    && #[trigger] self.func_literal_evidence(file, entry, limit, Ok(literals))
                    && self.call_output_failure(file, entry, limit, &scope.drivers, error),
            Err(error) if error is Signal || error is SelectionInputType || error is SelectionArgument
                || error is ConcatInputType || error is ConcatWidth || error is StructureLayout || error is StructureExpression =>
                exists|literals: FuncLiteralWidths, wiring: FuncWiring, roots: FuncCallOutputTypes|
                #[trigger] self.signal_type_sources(file, entry, limit, literals, &wiring, roots)
                && self.propagated_types_match(file, entry, limit, &wiring, literals, roots, Err(error)),
            Err(FuncSignalTypeError::CallInput(error)) => exists|literals: FuncLiteralWidths, wiring: FuncWiring,
                roots: FuncCallOutputTypes, types: Vec<Option<SignalType>>|
                #[trigger] self.signal_type_sources(file, entry, limit, literals, &wiring, roots)
                && #[trigger] self.propagated_types_match(file, entry, limit, &wiring, literals, roots, Ok(types))
                && self.prepared_call_inputs_match(file, entry, limit, types@, &wiring, Err(error)),
            Ok(result) => self.func_literal_evidence(file, entry, limit, Ok(result.literals))
                && if let FuncWiringResult::Checked(wiring) = result.literals.wiring {
                    exists|roots: FuncCallOutputTypes|
                        #[trigger] self.signal_type_sources(file, entry, limit, result.literals, &wiring, roots)
                        && self.propagated_types_match(file, entry, limit, &wiring, result.literals, roots, Ok(result.types))
                        && self.prepared_call_inputs_match(file, entry, limit, result.types@, &wiring, Ok(()))
                } else { result.types@.len() == 0 },
            _ => false,
        }
    }

    /// 定数と通常呼び出しから得た型を信号参照に伝え、関数内の呼び出しを検査する。
    ///
    /// 右辺全体が通常呼び出しなら、出力型を左辺の名前へ順に割り当てる。
    /// 裸の信号名は入力または先行定義の型を引き継ぐ。`bit` と `slice` の最内段の入力が
    /// 型の分かる裸の信号名、またはその信号の `field` なら、内側から順に選択範囲を検査する。
    /// 裸の信号名を入力とする `field`・`as`・`raw` は構造体の型と配置を検査する。
    /// `concat` では、型が判明した裸のビット列信号と定数 `0`・`1` の幅を足す。
    /// 幅が未確定の引数があっても、型が判明した引数は調べ、最初の型違反を返す。
    /// 呼び出しの直接の引数が定数か、
    /// 型の判明した裸の信号名なら、対応する入力型と照合する。
    /// 参照先の署名が得られたら、その署名をこの検査の入出力の照合で再利用する。
    /// ほかの複合式の結果型は保留する。展開待ちは呼び出し位置を保ったまま返す。
    ///
    /// # Examples
    ///
    /// 構造体を経由する定義から、フィールドの型と構造体の総幅を引き継ぐ。
    ///
    /// ```
    /// use circuitgame2_core::project::{
    ///     ResolvedPortType, SourceSnapshot, check_use_aliases, index_use_targets, parse_circuit_project,
    /// };
    /// let project = parse_circuit_project(&[SourceSnapshot {
    ///     path: "packet.ncg2", revision: 1,
    ///     text: "(struct Packet (width 8) (tag (bits 3) (at 2)))
    ///            (func unpack (in (bus (bits 8))) (out (tag (bits 3)) (raw-bus (bits 8)))
    ///                (def packet (as Packet bus))
    ///                (def tag (field packet tag))
    ///                (def raw-bus (raw packet)))",
    /// }]).unwrap();
    /// let targets = index_use_targets(&project).unwrap();
    /// let aliases = check_use_aliases(&targets).unwrap();
    /// let checked = aliases.check_func_signal_types(0, 1, 8).unwrap();
    /// assert!(matches!(checked.types[0].as_ref().unwrap().ty, ResolvedPortType::Struct { .. }));
    /// assert!(matches!(checked.types[1].as_ref().unwrap().ty, ResolvedPortType::Bits(3)));
    /// assert!(matches!(checked.types[2].as_ref().unwrap().ty, ResolvedPortType::Bits(8)));
    /// ```
    ///
    /// # Errors
    ///
    /// 配線・入出力数・定数幅、通常呼び出しの出力、定義順の型伝播、直接の引数の順に検査する。
    /// 型が判明した信号に対する構造体式を最初に調べる時点で、プロジェクト全体の構造体の配置と循環を検査する。
    /// その後、式ごとに `as` の型名を解決し、入力型、幅、フィールドを照合する。
    pub fn check_func_signal_types(
        &self, file: usize, entry: usize, max_width: u64,
    ) -> (result: Result<FuncSignalTypes<'p, 'a>, FuncSignalTypeError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.func_signal_types_evidence(file, entry, max_width, result),
    {
        match self.check_func_signal_projections(file, entry, max_width, false, false) {
            Ok((types, _)) => Ok(types),
            Err(error) => Err(error),
        }
    }

    pub(super) fn check_func_signal_projections(
        &self, file: usize, entry: usize, max_width: u64, retain_concat: bool, retain_calls: bool,
    ) -> (result: Result<(FuncSignalTypes<'p, 'a>, FuncProjections<'p, 'a>), FuncSignalTypeError<'p, 'a>>)
        requires self.can_resolve(),
        ensures
            self.func_signal_types_evidence(file, entry, max_width, match result {
                Ok((types, _)) => Ok(types),
                Err(error) => Err(error),
            }),
            result matches Ok((typed, projections)) ==> {
                &&& projections.layouts matches Some(layouts) ==> self.structure_types_match(max_width, Ok(layouts))
                &&& projections.layouts.is_none() ==> projections.entries@.len() == 0
                &&& !retain_concat ==> projections.concats@.len() == 0
                &&& !retain_calls ==> projections.calls@.len() == 0
                &&& projections.call_arguments.ranges@.len() == projections.calls@.len()
                &&& if let FuncWiringResult::Checked(wiring) = typed.literals.wiring {
                    &&& typed.types@.len() == wiring.drivers.definitions@.len()
                    &&& retain_calls ==> self.root_function_calls_match((file, entry, max_width), &wiring.drivers,
                        projections.calls@, typed.types@.len())
                    &&& (retain_calls ==> self.projected_references_match((file, entry, max_width), typed.types@, &wiring,
                        &projections.call_arguments, projections.calls@))
                    &&& concat_projections_match(file, entry, max_width,
                        &self.targets.project_model().sources_model()[file as int],
                        &self.targets.project_model().circuits_model()[file as int], &wiring, typed.types@, projections.concats@)
                    &&& structure_projections_in_order(projections.entries@, typed.types@.len() as int,
                        wiring.drivers.signature.inputs@.len() as int)
                    &&& projections.layouts matches Some(table) ==> forall|j: int| 0 <= j < projections.entries@.len()
                        ==> structure_projection_matches(self, file, entry, max_width, &wiring, table, typed.types@,
                            #[trigger] projections.entries@[j])
                    &&& self.func_structure_projections_complete(file, entry, max_width, typed, &wiring, projections.entries@)
                    &&& retain_concat ==> self.func_concat_projections_complete(file, entry, max_width, typed, &wiring, projections.concats@)
                } else {
                    projections.entries@.len() == 0 && projections.concats@.len() == 0 && projections.calls@.len() == 0
                }
            },
    {
        let literals = match self.check_func_literal_widths(file, entry, max_width) {
            Ok(literals) => literals,
            Err(error) => return Err(FuncSignalTypeError::Literal(error)),
        };
        if !matches!(literals.wiring, FuncWiringResult::Checked(_)) {
            return Ok((
                FuncSignalTypes { literals, types: Vec::new() },
                FuncProjections {
                    entries: Vec::new(), layouts: None, concats: Vec::new(), calls: Vec::new(),
                    call_arguments: CallArgumentProjections::new(),
                },
            ));
        }
        proof { self.literals_preserve_arity(file, entry, max_width, literals); }
        let ghost prepared = literals;
        let FuncLiteralWidths { wiring: prepared_wiring, widths: literal_widths } = literals;
        let mut signatures = SignatureCache::new();
        let mut calls = Vec::new();
        let outputs = match self.check_call_outputs_with_arity(file, entry, max_width, prepared_wiring, &mut signatures,
            &mut calls, retain_calls)
        {
            Ok(outputs) => outputs,
            Err(error) => {
                assert(self.func_signal_types_evidence(file, entry, max_width, Err(FuncSignalTypeError::CallOutput(error)))) by {
                    assert(self.func_literal_evidence(file, entry, max_width, Ok(prepared)));
                };
                return Err(FuncSignalTypeError::CallOutput(error));
            },
        };
        let ghost roots = outputs;
        let FuncCallOutputTypes { wiring: checked_wiring, types: call_types } = outputs;
        let literals = FuncLiteralWidths { wiring: checked_wiring, widths: literal_widths };
        let FuncWiringResult::Checked(ref scope) = literals.wiring else {
            proof { assert(false); }
            unreachable!()
        };
        proof {
            assert(literals == prepared);
            self.arity_preserves_wiring(file, entry, max_width, literals.wiring);
            self.checked_wiring_is_func(file, entry, max_width, *scope);
            self.literal_widths_fit_wiring(file, entry, max_width, &literals, scope);
            self.call_outputs_fit_wiring(file, entry, max_width, &roots, scope);
            assert(self.signal_type_sources(file, entry, max_width, literals, scope, roots));
        }
        let (types, mut projections) = match self.check_atoms(file, entry, max_width, &literals, scope, call_types.as_slice(), retain_concat) {
            Ok(propagated) => propagated,
            Err(error) => {
                assert(self.func_signal_types_evidence(file, entry, max_width, Err(error))) by {
                    assert(self.propagated_types_match(file, entry, max_width, scope, literals, roots, Err(error)));
                };
                return Err(error);
            },
        };
        assert(self.propagated_types_match(file, entry, max_width, scope, literals, roots, Ok(types)));
        let type_slice = types.as_slice();
        proof {
            if retain_calls {
                self.root_calls_follow_definition_order((file, entry, max_width), scope, calls@);
            }
        }
        let mut call_arguments = CallArgumentProjections::new();
        let checked = self.check_all_inputs_with_types(file, entry, max_width, type_slice, scope, &mut signatures,
            calls.as_slice(), &mut call_arguments, retain_calls);
        match checked {
            Ok(()) => {
                proof {
                    assert(type_slice@ == types@);
                    self.prepared_inputs_succeeded(file, entry, max_width, types@, scope, checked);
                }
                assert(exists|outputs: FuncCallOutputTypes|
                    #[trigger] self.signal_type_sources(file, entry, max_width, literals, scope, outputs)
                    && self.propagated_types_match(file, entry, max_width, scope, literals, outputs, Ok(types))
                    && self.prepared_call_inputs_match(file, entry, max_width, types@, scope, Ok(()))) by {
                    assert(self.signal_type_sources(file, entry, max_width, literals, scope, roots));
                };
                projections.calls = calls;
                projections.call_arguments = call_arguments;
                Ok((FuncSignalTypes { literals, types }, projections))
            },
            Err(error) => {
                assert(self.func_signal_types_evidence(file, entry, max_width, Err(FuncSignalTypeError::CallInput(error))));
                Err(FuncSignalTypeError::CallInput(error))
            },
        }
    }

    pub(super) open spec fn func_structure_projections_complete(
        &self, file: usize, entry: usize, limit: u64, typed: FuncSignalTypes,
        wiring: &FuncWiring, rows: Seq<StructureProjection>,
    ) -> bool {
        let project = self.targets.project_model();
        exists|roots: FuncCallOutputTypes|
            #[trigger] self.signal_type_sources(file, entry, limit, typed.literals, wiring, roots)
            && roots.types@.len() == wiring.drivers.definitions@.len()
            && (forall|target: int| 0 <= target < typed.types@.len() &&
                #[trigger] structure_projection_required(
                    &project.sources_model()[file as int], &project.circuits_model()[file as int],
                    entry, wiring, typed.literals.widths@, roots.types@, typed.types@, target,
                ) ==> exists|j: int| 0 <= j < rows.len() && (#[trigger] rows[j]).target == target)
    }

    pub(super) open spec fn func_concat_projections_complete(
        &self, file: usize, entry: usize, limit: u64, typed: FuncSignalTypes,
        wiring: &FuncWiring, rows: Seq<ConcatProjection>,
    ) -> bool {
        let project = self.targets.project_model();
        exists|roots: FuncCallOutputTypes|
            #[trigger] self.signal_type_sources(file, entry, limit, typed.literals, wiring, roots)
            && roots.types@.len() == wiring.drivers.definitions@.len()
            && concat_projections_complete(&project.sources_model()[file as int], &project.circuits_model()[file as int],
                wiring, typed.literals.widths@, roots.types@, typed.types@, rows)
    }
}

} // verus!
