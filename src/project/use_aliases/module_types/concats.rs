//! 連接の引数をソース順で型検査し、合計のビット幅を求める。

use super::{ModuleAliasTypes, ModuleAliasTypesError, UseAliases, aliases::find_member, selections::read_bound_type};
use crate::project::use_aliases::{function_atoms::copy_signal_type, selection_arguments::check_selection_chain};
use crate::project::{CheckedBitSelection, CircuitLiteralWidthError, ConcatResultWidthError, LocatedName, ModuleBodyPosition, OutputDriver,
    ProjectSource, ResolvedPortType, SelectionArgumentError, SignalType, check_circuit_literal_width, check_concat_result_width,
    circuits::{form_location, read_indexed_atom}};
#[cfg(verus_only)]
use crate::project::{circuit_literal_width_matches, concat_result_width_matches, location_in_source,
    circuits::{is_form_location, parsed_circuit_matches, parsed_index_evidence}};
#[cfg(verus_only)]
use super::{propagation::type_sites_valid, selections::bound_type};
#[cfg(verus_only)]
use crate::project::use_aliases::selection_arguments::{selection_chain_arguments_match, selection_parameters_match,
    successful_selection_chain_counts_agree};
#[cfg(verus_only)]
use crate::project::{concat_result_widths_agree, literal_width::successful_literal_widths_agree};
use crate::syntax::{AtomKind, Form, circuit::{NamedBuildCircuit, bit_selection_chain, concat_argument_range,
    definition_target_atoms, next_call_argument}};
#[cfg(verus_only)]
use crate::syntax::{complete_list_indices, form_span, form_spans_valid, nested_list_indices, circuit::{build_definition_scope_evidence,
    bit_selection_path, bit_selection_paths_agree, bit_selection_shape_matches, bit_selection_shape_positions, BitSelectionShape,
    concat_argument_ranges_agree, concat_arguments_evidence, concat_arguments_match, concat_excludes_other_shapes,
    definition_signal_positions_agree, definition_signal_positions_in_order, definition_target_range,
    ordinary_call_at, ordinary_call_excludes_special_forms,
    direct_form_in_range, expression_region, following_concat_argument, indexed_concat_selected_signal}};
use alloc::vec::Vec;
use core::ops::Range;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 連接の引数の構文位置と幅。引数順に低位から配置する。
#[derive(Debug)]
pub struct ModuleConcatOperand {
    /// 引数の先頭を指す構文木の添字。
    pub form: usize,
    /// 信号とその選択の駆動元。リテラルの場合は `None`。
    pub driver: Option<OutputDriver>,
    /// ビット選択の場合に、駆動元のビット列から引数への射影を表す。
    pub selection: Option<CheckedBitSelection>,
    /// 引数のビット幅。
    pub width: u64,
}

/// 幅が確定した連接と、低位側から並ぶ引数。
#[derive(Debug)]
pub struct ModuleConcat<'p, 'a> {
    /// 結果の型と、連接式全体のソース範囲。
    pub result: SignalType<'p, 'a>,
    /// ソース順の引数。
    pub operands: Vec<ModuleConcatOperand>,
}

/// 型伝播の結果と、この段階で幅を決められた連接。
#[derive(Debug)]
pub struct ModuleConcats<'p, 'a> {
    /// 全断片の配線と確定済みの型。
    pub typed: ModuleAliasTypes<'p, 'a>,
    /// 別名と連接で追加の型を求めた、左辺の駆動元順の型表。
    pub types: Vec<Option<SignalType<'p, 'a>>>,
    /// 左辺の駆動元順の連接。対象外または保留中なら `None`。
    pub concats: Vec<Option<ModuleConcat<'p, 'a>>>,
}

/// 連接の前段または直接引数の検査で見つかった違反。
#[derive(Debug)]
pub enum ModuleConcatsError<'p, 'a> {
    /// 配線など、連接を検査する前に見つかった違反。
    Types(ModuleAliasTypesError<'p, 'a>),
    /// 出力が一つの連接を複数の左辺に割り当てた。
    Outputs {
        /// 連接式全体のソース範囲。
        expression: LocatedName<'p, 'a>,
        /// 左辺全体のソース範囲。
        left: LocatedName<'p, 'a>,
        /// 左辺の名前の数。
        targets: usize,
    },
    /// ビット列以外の型の信号を連接に渡した。
    InputType {
        /// 信号を書いた引数の範囲。
        argument: LocatedName<'p, 'a>,
        /// 実際の型と、型の根拠となる範囲。
        actual: SignalType<'p, 'a>,
    },
    /// リテラルの幅に違反がある。
    Literal {
        /// リテラルのソース範囲。
        literal: LocatedName<'p, 'a>,
        /// 幅の違反の理由。
        error: CircuitLiteralWidthError,
    },
    /// 引数のビット選択が、選択元の幅または引数の条件を満たさない。
    Selection(SelectionArgumentError<'p, 'a>),
    /// 合計幅を表せないか、設定した上限を超えた。
    Width {
        /// 連接式全体のソース範囲。
        concat: LocatedName<'p, 'a>,
        /// 合計幅に関する違反。
        reason: ConcatResultWidthError,
    },
}

struct ConcatContext<'w, 'p, 'a> {
    typed: &'w ModuleAliasTypes<'p, 'a>,
    types: &'w Vec<Option<SignalType<'p, 'a>>>,
    body: ModuleBodyPosition,
    member: usize,
    definition: usize,
    source: &'p ProjectSource<'a>,
    parsed: &'p NamedBuildCircuit<'a>,
}

/// 定義の信号索引から、指定したフォームの位置を二分探索する。
pub(super) fn find_signal(signals: &[usize], start: usize, end: usize, form: usize) -> (result: Option<usize>)
    requires
        start <= end <= signals@.len(),
        forall|i: int, j: int| start <= i < j < end ==> #[trigger] signals@[i] < #[trigger] signals@[j],
    ensures
        result matches Some(position) ==> start <= position < end && signals@[position as int] == form,
        result.is_none() <==> (forall|i: int| start <= i < end ==> (#[trigger] signals@[i]) != form),
{
    let mut low = start;
    let mut high = end;
    while low < high
        invariant
            start <= low <= high <= end <= signals@.len(),
            forall|i: int, j: int| start <= i < j < end ==> #[trigger] signals@[i] < #[trigger] signals@[j],
            forall|i: int| start <= i < end && (i < low || high <= i) ==> (#[trigger] signals@[i]) != form,
        decreases high - low,
    {
        let middle = low + (high - low) / 2;
        let current = signals[middle];
        if current == form { return Some(middle); }
        if current < form {
            assert forall|i: int| low <= i <= middle implies (#[trigger] signals@[i]) != form by {
                if i < middle { assert(signals@[i] < signals@[middle as int]); }
            };
            low = middle + 1;
        } else {
            assert forall|i: int| middle <= i < high implies (#[trigger] signals@[i]) != form by {
                if middle < i { assert(signals@[middle as int] < signals@[i]); }
            };
            high = middle;
        }
    }
    None
}

spec fn argument_end(forms: Seq<Form>, root: int) -> int {
    if forms[root] is List { forms[root]->List_end as int } else { root + 1 }
}

spec fn concat_named_operand(
    context: &ConcatContext, form: usize, steps: Seq<BitSelectionShape>, leaf: usize,
    result: Result<Option<ModuleConcatOperand>, ModuleConcatsError>,
) -> bool {
    let forms = context.parsed.syntax.forms@;
    let wiring = &context.typed.sources.roots.wiring;
    let row = context.parsed.definitions@[context.definition as int];
    let frame = context.parsed.entry_ranges@[context.body.entry as int].signals;
    exists|i: int| row.signals.start <= i < row.signals.end && (#[trigger] context.parsed.signals@[i]) == leaf
        && {
            let bound = wiring.signals@[context.member as int]@[i - frame.start];
            &&& bound.form == leaf
            &&& concat_bound_operand(context.source, forms, form, steps, leaf, bound.driver,
                bound_type(context.typed, context.types@, bound.driver), result)
        }
}

spec fn concat_bound_operand(
    source: &ProjectSource, forms: Seq<Form>, form: usize, steps: Seq<BitSelectionShape>, leaf: usize,
    driver: OutputDriver, base: Option<SignalType>, result: Result<Option<ModuleConcatOperand>, ModuleConcatsError>,
) -> bool {
    match base {
        None => result == Ok(None),
        Some(ty) => match ty.ty {
            ResolvedPortType::Bits(width) => {
                if steps.len() == 0 {
                    result matches Ok(Some(item)) && item.form == form
                        && item.driver == Some(driver) && item.width == width && item.selection.is_none()
                } else {
                    match result {
                        Ok(Some(item)) => item.selection matches Some(selection)
                            && item.form == form && item.driver == Some(driver)
                            && item.width == selection.count && selection.fits(width)
                            && selection_chain_arguments_match(source, forms, steps, width, ty.origin, Ok(selection)),
                        Err(ModuleConcatsError::Selection(error)) =>
                            selection_chain_arguments_match(source, forms, steps, width, ty.origin, Err(error)),
                        _ => false,
                    }
                }
            },
            ResolvedPortType::Struct { .. } => result matches Err(ModuleConcatsError::InputType { argument, actual })
                && is_form_location(source, forms[leaf as int], argument) && actual == ty,
        },
    }
}

#[verifier::opaque]
spec fn concat_operand(
    context: &ConcatContext, form: usize, limit: u64, result: Result<Option<ModuleConcatOperand>, ModuleConcatsError>,
) -> bool {
    let forms = context.parsed.syntax.forms@;
    let atom = forms[form as int];
    let literal = atom is Atom && (atom->Atom_kind is Natural || atom->Atom_kind is Binary || atom->Atom_kind is Hexadecimal);
    &&& result matches Ok(Some(item)) ==> item.form == form && item.driver.is_none() == literal
    &&& if literal {
        let span = form_span(atom);
        let bytes = context.source.text.spec_bytes()[span.start as int..span.end as int];
        match result {
            Ok(Some(item)) => item.form == form && item.driver.is_none()
                && item.selection.is_none()
                && circuit_literal_width_matches(bytes, None, limit, Ok(item.width)),
            Err(ModuleConcatsError::Literal { literal, error }) => is_form_location(context.source, atom, literal)
                && circuit_literal_width_matches(bytes, None, limit, Err(error)),
            _ => false,
        }
    } else {
        exists|steps: Seq<BitSelectionShape>, leaf: usize|
            #[trigger] bit_selection_path(context.source.text, forms, form, steps, leaf)
                && !(exists|shape: BitSelectionShape| #[trigger] bit_selection_shape_matches(context.source.text, forms, leaf as int, shape))
                && if leaf < forms.len() && forms[leaf as int] is Atom && forms[leaf as int]->Atom_kind is Name {
                    concat_named_operand(context, form, steps, leaf, result)
                } else { result == Ok(None) }
    }
}

proof fn concat_operand_signal<'p, 'a>(
    context: &ConcatContext<'_, 'p, 'a>, form: usize, limit: u64, item: ModuleConcatOperand,
) -> (evidence: (Seq<BitSelectionShape>, usize, int, SignalType<'p, 'a>))
    requires
        form < context.parsed.syntax.forms@.len(),
        item.driver.is_some(),
        concat_operand(context, form, limit, Ok(Some(item))),
    ensures ({
        let (steps, leaf, position, base) = evidence;
        let parsed = context.parsed;
        let forms = parsed.syntax.forms@;
        let row = parsed.definitions@[context.definition as int];
        let frame = parsed.entry_ranges@[context.body.entry as int].signals;
        let bound = context.typed.sources.roots.wiring.signals@[context.member as int]@[position - frame.start];
        &&& bit_selection_path(context.source.text, forms, form, steps, leaf)
        &&& !(exists|shape: BitSelectionShape| #[trigger] bit_selection_shape_matches(context.source.text, forms, leaf as int, shape))
        &&& leaf < forms.len()
        &&& forms[leaf as int] is Atom && forms[leaf as int]->Atom_kind is Name
        &&& row.signals.start <= position < row.signals.end && parsed.signals@[position] == leaf
        &&& bound.form == leaf && item.driver == Some(bound.driver)
        &&& bound_type(context.typed, context.types@, bound.driver) == Some(base)
        &&& base.ty is Bits
        &&& item.form == form
        &&& match item.selection {
            Some(selection) => steps.len() > 0 && selection.count == item.width && selection.fits(base.ty->Bits_0)
                && selection_chain_arguments_match(context.source, forms, steps, base.ty->Bits_0, base.origin, Ok(selection)),
            None => steps.len() == 0 && base.ty == ResolvedPortType::Bits(item.width),
        }
    }),
{
    reveal(concat_operand);
    let parsed = context.parsed;
    let forms = parsed.syntax.forms@;
    let (steps, leaf) = choose|steps: Seq<BitSelectionShape>, leaf: usize|
        #[trigger] bit_selection_path(context.source.text, forms, form, steps, leaf)
        && !(exists|shape: BitSelectionShape| #[trigger] bit_selection_shape_matches(context.source.text, forms, leaf as int, shape))
        && leaf < forms.len() && forms[leaf as int] is Atom && forms[leaf as int]->Atom_kind is Name
        && concat_named_operand(context, form, steps, leaf, Ok(Some(item)));
    let wiring = context.typed.sources.roots.wiring;
    let row = parsed.definitions@[context.definition as int];
    let frame = parsed.entry_ranges@[context.body.entry as int].signals;
    let position = choose|i: int| row.signals.start <= i < row.signals.end && (#[trigger] parsed.signals@[i]) == leaf
        && {
            let bound = wiring.signals@[context.member as int]@[i - frame.start];
            &&& bound.form == leaf
            &&& concat_bound_operand(context.source, forms, form, steps, leaf, bound.driver,
                bound_type(context.typed, context.types@, bound.driver), Ok(Some(item)))
        };
    let bound = wiring.signals@[context.member as int]@[position - frame.start];
    (steps, leaf, position, bound_type(context.typed, context.types@, bound.driver)->Some_0)
}

#[verifier::opaque]
spec fn operand_prefix(context: &ConcatContext, arguments: Range<usize>, cursor: usize, limit: u64,
    operands: Seq<ModuleConcatOperand>) -> bool {
    let forms = context.parsed.syntax.forms@;
    &&& cursor as int == if operands.len() == 0 { arguments.start as int }
        else { argument_end(forms, operands.last().form as int) }
    &&& forall|i: int| 0 <= i < operands.len() ==> {
        let item = #[trigger] operands[i];
        &&& arguments.start <= item.form < argument_end(forms, item.form as int) <= cursor <= arguments.end
        &&& item.form == if i == 0 { arguments.start as int } else { argument_end(forms, operands[i - 1].form as int) }
        &&& concat_operand(context, item.form, limit, Ok(Some(item)))
    }
}

/// 同じ構文範囲を読む二つの検査では、指定した引数が同じフォームから始まる。
proof fn concat_operand_roots_agree(
    before: &ConcatContext, after: &ConcatContext, arguments: Range<usize>, limit: u64,
    left: Seq<ModuleConcatOperand>, right: Seq<ModuleConcatOperand>, index: int,
)
    requires
        before.parsed == after.parsed,
        operand_prefix(before, arguments, arguments.end, limit, left),
        operand_prefix(after, arguments, arguments.end, limit, right),
        0 <= index < left.len(), index < right.len(),
    ensures left[index].form == right[index].form,
    decreases index,
{
    reveal(operand_prefix);
    assert(left[index].form >= arguments.start && right[index].form >= arguments.start);
    if index > 0 {
        concat_operand_roots_agree(before, after, arguments, limit, left, right, index - 1);
        assert(left[index].form == argument_end(before.parsed.syntax.forms@, left[index - 1].form as int));
        assert(right[index].form == argument_end(after.parsed.syntax.forms@, right[index - 1].form as int));
    }
}

proof fn concat_operand_count_agrees(
    before: &ConcatContext, after: &ConcatContext, arguments: Range<usize>, limit: u64,
    left: Seq<ModuleConcatOperand>, right: Seq<ModuleConcatOperand>,
)
    requires
        before.parsed == after.parsed,
        arguments.start < arguments.end,
        operand_prefix(before, arguments, arguments.end, limit, left),
        operand_prefix(after, arguments, arguments.end, limit, right),
    ensures left.len() == right.len(),
{
    reveal(operand_prefix);
    if left.len() != right.len() {
        let i = if left.len() < right.len() { left.len() as int - 1 } else { right.len() as int - 1 };
        concat_operand_roots_agree(before, after, arguments, limit, left, right, i);
        if left.len() < right.len() {
            assert(right[i + 1].form == arguments.end);
            assert(right[i + 1].form < arguments.end);
        } else {
            assert(left[i + 1].form == arguments.end);
            assert(left[i + 1].form < arguments.end);
        }
    }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn concat_context(&self, owner: ModuleBodyPosition, limit: u64, context: &ConcatContext) -> bool {
        let project = self.targets.project_model();
        let wiring = context.typed.sources.roots.wiring;
        let body = context.body;
        &&& self.can_resolve() && self.module_alias_types_result(owner, limit, Ok(Some(*context.typed)))
        &&& context.types@.len() == wiring.drivers.definitions@.len()
        &&& body.file < project.circuits_model().len() && body.file < project.sources_model().len()
        &&& *context.parsed == project.circuits_model()[body.file as int]
        &&& *context.source == project.sources_model()[body.file as int]
        &&& parsed_circuit_matches(*context.source, *context.parsed)
        &&& body.entry < context.parsed.syntax.entries@.len() && body.entry < context.parsed.entry_ranges@.len()
        &&& context.member < wiring.drivers.body.members@.len() && wiring.drivers.body.members@[context.member as int] == body
        &&& {
            let frame = context.parsed.entry_ranges@[body.entry as int].definitions;
            frame.start <= context.definition < frame.end <= context.parsed.definitions@.len()
        }
    }

    fn check_concat_operand(&self, _owner: ModuleBodyPosition, limit: u64, context: &ConcatContext<'_, 'p, 'a>,
        Ghost(arguments): Ghost<Range<usize>>, at: usize,
    ) -> (result: Result<Option<ModuleConcatOperand>, ModuleConcatsError<'p, 'a>>)
        requires
            self.concat_context(_owner, limit, context), at < context.parsed.syntax.forms@.len(),
            type_sites_valid(context.types@),
            concat_arguments_match(context.source.text, context.parsed.syntax.forms@,
                context.parsed.definitions@[context.definition as int].expression.start as int, arguments),
            direct_form_in_range(context.parsed.syntax.forms@, arguments.start as int, arguments.end as int, at as int),
        ensures
            concat_operand(context, at, limit, result),
            result matches Ok(Some(item)) ==> item.form == at,
            result matches Err(error) ==> !(error is Types),
    {
        let source = context.source;
        let parsed = context.parsed;
        let forms = parsed.syntax.forms.as_slice();
        let row = &parsed.definitions[context.definition];
        proof { parsed_index_evidence(*source, *parsed); reveal(concat_operand); }
        if matches!(forms[at], Form::Atom { kind: AtomKind::Natural | AtomKind::Binary | AtomKind::Hexadecimal, .. }) {
            let (word, _) = read_indexed_atom(source.text, forms, at);
            return match check_circuit_literal_width(word, None, limit) {
                Ok(width) => Ok(Some(ModuleConcatOperand { form: at, driver: None, selection: None, width })),
                Err(error) => Err(ModuleConcatsError::Literal { literal: form_location(source, forms, at), error }),
            };
        }
        let (steps, leaf) = bit_selection_chain(source.text, forms, at);
        if leaf >= forms.len() || !matches!(forms[leaf], Form::Atom { kind: AtomKind::Name, .. }) {
            return Ok(None);
        }
        let ghost model = parsed.build_model();
        proof {
            indexed_concat_selected_signal(source.text, &model, context.body.entry as int, context.definition as int,
                arguments, at, steps@, leaf);
            definition_signal_positions_in_order(source.text, &model, context.body.entry as int, context.definition as int);
            build_definition_scope_evidence(source.text, &model, context.body.entry as int, context.definition as int);
        }
        let Some(position) = find_signal(parsed.signals.as_slice(), row.signals.start, row.signals.end, leaf) else {
            unreachable!()
        };
        let wiring = &context.typed.sources.roots.wiring;
        let frame = &parsed.entry_ranges[context.body.entry].signals;
        proof {
            self.module_alias_types_evidence(_owner, limit, *context.typed);
            self.module_signal_index_item(_owner, limit, *wiring, context.member as int, position as int);
            self.module_wiring_keeps_drivers(_owner, limit, *wiring);
            self.module_input_sites(_owner, limit, wiring.drivers);
        }
        let bound = &wiring.signals[context.member][position - frame.start];
        let Some(actual) = read_bound_type(context.typed, context.types.as_slice(), bound.driver) else { return Ok(None); };
        let ResolvedPortType::Bits(width) = actual.ty else {
            return Err(ModuleConcatsError::InputType { argument: form_location(source, forms, leaf), actual });
        };
        let (width, selection) = if steps.is_empty() {
            (width, None)
        } else {
            match check_selection_chain(source, forms, at, steps.as_slice(), leaf, width, &actual.origin) {
                Ok(selection) => (selection.count, Some(selection)),
                Err(error) => return Err(ModuleConcatsError::Selection(error)),
            }
        };
        Ok(Some(ModuleConcatOperand { form: at, driver: Some(bound.driver), selection, width }))
    }

    spec fn concat_result(&self, context: &ConcatContext, root: usize, arguments: Range<usize>, limit: u64,
        result: Result<Option<ModuleConcat>, ModuleConcatsError>) -> bool {
        let forms = context.parsed.syntax.forms@;
        let row = context.parsed.definitions@[context.definition as int];
        let (start, end) = definition_target_range(forms, row);
        if end - start != 1 {
            result matches Err(ModuleConcatsError::Outputs { expression, left, targets }) && targets == end - start
                && is_form_location(context.source, forms[root as int], expression)
                && is_form_location(context.source, forms[row.form + 2], left)
        } else if let Ok(Some(concat)) = result {
            let operands = concat.operands@;
            &&& operand_prefix(context, arguments, arguments.end, limit, operands)
            &&& concat.result.ty is Bits && is_form_location(context.source, forms[root as int], concat.result.origin)
            &&& concat_result_width_matches(operands.map_values(|item: ModuleConcatOperand| item.width), None, limit,
                Ok(concat.result.ty->Bits_0))
        } else {
            exists|cursor: usize, operands: Seq<ModuleConcatOperand>|
                #[trigger] operand_prefix(context, arguments, cursor, limit, operands)
                && if cursor < arguments.end {
                    &&& direct_form_in_range(forms, arguments.start as int, arguments.end as int, cursor as int)
                    &&& match result {
                        Ok(None) => concat_operand(context, cursor, limit, Ok(None)),
                        Err(error) => concat_operand(context, cursor, limit, Err(error)),
                        _ => false,
                    }
                } else {
                    &&& cursor == arguments.end
                    &&& result matches Err(ModuleConcatsError::Width { concat, reason })
                    &&& is_form_location(context.source, forms[root as int], concat)
                    &&& concat_result_width_matches(operands.map_values(|item: ModuleConcatOperand| item.width), None, limit, Err(reason))
                }
        }
    }

    fn check_concat_arguments(&self, _owner: ModuleBodyPosition, limit: u64, context: &ConcatContext<'_, 'p, 'a>, arguments: Range<usize>)
        -> (result: Result<Option<ModuleConcat<'p, 'a>>, ModuleConcatsError<'p, 'a>>)
        requires
            self.concat_context(_owner, limit, context), type_sites_valid(context.types@),
            concat_arguments_match(context.source.text, context.parsed.syntax.forms@,
                context.parsed.definitions@[context.definition as int].expression.start as int, arguments),
        ensures
            self.concat_result(context, context.parsed.definitions@[context.definition as int].expression.start, arguments, limit, result),
            result matches Err(error) ==> !(error is Types),
    {
        let source = context.source;
        let parsed = context.parsed;
        let forms = parsed.syntax.forms.as_slice();
        let row = &parsed.definitions[context.definition];
        let root = row.expression.start;
        proof {
            parsed_index_evidence(*source, *parsed);
            build_definition_scope_evidence(source.text, &parsed.build_model(), context.body.entry as int, context.definition as int);
            concat_arguments_evidence(source.text, forms@, root as int, row.expression.end as int, arguments);
        }
        let targets = definition_target_atoms(forms, row);
        let expression = form_location(source, forms, root);
        if targets.end - targets.start != 1 {
            return Err(ModuleConcatsError::Outputs { expression, left: form_location(source, forms, row.form + 2),
                targets: targets.end - targets.start });
        }
        let mut cursor = arguments.start;
        let mut operands: Vec<ModuleConcatOperand> = Vec::new();
        let mut widths: Vec<u64> = Vec::new();
        assert(operand_prefix(context, arguments, cursor, limit, operands@)) by { reveal(operand_prefix); };
        while cursor < arguments.end
            invariant
                self.concat_context(_owner, limit, context), type_sites_valid(context.types@),
                *source == *context.source, forms@ == context.parsed.syntax.forms@,
                *row == context.parsed.definitions@[context.definition as int], root == row.expression.start,
                root < forms@.len(), complete_list_indices(forms@), nested_list_indices(forms@),
                targets.end - targets.start == 1,
                (targets.start as int, targets.end as int) == definition_target_range(forms@, *row),
                is_form_location(source, forms@[root as int], expression),
                concat_arguments_match(source.text, forms@, root as int, arguments),
                arguments.start <= cursor <= arguments.end <= forms@.len(),
                cursor < arguments.end ==> direct_form_in_range(forms@, arguments.start as int, arguments.end as int, cursor as int),
                expression_region(forms@, cursor as int, arguments.end as int),
                operand_prefix(context, arguments, cursor, limit, operands@),
                widths@ == operands@.map_values(|item: ModuleConcatOperand| item.width),
            decreases arguments.end - cursor,
        {
            let Some(argument) = next_call_argument(forms, cursor..arguments.end) else {
                proof { assert(false); }
                unreachable!()
            };
            let item = match self.check_concat_operand(_owner, limit, context, Ghost(arguments), cursor) {
                Ok(Some(item)) => item,
                Ok(None) => return Ok(None),
                Err(error) => return Err(error),
            };
            proof { following_concat_argument(source.text, forms@, root as int, arguments, cursor, argument.end); }
            widths.push(item.width);
            let ghost before = operands@;
            operands.push(item);
            assert(widths@ =~= operands@.map_values(|item: ModuleConcatOperand| item.width));
            assert(operand_prefix(context, arguments, argument.end, limit, operands@)) by {
                reveal(operand_prefix);
                assert forall|i: int| 0 <= i < operands@.len() implies {
                    let item = #[trigger] operands@[i];
                    &&& arguments.start <= item.form < argument_end(forms@, item.form as int) <= argument.end <= arguments.end
                    &&& item.form == if i == 0 { arguments.start as int } else { argument_end(forms@, operands@[i - 1].form as int) }
                    &&& concat_operand(context, item.form, limit, Ok(Some(item)))
                } by { if i < before.len() { assert(operands@[i] == before[i]); } };
            };
            cursor = argument.end;
        }
        match check_concat_result_width(widths.as_slice(), None, limit) {
            Ok(width) => Ok(Some(ModuleConcat { result: SignalType { ty: ResolvedPortType::Bits(width), origin: expression }, operands })),
            Err(reason) => Err(ModuleConcatsError::Width { concat: expression, reason }),
        }
    }

    spec fn concat_at(&self, typed: &ModuleAliasTypes, types: &Vec<Option<SignalType>>, index: int, limit: u64, result: Result<Option<ModuleConcat>, ModuleConcatsError>) -> bool {
        let drivers = &typed.sources.roots.wiring.drivers;
        let body = drivers.origins@[index];
        let definition = drivers.definitions@[index].definition;
        let project = self.targets.project_model();
        let source = &project.sources_model()[body.file as int];
        let parsed = &project.circuits_model()[body.file as int];
        let root = parsed.definitions@[definition as int].expression.start as int;
        (result == Ok(None) && !(exists|arguments: Range<usize>| #[trigger]
            concat_arguments_match(source.text, parsed.syntax.forms@, root, arguments)))
        || exists|arguments: Range<usize>, member: usize| #[trigger] concat_arguments_match(source.text, parsed.syntax.forms@, root, arguments)
            && (#[trigger] drivers.body.members@[member as int]) == body && member < drivers.body.members@.len()
            && self.concat_result(&ConcatContext { typed, types, body, member, definition, source, parsed }, root as usize, arguments, limit, result)
    }

    fn check_module_concat_row(&self, _owner: ModuleBodyPosition, limit: u64, typed: &ModuleAliasTypes<'p, 'a>,
        types: &Vec<Option<SignalType<'p, 'a>>>, i: usize)
        -> (result: Result<Option<ModuleConcat<'p, 'a>>, ModuleConcatsError<'p, 'a>>)
        requires self.can_resolve(), self.module_alias_types_result(_owner, limit, Ok(Some(*typed))),
            i < typed.sources.roots.wiring.drivers.definitions@.len(),
            types@.len() == typed.sources.roots.wiring.drivers.definitions@.len(), type_sites_valid(types@),
        ensures self.concat_at(typed, types, i as int, limit, result),
            result matches Err(error) ==> !(error is Types),
            result matches Ok(Some(concat)) ==> location_in_source(concat.result.origin),
    {
        let wiring = &typed.sources.roots.wiring;
        proof {
            self.module_alias_types_evidence(_owner, limit, *typed);
            self.module_wiring_keeps_drivers(_owner, limit, *wiring);
            self.module_driver_sites(_owner, limit, wiring.drivers, i as int);
        }
        let body = wiring.drivers.origins[i];
        let definition = wiring.drivers.definitions[i].definition;
        let project = self.targets.project();
        let source = &project.sources()[body.file];
        let parsed = &project.circuits()[body.file];
        proof { parsed_index_evidence(*source, *parsed); }
        let row = &parsed.definitions[definition];
        let Some(arguments) = concat_argument_range(source.text, parsed.syntax.forms.as_slice(), row.expression.start) else {
            return Ok(None);
        };
        assert(concat_arguments_match(source.text, parsed.syntax.forms@, row.expression.start as int, arguments));
        let member = find_member(wiring.drivers.body.members.as_slice(), body);
        let context = ConcatContext { typed, types, body, member, definition, source, parsed };
        let result = self.check_concat_arguments(_owner, limit, &context, arguments);
        proof {
            let model = self.targets.project_model();
            assert(context == (ConcatContext { typed, types, body, member, definition,
                source: &model.sources_model()[body.file as int], parsed: &model.circuits_model()[body.file as int] }));
            assert(self.concat_result(&context, row.expression.start, arguments, limit, result));
            assert(self.concat_at(typed, types, i as int, limit, result));
        }
        result
    }

    spec fn next_type(&self, typed: &ModuleAliasTypes, types: &Vec<Option<SignalType>>, i: usize, limit: u64,
        result: Option<SignalType>) -> bool {
        match typed.sources.aliases@[i as int] {
            Some(alias) => result == bound_type(typed, types@, alias.driver),
            None => exists|checked: Result<Option<ModuleConcat>, ModuleConcatsError>|
                #[trigger] self.concat_at(typed, types, i as int, limit, checked)
                && result == match checked { Ok(Some(concat)) => Some(concat.result), _ => None },
        }
    }

    fn infer_concat_or_alias(&self, owner: ModuleBodyPosition, limit: u64, typed: &ModuleAliasTypes<'p, 'a>,
        types: &Vec<Option<SignalType<'p, 'a>>>, i: usize) -> (result: Option<SignalType<'p, 'a>>)
        requires
            self.can_resolve(), self.module_alias_types_result(owner, limit, Ok(Some(*typed))),
            i < types@.len() == typed.sources.roots.wiring.drivers.definitions@.len(),
            type_sites_valid(types@),
        ensures self.next_type(typed, types, i, limit, result),
            result matches Some(ty) ==> location_in_source(ty.origin),
    {
        proof {
            self.module_alias_types_evidence(owner, limit, *typed);
            self.module_type_sources_bounds(owner, limit, typed.sources);
            self.module_wiring_keeps_drivers(owner, limit, typed.sources.roots.wiring);
            self.module_input_sites(owner, limit, typed.sources.roots.wiring.drivers);
        }
        if let Some(alias) = &typed.sources.aliases[i] {
            return read_bound_type(typed, types.as_slice(), alias.driver);
        }
        let checked = self.check_module_concat_row(owner, limit, typed, types, i);
        match checked {
            Ok(Some(concat)) => Some(concat.result),
            _ => None,
        }
    }

    spec fn inference_step(&self, typed: &ModuleAliasTypes, limit: u64, before: Vec<Option<SignalType>>,
        after: Vec<Option<SignalType>>, index: usize) -> bool {
        &&& index < before@.len() && before@[index as int].is_none()
        &&& after@.len() == before@.len() && after@[index as int].is_some()
        &&& after@ == before@.update(index as int, after@[index as int])
        &&& self.next_type(typed, &before, index, limit, after@[index as int])
    }

    #[verifier::opaque]
    spec fn derivation(&self, typed: &ModuleAliasTypes, limit: u64,
        trail: Seq<(usize, Vec<Option<SignalType>>)>, types: Vec<Option<SignalType>>) -> bool {
        &&& trail.len() > 0 && trail[0].1@ == typed.types@ && trail.last().1 == types
        &&& forall|i: int| 0 < i < trail.len() ==> {
            let step = #[trigger] trail[i];
            self.inference_step(typed, limit, trail[i - 1].1, step.1, step.0)
        }
    }

    /// 途中で判明した型は、後続の連接や裸名の推論で変化しない。
    proof fn concat_derivation_preserves_known(
        &self, typed: &ModuleAliasTypes, limit: u64, trail: Seq<(usize, Vec<Option<SignalType>>)>,
        types: Vec<Option<SignalType>>, first: int, last: int,
    )
        requires self.derivation(typed, limit, trail, types), 0 <= first <= last < trail.len(),
        ensures
            trail[first].1@.len() == trail[last].1@.len(),
            forall|i: int| 0 <= i < trail[first].1@.len() && (#[trigger] trail[first].1@[i]).is_some()
                ==> trail[last].1@[i] == trail[first].1@[i],
        decreases last - first,
    {
        reveal(UseAliases::derivation);
        if first < last {
            self.concat_derivation_preserves_known(typed, limit, trail, types, first, last - 1);
            let before = trail[last - 1].1;
            let (updated, after) = trail[last];
            assert(self.inference_step(typed, limit, before, after, updated));
            assert forall|i: int| 0 <= i < trail[first].1@.len() && (#[trigger] trail[first].1@[i]).is_some()
                implies after@[i] == trail[first].1@[i] by {
                assert(before@[i] == trail[first].1@[i]);
                assert(i != updated);
            };
        }
    }

    /// 最後に残った型が、どの推論で初めて判明したかを取り出す。
    proof fn concat_derivation_discovered_type(
        &self, typed: &ModuleAliasTypes, limit: u64, trail: Seq<(usize, Vec<Option<SignalType>>)>,
        types: Vec<Option<SignalType>>, slot: usize, last: int,
    ) -> (step: int)
        requires self.derivation(typed, limit, trail, types), 0 <= last < trail.len(),
            slot < typed.types@.len(), typed.types@[slot as int].is_none(), trail[last].1@[slot as int].is_some(),
        ensures
            0 < step <= last,
            trail[step - 1].1@.len() == typed.types@.len(),
            trail[step].1@[slot as int] == trail[last].1@[slot as int],
            self.inference_step(typed, limit, trail[step - 1].1, trail[step].1, slot),
        decreases last,
    {
        reveal(UseAliases::derivation);
        assert(last > 0);
        let (updated, after) = trail[last];
        let before = trail[last - 1].1;
        assert(self.inference_step(typed, limit, before, after, updated));
        self.concat_derivation_preserves_known(typed, limit, trail, types, 0, last);
        if updated == slot {
            last
        } else {
            assert(before@[slot as int] == after@[slot as int]);
            self.concat_derivation_discovered_type(typed, limit, trail, types, slot, last - 1)
        }
    }

    proof fn record_inference(&self, typed: &ModuleAliasTypes, limit: u64,
        trail: Seq<(usize, Vec<Option<SignalType>>)>, before: Vec<Option<SignalType>>, after: Vec<Option<SignalType>>, index: usize,
    )
        requires self.derivation(typed, limit, trail, before), self.inference_step(typed, limit, before, after, index),
        ensures self.derivation(typed, limit, trail.push((index, after)), after),
    {
        reveal(UseAliases::derivation);
        let updated = trail.push((index, after));
        assert forall|i: int| 0 < i < updated.len() implies {
            let step = #[trigger] updated[i];
            self.inference_step(typed, limit, updated[i - 1].1, step.1, step.0)
        } by {
            if i < trail.len() { assert(updated[i] == trail[i]); }
        };
    }

    #[verifier::opaque]
    spec fn blocked_prefix(&self, typed: &ModuleAliasTypes, types: &Vec<Option<SignalType>>, limit: u64, stop: int) -> bool {
        forall|i: int| 0 <= i < stop && (#[trigger] types@[i]).is_none() ==> self.next_type(typed, types, i as usize, limit, None)
    }

    spec fn fixed_point(&self, typed: &ModuleAliasTypes, limit: u64, types: Vec<Option<SignalType>>) -> bool {
        &&& types@.len() == typed.types@.len()
        &&& type_sites_valid(types@)
        &&& self.blocked_prefix(typed, &types, limit, types@.len() as int)
        &&& exists|trail: Seq<(usize, Vec<Option<SignalType>>)>| #[trigger] self.derivation(typed, limit, trail, types)
    }

    /// 未確定の行だけを更新し、追加できる型がなくなるまで別名と連接を調べる。
    fn infer_module_concat_types(&self, owner: ModuleBodyPosition, limit: u64, typed: &ModuleAliasTypes<'p, 'a>)
        -> (result: Vec<Option<SignalType<'p, 'a>>>)
        requires self.can_resolve(), self.module_alias_types_result(owner, limit, Ok(Some(*typed))),
        ensures self.fixed_point(typed, limit, result),
    {
        proof { self.module_alias_types_evidence(owner, limit, *typed); }
        let count = typed.types.len();
        let mut types = Vec::new();
        let mut i = 0;
        while i < count
            invariant count == typed.types@.len(), i <= count, types@ == typed.types@.take(i as int),
            decreases count - i,
        {
            types.push(copy_signal_type(&typed.types[i]));
            assert(types@ =~= typed.types@.take(i + 1));
            i += 1;
        }
        assert(types@ =~= typed.types@);
        let ghost mut trail = seq![(0usize, types)];
        let ghost mut pending = vstd::set_lib::set_int_range(0, count as int);
        proof {
            vstd::set_lib::lemma_int_range(0, count as int);
            assert(self.derivation(typed, limit, trail, types)) by { reveal(UseAliases::derivation); };
        }
        loop
            invariant
                self.can_resolve(), self.module_alias_types_result(owner, limit, Ok(Some(*typed))),
                count == typed.types@.len() == typed.sources.roots.wiring.drivers.definitions@.len() == types@.len(),
                self.derivation(typed, limit, trail, types), type_sites_valid(types@),
                forall|j: int| 0 <= j < count && (#[trigger] types@[j]).is_none() ==> pending.contains(j),
            decreases pending.len(),
        {
            let ghost before_round = pending;
            let mut changed = false;
            let mut index = 0;
            assert(self.blocked_prefix(typed, &types, limit, 0)) by { reveal(UseAliases::blocked_prefix); };
            while index < count
                invariant
                    self.can_resolve(), self.module_alias_types_result(owner, limit, Ok(Some(*typed))),
                    index <= count == typed.types@.len() == typed.sources.roots.wiring.drivers.definitions@.len() == types@.len(),
                    self.derivation(typed, limit, trail, types), type_sites_valid(types@),
                    forall|j: int| 0 <= j < count && (#[trigger] types@[j]).is_none() ==> pending.contains(j),
                    if changed { pending.len() < before_round.len() } else { pending == before_round },
                    !changed ==> self.blocked_prefix(typed, &types, limit, index as int),
                decreases count - index,
            {
                if types[index].is_none() {
                    match self.infer_concat_or_alias(owner, limit, typed, &types, index) {
                        Some(value) => {
                            let ghost before = types;
                            types.set(index, Some(value));
                            proof {
                                self.record_inference(typed, limit, trail, before, types, index);
                                assert forall|j: int| 0 <= j < types@.len() implies
                                    ((#[trigger] types@[j]) matches Some(ty) ==> location_in_source(ty.origin)) by {
                                    if j != index { assert(types@[j] == before@[j]); }
                                };
                                trail = trail.push((index, types));
                                vstd::set::lemma_set_remove_len(pending, index as int);
                                pending = pending.remove(index as int);
                            }
                            changed = true;
                        },
                        None => {},
                    }
                }
                if !changed {
                    assert(self.blocked_prefix(typed, &types, limit, index + 1)) by {
                        reveal(UseAliases::blocked_prefix);
                    };
                }
                index += 1;
            }
            if !changed {
                assert(self.fixed_point(typed, limit, types));
                return types;
            }
        }
    }

    #[verifier::opaque]
    spec fn concat_prefix(&self, typed: &ModuleAliasTypes, types: &Vec<Option<SignalType>>, limit: u64, concats: Seq<Option<ModuleConcat>>) -> bool {
        &&& concats.len() <= typed.sources.roots.wiring.drivers.definitions@.len()
        &&& forall|i: int| 0 <= i < concats.len() ==> self.concat_at(typed, types, i, limit, Ok(#[trigger] concats[i]))
    }

    /// 連接の幅と引数順、または最初に見つかった違反を元の断片に対応付ける。
    pub closed spec fn module_concats_result(&self, owner: ModuleBodyPosition, limit: u64,
        result: Result<Option<ModuleConcats>, ModuleConcatsError>) -> bool {
        match result {
            Ok(None) => self.module_alias_types_result(owner, limit, Ok(None)),
            Err(ModuleConcatsError::Types(error)) => self.module_alias_types_result(owner, limit, Err(error)),
            Ok(Some(checked)) => self.module_alias_types_result(owner, limit, Ok(Some(checked.typed)))
                && checked.concats@.len() == checked.typed.sources.roots.wiring.drivers.definitions@.len()
                && self.fixed_point(&checked.typed, limit, checked.types)
                && self.concat_prefix(&checked.typed, &checked.types, limit, checked.concats@),
            Err(error) => exists|typed: ModuleAliasTypes, types: Vec<Option<SignalType>>, prefix: Seq<Option<ModuleConcat>>|
                #[trigger] self.module_alias_types_result(owner, limit, Ok(Some(typed)))
                && self.fixed_point(&typed, limit, types)
                && #[trigger] self.concat_prefix(&typed, &types, limit, prefix)
                && prefix.len() < typed.sources.roots.wiring.drivers.definitions@.len()
                && self.concat_at(&typed, &types, prefix.len() as int, limit, Err(error)),
        }
    }

    /// 後続の式検査で使う型表の長さと、型の根拠位置を示す。
    pub(super) proof fn module_concats_evidence(&self, owner: ModuleBodyPosition, limit: u64, checked: ModuleConcats)
        requires self.module_concats_result(owner, limit, Ok(Some(checked))),
        ensures
            self.module_alias_types_result(owner, limit, Ok(Some(checked.typed))),
            checked.types@.len() == checked.typed.sources.roots.wiring.drivers.definitions@.len(),
            checked.concats@.len() == checked.types@.len(),
            type_sites_valid(checked.types@),
    {
        self.module_alias_types_evidence(owner, limit, checked.typed);
    }

    proof fn successful_concat_context<'w>(
        &self, owner: ModuleBodyPosition, limit: u64, checked: &'w ModuleConcats<'p, 'a>, slot: usize,
    ) -> (evidence: (ConcatContext<'w, 'p, 'a>, Range<usize>))
        requires self.can_resolve(), self.module_concats_result(owner, limit, Ok(Some(*checked))),
            slot < checked.concats@.len(), checked.concats@[slot as int].is_some(),
        ensures ({
            let (context, arguments) = evidence;
            let project = self.targets.project_model();
            let wiring = checked.typed.sources.roots.wiring;
            let at = wiring.drivers.origins@[slot as int];
            let row = context.parsed.definitions@[context.definition as int];
            let forms = context.parsed.syntax.forms@;
            &&& context.typed == &checked.typed && context.types == &checked.types
            &&& context.body == at
            &&& context.definition == wiring.drivers.definitions@[slot as int].definition
            &&& context.member < wiring.drivers.body.members@.len()
            &&& wiring.drivers.body.members@[context.member as int] == at
            &&& at.file < project.sources_model().len() && at.file < project.circuits_model().len()
            &&& *context.source == project.sources_model()[at.file as int]
            &&& *context.parsed == project.circuits_model()[at.file as int]
            &&& self.concat_context(owner, limit, &context)
            &&& form_spans_valid(context.source.text, forms, context.source.text.spec_bytes().len() as int)
            &&& concat_arguments_match(context.source.text, forms, row.expression.start as int, arguments)
            &&& arguments.start < arguments.end <= forms.len()
            &&& self.concat_result(&context, row.expression.start, arguments, limit, Ok(checked.concats@[slot as int]))
        }),
    {
        self.module_concats_evidence(owner, limit, *checked);
        self.module_alias_types_evidence(owner, limit, checked.typed);
        let wiring = checked.typed.sources.roots.wiring;
        self.module_wiring_keeps_drivers(owner, limit, wiring);
        self.module_driver_sites(owner, limit, wiring.drivers, slot as int);
        reveal(UseAliases::concat_prefix);
        let body = wiring.drivers.origins@[slot as int];
        let definition = wiring.drivers.definitions@[slot as int].definition;
        let project = self.targets.project_model();
        let source = &project.sources_model()[body.file as int];
        let parsed = &project.circuits_model()[body.file as int];
        let row = parsed.definitions@[definition as int];
        let forms = parsed.syntax.forms@;
        let root = row.expression.start;
        let result = Ok(checked.concats@[slot as int]);
        assert(self.concat_at(&checked.typed, &checked.types, slot as int, limit, result));
        let (arguments, member) = choose|arguments: Range<usize>, member: usize|
            #[trigger] concat_arguments_match(source.text, forms, root as int, arguments)
            && (#[trigger] wiring.drivers.body.members@[member as int]) == body
            && member < wiring.drivers.body.members@.len()
            && self.concat_result(&ConcatContext { typed: &checked.typed, types: &checked.types,
                body, member, definition, source, parsed }, root, arguments, limit, result);
        self.targets.parsed_project_model();
        parsed_index_evidence(*source, *parsed);
        build_definition_scope_evidence(source.text, &parsed.build_model(), body.entry as int, definition as int);
        concat_arguments_evidence(source.text, forms, root as int, row.expression.end as int, arguments);
        (ConcatContext { typed: &checked.typed, types: &checked.types, body, member, definition, source, parsed }, arguments)
    }

    /// 連接幅は、ソース順に並ぶ各引数の幅から決まる。
    pub(super) proof fn checked_concat_width(
        &self, owner: ModuleBodyPosition, limit: u64, checked: &ModuleConcats, slot: usize,
    )
        requires self.can_resolve(), self.module_concats_result(owner, limit, Ok(Some(*checked))),
            slot < checked.concats@.len(), checked.concats@[slot as int].is_some(),
        ensures ({
            let concat = checked.concats@[slot as int]->Some_0;
            &&& concat.result.ty is Bits
            &&& concat_result_width_matches(concat.operands@.map_values(|item: ModuleConcatOperand| item.width),
                None, limit, Ok(concat.result.ty->Bits_0))
        }),
    {
        self.successful_concat_context(owner, limit, checked, slot);
    }

    /// 連接の型は、根の検査や裸名の伝播では決まらない。
    proof fn concat_has_no_seed_type(
        &self, owner: ModuleBodyPosition, limit: u64, checked: &ModuleConcats, slot: usize,
        context: &ConcatContext, arguments: Range<usize>,
    )
        requires self.can_resolve(), self.module_concats_result(owner, limit, Ok(Some(*checked))),
            slot < checked.concats@.len(), self.concat_context(owner, limit, context),
            ({
                let drivers = checked.typed.sources.roots.wiring.drivers;
                let row = context.parsed.definitions@[context.definition as int];
                &&& context.body == drivers.origins@[slot as int]
                &&& context.definition == drivers.definitions@[slot as int].definition
                &&& concat_arguments_match(context.source.text, context.parsed.syntax.forms@, row.expression.start as int, arguments)
            }),
        ensures checked.typed.types@[slot as int].is_none(), checked.typed.sources.aliases@[slot as int].is_none(),
    {
        let sources = checked.typed.sources;
        let roots = sources.roots;
        let at = roots.wiring.drivers.origins@[slot as int];
        let driver = roots.wiring.drivers.definitions@[slot as int];
        let row = context.parsed.definitions@[context.definition as int];
        let root = row.expression.start;
        let forms = context.parsed.syntax.forms@;
        let source = context.source.text;
        self.module_concats_evidence(owner, limit, *checked);
        self.module_alias_types_evidence(owner, limit, checked.typed);
        self.module_type_sources_bounds(owner, limit, sources);
        self.module_root_types_evidence(owner, limit, roots);
        concat_excludes_other_shapes(source, forms, root as int, arguments);
        if ordinary_call_at(source, forms, root as int, row.expression.end as int) {
            ordinary_call_excludes_special_forms(source, forms, root as int, row.expression.end as int);
            assert(false);
        }
        self.module_list_rhs_has_no_alias(owner, limit, sources, slot);
        reveal(UseAliases::root_types_prefix);
        assert(self.root_type(at, driver, limit, Ok(roots.types@[slot as int])));
        assert(super::selection_root_type(context.source, forms, row, Ok(roots.types@[slot as int])));
        assert(roots.types@[slot as int].is_none());
        self.module_alias_keeps_root_type(owner, limit, checked.typed, slot);
    }

    /// 確定した連接の型と、その型を求めた時点の表を取り出す。
    proof fn concat_type_before_assignment(
        &self, limit: u64, checked: &ModuleConcats, slot: usize,
    ) -> (evidence: (Vec<Option<SignalType>>, ModuleConcat))
        requires self.fixed_point(&checked.typed, limit, checked.types),
            slot < checked.types@.len(), checked.types@[slot as int].is_some(),
            checked.typed.types@[slot as int].is_none(), checked.typed.sources.aliases@[slot as int].is_none(),
        ensures ({
            let (before, concat) = evidence;
            &&& before@.len() == checked.types@.len()
            &&& checked.types@[slot as int] == Some(concat.result)
            &&& self.concat_at(&checked.typed, &before, slot as int, limit, Ok(Some(concat)))
            &&& forall|i: int| 0 <= i < before@.len() && (#[trigger] before@[i]).is_some()
                ==> checked.types@[i] == before@[i]
        }),
    {
        let trail = choose|trail: Seq<(usize, Vec<Option<SignalType>>)>|
            #[trigger] self.derivation(&checked.typed, limit, trail, checked.types);
        reveal(UseAliases::derivation);
        let last = trail.len() - 1;
        let step = self.concat_derivation_discovered_type(&checked.typed, limit, trail, checked.types, slot, last);
        let known = trail[step - 1].1;
        let outcome = choose|outcome: Result<Option<ModuleConcat>, ModuleConcatsError>|
            #[trigger] self.concat_at(&checked.typed, &known, slot as int, limit, outcome)
            && checked.types@[slot as int] == match outcome { Ok(Some(found)) => Some(found.result), _ => None };
        let old = outcome->Ok_0->Some_0;
        self.concat_derivation_preserves_known(&checked.typed, limit, trail, checked.types, step - 1, last);
        (known, old)
    }

    /// 型が確定した連接は、現在の引数幅の合計をその定義の型に持つ。
    pub(super) proof fn checked_concat_table_width(
        &self, owner: ModuleBodyPosition, limit: u64, checked: &ModuleConcats, slot: usize,
    )
        requires self.can_resolve(), self.module_concats_result(owner, limit, Ok(Some(*checked))),
            slot < checked.concats@.len(), checked.concats@[slot as int].is_some(),
            checked.types@[slot as int].is_some(),
        ensures checked.types@[slot as int]->Some_0.ty == checked.concats@[slot as int]->Some_0.result.ty,
    {
        self.module_concats_evidence(owner, limit, *checked);
        let (context, arguments) = self.successful_concat_context(owner, limit, checked, slot);
        self.concat_has_no_seed_type(owner, limit, checked, slot, &context, arguments);
        let (known, old) = self.concat_type_before_assignment(limit, checked, slot);
        let concat = checked.concats@[slot as int]->Some_0;
        self.concat_result_same_context(owner, limit, checked, &context, arguments, slot, &known, Ok(Some(old)));
        let before = ConcatContext { typed: context.typed, types: &known, body: context.body,
            member: context.member, definition: context.definition, source: context.source, parsed: context.parsed };
        assert(self.concat_context(owner, limit, &before));
        assert(operand_prefix(&before, arguments, arguments.end, limit, old.operands@));
        assert(operand_prefix(&context, arguments, arguments.end, limit, concat.operands@));
        concat_operand_count_agrees(&before, &context, arguments, limit, old.operands@, concat.operands@);
        let old_widths = old.operands@.map_values(|item: ModuleConcatOperand| item.width);
        let widths = concat.operands@.map_values(|item: ModuleConcatOperand| item.width);
        assert forall|i: int| 0 <= i < widths.len() implies widths[i] == old_widths[i] by {
            concat_operand_roots_agree(&before, &context, arguments, limit, old.operands@, concat.operands@, i);
            let earlier = old.operands@[i];
            let current = concat.operands@[i];
            reveal(operand_prefix);
            assert(concat_operand(&before, current.form, limit, Ok(Some(earlier))));
            assert(concat_operand(&context, current.form, limit, Ok(Some(current))));
            self.concat_known_operand_width(owner, limit, &before, &context, current.form, earlier, current);
        };
        assert(widths =~= old_widths);
        concat_result_widths_agree(widths, None, limit, Ok(old.result.ty->Bits_0), Ok(concat.result.ty->Bits_0));
    }

    /// 連接の各引数を、元のフォームと、型が合う駆動元またはリテラルの幅に結び付ける。
    pub(super) proof fn checked_concat_operand(
        &self, owner: ModuleBodyPosition, limit: u64, checked: &ModuleConcats, slot: usize, index: usize,
    )
        requires self.can_resolve(), self.module_concats_result(owner, limit, Ok(Some(*checked))),
            slot < checked.concats@.len(), checked.concats@[slot as int].is_some(),
            index < checked.concats@[slot as int]->Some_0.operands@.len(),
        ensures self.concat_operand_in_source(&checked.typed, checked.types@, slot as int,
            checked.concats@[slot as int]->Some_0.operands@[index as int], limit),
    {
        let (context, arguments) = self.successful_concat_context(owner, limit, checked, slot);
        let wiring = checked.typed.sources.roots.wiring;
        self.module_alias_types_evidence(owner, limit, checked.typed);
        let concat = checked.concats@[slot as int]->Some_0;
        let item = concat.operands@[index as int];
        let parsed = context.parsed;
        let source = context.source;
        let forms = parsed.syntax.forms@;
        assert(operand_prefix(&context, arguments, arguments.end, limit, concat.operands@));
        reveal(operand_prefix);
        assert(concat_operand(&context, item.form, limit, Ok(Some(item))));
        assert(arguments.start <= item.form < arguments.end);
        assert(item.form < forms.len());
        if item.driver.is_some() {
            let (steps, leaf, position, base) = concat_operand_signal(&context, item.form, limit, item);
            let frame = parsed.entry_ranges@[context.body.entry as int].signals;
            parsed_index_evidence(*source, *parsed);
            build_definition_scope_evidence(source.text, &parsed.build_model(),
                context.body.entry as int, context.definition as int);
            assert(frame.start <= position < frame.end);
            self.module_signal_index_item(owner, limit, wiring, context.member as int, position);
            let bound = wiring.signals@[context.member as int]@[position - frame.start];
            assert(item.driver == Some(bound.driver));
            assert(match bound.driver {
                OutputDriver::Input(index) => index < wiring.drivers.signature.inputs@.len(),
                OutputDriver::Definition(index) => index < wiring.drivers.definitions@.len(),
            });
            if let Some(selection) = item.selection {
                assert(exists|path: Seq<BitSelectionShape>, name: usize|
                    #[trigger] bit_selection_path(source.text, forms, item.form, path, name)
                    && path.len() > 0 && name < forms.len() && forms[name as int] is Atom
                    && forms[name as int]->Atom_kind is Name
                    && selection_chain_arguments_match(source, forms, path, base.ty->Bits_0, base.origin, Ok(selection))) by {
                    assert(bit_selection_path(source.text, forms, item.form, steps, leaf));
                };
            }
        } else {
            reveal(concat_operand);
            assert(item.driver.is_none());
        }
    }

    proof fn concat_result_same_context(
        &self, owner: ModuleBodyPosition, limit: u64, checked: &ModuleConcats, context: &ConcatContext,
        arguments: Range<usize>, slot: usize, types: &Vec<Option<SignalType>>,
        result: Result<Option<ModuleConcat>, ModuleConcatsError>,
    )
        requires
            self.concat_context(owner, limit, context), context.typed == &checked.typed,
            self.module_concats_result(owner, limit, Ok(Some(*checked))),
            slot < checked.concats@.len(),
            ({
                let drivers = checked.typed.sources.roots.wiring.drivers;
                let root = context.parsed.definitions@[context.definition as int].expression.start as int;
                &&& context.definition == drivers.definitions@[slot as int].definition
                &&& context.body == drivers.origins@[slot as int]
                &&& concat_arguments_match(context.source.text, context.parsed.syntax.forms@, root, arguments)
            }),
            self.concat_at(&checked.typed, types, slot as int, limit, result),
        ensures ({
            let root = context.parsed.definitions@[context.definition as int].expression.start;
            self.concat_result(&ConcatContext { typed: context.typed, types, body: context.body,
                member: context.member, definition: context.definition, source: context.source,
                parsed: context.parsed }, root, arguments, limit, result)
        }),
    {
        let wiring = checked.typed.sources.roots.wiring;
        self.module_concats_evidence(owner, limit, *checked);
        self.module_alias_types_evidence(owner, limit, checked.typed);
        self.module_wiring_keeps_drivers(owner, limit, wiring);
        self.module_driver_sites(owner, limit, wiring.drivers, slot as int);
        self.checked_module_driver_body(owner, limit, wiring.drivers);
        let root = context.parsed.definitions@[context.definition as int].expression.start;
        let forms = context.parsed.syntax.forms@;
        let source = context.source;
        let (range, member) = choose|range: Range<usize>, member: usize|
            #[trigger] concat_arguments_match(source.text, forms, root as int, range)
            && (#[trigger] wiring.drivers.body.members@[member as int]) == context.body
            && member < wiring.drivers.body.members@.len()
            && self.concat_result(&ConcatContext { typed: context.typed, types, body: context.body,
                member, definition: context.definition, source, parsed: context.parsed },
                root, range, limit, result);
        concat_argument_ranges_agree(source.text, forms, root as int, arguments, range);
        if member != context.member {
            let (first, last) = if member < context.member { (member, context.member) } else { (context.member, member) };
            self.targets.module_body_members_distinct(&wiring.drivers.body, first as int, last as int);
            assert(false);
        }
    }

    proof fn concat_known_operand_width(
        &self, owner: ModuleBodyPosition, limit: u64, before: &ConcatContext, after: &ConcatContext,
        form: usize, known: ModuleConcatOperand, other: ModuleConcatOperand,
    )
        requires
            self.concat_context(owner, limit, before), self.concat_context(owner, limit, after),
            before.typed == after.typed && before.body == after.body && before.definition == after.definition
                && before.member == after.member && before.parsed == after.parsed && before.source == after.source,
            form < before.parsed.syntax.forms@.len(),
            concat_operand(before, form, limit, Ok(Some(known))),
            concat_operand(after, form, limit, Ok(Some(other))),
            forall|i: int| 0 <= i < before.types@.len() && (#[trigger] before.types@[i]).is_some()
                ==> after.types@[i] == before.types@[i],
        ensures known.width == other.width,
    {
        reveal(concat_operand);
        let forms = before.parsed.syntax.forms@;
        if known.driver.is_some() {
            assert(other.driver.is_some());
            let (a_steps, a_leaf, left, a) = concat_operand_signal(before, form, limit, known);
            let (b_steps, b_leaf, right, b) = concat_operand_signal(after, form, limit, other);
            bit_selection_paths_agree(before.source.text, forms, form, a_steps, a_leaf, b_steps, b_leaf);
            if let Some(selection) = known.selection {
                assert(other.selection.is_some());
                successful_selection_chain_counts_agree(before.source, forms, a_steps, a.ty->Bits_0,
                    a.origin, selection, b.ty->Bits_0, b.origin, other.selection->Some_0);
                return;
            }
            self.module_alias_types_evidence(owner, limit, *before.typed);
            let wiring = before.typed.sources.roots.wiring;
            let parsed = before.parsed;
            let source = before.source;
            let frame = parsed.entry_ranges@[before.body.entry as int].signals;
            parsed_index_evidence(*source, *parsed);
            build_definition_scope_evidence(source.text, &parsed.build_model(), before.body.entry as int, before.definition as int);
            definition_signal_positions_agree(source.text, &parsed.build_model(), before.body.entry as int,
                before.definition as int, left, right);
            self.module_signal_index_item(owner, limit, wiring, before.member as int, left);
            let driver = wiring.signals@[before.member as int]@[left - frame.start].driver;
            if let OutputDriver::Definition(index) = driver {
                assert(before.types@[index as int].is_some());
                assert(after.types@[index as int] == before.types@[index as int]);
            }
        } else {
            let span = form_span(forms[form as int]);
            let bytes = before.source.text.spec_bytes()[span.start as int..span.end as int];
            successful_literal_widths_agree(bytes, None, limit, known.width, other.width);
        }
    }

    pub(super) open spec fn concat_operand_in_source(
        &self, typed: &ModuleAliasTypes, types: Seq<Option<SignalType>>, slot: int, item: ModuleConcatOperand, limit: u64,
    ) -> bool {
        let project = self.targets.project_model();
        let drivers = typed.sources.roots.wiring.drivers;
        let at = drivers.origins@[slot];
        let parsed = &project.circuits_model()[at.file as int];
        let source = &project.sources_model()[at.file as int];
        let forms = parsed.syntax.forms@;
        let atom = forms[item.form as int];
        &&& at.file < project.sources_model().len() && at.file < project.circuits_model().len()
        &&& item.form < forms.len()
        &&& form_spans_valid(source.text, forms, source.text.spec_bytes().len() as int)
        &&& match item.driver {
            Some(driver) => {
                &&& match driver {
                    OutputDriver::Input(index) => index < drivers.signature.inputs@.len(),
                    OutputDriver::Definition(index) => index < drivers.definitions@.len(),
                }
                &&& bound_type(typed, types, driver) matches Some(ty)
                &&& match item.selection {
                    Some(selection) => {
                        &&& ty.ty is Bits
                        &&& selection.count == item.width && selection.fits(ty.ty->Bits_0)
                        &&& exists|path: Seq<BitSelectionShape>, name: usize|
                            #[trigger] bit_selection_path(source.text, forms, item.form, path, name)
                            && path.len() > 0 && name < forms.len() && forms[name as int] is Atom
                            && forms[name as int]->Atom_kind is Name
                            && selection_chain_arguments_match(source, forms, path, ty.ty->Bits_0, ty.origin, Ok(selection))
                    },
                    None => atom is Atom && atom->Atom_kind is Name && ty.ty == ResolvedPortType::Bits(item.width),
                }
            },
            None => {
                let span = form_span(atom);
                &&& atom is Atom && item.selection.is_none()
                &&& atom->Atom_kind is Natural || atom->Atom_kind is Binary || atom->Atom_kind is Hexadecimal
                &&& circuit_literal_width_matches(source.text.spec_bytes()[span.start as int..span.end as int],
                    None, limit, Ok(item.width))
            },
        }
    }

    proof fn alias_binding_along_inference(
        &self, owner: ModuleBodyPosition, limit: u64, typed: &ModuleAliasTypes,
        trail: Seq<(usize, Vec<Option<SignalType>>)>, result: Vec<Option<SignalType>>, step: int, slot: usize,
    )
        requires
            self.module_alias_types_result(owner, limit, Ok(Some(*typed))),
            self.derivation(typed, limit, trail, result),
            0 <= step < trail.len(),
            slot < typed.sources.aliases@.len(),
        ensures
            trail[step].1@.len() == typed.sources.aliases@.len(),
            typed.sources.aliases@[slot as int] matches Some(alias) ==>
                (trail[step].1@[slot as int].is_some() ==> trail[step].1@[slot as int]
                    == bound_type(typed, trail[step].1@, alias.driver)),
        decreases step,
    {
        reveal(UseAliases::derivation);
        if step == 0 {
            self.module_alias_types_evidence(owner, limit, *typed);
            self.module_type_sources_bounds(owner, limit, typed.sources);
            self.initial_module_alias_binding(owner, limit, *typed, slot);
        } else {
            self.alias_binding_along_inference(owner, limit, typed, trail, result, step - 1, slot);
            let before = trail[step - 1].1;
            let (updated, after) = trail[step];
            assert(self.inference_step(typed, limit, before, after, updated));
            if let Some(alias) = typed.sources.aliases@[slot as int] {
                if after@[slot as int].is_some() {
                    if updated == slot {
                        assert(after@[slot as int] == bound_type(typed, before@, alias.driver));
                    } else {
                        assert(after@[slot as int] == before@[slot as int]);
                        assert(before@[slot as int] == bound_type(typed, before@, alias.driver));
                    }
                    match alias.driver {
                        OutputDriver::Input(_) => {},
                        OutputDriver::Definition(driver) => {
                            self.module_alias_types_evidence(owner, limit, *typed);
                            self.module_type_sources_bounds(owner, limit, typed.sources);
                            assert(before@[driver as int] == after@[slot as int]);
                            assert(before@[driver as int].is_some());
                            assert(updated != driver);
                            assert(after@[driver as int] == before@[driver as int]);
                        },
                    }
                }
            }
        }
    }

    /// 連接から型を推論した後も、型が確定した裸名の定義は駆動元と型が一致する。
    pub(super) proof fn module_concat_alias_binding(
        &self, owner: ModuleBodyPosition, limit: u64, checked: ModuleConcats, slot: usize,
    )
        requires self.module_concats_result(owner, limit, Ok(Some(checked))),
            slot < checked.typed.sources.aliases@.len(),
        ensures checked.typed.sources.aliases@[slot as int] matches Some(alias) ==>
            (checked.types@[slot as int].is_some() ==> checked.types@[slot as int]
                == bound_type(&checked.typed, checked.types@, alias.driver)),
    {
        let trail = choose|trail: Seq<(usize, Vec<Option<SignalType>>)>|
            #[trigger] self.derivation(&checked.typed, limit, trail, checked.types);
        reveal(UseAliases::derivation);
        self.alias_binding_along_inference(owner, limit, &checked.typed, trail, checked.types, trail.len() - 1, slot);
    }

    proof fn concat_derivation_keeps_initial_type(
        &self, typed: &ModuleAliasTypes, limit: u64, trail: Seq<(usize, Vec<Option<SignalType>>)>,
        types: Vec<Option<SignalType>>, step: int, slot: usize,
    )
        requires
            self.derivation(typed, limit, trail, types),
            0 <= step < trail.len(),
            slot < typed.types@.len(),
            typed.types@[slot as int].is_some(),
        ensures
            trail[step].1@.len() == typed.types@.len(),
            trail[step].1@[slot as int] == typed.types@[slot as int],
        decreases step,
    {
        reveal(UseAliases::derivation);
        if step > 0 {
            self.concat_derivation_keeps_initial_type(typed, limit, trail, types, step - 1, slot);
            let before = trail[step - 1].1;
            let (updated, after) = trail[step];
            assert(self.inference_step(typed, limit, before, after, updated));
            assert(updated != slot);
        }
    }

    /// 別名と連接の推論を経た後も、ビット選択の型と根拠が元の選択数に対応する。
    pub(super) proof fn module_concat_selection_type(
        &self, owner: ModuleBodyPosition, limit: u64, checked: ModuleConcats, slot: usize, shape: BitSelectionShape,
    ) -> (numbers: (u64, u64, u64, usize))
        requires
            self.module_concats_result(owner, limit, Ok(Some(checked))),
            slot < checked.typed.sources.roots.wiring.drivers.definitions@.len(),
            ({
                let project = self.targets.project_model();
                let drivers = checked.typed.sources.roots.wiring.drivers;
                let at = drivers.origins@[slot as int];
                let driver = drivers.definitions@[slot as int];
                let parsed = &project.circuits_model()[at.file as int];
                let source = &project.sources_model()[at.file as int];
                let row = parsed.definitions@[driver.definition as int];
                bit_selection_shape_matches(source.text, parsed.syntax.forms@, row.expression.start as int, shape)
            }),
        ensures ({
            let project = self.targets.project_model();
            let drivers = checked.typed.sources.roots.wiring.drivers;
            let at = drivers.origins@[slot as int];
            let driver = drivers.definitions@[slot as int];
            let parsed = &project.circuits_model()[at.file as int];
            let source = &project.sources_model()[at.file as int];
            let root = parsed.definitions@[driver.definition as int].expression.start as int;
            &&& checked.types@[slot as int] matches Some(ty)
            &&& ty.ty == ResolvedPortType::Bits(numbers.1) && numbers.1 > 0
            &&& is_form_location(source, parsed.syntax.forms@[root], ty.origin)
            &&& selection_parameters_match(source, parsed.syntax.forms@, &shape, Ok(numbers))
        }),
    {
        self.module_concats_evidence(owner, limit, checked);
        self.module_alias_types_evidence(owner, limit, checked.typed);
        let sources = checked.typed.sources;
        self.module_type_sources_bounds(owner, limit, sources);
        let numbers = self.module_selection_root_numbers(owner, limit, sources.roots, slot, shape);
        let project = self.targets.project_model();
        let drivers = sources.roots.wiring.drivers;
        let at = drivers.origins@[slot as int];
        let driver = drivers.definitions@[slot as int];
        let parsed = &project.circuits_model()[at.file as int];
        let source = &project.sources_model()[at.file as int];
        let root = parsed.definitions@[driver.definition as int].expression.start as int;
        bit_selection_shape_positions(source.text, parsed.syntax.forms@, root, shape);
        self.module_list_rhs_has_no_alias(owner, limit, sources, slot);
        self.module_alias_keeps_root_type(owner, limit, checked.typed, slot);
        let trail = choose|trail: Seq<(usize, Vec<Option<SignalType>>)>|
            #[trigger] self.derivation(&checked.typed, limit, trail, checked.types);
        reveal(UseAliases::derivation);
        self.concat_derivation_keeps_initial_type(&checked.typed, limit, trail, checked.types, trail.len() - 1, slot);
        numbers
    }

    proof fn concat_inference_keeps_declarations(
        &self, typed: &ModuleAliasTypes, limit: u64, before: Vec<Option<SignalType>>,
        after: Vec<Option<SignalType>>, index: usize,
    )
        requires
            self.inference_step(typed, limit, before, after, index),
            before@.len() == typed.sources.aliases@.len(),
            self.module_types_declared(before@),
            ({
                let inputs = typed.sources.roots.wiring.drivers.signature.inputs@;
                forall|i: int| 0 <= i < inputs.len() ==> self.declared_port_type((#[trigger] inputs[i]).ty)
            }),
            ({
                let inputs = typed.sources.roots.wiring.drivers.signature.inputs@;
                typed.sources.aliases@[index as int] matches Some(alias) ==> match alias.driver {
                    OutputDriver::Input(port) => port < inputs.len(),
                    OutputDriver::Definition(slot) => slot < before@.len(),
                }
            }),
        ensures self.module_types_declared(after@),
    {
        let new = after@[index as int];
        let value = new->Some_0;
        match typed.sources.aliases@[index as int] {
            Some(alias) => {
                assert(new == bound_type(typed, before@, alias.driver));
                if let OutputDriver::Definition(slot) = alias.driver {
                    assert(before@[slot as int] == new);
                }
            },
            None => {
                let checked = choose|checked: Result<Option<ModuleConcat>, ModuleConcatsError>|
                    #[trigger] self.concat_at(typed, &before, index as int, limit, checked)
                    && new == match checked { Ok(Some(concat)) => Some(concat.result), _ => None };
                assert(checked matches Ok(Some(concat)) && concat.result == value);
                assert(value.ty is Bits);
            },
        }
        assert(self.declared_port_type(value.ty));
        assert forall|i: int| 0 <= i < after@.len() implies
            ((#[trigger] after@[i]) matches Some(ty) ==> self.declared_port_type(ty.ty)) by {
            if i != index { assert(after@[i] == before@[i]); }
        };
    }

    proof fn concat_derivation_keeps_declarations(
        &self, owner: ModuleBodyPosition, limit: u64, typed: &ModuleAliasTypes,
        trail: Seq<(usize, Vec<Option<SignalType>>)>, result: Vec<Option<SignalType>>, step: int,
    )
        requires
            self.module_alias_types_result(owner, limit, Ok(Some(*typed))),
            self.derivation(typed, limit, trail, result),
            0 <= step < trail.len(),
        ensures
            trail[step].1@.len() == typed.types@.len(),
            self.module_types_declared(trail[step].1@),
        decreases step,
    {
        reveal(UseAliases::derivation);
        if step == 0 {
            self.module_alias_type_declarations(owner, limit, *typed);
        } else {
            self.concat_derivation_keeps_declarations(owner, limit, typed, trail, result, step - 1);
            let row = trail[step];
            let before = trail[step - 1].1;
            self.module_alias_types_evidence(owner, limit, *typed);
            self.module_type_sources_bounds(owner, limit, typed.sources);
            let wiring = typed.sources.roots.wiring;
            self.module_wiring_keeps_drivers(owner, limit, wiring);
            self.module_output_driver(owner, limit, wiring.drivers, 0);
            self.typed_signature_types_declared(owner.file, owner.entry, limit, wiring.drivers.signature);
            assert(self.inference_step(typed, limit, before, row.1, row.0));
            self.concat_inference_keeps_declarations(typed, limit, before, row.1, row.0);
        }
    }

    /// 連接を推論するときも、構造体型は入力または右辺から引き継いだ元の宣言を指す。
    pub(super) proof fn module_concat_type_declarations(&self, owner: ModuleBodyPosition, limit: u64, checked: ModuleConcats)
        requires self.module_concats_result(owner, limit, Ok(Some(checked))),
        ensures self.module_types_declared(checked.types@),
    {
        let trail = choose|trail: Seq<(usize, Vec<Option<SignalType>>)>|
            #[trigger] self.derivation(&checked.typed, limit, trail, checked.types);
        reveal(UseAliases::derivation);
        self.concat_derivation_keeps_declarations(owner, limit, &checked.typed, trail, checked.types, trail.len() - 1);
    }

    /// 右辺全体を占める連接の幅を、型が分かった信号名とリテラルから求める。
    ///
    /// 連接の幅を別名や別の連接へ伝え、追加の型が得られなくなったときの結果を返す。
    /// ビット列の信号とリテラル、信号を起点にした `bit`・`slice` の幅を求める。
    /// 幅が未確定の引数があれば、その引数から先を保留する。
    ///
    /// # Errors
    ///
    /// 配線と型伝播を先に検査する。型表が確定した後、定義順に左辺の名前数、引数、合計幅を検査する。
    pub fn check_module_concats(&self, owner: ModuleBodyPosition, limit: u64)
        -> (result: Result<Option<ModuleConcats<'p, 'a>>, ModuleConcatsError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.module_concats_result(owner, limit, result),
    {
        let typed = match self.resolve_module_alias_types(owner, limit) {
            Ok(Some(typed)) => typed,
            Ok(None) => return Ok(None),
            Err(error) => return Err(ModuleConcatsError::Types(error)),
        };
        proof { self.module_alias_types_evidence(owner, limit, typed); }
        let types = self.infer_module_concat_types(owner, limit, &typed);
        let count = typed.sources.roots.wiring.drivers.definitions.len();
        let mut concats = Vec::new();
        let mut i = 0;
        assert(self.concat_prefix(&typed, &types, limit, concats@)) by { reveal(UseAliases::concat_prefix); };
        while i < count
            invariant
                self.can_resolve(), self.module_alias_types_result(owner, limit, Ok(Some(typed))),
                i == concats@.len() <= count == typed.sources.roots.wiring.drivers.definitions@.len(),
                types@.len() == count, self.fixed_point(&typed, limit, types),
                self.concat_prefix(&typed, &types, limit, concats@),
            decreases count - i,
        {
            let concat = self.check_module_concat_row(owner, limit, &typed, &types, i)?;
            let ghost before = concats@;
            concats.push(concat);
            assert(self.concat_prefix(&typed, &types, limit, concats@)) by {
                reveal(UseAliases::concat_prefix);
                assert forall|j: int| 0 <= j < concats@.len() implies self.concat_at(&typed, &types, j, limit, Ok(#[trigger] concats@[j])) by {
                    if j < i { assert(concats@[j] == before[j]); }
                };
            };
            i += 1;
        }
        Ok(Some(ModuleConcats { typed, types, concats }))
    }
}

} // verus!
