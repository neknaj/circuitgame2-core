//! 連接の引数をソース順で型検査し、合計のビット幅を求める。

use super::{ModuleAliasTypes, ModuleAliasTypesError, UseAliases, aliases::find_member, selections::read_bound_type};
use crate::project::use_aliases::function_atoms::copy_signal_type;
use crate::project::{CircuitLiteralWidthError, ConcatResultWidthError, LocatedName, ModuleBodyPosition, OutputDriver,
    ProjectSource, ResolvedPortType, SignalType, check_circuit_literal_width, check_concat_result_width,
    circuits::{form_location, read_indexed_atom}};
#[cfg(verus_only)]
use crate::project::{circuit_literal_width_matches, concat_result_width_matches, location_in_source,
    circuits::{is_form_location, parsed_circuit_matches, parsed_index_evidence}};
#[cfg(verus_only)]
use super::{propagation::type_sites_valid, selections::bound_type};
use crate::syntax::{AtomKind, Form, circuit::{NamedBuildCircuit, concat_argument_range,
    definition_target_atoms, next_call_argument}};
#[cfg(verus_only)]
use crate::syntax::{complete_list_indices, form_span, nested_list_indices, circuit::{build_definition_scope_evidence,
    concat_arguments_evidence, concat_arguments_match, definition_signal_positions_in_order, definition_target_range,
    direct_form_in_range, expression_region, following_concat_argument, indexed_concat_argument_signal}};
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
    /// 信号の場合は駆動元。リテラルの場合は `None`。
    pub driver: Option<OutputDriver>,
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

spec fn concat_operand(
    context: &ConcatContext, form: usize, limit: u64, result: Result<Option<ModuleConcatOperand>, ModuleConcatsError>,
) -> bool {
    let forms = context.parsed.syntax.forms@;
    let atom = forms[form as int];
    if atom is Atom && atom->Atom_kind is Name {
        let wiring = &context.typed.sources.roots.wiring;
        let row = context.parsed.definitions@[context.definition as int];
        let frame = context.parsed.entry_ranges@[context.body.entry as int].signals;
        exists|i: int| row.signals.start <= i < row.signals.end && (#[trigger] context.parsed.signals@[i]) == form
            && {
                let bound = wiring.signals@[context.member as int]@[i - frame.start];
                &&& bound.form == form
                &&& match bound_type(context.typed, context.types@, bound.driver) {
                    None => result == Ok(None),
                    Some(ty) => match ty.ty {
                        ResolvedPortType::Bits(width) => result matches Ok(Some(item))
                            && item.form == form && item.driver == Some(bound.driver) && item.width == width,
                        ResolvedPortType::Struct { .. } => result matches Err(ModuleConcatsError::InputType { argument, actual })
                            && is_form_location(context.source, atom, argument) && actual == ty,
                    },
                }
            }
    } else if atom is Atom && (atom->Atom_kind is Natural || atom->Atom_kind is Binary || atom->Atom_kind is Hexadecimal) {
        let span = form_span(atom);
        let bytes = context.source.text.spec_bytes()[span.start as int..span.end as int];
        match result {
            Ok(Some(item)) => item.form == form && item.driver.is_none()
                && circuit_literal_width_matches(bytes, None, limit, Ok(item.width)),
            Err(ModuleConcatsError::Literal { literal, error }) => is_form_location(context.source, atom, literal)
                && circuit_literal_width_matches(bytes, None, limit, Err(error)),
            _ => false,
        }
    } else { result == Ok(None) }
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
            concat_arguments_match(context.source.text, context.parsed.syntax.forms@,
                context.parsed.definitions@[context.definition as int].expression.start as int, arguments),
            direct_form_in_range(context.parsed.syntax.forms@, arguments.start as int, arguments.end as int, at as int),
        ensures concat_operand(context, at, limit, result),
    {
        let source = context.source;
        let parsed = context.parsed;
        let forms = parsed.syntax.forms.as_slice();
        let row = &parsed.definitions[context.definition];
        proof { parsed_index_evidence(*source, *parsed); }
        match forms[at] {
            Form::Atom { kind: AtomKind::Name, .. } => {
                let ghost model = parsed.build_model();
                proof {
                    indexed_concat_argument_signal(source.text, &model, context.body.entry as int, context.definition as int, arguments, at);
                    definition_signal_positions_in_order(source.text, &model, context.body.entry as int, context.definition as int);
                    build_definition_scope_evidence(source.text, &model, context.body.entry as int, context.definition as int);
                }
                let Some(position) = find_signal(parsed.signals.as_slice(), row.signals.start, row.signals.end, at) else {
                    unreachable!()
                };
                let wiring = &context.typed.sources.roots.wiring;
                let frame = &parsed.entry_ranges[context.body.entry].signals;
                proof {
                    self.module_alias_types_evidence(_owner, limit, *context.typed);
                    self.module_signal_index_item(_owner, limit, *wiring, context.member as int, position as int);
                }
                let bound = &wiring.signals[context.member][position - frame.start];
                let Some(actual) = read_bound_type(context.typed, context.types.as_slice(), bound.driver) else { return Ok(None); };
                let ResolvedPortType::Bits(width) = actual.ty else {
                    return Err(ModuleConcatsError::InputType { argument: form_location(source, forms, at), actual });
                };
                Ok(Some(ModuleConcatOperand { form: at, driver: Some(bound.driver), width }))
            },
            Form::Atom { kind: AtomKind::Natural | AtomKind::Binary | AtomKind::Hexadecimal, .. } => {
                let (word, _) = read_indexed_atom(source.text, forms, at);
                match check_circuit_literal_width(word, None, limit) {
                    Ok(width) => Ok(Some(ModuleConcatOperand { form: at, driver: None, width })),
                    Err(error) => Err(ModuleConcatsError::Literal { literal: form_location(source, forms, at), error }),
                }
            },
            _ => Ok(None),
        }
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
            self.concat_context(_owner, limit, context),
            concat_arguments_match(context.source.text, context.parsed.syntax.forms@,
                context.parsed.definitions@[context.definition as int].expression.start as int, arguments),
        ensures self.concat_result(context, context.parsed.definitions@[context.definition as int].expression.start, arguments, limit, result),
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
                self.concat_context(_owner, limit, context), *source == *context.source, forms@ == context.parsed.syntax.forms@,
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
            types@.len() == typed.sources.roots.wiring.drivers.definitions@.len(),
        ensures self.concat_at(typed, types, i as int, limit, result),
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
            type_sites_valid(checked.types@),
    {
        self.module_alias_types_evidence(owner, limit, checked.typed);
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
    /// 型が未確定の子式や信号を含む場合は、その引数から先を保留する。
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
