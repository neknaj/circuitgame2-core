//! 連接の引数をソース順で型検査し、合計のビット幅を求める。

use super::{ModuleAliasTypes, ModuleAliasTypesError, UseAliases, aliases::find_member, selections::read_bound_type};
use crate::project::{CircuitLiteralWidthError, ConcatResultWidthError, LocatedName, ModuleBodyPosition, OutputDriver,
    ProjectSource, ResolvedPortType, SignalType, check_circuit_literal_width, check_concat_result_width,
    circuits::{form_location, read_indexed_atom}};
#[cfg(verus_only)]
use crate::project::{circuit_literal_width_matches, concat_result_width_matches, circuits::{is_form_location, parsed_circuit_matches, parsed_index_evidence}};
#[cfg(verus_only)]
use super::selections::bound_type;
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
    body: ModuleBodyPosition,
    member: usize,
    definition: usize,
    source: &'p ProjectSource<'a>,
    parsed: &'p NamedBuildCircuit<'a>,
}

fn find_signal(signals: &[usize], start: usize, end: usize, form: usize) -> (result: usize)
    requires
        start <= end <= signals@.len(),
        exists|i: int| start <= i < end && (#[trigger] signals@[i]) == form,
        forall|i: int, j: int| start <= i < j < end ==> #[trigger] signals@[i] < #[trigger] signals@[j],
    ensures start <= result < end && signals@[result as int] == form,
{
    let ghost target = choose|i: int| start <= i < end && (#[trigger] signals@[i]) == form;
    let mut low = start;
    let mut high = end;
    while low < high
        invariant
            start <= low <= target < high <= end <= signals@.len(), signals@[target] == form,
            forall|i: int, j: int| start <= i < j < end ==> #[trigger] signals@[i] < #[trigger] signals@[j],
        decreases high - low,
    {
        let middle = low + (high - low) / 2;
        let current = signals[middle];
        if current == form { return middle; }
        if current < form {
            assert(middle < target) by { if target < middle { assert(signals@[target] < signals@[middle as int]); } };
            low = middle + 1;
        } else {
            assert(target < middle) by { if middle < target { assert(signals@[middle as int] < signals@[target]); } };
            high = middle;
        }
    }
    proof { assert(false); }
    unreachable!()
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
                &&& match bound_type(context.typed, bound.driver) {
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
                let position = find_signal(parsed.signals.as_slice(), row.signals.start, row.signals.end, at);
                let wiring = &context.typed.sources.roots.wiring;
                let frame = &parsed.entry_ranges[context.body.entry].signals;
                proof {
                    self.module_alias_types_evidence(_owner, limit, *context.typed);
                    self.module_signal_index_item(_owner, limit, *wiring, context.member as int, position as int);
                }
                let bound = &wiring.signals[context.member][position - frame.start];
                let Some(actual) = read_bound_type(context.typed, bound.driver) else { return Ok(None); };
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

    spec fn concat_at(&self, typed: &ModuleAliasTypes, index: int, limit: u64, result: Result<Option<ModuleConcat>, ModuleConcatsError>) -> bool {
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
            && self.concat_result(&ConcatContext { typed, body, member, definition, source, parsed }, root as usize, arguments, limit, result)
    }

    fn check_module_concat_row(&self, _owner: ModuleBodyPosition, limit: u64, typed: &ModuleAliasTypes<'p, 'a>, i: usize)
        -> (result: Result<Option<ModuleConcat<'p, 'a>>, ModuleConcatsError<'p, 'a>>)
        requires self.can_resolve(), self.module_alias_types_result(_owner, limit, Ok(Some(*typed))),
            i < typed.sources.roots.wiring.drivers.definitions@.len(),
        ensures self.concat_at(typed, i as int, limit, result),
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
        let context = ConcatContext { typed, body, member, definition, source, parsed };
        let result = self.check_concat_arguments(_owner, limit, &context, arguments);
        proof {
            let model = self.targets.project_model();
            assert(context == (ConcatContext { typed, body, member, definition,
                source: &model.sources_model()[body.file as int], parsed: &model.circuits_model()[body.file as int] }));
            assert(self.concat_result(&context, row.expression.start, arguments, limit, result));
            assert(self.concat_at(typed, i as int, limit, result));
        }
        result
    }

    #[verifier::opaque]
    spec fn concat_prefix(&self, typed: &ModuleAliasTypes, limit: u64, concats: Seq<Option<ModuleConcat>>) -> bool {
        &&& concats.len() <= typed.sources.roots.wiring.drivers.definitions@.len()
        &&& forall|i: int| 0 <= i < concats.len() ==> self.concat_at(typed, i, limit, Ok(#[trigger] concats[i]))
    }

    /// 連接の幅と引数順、または最初に見つかった違反を元の断片に対応付ける。
    pub closed spec fn module_concats_result(&self, owner: ModuleBodyPosition, limit: u64,
        result: Result<Option<ModuleConcats>, ModuleConcatsError>) -> bool {
        match result {
            Ok(None) => self.module_alias_types_result(owner, limit, Ok(None)),
            Err(ModuleConcatsError::Types(error)) => self.module_alias_types_result(owner, limit, Err(error)),
            Ok(Some(checked)) => self.module_alias_types_result(owner, limit, Ok(Some(checked.typed)))
                && checked.concats@.len() == checked.typed.sources.roots.wiring.drivers.definitions@.len()
                && self.concat_prefix(&checked.typed, limit, checked.concats@),
            Err(error) => exists|typed: ModuleAliasTypes, prefix: Seq<Option<ModuleConcat>>|
                #[trigger] self.module_alias_types_result(owner, limit, Ok(Some(typed)))
                && #[trigger] self.concat_prefix(&typed, limit, prefix)
                && prefix.len() < typed.sources.roots.wiring.drivers.definitions@.len()
                && self.concat_at(&typed, prefix.len() as int, limit, Err(error)),
        }
    }

    /// 右辺全体を占める連接の幅を、型が分かった信号名とリテラルから求める。
    ///
    /// 引数順に幅を記録する。子式や型が未確定の信号を含む場合は、その引数から先を保留する。
    ///
    /// # Errors
    ///
    /// 配線と型伝播を先に検査する。定義順に、左辺の名前数、引数、合計幅の順で違反を調べる。
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
        let count = typed.sources.roots.wiring.drivers.definitions.len();
        let mut concats = Vec::new();
        let mut i = 0;
        assert(self.concat_prefix(&typed, limit, concats@)) by { reveal(UseAliases::concat_prefix); };
        while i < count
            invariant
                self.can_resolve(), self.module_alias_types_result(owner, limit, Ok(Some(typed))),
                i == concats@.len() <= count == typed.sources.roots.wiring.drivers.definitions@.len(),
                self.concat_prefix(&typed, limit, concats@),
            decreases count - i,
        {
            let concat = self.check_module_concat_row(owner, limit, &typed, i)?;
            let ghost before = concats@;
            concats.push(concat);
            assert(self.concat_prefix(&typed, limit, concats@)) by {
                reveal(UseAliases::concat_prefix);
                assert forall|j: int| 0 <= j < concats@.len() implies self.concat_at(&typed, j, limit, Ok(#[trigger] concats@[j])) by {
                    if j < i { assert(concats@[j] == before[j]); }
                };
            };
            i += 1;
        }
        Ok(Some(ModuleConcats { typed, concats }))
    }
}

} // verus!
