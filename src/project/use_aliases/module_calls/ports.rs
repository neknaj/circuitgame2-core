//! 通常呼び出しの入出力数を検査し、実引数の構文位置を入力ポートと対応付ける。

use super::{ModuleCallSignature, ModuleCallSignatureError, ModuleCallTarget, UseAliases};
use crate::project::{CallPortType, DefinitionPosition, LocatedName, PortDirection};
#[cfg(verus_only)]
use crate::project::{FuncCallSignature, circuits::{is_form_location, parsed_index_evidence}, location_in_source};
use crate::project::circuits::form_location;
use crate::project::use_aliases::{call_arity::signature_port, function_atoms::copy_location};
#[cfg(verus_only)]
use crate::project::use_aliases::call_arity::signature_port_matches;
use crate::syntax::{Form, circuit::{BuildDefinition, CallShape, RoutineArity, call_argument_range, definition_target_atoms, next_call_argument}};
#[cfg(verus_only)]
use crate::syntax::{complete_list_indices, form_spans_valid, nested_list_indices, circuit::{
    build_definition_scope_evidence, build_entry_ranges_evidence, call_argument_positions,
    call_argument_positions_from_steps, call_argument_sequence, call_arguments_match, definition_target_range,
    definition_targets_match, direct_call_argument, exhausted_call_arguments, expression_region,
    first_call_argument_evidence, following_call_argument,
}};
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// 入出力数を照合した通常呼び出しと、宣言順に対応する引数の構文位置。
#[derive(Debug)]
pub struct ModuleCallPorts<'p, 'a> {
    /// 元の呼び出し位置と、名前解決した参照先。
    pub signature: ModuleCallSignature<'p, 'a>,
    /// 直接の引数式の先頭。入力ポートと同じ順で、入れ子の式を一つとして扱う。
    pub arguments: Vec<usize>,
}

/// 呼び出しの入出力数を照合するまでに見つかった違反。
#[derive(Debug)]
pub enum ModuleCallPortsError<'p, 'a> {
    /// 呼び出し名の解決または参照先の署名の診断。
    Signature(ModuleCallSignatureError<'p, 'a>),
    /// この検査で使う署名を持たない状態素子の呼び出し。
    StateElement {
        /// ラッチまたはメモリの宣言種別。
        head: crate::syntax::circuit::Head,
        /// 呼び出し式全体の範囲。
        call: LocatedName<'p, 'a>,
        /// ラッチまたはメモリの宣言名の範囲。
        state_declaration: LocatedName<'p, 'a>,
    },
    /// 入力ポート数と実引数数の不一致。
    InputCount {
        /// 呼び出し式全体の範囲。
        call: LocatedName<'p, 'a>,
        /// 呼び出し先の宣言名。基底 NOR では `None`。
        declaration: Option<LocatedName<'p, 'a>>,
        /// 呼び出し先が要求する入力ポート数。
        expected: usize,
        /// ソースに書かれた直接の引数数。
        actual: usize,
    },
    /// 右辺を使う箇所が要求する出力数と、参照先の出力数の不一致。
    OutputCount {
        /// 呼び出し式全体の範囲。
        call: LocatedName<'p, 'a>,
        /// 右辺全体を占める場合は左辺の範囲。子式では `None`。
        left: Option<LocatedName<'p, 'a>>,
        /// 呼び出し先の宣言名。基底 NOR では `None`。
        declaration: Option<LocatedName<'p, 'a>>,
        /// 左辺の名前の数。子式では1。
        expected: usize,
        /// 呼び出し先が返す出力ポート数。
        actual: usize,
    },
}

impl<'p, 'a> ModuleCallTarget<'p, 'a> {
    spec fn port_counts(&self) -> Option<RoutineArity> {
        match self {
            ModuleCallTarget::Nor => Some(RoutineArity { inputs: 2, outputs: 1 }),
            ModuleCallTarget::Routine { signature, .. } => Some(RoutineArity {
                inputs: signature.inputs@.len() as usize, outputs: signature.outputs@.len() as usize,
            }),
            ModuleCallTarget::StateElement { .. } => None,
        }
    }

    fn arity(&self) -> (result: Option<RoutineArity>)
        ensures result == self.port_counts(),
    {
        match self {
            Self::Nor => Some(RoutineArity { inputs: 2, outputs: 1 }),
            Self::Routine { signature, .. } => Some(RoutineArity {
                inputs: signature.inputs.len(), outputs: signature.outputs.len(),
            }),
            Self::StateElement { .. } => None,
        }
    }

    spec fn declaration_site(&self) -> Option<LocatedName<'p, 'a>> {
        match self {
            ModuleCallTarget::Nor => None,
            ModuleCallTarget::Routine { declaration, .. } | ModuleCallTarget::StateElement { declaration, .. } => Some(*declaration),
        }
    }

    fn copy_declaration(&self) -> (location: Option<LocatedName<'p, 'a>>)
        ensures location == self.declaration_site(),
    {
        match self {
            Self::Nor => None,
            Self::Routine { declaration, .. } | Self::StateElement { declaration, .. } => Some(copy_location(declaration)),
        }
    }

    /// 指定した方向のポート型を宣言順の添字で参照する。範囲外や状態素子の場合は `None` を返す。
    pub fn port<'s>(&'s self, direction: PortDirection, index: usize) -> (port: Option<CallPortType<'s, 'p, 'a>>)
        ensures
            self.port_matches(direction, index, port),
            port.is_some() == match self {
                ModuleCallTarget::Nor => index < if direction is Input { 2usize } else { 1usize },
                ModuleCallTarget::Routine { signature, .. } => index < if direction is Input {
                    signature.inputs@.len()
                } else { signature.outputs@.len() },
                ModuleCallTarget::StateElement { .. } => false,
            },
    {
        match self {
            Self::Nor => signature_port(None, direction, index),
            Self::Routine { signature, .. } => signature_port(Some(signature), direction, index),
            Self::StateElement { .. } => None,
        }
    }

    /// 返したポート型と注釈が、指定した方向と宣言順の添字に対応することを表す。
    pub closed spec fn port_matches(&self, direction: PortDirection, index: usize, port: Option<CallPortType>) -> bool {
        match self {
            ModuleCallTarget::Nor => signature_port_matches(FuncCallSignature::Nor, direction, index, port),
            ModuleCallTarget::Routine { signature, .. } =>
                signature_port_matches(FuncCallSignature::Function(*signature), direction, index, port),
            ModuleCallTarget::StateElement { .. } => port.is_none(),
        }
    }
}

spec fn after_argument(forms: Seq<Form>, root: int) -> int {
    if forms[root] is List { forms[root]->List_end as int } else { root + 1 }
}

#[verifier::opaque]
spec fn argument_prefix(forms: Seq<Form>, call: CallShape, roots: Seq<usize>, cursor: int) -> bool {
    &&& cursor == if roots.len() == 0 { call.form + 2 } else { after_argument(forms, roots.last() as int) }
    &&& forall|i: int| 0 <= i < roots.len() ==> {
        let at = (#[trigger] roots[i]) as int;
        &&& direct_call_argument(forms, call, at)
        &&& at == if i == 0 { call.form + 2 } else { after_argument(forms, roots[i - 1] as int) }
    }
}

proof fn push_argument_root(forms: Seq<Form>, call: CallShape, before: Seq<usize>, root: usize)
    requires argument_prefix(forms, call, before, root as int), direct_call_argument(forms, call, root as int),
    ensures argument_prefix(forms, call, before.push(root), after_argument(forms, root as int)),
{
    reveal(argument_prefix);
    let after = before.push(root);
    assert(after.last() == root);
    assert forall|i: int| 0 <= i < after.len() implies {
        let at = (#[trigger] after[i]) as int;
        &&& direct_call_argument(forms, call, at)
        &&& at == if i == 0 { call.form + 2 } else { after_argument(forms, after[i - 1] as int) }
    } by {
        if i < before.len() {
            assert(after[i] == before[i]);
            assert(direct_call_argument(forms, call, before[i] as int));
        } else {
            assert(after[i] == root);
            if i > 0 { assert(after[i - 1] == before.last()); }
        }
    };
}

fn collect_argument_roots(forms: &[Form], call: &CallShape) -> (roots: Vec<usize>)
    requires call_arguments_match(forms@, *call), nested_list_indices(forms@), complete_list_indices(forms@),
    ensures roots@.len() == call.arguments, call_argument_positions(forms@, *call, roots@),
{
    let mut remaining = call_argument_range(forms, call);
    let mut roots = Vec::new();
    proof {
        first_call_argument_evidence(forms@, *call, remaining);
        assert(argument_prefix(forms@, *call, roots@, remaining.start as int)) by { reveal(argument_prefix); };
    }
    while remaining.start < remaining.end
        invariant
            call_arguments_match(forms@, *call), nested_list_indices(forms@), complete_list_indices(forms@),
            call.form < forms@.len(), forms@[call.form as int] is List,
            remaining.end == forms@[call.form as int]->List_end,
            call.form + 2 <= remaining.start <= remaining.end <= forms@.len(),
            expression_region(forms@, remaining.start as int, remaining.end as int),
            roots@.len() <= call.arguments,
            call_argument_sequence(forms@, remaining, call.arguments - roots@.len()),
            remaining.start < remaining.end ==> direct_call_argument(forms@, *call, remaining.start as int),
            argument_prefix(forms@, *call, roots@, remaining.start as int),
        decreases remaining.end - remaining.start,
    {
        let Some(argument) = next_call_argument(forms, remaining.start..remaining.end) else {
            proof { assert(false); }
            unreachable!()
        };
        proof {
            following_call_argument(forms@, *call, argument.start as int, argument.end as int);
            push_argument_root(forms@, *call, roots@, argument.start);
        }
        roots.push(argument.start);
        remaining.start = argument.end;
    }
    proof {
        exhausted_call_arguments(forms@, remaining, call.arguments - roots@.len());
        reveal(argument_prefix);
        call_argument_positions_from_steps(forms@, *call, roots@);
    }
    roots
}

spec fn expected_outputs(forms: Seq<Form>, row: BuildDefinition, call: CallShape) -> int {
    if call.form == row.expression.start {
        let (start, end) = definition_target_range(forms, row);
        end - start
    } else { 1 }
}

spec fn call_span(signature: ModuleCallSignature, location: LocatedName) -> bool {
    *location.source == *signature.source && location.span == signature.call.span && location_in_source(location)
}

spec fn checked_ports(
    forms: Seq<Form>, row: BuildDefinition, signature: ModuleCallSignature,
    result: Result<Option<ModuleCallPorts>, ModuleCallPortsError>,
) -> bool {
    match signature.target.port_counts() {
        None => result matches Err(ModuleCallPortsError::StateElement { head, call, state_declaration })
            && signature.target is StateElement && head == signature.target->StateElement_head
            && call_span(signature, call) && signature.target.declaration_site() == Some(state_declaration),
        Some(arity) => {
            let outputs = expected_outputs(forms, row, signature.call);
            if signature.call.arguments != arity.inputs {
                result matches Err(ModuleCallPortsError::InputCount { call, declaration, expected, actual })
                    && call_span(signature, call) && declaration == signature.target.declaration_site()
                    && expected == arity.inputs && actual == signature.call.arguments
            } else if outputs != arity.outputs {
                result matches Err(ModuleCallPortsError::OutputCount { call, left, declaration, expected, actual })
                    && call_span(signature, call) && declaration == signature.target.declaration_site()
                    && expected == outputs && actual == arity.outputs
                    && if signature.call.form == row.expression.start {
                        left matches Some(site) && is_form_location(signature.source, forms[row.form + 2], site)
                    } else { left.is_none() }
            } else {
                result matches Ok(Some(plan)) && plan.signature == signature
                    && plan.arguments@.len() == arity.inputs
                    && call_argument_positions(forms, signature.call, plan.arguments@)
            }
        },
    }
}

fn plan_call_ports<'p, 'a>(forms: &[Form], row: &BuildDefinition, signature: ModuleCallSignature<'p, 'a>)
    -> (result: Result<Option<ModuleCallPorts<'p, 'a>>, ModuleCallPortsError<'p, 'a>>)
    requires
        nested_list_indices(forms@), complete_list_indices(forms@),
        definition_targets_match(forms@, *row), call_arguments_match(forms@, signature.call),
        form_spans_valid(signature.source.text, forms@, signature.source.text.spec_bytes().len() as int),
        location_in_source(LocatedName { source: signature.source, span: signature.call.span }),
    ensures checked_ports(forms@, *row, signature, result),
{
    let source = signature.source;
    let call = LocatedName { source, span: signature.call.span.start..signature.call.span.end };
    assert(call_span(signature, call));
    let Some(arity) = signature.target.arity() else {
        let ModuleCallTarget::StateElement { head: kind, declaration: location, .. } = &signature.target else {
            proof { assert(false); }
            unreachable!()
        };
        return Err(ModuleCallPortsError::StateElement { head: *kind, call, state_declaration: copy_location(location) });
    };
    if signature.call.arguments != arity.inputs {
        return Err(ModuleCallPortsError::InputCount {
            call, declaration: signature.target.copy_declaration(), expected: arity.inputs, actual: signature.call.arguments,
        });
    }
    let outputs = if signature.call.form == row.expression.start {
        let targets = definition_target_atoms(forms, row);
        targets.end - targets.start
    } else { 1 };
    if outputs != arity.outputs {
        let left = if signature.call.form == row.expression.start {
            Some(form_location(source, forms, row.form + 2))
        } else { None };
        return Err(ModuleCallPortsError::OutputCount {
            call, left, declaration: signature.target.copy_declaration(), expected: outputs, actual: arity.outputs,
        });
    }
    let arguments = collect_argument_roots(forms, &signature.call);
    Ok(Some(ModuleCallPorts { signature, arguments }))
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// 入出力数と実引数の順序、または最初の違反の根拠を定める。
    pub closed spec fn module_call_ports_result(
        &self, at: DefinitionPosition, max_width: u64, result: Result<Option<ModuleCallPorts>, ModuleCallPortsError>,
    ) -> bool {
        match result {
            Ok(None) => self.module_call_signature_result(at, max_width, Ok(None)),
            Err(ModuleCallPortsError::Signature(error)) => self.module_call_signature_result(at, max_width, Err(error)),
            _ => {
                let project = self.targets.project_model();
                let parsed = &project.circuits_model()[at.file as int];
                let row = parsed.definitions@[parsed.entry_ranges@[at.entry as int].definitions.start + at.definition];
                exists|signature: ModuleCallSignature|
                    #[trigger] self.module_call_signature_result(at, max_width, Ok(Some(signature)))
                    && checked_ports(parsed.syntax.forms@, row, signature, result)
            },
        }
    }

    /// 引数の型を照合するときに、元の構文位置と入力ポート数が対応することを示す。
    pub(in crate::project::use_aliases) proof fn module_call_ports_evidence(
        &self, at: DefinitionPosition, max_width: u64, plan: ModuleCallPorts,
    )
        requires self.module_call_ports_result(at, max_width, Ok(Some(plan))),
        ensures
            self.module_call_signature_result(at, max_width, Ok(Some(plan.signature))),
            call_argument_positions(self.targets.project_model().circuits_model()[at.file as int].syntax.forms@,
                plan.signature.call, plan.arguments@),
            match plan.signature.target {
                ModuleCallTarget::Nor => plan.arguments@.len() == 2,
                ModuleCallTarget::Routine { signature, .. } => plan.arguments@.len() == signature.inputs@.len(),
                ModuleCallTarget::StateElement { .. } => false,
            },
    {
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[at.file as int];
        let row = parsed.definitions@[parsed.entry_ranges@[at.entry as int].definitions.start + at.definition];
        let signature = choose|signature: ModuleCallSignature|
            #[trigger] self.module_call_signature_result(at, max_width, Ok(Some(signature)))
            && checked_ports(parsed.syntax.forms@, row, signature, Ok(Some(plan)));
        assert(plan.signature == signature);
        if let ModuleCallTarget::Routine { signature, .. } = &plan.signature.target {
            vstd::std_specs::vec::axiom_spec_len(&signature.inputs);
        }
    }

    /// 通常呼び出しの入出力数を照合し、各入力ポートに対応する引数位置を返す。
    ///
    /// `at` は同じ厳格解析の添字を指す。呼び出しを指さない場合は `None` を返す。
    /// 引数の型を検査するときは、同じ添字で [`ModuleCallTarget::port`] から要求型を得られる。
    ///
    /// # Errors
    ///
    /// 名前解決と署名を検査してから入力数、出力数の順に検査する。
    /// ラッチまたはメモリを呼ぶ場合は、状態素子の宣言を示す診断を返す。
    pub fn check_module_call_ports(&self, at: DefinitionPosition, max_width: u64)
        -> (result: Result<Option<ModuleCallPorts<'p, 'a>>, ModuleCallPortsError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.module_call_ports_result(at, max_width, result),
    {
        let signature = match self.resolve_module_call_signature(at, max_width) {
            Ok(Some(signature)) => signature,
            Ok(None) => return Ok(None),
            Err(error) => return Err(ModuleCallPortsError::Signature(error)),
        };
        proof { self.module_call_site_evidence(at, max_width, signature); }
        let project = self.targets.project();
        let parsed = &project.circuits()[at.file];
        let forms = parsed.syntax.forms.as_slice();
        let ghost source = signature.source;
        let ghost model = parsed.build_model();
        proof {
            parsed_index_evidence(*source, *parsed);
            build_entry_ranges_evidence(source.text, &model, at.entry as int);
        }
        let definition = parsed.entry_ranges[at.entry].definitions.start + at.definition;
        proof { build_definition_scope_evidence(source.text, &model, at.entry as int, definition as int); }
        let row = &parsed.definitions[definition];
        let ghost input_signature = signature;
        let plan = plan_call_ports(forms, row, signature);
        assert(checked_ports(forms@, *row, input_signature, plan));
        plan
    }
}

} // verus!
