//! 回路本体の展開呼び出しから、生成した信号接続を元の順序で集める。

use super::GeneratedWiringError;
use crate::project::{GeneratedSignalAlias, GeneratedSignalPosition, LocatedName, MacroCalls, MixedUseAliases};
use crate::ncg2m::call_evaluation::macro_expansion::{MacroExpandedBody, MacroExpansionSlice};
use crate::ncg2m::call_evaluation::macro_syntax::TemplateDefinitionError;
use crate::project::use_aliases::generated_signals::generated_event_location;
#[cfg(verus_only)]
use crate::project::{
    generated_signal_alias_shape, generated_template_signal_matches, location_in_source,
};
#[cfg(verus_only)]
use crate::ncg2m::call_evaluation::macro_expansion::{MacroExpansion, macro_expansion_slice_matches};
#[cfg(verus_only)]
use crate::ncg2m::call_evaluation::macro_syntax::{CheckedTemplateDefinition, template_definition_check_matches};
#[cfg(verus_only)]
use crate::syntax::circuit::routine_expansion_sites_match;
use alloc::vec::Vec;
use core::num::NonZeroUsize;
use vstd::prelude::*;

verus! {

/// 一つの生成信号接続が、選んだ展開要素の構文・左辺・右辺に対応する。
#[verifier::opaque]
pub open spec fn generated_alias_element_matches(
    expanded: &MacroExpandedBody, element: usize, alias: GeneratedSignalAlias,
) -> bool {
    &&& element < expanded.elements_model().len()
    &&& location_in_source(alias.reference_model().location_model())
    &&& exists|checked: CheckedTemplateDefinition|
        #[trigger] template_definition_check_matches(expanded, element, Some(Ok(checked)))
        && generated_signal_alias_shape(checked.row_model())
        && generated_template_signal_matches(&checked, GeneratedSignalPosition::Target(0), Some(alias.target_model()))
        && generated_template_signal_matches(&checked, GeneratedSignalPosition::Reference(0), Some(alias.reference_model()))
}

proof fn record_alias_element(
    expanded: &MacroExpandedBody, element: usize, checked: CheckedTemplateDefinition, alias: GeneratedSignalAlias,
)
    requires element < expanded.elements_model().len(),
        template_definition_check_matches(expanded, element, Some(Ok(checked))),
        generated_signal_alias_shape(checked.row_model()),
        generated_template_signal_matches(&checked, GeneratedSignalPosition::Target(0), Some(alias.target_model())),
        generated_template_signal_matches(&checked, GeneratedSignalPosition::Reference(0), Some(alias.reference_model())),
    ensures generated_alias_element_matches(expanded, element, alias),
{
    reveal(generated_alias_element_matches);
    assert(location_in_source(alias.reference_model().location_model()));
}

/// 完成した展開の全要素から、同じ順序で信号接続を取り出したことを表す。
pub open spec fn generated_alias_elements_match(expanded: &MacroExpandedBody, aliases: Seq<GeneratedSignalAlias>) -> bool {
    &&& expanded.elements_model().len() == aliases.len()
    &&& forall|i: int| 0 <= i < aliases.len() ==> generated_alias_element_matches(expanded, i as usize, #[trigger] aliases[i])
}

fn check_generated_alias_elements<'p, 'a>(
    expanded: &MacroExpandedBody<'_, 'p, 'a>, aliases: &mut Vec<GeneratedSignalAlias<'p, 'a>>,
) -> (result: Result<(), GeneratedWiringError<'p, 'a>>)
    ensures result.is_ok() ==> {
        &&& old(aliases)@.len() <= final(aliases)@.len()
        &&& final(aliases)@.take(old(aliases)@.len() as int) == old(aliases)@
        &&& generated_alias_elements_match(expanded, final(aliases)@.skip(old(aliases)@.len() as int))
    },
{
    let bound = expanded.call();
    let site = bound.site();
    let source = bound.scope().source;
    let prefix = aliases.len();
    let ghost initial = aliases@;
    let mut i = 0;
    let count = expanded.elements().len();
    while i < count
        invariant
            prefix == initial.len(),
            i <= count == expanded.elements_model().len(),
            prefix + i == aliases@.len(), aliases@.take(prefix as int) == initial,
            forall|j: int| 0 <= j < i ==> generated_alias_element_matches(
                expanded, j as usize, #[trigger] aliases@[prefix + j],
            ),
        decreases count - i,
    {
        let call = LocatedName { source, span: site.span.start..site.span.end };
        let checked = match expanded.check_template_definition(i) {
            Some(Ok(checked)) => checked,
            Some(Err(error)) => match error.error {
                TemplateDefinitionError::Definition { kind, related } => {
                    let location = match related {
                        Some(event) => Some(generated_event_location(event)),
                        None => None,
                    };
                    return Err(GeneratedWiringError::InvalidDefinition { call, element: i, related: location, kind });
                },
                TemplateDefinitionError::UnexpectedClose(event) | TemplateDefinitionError::Unclosed(event) =>
                    return Err(GeneratedWiringError::InvalidProjection {
                        call, element: i, related: Some(generated_event_location(event)), token: event.token,
                    }),
                TemplateDefinitionError::Source(error) =>
                    return Err(GeneratedWiringError::InvalidProjection { call, element: i, related: None, token: error.token }),
            },
            None => return Err(GeneratedWiringError::UnsupportedDefinition { call, element: i }),
        };
        let Some(alias) = checked.signal_alias() else {
            return Err(GeneratedWiringError::UnsupportedDefinition { call, element: i });
        };
        assert(location_in_source(alias.reference_model().location_model()));
        proof { record_alias_element(expanded, i, checked, alias); }
        let ghost before = aliases@;
        aliases.push(alias);
        proof {
            assert(aliases@.take(prefix as int) =~= initial);
            assert forall|j: int| 0 <= j < i + 1 implies generated_alias_element_matches(
                expanded, j as usize, #[trigger] aliases@[prefix + j],
            ) by {
                if j < i { assert(aliases@[prefix + j] == before[prefix + j]); }
            };
        }
        i += 1;
    }
    proof {
        let saved = aliases@.skip(prefix as int);
        assert forall|j: int| 0 <= j < saved.len() implies generated_alias_element_matches(
            expanded, j as usize, #[trigger] saved[j],
        ) by {
            assert(saved[j] == aliases@[prefix + j]);
        };
    }
    Ok(())
}

/// 本体の次のマクロを展開し、既に集めた信号接続の後に全要素を追加する一歩。
#[verifier::opaque]
pub open spec fn collected_alias_step(
    before: &MacroCalls, after: &MacroCalls, fuel: nat,
    old_aliases: Seq<GeneratedSignalAlias>, added_aliases: Seq<GeneratedSignalAlias>,
) -> bool {
    &&& old_aliases.is_prefix_of(added_aliases)
    &&& exists|start: MacroExpansion, expanded: MacroExpandedBody| {
        &&& before.binding_advances(after, Some(Ok(*expanded.call_model())))
        &&& start.initial_for(expanded.call_model())
        &&& #[trigger] macro_expansion_slice_matches(start, fuel, Ok(MacroExpansionSlice::Complete(expanded)))
        &&& generated_alias_elements_match(&expanded, added_aliases.skip(old_aliases.len() as int))
    }
}

proof fn record_alias_call(
    before: &MacroCalls, after: &MacroCalls, start: MacroExpansion, expanded: MacroExpandedBody, fuel: nat,
    earlier: Seq<GeneratedSignalAlias>, current: Seq<GeneratedSignalAlias>,
)
    requires
        earlier.is_prefix_of(current),
        before.binding_advances(after, Some(Ok(*expanded.call_model()))),
        start.initial_for(expanded.call_model()),
        macro_expansion_slice_matches(start, fuel, Ok(MacroExpansionSlice::Complete(expanded))),
        generated_alias_elements_match(&expanded, current.skip(earlier.len() as int)),
    ensures collected_alias_step(before, after, fuel, earlier, current),
{
    reveal(collected_alias_step);
}

/// すべての展開呼び出しを元の順に評価し、それぞれの結果から信号接続を取り出した履歴。
pub open spec fn collected_alias_prefix(
    initial: &MacroCalls, fuel: nat, calls: Seq<MacroCalls>, aliases: Seq<Seq<GeneratedSignalAlias>>,
) -> bool {
    &&& 0 < calls.len() == aliases.len()
    &&& calls[0] == *initial && aliases[0].len() == 0
    &&& forall|i: int| 0 <= i + 1 < calls.len() && 0 <= i ==> #[trigger]
        collected_alias_step(&calls[i], &calls[i+1], fuel, aliases[i], aliases[i+1])
}

/// 全呼び出しを消費したまま、先頭から末尾までの信号接続を保持する。
#[verifier::opaque]
pub open spec fn collected_aliases_match(initial: &MacroCalls, fuel: nat, aliases: Seq<GeneratedSignalAlias>) -> bool {
    exists|calls: Seq<MacroCalls>, history: Seq<Seq<GeneratedSignalAlias>>, end: MacroCalls| {
        &&& #[trigger] collected_alias_prefix(initial, fuel, calls, history)
        &&& #[trigger] calls.last().binding_advances(&end, None)
        &&& history.last() == aliases
    }
}

proof fn extend_alias_prefix(
    initial: &MacroCalls, fuel: nat, calls: Seq<MacroCalls>, history: Seq<Seq<GeneratedSignalAlias>>,
    next: MacroCalls, after: Seq<GeneratedSignalAlias>,
)
    requires collected_alias_prefix(initial, fuel, calls, history),
        collected_alias_step(&calls.last(), &next, fuel, history.last(), after),
    ensures collected_alias_prefix(initial, fuel, calls.push(next), history.push(after)),
{
    let updated_calls = calls.push(next);
    let updated_history = history.push(after);
    assert forall|i: int| 0 <= i && i + 1 < updated_calls.len() implies #[trigger]
        collected_alias_step(&updated_calls[i], &updated_calls[i+1], fuel, updated_history[i], updated_history[i+1]) by {
        if i + 1 < calls.len() {
            assert(collected_alias_step(&calls[i], &calls[i+1], fuel, history[i], history[i+1]));
        }
    };
}

proof fn complete_alias_prefix(
    initial: &MacroCalls, fuel: nat, calls: Seq<MacroCalls>, history: Seq<Seq<GeneratedSignalAlias>>, end: MacroCalls,
)
    requires collected_alias_prefix(initial, fuel, calls, history),
        calls.last().binding_advances(&end, None),
    ensures collected_aliases_match(initial, fuel, history.last()),
{
    reveal(collected_aliases_match);
}

/// 検査対象の関数の先頭から展開呼び出しと全要素を消費したことを表す。
#[verifier::opaque]
pub open spec fn function_generated_aliases_match(
    expected: &MixedUseAliases, file: usize, entry: usize, fuel: nat, aliases: Seq<GeneratedSignalAlias>,
) -> bool {
    exists|initial: MacroCalls| {
        &&& initial.valid() && initial.aliases_model() == expected && initial.origin_model() == (file, entry)
        &&& routine_expansion_sites_match(
            initial.source_model().text_model(), initial.sites_model().syntax_model(), entry as int, Some(initial.sites_model()),
        )
        &&& #[trigger] collected_aliases_match(&initial, fuel, aliases)
    }
}

pub(super) proof fn collected_aliases_from_function(
    expected: &MixedUseAliases, file: usize, entry: usize, fuel: nat, initial: MacroCalls, aliases: Seq<GeneratedSignalAlias>,
)
    requires initial.valid(), initial.aliases_model() == expected, initial.origin_model() == (file, entry),
        routine_expansion_sites_match(
            initial.source_model().text_model(), initial.sites_model().syntax_model(), entry as int, Some(initial.sites_model()),
        ),
        collected_aliases_match(&initial, fuel, aliases),
    ensures function_generated_aliases_match(expected, file, entry, fuel, aliases),
{
    reveal(function_generated_aliases_match);
}

proof fn added_alias_locations(
    expanded: &MacroExpandedBody, earlier: Seq<GeneratedSignalAlias>, current: Seq<GeneratedSignalAlias>,
)
    requires earlier.len() <= current.len(), current.take(earlier.len() as int) == earlier,
        generated_alias_elements_match(expanded, current.skip(earlier.len() as int)),
        forall|i: int| 0 <= i < earlier.len()
            ==> location_in_source((#[trigger] earlier[i]).reference_model().location_model()),
    ensures earlier.is_prefix_of(current),
        forall|i: int| 0 <= i < current.len()
            ==> location_in_source((#[trigger] current[i]).reference_model().location_model()),
{
    assert forall|i: int| 0 <= i < earlier.len() implies #[trigger] current[i] == earlier[i] by {
        assert(current.take(earlier.len() as int)[i] == current[i]);
    };
    reveal(generated_alias_element_matches);
    assert forall|i: int| 0 <= i < current.len()
        implies location_in_source((#[trigger] current[i]).reference_model().location_model()) by {
        if i < earlier.len() {
            assert(current[i] == earlier[i]);
        } else {
            let added = current.skip(earlier.len() as int);
            assert(added[i - earlier.len()] == current[i]);
            assert(generated_alias_element_matches(&expanded, (i - earlier.len()) as usize, added[i - earlier.len()]));
        }
    };
}

pub(super) fn collect_generated_aliases<'p, 'a>(initial: MacroCalls<'_, '_, 'p, 'a>, fuel: NonZeroUsize)
    -> (result: Result<Vec<GeneratedSignalAlias<'p, 'a>>, GeneratedWiringError<'p, 'a>>)
    requires initial.valid(),
    ensures result matches Ok(aliases) ==>
        collected_aliases_match(&initial, fuel@ as nat, aliases@)
        && forall|i: int| 0 <= i < aliases@.len()
            ==> location_in_source((#[trigger] aliases@[i]).reference_model().location_model()),
{
    let mut calls = initial;
    let mut aliases: Vec<GeneratedSignalAlias<'p, 'a>> = Vec::new();
    let ghost mut steps = seq![initial];
    let ghost mut history = seq![aliases@];
    loop
        invariant
            calls.valid(), calls == steps.last(), aliases@ == history.last(),
            collected_alias_prefix(&initial, fuel@ as nat, steps, history),
            forall|i: int| 0 <= i < aliases@.len()
                ==> location_in_source((#[trigger] aliases@[i]).reference_model().location_model()),
        decreases calls.sites_model().body_model().end - calls.sites_model().position_model(),
    {
        let ghost before = calls;
        let Some(bound) = calls.next_bound_macro() else {
            proof { complete_alias_prefix(&initial, fuel@ as nat, steps, history, calls); }
            return Ok(aliases);
        };
        let bound = match bound {
            Ok(bound) => bound,
            Err(error) => return Err(GeneratedWiringError::Preparation(error)),
        };
        let site = bound.site();
        let source = bound.scope().source;
        let call = LocatedName { source, span: site.span.start..site.span.end };
        let start = bound.start_expansion();
        let ghost start_model = start;
        let expanded = match start.run_slice(fuel) {
            Ok(MacroExpansionSlice::Complete(expanded)) => expanded,
            Ok(MacroExpansionSlice::Suspended(_)) => return Err(GeneratedWiringError::Fuel(call)),
            Err(error) => return Err(GeneratedWiringError::Expansion {
                call, definition: error.definition, related: error.related, kind: error.kind,
            }),
        };
        let ghost earlier = aliases@;
        check_generated_alias_elements(&expanded, &mut aliases)?;
        proof {
            added_alias_locations(&expanded, earlier, aliases@);
            record_alias_call(&before, &calls, start_model, expanded, fuel@ as nat, earlier, aliases@);
            extend_alias_prefix(&initial, fuel@ as nat, steps, history, calls, aliases@);
            steps = steps.push(calls);
            history = history.push(aliases@);
        }
    }
}

} // verus!
