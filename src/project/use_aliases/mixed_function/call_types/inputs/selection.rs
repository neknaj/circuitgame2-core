//! 混在関数の右辺を占めるビット選択の型を調べる。

use super::*;
use crate::project::{FuncSignalTypeError, TypedPort};
use crate::project::use_aliases::{
    function_atoms::{check_nested_selection_type, check_selection_type, named_selection},
    selection_arguments::nested_named_selection,
};
#[cfg(verus_only)]
use crate::project::use_aliases::{
    function_atoms::{named_selection_matches, nested_selection_type_matches, selection_type_matches},
    selection_arguments::nested_named_selection_matches,
};
use crate::syntax::circuit::BitSelectionShape;
#[cfg(verus_only)]
use crate::syntax::circuit::{build_selection_chain_signal, build_selection_input_position};

verus! {

enum RootSelection {
    Single(BitSelectionShape),
    Nested(Vec<BitSelectionShape>, usize),
}

impl<'t, 'p, 'a> MixedUseAliases<'t, 'p, 'a> {
    #[verifier::opaque]
    pub(super) closed spec fn mixed_root_selection_matches(
        &self, source: &ProjectSource, parsed: &NamedBuildCircuit, root: usize,
        input: Option<SignalType>, expected: Option<TypedPort>,
        selected: Option<Result<Option<SignalType>, MixedFuncTypeError>>,
    ) -> bool {
        let forms = parsed.syntax.forms@;
        let single = exists|shape: BitSelectionShape| #[trigger] named_selection_matches(source.text, forms, root as int, shape);
        let nested = exists|shapes: Seq<BitSelectionShape>, leaf: usize|
            #[trigger] nested_named_selection_matches(source.text, forms, root, shapes, leaf);
        match selected {
            None => !single && !nested,
            Some(result) => exists|checked: Result<Option<SignalType>, FuncSignalTypeError>| {
                &&& #[trigger] selection_result(checked) == Some(result)
                &&& ((exists|shape: BitSelectionShape| #[trigger] named_selection_matches(source.text, forms, root as int, shape)
                    && selection_type_matches(source, forms, root, shape, input, expected, checked))
                    || (!single && exists|steps: Seq<BitSelectionShape>, leaf: usize|
                        #[trigger] nested_named_selection_matches(source.text, forms, root, steps, leaf)
                        && nested_selection_type_matches(source, forms, root, steps, leaf, input, expected, checked)))
            },
        }
    }

    #[verifier::spinoff_prover]
    pub(super) fn check_mixed_root_selection(
        &self, _caller: Ghost<(usize, usize, u64)>, entry: usize, source: &'p ProjectSource<'a>,
        parsed: &NamedBuildCircuit<'a>, scope: &FuncWiring<'p, 'a>, prior: &[Option<SignalType<'p, 'a>>],
        index: usize, expected: Option<&TypedPort<'p, 'a>>,
    ) -> (selected: Option<Result<Option<SignalType<'p, 'a>>, MixedFuncTypeError<'p, 'a>>>)
        requires
            ({
                let (file, item, limit) = _caller@;
                let project = self.targets_model().project_model();
                &&& entry == item
                &&& self.mixed_func_wiring_matches(file, entry, limit, Ok(FuncWiringResult::Checked(*scope)))
                &&& *source == project.sources_model()[file as int]
                &&& *parsed == project.indexes_model()[file as int]->Circuit_0
            }),
            crate::project::parsed_circuit_matches(*source, *parsed),
            entry < parsed.syntax.entries@.len(), expected_output_context(source, parsed, entry as int, scope.drivers),
            index == prior@.len() < scope.drivers.definitions@.len(), mixed_signal_origins(prior@),
        ensures ({
            let row = parsed.definitions@[scope.drivers.definitions@[index as int].definition as int];
            self.mixed_root_selection_matches(source, parsed, row.expression.start,
                selection_input(parsed, entry, row, scope, prior@),
                match expected { Some(port) => Some(*port), None => None }, selected)
        }),
        selected matches Some(Ok(Some(ty))) ==> location_in_source(ty.origin),
    {
        let driver = &scope.drivers.definitions[index];
        let row = &parsed.definitions[driver.definition];
        let root = row.expression.start;
        let forms = parsed.syntax.forms.as_slice();
        proof {
            reveal(MixedUseAliases::mixed_root_selection_matches);
            parsed_index_evidence(*source, *parsed);
            build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, driver.definition as int);
        }
        let selected = if let Some(shape) = named_selection(source.text, forms, root) {
            proof {
                build_selection_input_position(source.text, &parsed.build_model(), entry as int, driver.definition as int, shape);
            }
            RootSelection::Single(shape)
        } else if let Some((steps, leaf)) = nested_named_selection(source.text, forms, root) {
            proof {
                reveal(nested_named_selection_matches);
                build_selection_chain_signal(source.text, &parsed.build_model(), entry as int, driver.definition as int, steps@, leaf);
            }
            RootSelection::Nested(steps, leaf)
        } else {
            return None;
        };
        proof {
            let (file, _, limit) = _caller@;
            self.mixed_wiring_signal_driver(file, entry, limit, *scope, driver.definition, row.signals.start);
        }
        let position = row.signals.start - parsed.entry_ranges[entry].signals.start;
        let bound = &scope.signals[position];
        proof {
            if let OutputDriver::Definition(previous) = bound.driver {
                assert(previous < index) by {
                    if index < previous {
                        assert(scope.drivers.definitions@[index as int].definition
                            <= scope.drivers.definitions@[previous as int].definition);
                    }
                };
            }
        }
        let input = inherit_type(scope, prior, bound.driver);
        assert(input == selection_input(parsed, entry, *row, scope, prior@));
        let checked = match selected {
            RootSelection::Single(shape) => check_selection_type(source, forms, root, &shape, input, expected),
            RootSelection::Nested(steps, leaf) =>
                match check_nested_selection_type(source, forms, root, steps.as_slice(), leaf, input, expected) {
                    Ok(Some((ty, _))) => Ok(Some(ty)),
                    Ok(None) => Ok(None),
                    Err(error) => Err(error),
                },
        };
        let ghost original = checked;
        let result = selection_diagnostic(checked);
        assert(selection_result(original) == Some(result));
        Some(result)
    }
}

pub(super) open spec fn selection_input<'p, 'a>(
    parsed: &NamedBuildCircuit, entry: usize, row: BuildDefinition, scope: &FuncWiring<'p, 'a>,
    prior: Seq<Option<SignalType<'p, 'a>>>,
) -> Option<SignalType<'p, 'a>> {
    let first = parsed.entry_ranges@[entry as int].signals.start;
    if first <= row.signals.start < first + scope.signals@.len() && row.signals.start < row.signals.end {
        signal_type_at(scope, prior, scope.signals@[row.signals.start - first].driver)
    } else { None }
}

spec fn selection_result<'p, 'a>(checked: Result<Option<SignalType<'p, 'a>>, FuncSignalTypeError<'p, 'a>>)
    -> Option<Result<Option<SignalType<'p, 'a>>, MixedFuncTypeError<'p, 'a>>> {
    match checked {
        Ok(ty) => Some(Ok(ty)),
        Err(FuncSignalTypeError::Signal(error)) => Some(Err(MixedFuncTypeError::Signal(error))),
        Err(FuncSignalTypeError::SelectionInputType { reference, actual }) =>
            Some(Err(MixedFuncTypeError::SelectionInputType { reference, actual })),
        Err(FuncSignalTypeError::SelectionArgument(error)) => Some(Err(MixedFuncTypeError::SelectionArgument(error))),
        _ => None,
    }
}

fn selection_diagnostic<'p, 'a>(checked: Result<Option<SignalType<'p, 'a>>, FuncSignalTypeError<'p, 'a>>)
    -> (result: Result<Option<SignalType<'p, 'a>>, MixedFuncTypeError<'p, 'a>>)
    requires selection_result(checked).is_some(),
    ensures selection_result(checked) == Some(result),
{
    match checked {
        Ok(ty) => Ok(ty),
        Err(FuncSignalTypeError::Signal(error)) => Err(MixedFuncTypeError::Signal(error)),
        Err(FuncSignalTypeError::SelectionInputType { reference, actual }) =>
            Err(MixedFuncTypeError::SelectionInputType { reference, actual }),
        Err(FuncSignalTypeError::SelectionArgument(error)) => Err(MixedFuncTypeError::SelectionArgument(error)),
        _ => unreachable!(),
    }
}

}
