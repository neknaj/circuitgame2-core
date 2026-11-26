//! NOR 候補の名前を、元の回路本体またはマクロ定義側のスコープで解決する。

use crate::ncg2m::call_evaluation::macro_syntax::MacroSyntaxOrigin;
use crate::project::{
    LocatedName, MixedFuncCalleeError, MixedUseAliases, ProjectDeclaration, ProjectDeclarationKind, ProjectSourceIndex,
    source_indexes::DefnScope,
};
use crate::project::use_aliases::find_namespace;
use crate::syntax::circuit::Head;
#[cfg(verus_only)]
use crate::syntax::{AtomKind, bare_atom_kind};
#[cfg(verus_only)]
use crate::project::{
    source_indexes::project_source_index_evidence, use_aliases::mixed_function::scoped_circuit_name_matches,
};
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
use vstd::prelude::*;

verus! {

// circuit の entry と NCG2M の item は別の索引を指す。
#[derive(Clone, Copy, Debug)]
pub(super) enum CalleeScope {
    Circuit { file: usize, entry: usize },
    Template { file: usize, item: usize },
}

impl CalleeScope {
    pub(super) fn from_event(origin: MacroSyntaxOrigin) -> (scope: Self)
        ensures scope == event_callee_scope(origin),
    {
        match origin {
            MacroSyntaxOrigin::Template(call) => {
                let declaration = &call.definition().declaration;
                Self::Template { file: declaration.file, item: declaration.item }
            },
            MacroSyntaxOrigin::Argument(argument) => {
                let caller = argument.scope();
                Self::Circuit { file: caller.file, entry: caller.entry }
            },
        }
    }
}

pub(super) open spec fn event_callee_scope(origin: MacroSyntaxOrigin) -> CalleeScope {
    match origin {
        MacroSyntaxOrigin::Template(call) => {
            let declaration = call.definition_model().declaration;
            CalleeScope::Template { file: declaration.file, item: declaration.item }
        },
        MacroSyntaxOrigin::Argument(argument) => {
            let caller = argument.scope_model();
            CalleeScope::Circuit { file: caller.file, entry: caller.entry }
        },
    }
}

#[derive(Debug)]
pub(super) enum NorScopeError<'p, 'a> {
    /// 名前を解決するための宣言スコープを参照できない。
    MissingScope(LocatedName<'p, 'a>),
    /// 同じ綴りが利用位置でユーザー定義の関数に解決された。
    Function {
        callee: LocatedName<'p, 'a>,
        declaration: ProjectDeclaration<'p, 'a>,
    },
    /// 同じ綴りが別の宣言種別に解決されるなど、既存の名前解決に失敗した。
    Name {
        callee: LocatedName<'p, 'a>,
        error: MixedFuncCalleeError<'p, 'a>,
    },
}

spec fn selected_nor_scope(aliases: &MixedUseAliases, at: CalleeScope, selected: Option<(usize, DefnScope)>) -> bool {
    let project = aliases.targets_model().project_model();
    match at {
        CalleeScope::Template { file, item } => {
            let scope = match selected { Some((_, scope)) => Some(scope), None => None };
            project.defmacro_scope_matches(file, item, scope) && (selected matches Some((i, _)) ==> i == file)
        },
        CalleeScope::Circuit { file, entry } => {
            let indexes = project.indexes_model();
            if file < indexes.len() && (indexes[file as int] matches ProjectSourceIndex::Circuit(parsed)
                && entry < parsed.syntax.entries@.len()) {
                let parsed = indexes[file as int]->Circuit_0;
                let block = parsed.syntax.entries@[entry as int].namespace;
                selected matches Some((i, scope)) && i == file && scope.block == block
                    && match block {
                        None => scope.namespace.is_none(),
                        Some(block) => scope.namespace.is_some() && exists|i: int| 0 <= i < parsed.names@.len()
                            && #[trigger] crate::project::use_aliases::is_namespace_block(parsed.names@[i], block)
                            && scope.namespace == Some(parsed.names@[i].name.word),
                    }
            } else {
                selected.is_none()
            }
        },
    }
}

fn read_nor_scope<'t, 'p, 'a>(aliases: &MixedUseAliases<'t, 'p, 'a>, at: CalleeScope) -> (selected: Option<(usize, DefnScope<'a>)>)
    ensures selected_nor_scope(aliases, at, selected),
{
    let project = aliases.targets().project();
    match at {
        CalleeScope::Template { file, item } => match project.defmacro_scope(file, item) {
            Some(scope) => Some((file, scope)),
            None => None,
        },
        CalleeScope::Circuit { file, entry } => {
            let Some(index) = project.indexes().get(file) else { return None; };
            let ProjectSourceIndex::Circuit(parsed) = index else { return None; };
            let Some(row) = parsed.syntax.entries.get(entry) else { return None; };
            let block = row.namespace;
            if let Some(block) = block {
                proof {
                    let source = &project.sources_model()[file as int];
                    project_source_index_evidence(*source, *index);
                    crate::project::circuits::parsed_index_evidence(*source, *parsed);
                    crate::syntax::circuit::indexed_entry_evidence(source.text, parsed.syntax.forms@, parsed.syntax.entries@, entry as int);
                    crate::syntax::circuit::namespace_name_evidence(source.text, parsed.syntax.forms@,
                        parsed.syntax.entries@, parsed.names@, row.form as int, block);
                }
                let namespace = find_namespace(parsed, block);
                proof {
                    let i = choose|i: int| 0 <= i < parsed.names@.len()
                        && #[trigger] crate::project::use_aliases::is_namespace_block(parsed.names@[i], block);
                    assert(crate::project::use_aliases::is_namespace_block(parsed.names@[i], block));
                }
                Some((file, DefnScope { block: Some(block), namespace }))
            } else {
                Some((file, DefnScope { block: None, namespace: None }))
            }
        },
    }
}

spec fn resolved_nor_matches(
    aliases: &MixedUseAliases, at: CalleeScope, file: usize, scope: DefnScope, spelling: &str,
    callee: LocatedName, outcome: Result<(), NorScopeError>,
) -> bool {
    &&& selected_nor_scope(aliases, at, Some((file, scope)))
    &&& spelling.spec_bytes() == "nor".spec_bytes()
    &&& match outcome {
        Ok(()) => scoped_circuit_name_matches(aliases, file, scope, spelling, ProjectDeclarationKind::Circuit(Head::Func), Ok(None)),
        Err(NorScopeError::Function { callee: site, declaration }) => site == callee
            && scoped_circuit_name_matches(aliases, file, scope, spelling, ProjectDeclarationKind::Circuit(Head::Func), Ok(Some(declaration))),
        Err(NorScopeError::Name { callee: site, error }) => site == callee
            && scoped_circuit_name_matches(aliases, file, scope, spelling, ProjectDeclarationKind::Circuit(Head::Func), Err(error)),
        _ => false,
    }
}

pub(super) closed spec fn scoped_nor_matches(
    aliases: &MixedUseAliases, at: CalleeScope, callee: LocatedName, outcome: Result<(), NorScopeError>,
) -> bool {
    match outcome {
        Err(NorScopeError::MissingScope(site)) => site == callee && selected_nor_scope(aliases, at, None),
        _ => exists|file: usize, scope: DefnScope, spelling: &str|
            #[trigger] resolved_nor_matches(aliases, at, file, scope, spelling, callee, outcome),
    }
}

proof fn nor_scope_witness(
    aliases: &MixedUseAliases, at: CalleeScope, file: usize, scope: DefnScope, spelling: &str,
    callee: LocatedName, outcome: Result<(), NorScopeError>,
)
    requires resolved_nor_matches(aliases, at, file, scope, spelling, callee, outcome),
    ensures scoped_nor_matches(aliases, at, callee, outcome),
{}

pub(super) fn check_scoped_nor<'p, 'a>(
    aliases: &MixedUseAliases<'_, 'p, 'a>, scope: CalleeScope, spelling: &str, callee: LocatedName<'p, 'a>,
) -> (outcome: Result<(), NorScopeError<'p, 'a>>)
    requires spelling.spec_bytes() == "nor".spec_bytes(), bare_atom_kind(spelling.spec_bytes()) == Some(AtomKind::Name),
    ensures scoped_nor_matches(aliases, scope, callee, outcome),
{
    let Some((file, found)) = read_nor_scope(aliases, scope) else { return Err(NorScopeError::MissingScope(callee)); };
    let ghost original = callee;
    let result = match aliases.resolve_scoped_circuit_name(file, found, spelling, ProjectDeclarationKind::Circuit(Head::Func)) {
        Ok(None) => Ok(()),
        Ok(Some(declaration)) => Err(NorScopeError::Function { callee, declaration }),
        Err(error) => Err(NorScopeError::Name { callee, error }),
    };
    proof { nor_scope_witness(aliases, scope, file, found, spelling, original, result); }
    result
}

} // verus!
