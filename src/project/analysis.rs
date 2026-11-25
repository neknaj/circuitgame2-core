//! 厳格構文木を使って基底、別名、定義の参照を検査する。

mod definition_lookup;

use super::use_aliases::own_conflict;
#[cfg(verus_only)]
use super::use_aliases::owned_conflict_matches;
use super::{
    AliasDisposition, CircuitBasisError, CircuitProject, DefinitionBatchError,
    IndexedDefinitionBinding, LocatedName, OwnedUseAliasConflict, UseTargetError, UseTargets,
    check_use_aliases, index_use_targets, validate_circuit_basis,
};
#[cfg(verus_only)]
use super::{
    UseAliasConflict, UseAliases, alias_conflict_evidence, basis_result_evidence,
    circuit_basis_valid, use_aliases_match, use_target_error_evidence, use_targets_match,
};
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// 別名の束縛と重複警告を、元の指定と対応させた検査結果。
#[derive(Debug)]
pub struct UseAliasReport<'p, 'a> {
    /// 指定位置と対象を含む解決済みの `use` 一覧。
    pub targets: UseTargets<'p, 'a>,
    /// `targets.directives()` と同じ順に並ぶ束縛または警告。警告は最初の指定を指す。
    pub dispositions: Vec<AliasDisposition>,
}

/// 回路ソース集合の基底と、別名および定義参照の検査結果。
#[derive(Debug)]
pub struct DefinitionAnalysis<'p, 'a> {
    /// 基底指定の元ソース範囲。回路ソースが一件もなければ `None`。
    pub basis: Option<LocatedName<'p, 'a>>,
    /// 別名の束縛と重複警告。
    pub aliases: UseAliasReport<'p, 'a>,
    /// 元ソース順に並ぶ `def` の解決済み参照。
    pub definitions: Vec<IndexedDefinitionBinding<'p, 'a>>,
}

/// 構文解析後の名前検査で、最初に失敗した段階の診断。
#[derive(Debug)]
pub enum DefinitionAnalysisError<'p, 'a> {
    /// ソース集合全体の基底指定の違反。
    Basis(CircuitBasisError<'p, 'a>),
    /// 共有宣言、公開指定、または `use` の参照先の違反。
    UseTarget(UseTargetError<'p, 'a>),
    /// 別名が他の束縛と衝突した。
    Alias(OwnedUseAliasConflict<'p, 'a>),
    /// `def` の参照先を解決できないか、用途に合わない。
    Definition {
        /// 最初に違反した参照の診断。
        error: DefinitionBatchError<'p, 'a>,
        /// 定義の検査前に確定した束縛と警告。
        aliases: UseAliasReport<'p, 'a>,
    },
}

spec fn alias_report_matches(project: &CircuitProject, report: UseAliasReport, aliases: UseAliases) -> bool {
    &&& use_targets_match(project, report.targets)
    &&& use_aliases_match(&report.targets, aliases)
    &&& aliases.can_resolve()
    &&& report.dispositions@ == aliases.dispositions_model()
}

/// 検査結果や診断がそれぞれの段階の規則と出現順に対応することを表す。
pub closed spec fn definition_analysis_evidence(
    project: &CircuitProject, result: Result<DefinitionAnalysis, DefinitionAnalysisError>,
) -> bool {
    match result {
        Ok(analysis) => basis_result_evidence(project, Ok(analysis.basis))
            && (exists|aliases: UseAliases| #[trigger] alias_report_matches(project, analysis.aliases, aliases)
                && aliases.definition_bindings_match(analysis.definitions@)),
        Err(DefinitionAnalysisError::Basis(error)) => basis_result_evidence(project, Err(error)),
        Err(DefinitionAnalysisError::UseTarget(error)) =>
            circuit_basis_valid(project) && use_target_error_evidence(project, error),
        Err(DefinitionAnalysisError::Alias(error)) => circuit_basis_valid(project)
            && (exists|targets: UseTargets, conflict: UseAliasConflict|
                #![trigger use_targets_match(project, targets), owned_conflict_matches(conflict, error)]
                use_targets_match(project, targets) && alias_conflict_evidence(&targets, conflict)
                    && owned_conflict_matches(conflict, error)),
        Err(DefinitionAnalysisError::Definition { error, aliases: report }) => circuit_basis_valid(project)
            && (exists|aliases: UseAliases| #[trigger] alias_report_matches(project, report, aliases)
                && aliases.definition_batch_error_evidence(error)),
    }
}

/// 構文解析済みのソースから基底と `def` の参照を検査する。
///
/// 基底、共有宣言と公開指定、`use` の参照先、別名衝突、定義参照の順で検査する。
/// 重複する別名は警告として保持する。型の幅、結線、マクロ展開は後続の検査で扱う。
///
/// # Errors
///
/// 最初に失敗した段階の違反を返す。定義参照で失敗した場合は、確定済みの別名警告も返す。
pub fn analyze_definitions<'p, 'a>(project: &'p CircuitProject<'a>)
    -> (result: Result<DefinitionAnalysis<'p, 'a>, DefinitionAnalysisError<'p, 'a>>)
    requires project.has_parsed_sources(),
    ensures definition_analysis_evidence(project, result),
{
    let basis = match validate_circuit_basis(project) {
        Ok(basis) => basis,
        Err(error) => return Err(DefinitionAnalysisError::Basis(error)),
    };
    assert(basis_result_evidence(project, Ok(basis)));
    assert(circuit_basis_valid(project));
    let targets = match index_use_targets(project) {
        Ok(targets) => targets,
        Err(error) => return Err(DefinitionAnalysisError::UseTarget(error)),
    };
    let aliases = match check_use_aliases(&targets) {
        Ok(aliases) => aliases,
        Err(conflict) => {
            let error = own_conflict(conflict);
            return Err(DefinitionAnalysisError::Alias(error));
        },
    };
    let definitions = aliases.resolve_definitions();
    let ghost evidence = aliases;
    let dispositions = aliases.into_dispositions();
    let report = UseAliasReport { targets, dispositions };
    assert(alias_report_matches(project, report, evidence));
    match definitions {
        Ok(definitions) => {
            assert(evidence.definition_bindings_match(definitions@));
            assert(exists|aliases: UseAliases| #[trigger] alias_report_matches(project, report, aliases)
                && aliases.definition_bindings_match(definitions@));
            let result = Ok(DefinitionAnalysis { basis, aliases: report, definitions });
            assert(definition_analysis_evidence(project, result)) by {
                reveal(definition_analysis_evidence);
                assert(result->Ok_0.aliases == report);
                assert(result->Ok_0.definitions@ == definitions@);
            }
            result
        },
        Err(error) => {
            assert(evidence.definition_batch_error_evidence(error));
            assert(exists|aliases: UseAliases| #[trigger] alias_report_matches(project, report, aliases)
                && aliases.definition_batch_error_evidence(error));
            let result = Err(DefinitionAnalysisError::Definition { error, aliases: report });
            assert(definition_analysis_evidence(project, result)) by {
                reveal(definition_analysis_evidence);
                assert(result->Err_0->Definition_aliases == report);
                assert(result->Err_0->Definition_error == error);
            }
            result
        },
    }
}

} // verus!
