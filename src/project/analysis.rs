//! 厳格構文木を使って基底、別名、定義の参照を検査する。

mod definition_lookup;

use super::use_aliases::own_conflict;
#[cfg(verus_only)]
use super::use_aliases::owned_conflict_matches;
use super::{
    AliasDisposition, CircuitBasisError, CircuitProject, DefinitionBatchError,
    FunctionCallSite, FunctionExpansionOrder, IndexedDefinitionBinding, LocatedName, OwnedUseAliasConflict, UseAliases, UseTargetError, UseTargets,
    check_use_aliases, index_use_targets, validate_circuit_basis,
};
#[cfg(verus_only)]
use super::{
    UseAliasConflict, alias_conflict_evidence, basis_result_evidence,
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

/// 基底と `use` の参照先を検査し、別名と定義参照の検査に使う状態。
pub struct PreparedDefinitionAnalysis<'p, 'a> {
    basis: Option<LocatedName<'p, 'a>>,
    targets: UseTargets<'p, 'a>,
}

/// 別名の索引と、同じ索引で解決した定義参照。
pub struct CheckedDefinitionAnalysis<'t, 'p, 'a> {
    aliases: UseAliases<'t, 'p, 'a>,
    definitions: Vec<IndexedDefinitionBinding<'p, 'a>>,
}

/// 準備したプロジェクトの別名または定義参照に見つかった最初の違反。
#[derive(Debug)]
pub enum PreparedDefinitionError<'t, 'p, 'a> {
    /// 別名が他の束縛と衝突した。
    Alias(OwnedUseAliasConflict<'p, 'a>),
    /// `def` の参照先を解決できないか、用途に合わない。
    Definition {
        /// 最初に違反した参照の診断。
        error: DefinitionBatchError<'p, 'a>,
        /// 参照を調べる前に確定した束縛と警告。
        aliases: UseAliases<'t, 'p, 'a>,
    },
}

impl<'t, 'p, 'a> CheckedDefinitionAnalysis<'t, 'p, 'a> {
    #[verifier::type_invariant]
    spec fn valid(self) -> bool {
        self.aliases.can_resolve() && self.aliases.definition_bindings_match(self.definitions@)
    }

    /// この検査で使った別名の索引を表す。
    pub closed spec fn aliases_model(&self) -> UseAliases<'t, 'p, 'a> {
        self.aliases
    }

    /// この検査で解決した定義参照の列を表す。
    pub closed spec fn definitions_model(&self) -> Seq<IndexedDefinitionBinding<'p, 'a>> {
        self.definitions@
    }

    /// 別名の検索と重複警告に使う索引を返す。
    pub fn aliases(&self) -> (aliases: &UseAliases<'t, 'p, 'a>)
        ensures *aliases == self.aliases_model(), aliases.can_resolve(),
    {
        proof { use_type_invariant(self); }
        &self.aliases
    }

    /// 検査時に解決した参照を使い、関数の展開順を求める。
    ///
    /// # Errors
    ///
    /// 関数呼び出しが循環する場合は、閉路を構成する呼び出し先名の元ソース範囲を返す。
    pub fn function_expansion_order(&self)
        -> (result: Result<FunctionExpansionOrder<'p, 'a>, Vec<FunctionCallSite<'p, 'a>>>)
        ensures self.aliases_model().function_expansion_order_matches(self.definitions_model(), result),
    {
        proof { use_type_invariant(self); }
        self.aliases.function_expansion_order(self.definitions.as_slice())
    }
}

impl<'p, 'a> PreparedDefinitionAnalysis<'p, 'a> {
    #[verifier::type_invariant]
    spec fn valid(self) -> bool {
        self.targets.covers_project() && self.targets.exports_model().declarations_model().well_formed()
    }

    /// 解決済みの `use` と共有宣言を返す。
    pub fn targets(&self) -> (targets: &UseTargets<'p, 'a>)
        ensures *targets == self.targets_model(),
    {
        &self.targets
    }

    /// 検査した基底宣言の元ソース範囲を表す。
    pub closed spec fn basis_model(&self) -> Option<LocatedName<'p, 'a>> {
        self.basis
    }

    /// 検査で共有する `use` と宣言の索引を表す。
    pub closed spec fn targets_model(&self) -> UseTargets<'p, 'a> {
        self.targets
    }

    /// 別名と定義参照の検査結果を、準備したプロジェクトと照合する。
    pub closed spec fn resolution_matches(
        &self, result: Result<CheckedDefinitionAnalysis, PreparedDefinitionError>,
    ) -> bool {
        match result {
            Ok(checked) => use_aliases_match(&self.targets, checked.aliases)
                && checked.aliases.can_resolve()
                && checked.aliases.definition_bindings_match(checked.definitions@),
            Err(PreparedDefinitionError::Alias(error)) =>
                exists|conflict: UseAliasConflict| #![trigger owned_conflict_matches(conflict, error)]
                    alias_conflict_evidence(&self.targets, conflict) && owned_conflict_matches(conflict, error),
            Err(PreparedDefinitionError::Definition { error, aliases }) =>
                use_aliases_match(&self.targets, aliases) && aliases.can_resolve()
                    && aliases.definition_batch_error_evidence(error),
        }
    }

    /// 別名を検査し、その索引で定義参照を元ソース順に解決する。
    ///
    /// # Errors
    ///
    /// 最初の別名の衝突または解決できない定義参照を返す。定義参照の失敗には別名の警告も付く。
    pub fn resolve(&self)
        -> (result: Result<CheckedDefinitionAnalysis<'_, 'p, 'a>, PreparedDefinitionError<'_, 'p, 'a>>)
        ensures self.resolution_matches(result),
    {
        proof { use_type_invariant(self); }
        let aliases = match check_use_aliases(&self.targets) {
            Ok(aliases) => aliases,
            Err(conflict) => {
                let error = own_conflict(conflict);
                return Err(PreparedDefinitionError::Alias(error));
            },
        };
        match aliases.resolve_definitions() {
            Ok(definitions) => Ok(CheckedDefinitionAnalysis { aliases, definitions }),
            Err(error) => Err(PreparedDefinitionError::Definition { error, aliases }),
        }
    }
}

/// 基底宣言、共有宣言、公開指定、`use` の参照先を検査する。
///
/// # Errors
///
/// 最初に違反が見つかった段階の診断を返す。
pub fn prepare_definition_analysis<'p, 'a>(project: &'p CircuitProject<'a>)
    -> (result: Result<PreparedDefinitionAnalysis<'p, 'a>, DefinitionAnalysisError<'p, 'a>>)
    requires project.has_parsed_sources(),
    ensures match result {
        Ok(prepared) => circuit_basis_valid(project)
            && basis_result_evidence(project, Ok(prepared.basis_model()))
            && use_targets_match(project, prepared.targets_model())
            && prepared.targets_model().covers_project()
            && prepared.targets_model().exports_model().declarations_model().well_formed(),
        Err(error) => (error is Basis || error is UseTarget) && definition_analysis_evidence(project, Err(error)),
    },
{
    let basis = match validate_circuit_basis(project) {
        Ok(basis) => basis,
        Err(error) => return Err(DefinitionAnalysisError::Basis(error)),
    };
    let targets = match index_use_targets(project) {
        Ok(targets) => targets,
        Err(error) => return Err(DefinitionAnalysisError::UseTarget(error)),
    };
    Ok(PreparedDefinitionAnalysis { basis, targets })
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
    let prepared = match prepare_definition_analysis(project) {
        Ok(prepared) => prepared,
        Err(error) => return Err(error),
    };
    assert(circuit_basis_valid(project));
    let resolved = prepared.resolve();
    proof { reveal(PreparedDefinitionAnalysis::resolution_matches); }
    let (aliases, definitions) = match resolved {
        Ok(checked) => (checked.aliases, Ok(checked.definitions)),
        Err(PreparedDefinitionError::Alias(error)) => return Err(DefinitionAnalysisError::Alias(error)),
        Err(PreparedDefinitionError::Definition { error, aliases }) => (aliases, Err(error)),
    };
    let ghost evidence = aliases;
    let dispositions = aliases.into_dispositions();
    let report = UseAliasReport { targets: prepared.targets, dispositions };
    let basis = prepared.basis;
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
