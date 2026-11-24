//! ラッチと RAM の宣言を呼び出しに使う型付き署名にする。

use super::{DefinitionReferenceReason, ResolvedPortType, UseAliases};
#[cfg(verus_only)]
use super::{DefinitionBinding, PortContext};
use crate::project::{DeclaredPortType, LocatedName, PortWidthError, StorageDeclaration, check_storage_declaration};
#[cfg(verus_only)]
use crate::project::{location_in_source, storage_declaration_result};
#[cfg(verus_only)]
use crate::project::storage_declarations::{checked_storage_declaration, storage_declaration_presence, storage_entry};
use vstd::prelude::*;

verus! {

/// 状態素子のポート型。許可入力はどちらも1ビットで、出力はデータ入力と同じ型になる。
#[derive(Debug)]
pub enum StorageSignature<'p, 'a> {
    /// ラッチのデータ入力と保持出力。
    Latch {
        /// データのビット幅。
        width: u64,
        /// 幅を宣言した字句の範囲。
        annotation: LocatedName<'p, 'a>,
    },
    /// RAM のアドレス入力と、書き込みデータおよび読み出し出力。
    Memory {
        /// アドレス入力のビット幅。
        address: u64,
        /// アドレス幅を宣言した字句の範囲。
        address_annotation: LocatedName<'p, 'a>,
        /// 書き込みデータと読み出し出力に共通の解決済み型。
        data: ResolvedPortType<'p, 'a>,
        /// データ型を宣言した幅または型名の字句の範囲。
        data_annotation: LocatedName<'p, 'a>,
    },
}

/// 呼び出された状態素子の幅または型名の診断。
#[derive(Debug)]
pub enum StorageSignatureError<'p, 'a> {
    /// 幅の検査で最初に見つかった違反。
    Width(PortWidthError<'p, 'a>),
    /// RAM のデータ型に指定した構造体名の解決に失敗した。
    TypeReference {
        /// RAM の宣言に書いた型名の範囲。
        reference: LocatedName<'p, 'a>,
        /// 名前解決の結果と、関連する宣言の位置。
        reason: DefinitionReferenceReason<'p, 'a>,
    },
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn storage_signature_after_widths(
        &self, file: usize, entry: usize, declared: StorageDeclaration,
        result: Result<Option<StorageSignature>, StorageSignatureError>,
    ) -> bool {
        match declared {
            StorageDeclaration::Latch { width, annotation } =>
                result == Ok(Some(StorageSignature::Latch { width, annotation })),
            StorageDeclaration::Memory { address, address_annotation, data: declared_data, data_annotation } => {
                match result {
                    Ok(Some(StorageSignature::Memory { address: found, address_annotation: address_at, data, data_annotation: data_at })) =>
                        found == address && address_at == address_annotation && data_at == data_annotation
                        && match (declared_data, data) {
                            (DeclaredPortType::Bits(width), ResolvedPortType::Bits(actual)) => actual == width,
                            (DeclaredPortType::Named { form: atom }, ResolvedPortType::Struct { source, form }) =>
                                self.declared_port_type(data) && exists|context: PortContext|
                                    #[trigger] self.port_context_evidence(file, entry, &context)
                                        && #[trigger] self.port_binding_evidence(&context, atom, Ok(DefinitionBinding::Declaration { source, form })),
                            _ => false,
                        },
                    Err(StorageSignatureError::TypeReference { reference, reason }) =>
                        reference == data_annotation && (declared_data matches DeclaredPortType::Named { form }
                        && exists|context: PortContext| #[trigger] self.port_context_evidence(file, entry, &context)
                            && #[trigger] self.port_binding_evidence(&context, form, Err(reason))),
                    _ => false,
                }
            },
        }
    }

    /// 幅の検査と、状態素子の宣言位置でのデータ型名の解決を対応付ける。
    pub closed spec fn storage_signature_result(
        &self, file: usize, entry: usize, limit: u64,
        result: Result<Option<StorageSignature>, StorageSignatureError>,
    ) -> bool {
        let project = &self.targets.project_model();
        match result {
            Ok(None) => storage_declaration_result(project, file, entry, limit, Ok(None)),
            Err(StorageSignatureError::Width(error)) => storage_declaration_result(project, file, entry, limit, Err(error)),
            _ => exists|declared: StorageDeclaration|
                #[trigger] storage_declaration_result(project, file, entry, limit, Ok(Some(declared)))
                    && self.storage_signature_after_widths(file, entry, declared, result),
        }
    }

    pub(in crate::project::use_aliases) proof fn storage_signature_present(&self, file: usize, entry: usize, limit: u64)
        requires
            storage_entry(&self.targets.project_model(), file, entry),
        ensures !self.storage_signature_result(file, entry, limit, Ok(None)),
    {
        let project = &self.targets.project_model();
        if self.storage_signature_result(file, entry, limit, Ok(None)) {
            storage_declaration_presence(project, file, entry, limit, Ok(None));
        }
    }

    pub(in crate::project::use_aliases) proof fn storage_signature_sites(
        &self, file: usize, entry: usize, limit: u64, signature: StorageSignature,
    )
        requires self.storage_signature_result(file, entry, limit, Ok(Some(signature))),
        ensures match signature {
            StorageSignature::Latch { annotation, width } => location_in_source(annotation) && 0 < width <= limit,
            StorageSignature::Memory { address, address_annotation, data, data_annotation } =>
                location_in_source(address_annotation) && location_in_source(data_annotation)
                    && 0 < address <= limit && self.declared_port_type(data)
                    && (data matches ResolvedPortType::Bits(width) ==> 0 < width <= limit),
        },
    {
        let project = &self.targets.project_model();
        let declaration = choose|declared: StorageDeclaration|
            #[trigger] storage_declaration_result(project, file, entry, limit, Ok(Some(declared)))
                && self.storage_signature_after_widths(file, entry, declared, Ok(Some(signature)));
        checked_storage_declaration(project, file, entry, limit, declaration);
    }

    /// ラッチまたは RAM のポート署名を解決する。
    ///
    /// `file` はソース一覧、`entry` はそのファイルの厳格索引の添字。範囲外や他の宣言は
    /// `Ok(None)` を返す。RAM のデータ型に書いた名前は RAM の宣言位置で解決する。
    ///
    /// # Errors
    ///
    /// 明示幅を検査した後、RAM のデータ型名を解決し、最初の違反を返す。
    pub fn resolve_storage_signature(
        &self, file: usize, entry: usize, limit: u64,
    ) -> (result: Result<Option<StorageSignature<'p, 'a>>, StorageSignatureError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.storage_signature_result(file, entry, limit, result),
    {
        let project = self.targets.project();
        let declared = match check_storage_declaration(project, file, entry, limit) {
            Ok(Some(declaration)) => declaration,
            Ok(None) => return Ok(None),
            Err(error) => return Err(StorageSignatureError::Width(error)),
        };
        proof { checked_storage_declaration(project, file, entry, limit, declared); }
        let signature = match declared {
            StorageDeclaration::Latch { width, annotation } => StorageSignature::Latch { width, annotation },
            StorageDeclaration::Memory { address, address_annotation, data, data_annotation } => {
                let data = match data {
                    DeclaredPortType::Bits(width) => ResolvedPortType::Bits(width),
                    DeclaredPortType::Named { form } => {
                        let context = self.port_context(file, entry);
                        match self.resolve_port_structure(&context, form) {
                            Ok((ty, _)) => ty,
                            Err((reference, reason)) => {
                                let error = Err(StorageSignatureError::TypeReference { reference, reason });
                                assert(self.storage_signature_after_widths(file, entry, declared, error));
                                return error;
                            },
                        }
                    },
                };
                StorageSignature::Memory { address, address_annotation, data, data_annotation }
            },
        };
        Ok(Some(signature))
    }
}

} // verus!
