//! 一回の型検査で解決した呼び出し先の署名を保持する。

use super::{MixedTypedSignatureError, MixedUseAliases, TypedRoutineSignature, TypedSignatureError, UseAliases};
#[cfg(verus_only)]
use crate::project::mixed_use_targets_match;
use alloc::collections::BTreeMap;
#[cfg(verus_only)]
use vstd::laws_cmp::obeys_cmp;
use vstd::prelude::*;

verus! {

type RoutinePosition = (usize, usize);

pub(super) struct SignatureCache<'p, 'a> {
    signatures: BTreeMap<RoutinePosition, TypedRoutineSignature<'p, 'a>>,
}

impl<'p, 'a> SignatureCache<'p, 'a> {
    pub(super) closed spec fn signatures(&self) -> Map<RoutinePosition, TypedRoutineSignature<'p, 'a>> {
        self.signatures@
    }

    /// 各署名が、同じ名前解決環境と幅上限で検査されたことを表す。
    pub(super) open spec fn matches(&self, aliases: &UseAliases, max_width: u64) -> bool {
        let signatures = self.signatures();
        forall|place: RoutinePosition| #[trigger] signatures.contains_key(place) ==>
            aliases.typed_signature_evidence(place.0, place.1, max_width, Ok(Some(signatures[place])))
    }

    pub(super) open spec fn matches_mixed(&self, aliases: &MixedUseAliases, max_width: u64) -> bool {
        let signatures = self.signatures();
        forall|place: RoutinePosition| #[trigger] signatures.contains_key(place) ==>
            aliases.mixed_typed_signature_matches(place.0, place.1, max_width, Ok(Some(signatures[place])))
    }

    pub(super) fn new() -> (cache: Self)
        ensures cache.signatures().dom().is_empty(),
    {
        Self { signatures: BTreeMap::new() }
    }

    /// 登録済みの署名を宣言の添字で検索する。
    pub(super) fn get(&self, file: usize, entry: usize)
        -> (result: Option<&TypedRoutineSignature<'p, 'a>>)
        ensures match result {
            Some(signature) => self.signatures().contains_key((file, entry))
                && *signature == self.signatures()[(file, entry)],
            None => !self.signatures().contains_key((file, entry)),
        },
    {
        proof {
            broadcast use vstd::laws_cmp::group_laws_cmp;
            assert(obeys_cmp::<RoutinePosition>());
        }
        self.signatures.get(&(file, entry))
    }

    /// 必要なときに署名を解決し、成功した署名を登録する。
    ///
    /// `Ok(true)` は登録済み、`Ok(false)` は添字に対応する署名がないことを表す。
    ///
    /// # Errors
    ///
    /// 宣言側の署名に違反があれば、その場で診断を返す。
    pub(super) fn prepare(
        &mut self, aliases: &UseAliases<'_, 'p, 'a>, file: usize, entry: usize, max_width: u64,
    ) -> (result: Result<bool, TypedSignatureError<'p, 'a>>)
        requires aliases.can_resolve(), old(self).matches(aliases, max_width),
        ensures
            final(self).matches(aliases, max_width),
            match result {
                Ok(true) => {
                    let signatures = final(self).signatures();
                    let stored = signatures[(file, entry)];
                    &&& signatures.contains_key((file, entry))
                    &&& forall|fresh: Result<Option<TypedRoutineSignature>, TypedSignatureError>| #[trigger]
                        aliases.typed_signature_evidence(file, entry, max_width, fresh) ==>
                            (fresh matches Ok(Some(signature))
                                && signature.inputs@ == stored.inputs@ && signature.outputs@ == stored.outputs@
                                && signature.output_inputs@ == stored.output_inputs@)
                },
                Ok(false) => aliases.typed_signature_evidence(file, entry, max_width, Ok(None)),
                Err(error) => aliases.typed_signature_evidence(file, entry, max_width, Err(error)),
            },
            forall|place: RoutinePosition| #[trigger] old(self).signatures().contains_key(place) ==>
                final(self).signatures().contains_key(place)
                    && final(self).signatures()[place] == old(self).signatures()[place],
    {
        if self.get(file, entry).is_none() {
            let Some(signature) = aliases.resolve_routine_signature(file, entry, max_width)? else {
                return Ok(false);
            };
            self.insert((file, entry), signature);
        }
        proof {
            let signatures = self.signatures();
            let stored = signatures[(file, entry)];
            assert(self.matches(aliases, max_width));
            assert(aliases.typed_signature_evidence(file, entry, max_width, Ok(Some(stored))));
            assert forall|fresh: Result<Option<TypedRoutineSignature>, TypedSignatureError>| #[trigger]
                aliases.typed_signature_evidence(file, entry, max_width, fresh) implies
                    (fresh matches Ok(Some(signature)) && signature.inputs@ == stored.inputs@
                        && signature.outputs@ == stored.outputs@ && signature.output_inputs@ == stored.output_inputs@) by {
                aliases.typed_signature_success_excludes_other(file, entry, max_width, stored, fresh);
                aliases.typed_routine_signatures_agree(file, entry, max_width, fresh->Ok_0->Some_0, stored);
            };
        }
        Ok(true)
    }

    /// 混在索引が指す署名を、現在の幅上限で解決して登録する。
    pub(super) fn prepare_mixed(
        &mut self, aliases: &MixedUseAliases<'_, 'p, 'a>, file: usize, entry: usize, max_width: u64,
    ) -> (result: Result<bool, MixedTypedSignatureError<'p, 'a>>)
        requires
            mixed_use_targets_match(&aliases.targets_model().project_model(), aliases.targets_model()),
            old(self).matches_mixed(aliases, max_width),
        ensures
            final(self).matches_mixed(aliases, max_width),
            match result {
                Ok(true) => final(self).signatures().contains_key((file, entry)),
                Ok(false) => aliases.mixed_typed_signature_matches(file, entry, max_width, Ok(None))
                    && !aliases.targets_model().project_model().has_mixed_routine_signature(file, entry),
                Err(error) => aliases.mixed_typed_signature_matches(file, entry, max_width, Err(error)),
            },
            forall|place: RoutinePosition| #[trigger] old(self).signatures().contains_key(place) ==>
                final(self).signatures().contains_key(place)
                    && final(self).signatures()[place] == old(self).signatures()[place],
    {
        if self.get(file, entry).is_none() {
            let Some(signature) = aliases.resolve_mixed_routine_signature(file, entry, max_width)? else {
                return Ok(false);
            };
            self.insert((file, entry), signature);
        }
        Ok(true)
    }

    fn insert(&mut self, position: RoutinePosition, signature: TypedRoutineSignature<'p, 'a>)
        ensures final(self).signatures() == old(self).signatures().insert(position, signature),
    {
        proof {
            broadcast use vstd::laws_cmp::group_laws_cmp;
            assert(obeys_cmp::<RoutinePosition>());
        }
        let _ = self.signatures.insert(position, signature);
    }
}

} // verus!
