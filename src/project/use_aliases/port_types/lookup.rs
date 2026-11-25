//! 設定にあるポート名を、回路の型付き署名に照合する。

use super::{
    LocatedName, PortContext, PortDirection, ResolvedPortType, TypedPort, TypedSignatureError,
    UseAliases, read_indexed_atom,
};
#[cfg(verus_only)]
use super::{
    CheckedRoutineSignature, Form, ProjectSource, TypedRoutineSignature, encode_utf8_decode_utf8, form_span,
    form_spans_valid, located_name_evidence, location_in_source, routine_signature_evidence,
    typed_name_sites,
};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 名前で指定した回路ポートの署名上の位置と型。
#[derive(Debug)]
pub struct NamedRoutinePort<'p, 'a> {
    /// 見つかったポートと同じ方向のポート列での添字。
    pub index: usize,
    /// 元ソースにあるポート名の範囲。
    pub name: LocatedName<'p, 'a>,
    /// 構造体名を解決したポート型。
    pub ty: ResolvedPortType<'p, 'a>,
}

/// 回路ポートを探した結果。
#[derive(Debug)]
pub enum RoutinePortLookup<'p, 'a> {
    /// 指定した方向のポートが見つかった。
    Found(NamedRoutinePort<'p, 'a>),
    /// 同名のポートは反対方向にある。
    OppositeDirection(NamedRoutinePort<'p, 'a>),
    /// どちらの方向にも同名のポートがない。
    UnknownName,
    /// 指定位置に回路の署名がない。
    NoSignature,
}

spec fn named_port_at(
    source: &ProjectSource, forms: Seq<Form>, port: TypedPort, word: &str,
) -> bool {
    let span = form_span(forms[port.declared.site.name as int]);
    source.text.spec_bytes()[span.start as int..span.end as int] == word.spec_bytes()
}

spec fn port_search(
    source: &ProjectSource, forms: Seq<Form>, ports: Seq<TypedPort>, word: &str,
    result: Option<NamedRoutinePort>,
) -> bool {
    &&& match result {
        None => true,
        Some(port) => {
            &&& port.index < ports.len()
            &&& *port.name.source == *source
            &&& location_in_source(port.name)
            &&& port.name.source.text_model().spec_bytes()[port.name.span.start as int..port.name.span.end as int]
                == word.spec_bytes()
            &&& {
                let declaration = ports[port.index as int];
                &&& port.ty == declaration.ty
                &&& port.name.span == form_span(forms[declaration.declared.site.name as int])
                &&& named_port_at(source, forms, declaration, word)
            }
        },
    }
    &&& forall|i: int| 0 <= i < ports.len() && (result is None || i < result->Some_0.index) ==>
        !named_port_at(source, forms, #[trigger] ports[i], word)
}

fn find_named_port<'p, 'a>(
    context: &PortContext<'p, 'a>, ports: &[TypedPort<'p, 'a>], word: &str,
) -> (result: Option<NamedRoutinePort<'p, 'a>>)
    requires
        typed_name_sites(context.forms@, ports@),
        form_spans_valid(context.source.text, context.forms@, context.source.text.spec_bytes().len() as int),
    ensures port_search(context.source, context.forms@, ports@, word, result),
{
    let mut index = 0;
    while index < ports.len()
        invariant
            index <= ports.len(),
            typed_name_sites(context.forms@, ports@),
            form_spans_valid(context.source.text, context.forms@, context.source.text.spec_bytes().len() as int),
            forall|i: int| 0 <= i < index ==> !named_port_at(context.source, context.forms@, #[trigger] ports@[i], word),
        decreases ports.len() - index,
    {
        let declaration = &ports[index];
        let atom = declaration.declared.site.name;
        let (candidate, span) = read_indexed_atom(context.source.text, context.forms, atom);
        proof {
            encode_utf8_decode_utf8(candidate@);
            encode_utf8_decode_utf8(word@);
        }
        if candidate == word {
            let name = LocatedName { source: context.source, span };
            proof {
                located_name_evidence(name);
                name.source.text_model_is_text();
            }
            return Some(NamedRoutinePort { index, name, ty: declaration.ty });
        }
        index += 1;
    }
    None
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// 署名が存在し、指定方向の検索結果と、必要な場合の逆方向の検索結果が一致することを表す。
    pub closed spec fn routine_port_lookup_matches(
        &self, file: usize, entry: usize, max_width: u64, direction: PortDirection, word: &str,
        result: Result<RoutinePortLookup, TypedSignatureError>,
    ) -> bool {
        match result {
            Err(error) => self.typed_signature_evidence(file, entry, max_width, Err(error)),
            Ok(RoutinePortLookup::NoSignature) => self.typed_signature_evidence(file, entry, max_width, Ok(None)),
            Ok(found) => exists|signature: TypedRoutineSignature| {
                &&& #[trigger] self.typed_signature_evidence(file, entry, max_width, Ok(Some(signature)))
                &&& {
                    let project = self.targets.project_model();
                    let source = &project.sources_model()[file as int];
                    let forms = project.circuits_model()[file as int].syntax.forms@;
                    let (requested, opposite) = match direction {
                        PortDirection::Input => (signature.inputs@, signature.outputs@),
                        PortDirection::Output => (signature.outputs@, signature.inputs@),
                    };
                    match found {
                        RoutinePortLookup::Found(port) => port_search(source, forms, requested, word, Some(port)),
                        RoutinePortLookup::OppositeDirection(port) =>
                            port_search(source, forms, requested, word, None)
                                && port_search(source, forms, opposite, word, Some(port)),
                        RoutinePortLookup::UnknownName =>
                            port_search(source, forms, requested, word, None)
                                && port_search(source, forms, opposite, word, None),
                        RoutinePortLookup::NoSignature => false,
                    }
                }
            },
        }
    }

    /// 回路の署名から、方向と名前で指定したポートの型と位置を得る。
    ///
    /// 入出力の両方に同じ名前がある場合は、指定した方向のポートを選ぶ。
    ///
    /// # Errors
    ///
    /// 署名の検査でエラーになった場合は、型解決が返した診断を返す。
    ///
    /// # Examples
    ///
    /// ```
    /// use circuitgame2_core::project::{
    ///     PortDirection, ResolvedPortType, RoutinePortLookup, SourceSnapshot,
    ///     check_use_aliases, index_use_targets, parse_circuit_project,
    /// };
    ///
    /// let text = "(using nor) (module main (in tap) (out tap q) (def q (nor tap tap)))";
    /// let project = parse_circuit_project(&[SourceSnapshot {
    ///     path: "main.ncg2", revision: 1, text,
    /// }]).unwrap();
    /// let targets = index_use_targets(&project).unwrap();
    /// let aliases = check_use_aliases(&targets).unwrap();
    /// let RoutinePortLookup::Found(port) =
    ///     aliases.resolve_routine_port(0, 1, 64, PortDirection::Output, "tap").unwrap()
    /// else { panic!("出力のポートが見つからない") };
    /// assert!(matches!(port.ty, ResolvedPortType::Bits(1)));
    /// assert_eq!(port.index, 0);
    /// assert_eq!(&text[port.name.span], "tap");
    /// assert!(matches!(
    ///     aliases.resolve_routine_port(0, 1, 64, PortDirection::Input, "q").unwrap(),
    ///     RoutinePortLookup::OppositeDirection(_),
    /// ));
    /// ```
    pub fn resolve_routine_port(
        &self, file: usize, entry: usize, max_width: u64, direction: PortDirection, word: &str,
    ) -> (result: Result<RoutinePortLookup<'p, 'a>, TypedSignatureError<'p, 'a>>)
        requires self.can_resolve(),
        ensures
            self.routine_port_lookup_matches(file, entry, max_width, direction, word, result),
            match result {
                Ok(RoutinePortLookup::Found(port) | RoutinePortLookup::OppositeDirection(port)) => {
                    &&& location_in_source(port.name)
            &&& port.name.source.text_model().spec_bytes()[port.name.span.start as int..port.name.span.end as int]
                == word.spec_bytes()
                    &&& port.name.source.text_model().spec_bytes()[port.name.span.start as int..port.name.span.end as int]
                        == word.spec_bytes()
                },
                _ => true,
            },
    {
        let signature = match self.resolve_routine_signature(file, entry, max_width) {
            Ok(Some(signature)) => signature,
            Ok(None) => return Ok(RoutinePortLookup::NoSignature),
            Err(error) => return Err(error),
        };
        proof {
            self.typed_signature_sites(file, entry, max_width, signature);
            let (context, _) = choose|context: PortContext, checked: CheckedRoutineSignature|
                #[trigger] self.port_context_evidence(file, entry, &context)
                && #[trigger] routine_signature_evidence(&self.targets.project_model(), file as int, entry as int, max_width, Ok(Some(checked)))
                && self.typed_after_signature(&context, &checked, Ok(Some(signature)));
            assert(self.port_context_evidence(file, entry, &context));
        }
        let context = self.port_context(file, entry);
        let (requested, opposite) = match direction {
            PortDirection::Input => (signature.inputs.as_slice(), signature.outputs.as_slice()),
            PortDirection::Output => (signature.outputs.as_slice(), signature.inputs.as_slice()),
        };
        let found = match find_named_port(&context, requested, word) {
            Some(port) => RoutinePortLookup::Found(port),
            None => match find_named_port(&context, opposite, word) {
                Some(port) => RoutinePortLookup::OppositeDirection(port),
                None => RoutinePortLookup::UnknownName,
            },
        };
        Ok(found)
    }
}

} // verus!
