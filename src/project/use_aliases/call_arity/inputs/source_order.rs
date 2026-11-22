//! 引数の型検査で保存した位置を、元の構文木の順序と照合する。

use super::*;
use crate::syntax::circuit::{call_argument_positions, call_argument_positions_from_steps};

verus! {

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// 型検査で取り出した引数位置が、元の構文木の出現順と一致することを示す。
    pub(in crate::project::use_aliases) proof fn projected_arguments_in_source_order(
        &self, at: (usize, usize, usize, usize), limit: u64, types: Seq<Option<SignalType>>,
        wiring: &FuncWiring, call: TypedFuncCall, projected: Seq<ProjectedCallArgument>,
    )
        requires
            self.can_resolve(),
            self.func_wiring_evidence(at.0, at.1, limit, Ok(FuncWiringResult::Checked(*wiring))),
            self.projected_input_arguments(at, limit, types, wiring, projected),
            self.func_call_signature_evidence(at.0, at.1, at.2, at.3, limit, Ok(Some(call))),
        ensures call_argument_positions(self.targets.project_model().circuits_model()[at.0 as int].syntax.forms@,
            call.call.call, Seq::new(projected.len(), |i: int| projected[i].form)),
    {
        let (file, entry, definition, reference) = at;
        self.typed_call_arguments_ready(file, entry, definition, reference, limit, call);
        self.checked_wiring_is_func(file, entry, limit, *wiring);
        self.resolved_signature_excludes_no_call(at, limit, call);
        self.targets.parsed_project_model();
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[file as int];
        let source = &project.sources_model()[file as int];
        parsed_index_evidence(*source, *parsed);
        build_entry_ranges_evidence(source.text, &parsed.build_model(), entry as int);
        build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int,
            parsed.entry_ranges@[entry as int].definitions.start + definition);
        let (other, visited, values) = self.projected_inputs_witness(at, limit, types, wiring, projected);
        self.successful_call_signatures_agree(file, entry, definition, reference, limit, call, other);
        let forms = parsed.syntax.forms@;
        let frame = parsed.entry_ranges@[entry as int];
        let row = parsed.definitions@[frame.definitions.start + definition];
        let slots = parsed.signals@[row.signals.start as int..row.signals.end as int];
        let start = row.signals.start - frame.signals.start;
        reveal(argument_prefix);
        reveal(argument_projections_match);
        reveal(argument_projection_matches);
        assert forall|i: int| 0 <= i < visited.len() implies (#[trigger] projected[i]).form == visited[i] by {
            assert(argument_projection_matches((self, file, entry, definition), projected[i], visited[i],
                forms, wiring, types, slots, start, values[i]));
        };
        let positions = Seq::new(projected.len(), |i: int| projected[i].form);
        assert(positions =~= visited);
        assert forall|i: int| 0 <= i < visited.len()
            implies direct_call_argument(forms, call.call.call, (#[trigger] visited[i]) as int) by {
            self.checked_projected_argument(at, limit, types, wiring, call, projected, i);
        };
        call_argument_positions_from_steps(forms, call.call.call, visited);
    }
}

} // verus!
