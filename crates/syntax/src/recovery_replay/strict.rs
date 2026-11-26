//! 修復がなかった回復解析を、厳格な字句と括弧の導出に結び付ける。

use super::*;
use crate::lexical::{
    InputDerivation, Lexeme, input_lexeme_valid, parenthesis_delta,
    sexpr_input_derivation, well_formed_sexpr, well_formed_sexpr_bytes,
};
use crate::{lexical_step_agrees, segment_lexeme};

verus! {

// 入力末尾の補完前後で、修復の件数が減らないことを示す。
proof fn final_repairs_keep_history(state: RecoveryState, eof: int)
    ensures
        finish_recovery(state, eof).repairs.len() >= state.repairs.len(),
        finish_recovery(state, eof).repairs.len() == 0 ==> state.open.len() == 0,
    decreases state.open.len(),
{
    reveal(finish_recovery);
    if state.open.len() > 0 {
        final_repairs_keep_history(close_recovery_at_eof(state, eof as usize), eof);
    }
}

proof fn repair_counts_monotone(bytes: Seq<u8>, frames: Seq<ReplayFrame>, i: int, end: int)
    requires replay_valid(bytes, frames), 0 <= i <= end <= frames.len(),
    ensures replay_at(frames, i).repairs.len() <= replay_at(frames, end).repairs.len(),
    decreases end - i,
{
    if i < end {
        replay_frame_evidence(bytes, frames, i);
        reveal(apply_recovery_segment);
        assert(replay_at(frames, i + 1).repairs.len() >= replay_at(frames, i).repairs.len());
        repair_counts_monotone(bytes, frames, i + 1, end);
    }
}

// 修復を追加しない一字句は厳格な字句として読め、括弧の深さを負にしない。
proof fn clean_frame_lexeme(
    bytes: Seq<u8>, frames: Seq<ReplayFrame>, i: int,
)
    requires replay_valid(bytes, frames), 0 <= i < frames.len(),
        replay_at(frames, i + 1).repairs.len() == 0,
    ensures ({
        let segment = frames[i].segment;
        let lexeme = segment_lexeme(segment.kind);
        &&& lexeme is Some
        &&& !segment.missing_separator
        &&& segment.span.start == replay_position(frames, i)
        &&& crate::lexical::lexeme_at(bytes, segment.span.start as int, segment.span.end as int, lexeme->Some_0)
        &&& replay_at(frames, i + 1).open.len() as int
            == replay_at(frames, i).open.len() as int + parenthesis_delta(lexeme->Some_0)
    }),
{
    replay_frame_evidence(bytes, frames, i);
    reveal(apply_recovery_segment);
    reveal(recovery_segment_at);
    reveal(lexical_step_agrees);
}

/// 修復のない回復再生が得られた本文は、厳格な S 式として受理される。
pub proof fn recovery_without_repairs_is_strict(source: &str, recovered: &crate::Recovered)
    requires
        recovered_replay_matches(source, recovered.forms@, recovered.repairs@, recovered.original_lists@),
        recovered.repairs@.len() == 0,
    ensures well_formed_sexpr(source),
{
    let frames = recovered_history(source, recovered);
    let bytes = source.spec_bytes();
    let len = frames.len();
    final_repairs_keep_history(replay_at(frames, len as int), bytes.len() as int);
    let witness = InputDerivation {
        lexemes: Seq::new(len, |i: int| {
            let segment = frames[i].segment;
            Lexeme {
                start: segment.span.start as int,
                end: segment.span.end as int,
                kind: segment_lexeme(segment.kind)->Some_0,
            }
        }),
        depths: Seq::new(len + 1, |i: int| replay_at(frames, i).open.len() as int),
    };
    assert forall|i: int| 0 <= i < len implies #[trigger] input_lexeme_valid(bytes, witness, i) by {
        let segment = frames[i].segment;
        let lexeme = witness.lexemes[i];
        repair_counts_monotone(bytes, frames, i + 1, len as int);
        clean_frame_lexeme(bytes, frames, i);
        assert(lexeme.kind == segment_lexeme(segment.kind)->Some_0);
        assert(lexeme.start == replay_position(frames, i));
        assert(witness.depths[i + 1] == witness.depths[i] + parenthesis_delta(lexeme.kind));
        if i > 0 {
            let previous = frames[i - 1].segment;
            assert(lexeme.start == witness.lexemes[i - 1].end);
            if lexeme.kind is Atom {
                repair_counts_monotone(bytes, frames, i, len as int);
                clean_frame_lexeme(bytes, frames, i - 1);
                replay_frame_evidence(bytes, frames, i);
                reveal(recovery_segment_at);
                assert(segment.kind is Atom);
                assert(!replay_separator(frames, i));
                assert(!previous.kind.is_atom());
                assert(!(witness.lexemes[i - 1].kind is Atom));
            }
        }
        reveal(input_lexeme_valid);
    };

    reveal(sexpr_input_derivation);
    assert(sexpr_input_derivation(bytes, witness));
    reveal(well_formed_sexpr);
    reveal(well_formed_sexpr_bytes);
}

} // verus!
