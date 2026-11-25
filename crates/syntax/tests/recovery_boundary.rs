use circuitgame2_syntax::{
    ErrorKind, Form, Recovered, Repair, parse_recovering, recovery_boundary_at, recovery_window,
};
use std::ops::Range;

#[test]
fn only_real_top_level_closes_are_checkpoints() {
    let text = "\u{061f}; )\r\n(\" ) 🐈\" (x)))(z \"bad\\q )\r\n  (nested)";
    let nested = text.find("(x)").unwrap() + 3;
    let outer = nested + 1;
    let unmatched = nested + 2;
    let quote = text.find(" ) 🐈").unwrap() + 2;
    let repair = text.find("q )").unwrap() + 3;
    assert!(recovery_boundary_at(text, 0).is_some());
    assert!(recovery_boundary_at(text, 1).is_none());
    assert!(recovery_boundary_at(text, text.find(';').unwrap() + 3).is_none());
    for position in [quote, nested, unmatched, repair, text.len(), text.len() + 1] {
        assert!(recovery_boundary_at(text, position).is_none(), "{position}");
    }
    assert_eq!(recovery_boundary_at(text, outer).unwrap().offset(), outer);
    let boundary = recovery_boundary_at(text, outer).unwrap();
    assert!(boundary.scan_to(0).is_none());
    assert!(boundary.scan_to(text.len()).is_none());

    let repaired_root = r#"(a "bad\q")"#;
    assert!(recovery_boundary_at(repaired_root, repaired_root.len()).is_some());
    assert!(parse_recovering(repaired_root).original_lists.is_empty());
}

fn relative_to_tail(mut whole: Recovered, offset: usize) -> Recovered {
    let relative = |span: &Range<usize>| span.start - offset..span.end - offset;
    let first_form = whole.forms.partition_point(|form| match form {
        Form::Atom { span, .. } | Form::List { span, .. } => span.start < offset,
    });
    whole.forms.drain(..first_form);
    for form in &mut whole.forms {
        match form {
            Form::Atom { span, .. } => *span = relative(span),
            Form::List { span, end } => {
                *span = relative(span);
                *end -= first_form;
            }
        }
    }
    whole.original_lists.retain(|span| span.start >= offset);
    for span in &mut whole.original_lists {
        *span = relative(span);
    }
    whole.repairs.retain_mut(|repair| {
        match repair {
            Repair::Skipped { span, error } if span.start >= offset => {
                *span = relative(span);
                error.span = relative(&error.span);
                match &mut error.kind {
                    ErrorKind::InvalidEscape { opening }
                    | ErrorKind::NewlineInString { opening } => *opening -= offset,
                    ErrorKind::UnclosedList { eof } => *eof -= offset,
                    _ => {}
                }
            }
            Repair::InsertedSeparator { offset: at } if *at >= offset => *at -= offset,
            Repair::InsertedClose {
                offset: at,
                opening,
                list,
            } if opening.start >= offset => {
                *at -= offset;
                *opening = relative(opening);
                *list -= first_form;
            }
            _ => return false,
        }
        true
    });
    whole
}

#[test]
fn shifted_join_matches_fresh_recovery_of_the_same_tail() {
    let prefix = "(unchanged 🐈)";
    let old_middle = "(abc)";
    let current_middle = "(abc (deeply nested) \"broken\\q\")";
    let tail = concat!(
        ") (intact) (partial \"invalid\\q\" (head foo\"text\"))",
        " (broken \"line\r\n (nested)) (unfinished",
    );
    let old = format!("{prefix}{old_middle}{tail}");
    let current = format!("{prefix}{current_middle}{tail}");
    let start = prefix.len();
    let old_end = start + old_middle.len();
    let current_end = start + current_middle.len();
    let window = recovery_window(&old, &current, start, old_end, current_end).unwrap();
    assert_eq!(window.old, start..old_end);
    assert_eq!(window.current, start..current_end);
    let fresh = parse_recovering(tail);
    let prior = parse_recovering(&old);
    let edited = parse_recovering(&current);
    assert_eq!(edited.repairs.len(), prior.repairs.len() + 1);
    assert_eq!(relative_to_tail(prior, old_end), fresh);
    assert_eq!(relative_to_tail(edited, current_end), fresh);
    assert!(recovery_window(&old, &current, start, old_end, current_end - 1).is_none());
    assert!(recovery_window(&old, &format!("{current}x"), start, old_end, current_end).is_none());
    assert!(
        recovery_window(
            &old,
            &current.replacen("unchanged", "different", 1),
            start,
            old_end,
            current_end
        )
        .is_none()
    );
}
