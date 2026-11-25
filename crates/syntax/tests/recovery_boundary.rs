use circuitgame2_syntax::{
    ErrorKind, Form, Recovered, Repair, parse_recovering, recovery_boundary_at, recovery_window,
    remember_recovery_edges,
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

#[test]
fn local_recovery_keeps_only_the_changed_middle_owned_by_the_update() {
    let prefix = "(unchanged \"🐈\")";
    let old_middle = " (old (tree))";
    let new_middle = " (new \"🦊\" (level (deep)))";
    let suffix = "\r\n) (valid) (broken \"invalid\\文\") (unfinished";
    let old = format!("{prefix}{old_middle}{suffix}");
    let current = format!("{prefix}{new_middle}{suffix}");
    let start = prefix.len();
    let join = start + new_middle.len();
    let retained = remember_recovery_edges(&old, start, start + old_middle.len()).unwrap();
    let baseline = retained.reparse(&old).unwrap();
    let update = retained.reparse(&current).unwrap();
    let [head, changed, tail] = update.sections();
    let previous = baseline.sections();
    assert!(core::ptr::eq(head.recovered, previous[0].recovered));
    assert!(core::ptr::eq(tail.recovered, previous[2].recovered));
    assert_eq!(head.byte_base, 0);
    assert_eq!(changed.byte_base, start);
    assert_eq!(tail.byte_base, join);
    assert_eq!(changed.form_base, head.recovered.forms.len());
    assert_eq!(
        tail.form_base,
        changed.form_base + changed.recovered.forms.len()
    );
    assert_eq!(*head.recovered, parse_recovering(prefix));
    assert_eq!(
        *changed.recovered,
        relative_to_tail(parse_recovering(&current[..join]), start)
    );
    assert_eq!(
        *tail.recovered,
        relative_to_tail(parse_recovering(&current), join)
    );

    let removal = retained
        .reparse(&format!("{prefix}{suffix}"))
        .unwrap()
        .sections()[1]
        .recovered
        .forms
        .len();
    assert_eq!(removal, 0);
    assert!(
        retained
            .reparse(&format!("{prefix} (unclosed {suffix}"))
            .is_none()
    );
    assert!(
        retained
            .reparse(&current.replacen("unchanged", "different", 1))
            .is_none()
    );
    assert!(retained.reparse(&format!("{current}x")).is_none());
    assert!(
        remember_recovery_edges(
            &old,
            prefix.find('🐈').unwrap() + 1,
            start + old_middle.len()
        )
        .is_none()
    );
}

#[test]
fn localized_original_list_inspection_uses_current_document_positions() {
    use circuitgame2_syntax::circuit::{CircuitRecovery, recover_circuit_forms};

    let previous = "(using nor)(before)\r\n) (unknown-directive) (unfinished";
    let current = "(using nor)(after \"🦊\")\r\n) (unknown-directive) (unfinished";
    let start = "(using nor)".len();
    let join = "(using nor)(before)".len();
    let edges = remember_recovery_edges(previous, start, join).unwrap();
    let update = edges.reparse(current).unwrap();
    assert!(update.has_repairs());
    let CircuitRecovery::WithSyntaxRepairs { recovered, original } = recover_circuit_forms(current) else {
        panic!("expected syntax repairs");
    };

    let location = update.original_list_location(2, 0).unwrap();
    assert_eq!(location.span, recovered.original_lists[2]);
    assert!(matches!(&recovered.forms[location.form], Form::List { span, .. } if span == &location.span));
    assert_eq!(
        update.form_location(2, 0).unwrap(),
        location,
    );
    let verified = update.inspect_original_list(2, 0).unwrap();
    let reference = original[2].as_ref().unwrap();
    assert_eq!(verified.span, reference.span);
    assert_eq!(verified.forms, reference.forms);
    assert!(!verified.source_diagnostics().is_empty());
    assert!(verified.source_diagnostics().iter().any(Option::is_some));
    assert_eq!(verified.source_diagnostics(), reference.source_diagnostics());
    assert!(update.original_list_location(2, 1).is_none());
    assert!(update.form_location(3, 0).is_none());
    assert!(update.inspect_original_list(2, 1).is_none());
}

#[test]
fn owned_cache_borrows_local_views_and_reparses_the_current_text_on_fallback() {
    use circuitgame2_syntax::{OwnedRecoveryCache, SnapshotRecovery, recover_snapshot};

    let prefix = "(using nor)";
    let old_middle = "(old)";
    let suffix = "\r\n) (original) (unfinished";
    let old = format!("{prefix}{old_middle}{suffix}");
    let cache = OwnedRecoveryCache::remember(
        old,
        u64::MAX - 1,
        prefix.len(),
        prefix.len() + old_middle.len(),
    ).unwrap();
    assert_eq!(cache.revision(), u64::MAX - 1);
    assert_eq!(cache.text(), format!("{prefix}{old_middle}{suffix}"));

    let current = format!("{prefix}(new \"🦊\"){suffix}");
    let local = recover_snapshot(Some(&cache), &current, u64::MAX);
    assert_eq!(local.revision(), u64::MAX);
    assert_eq!(local.source(), current);
    let SnapshotRecovery::Local(local) = local.recovery() else { panic!("expected local recovery"); };
    let original = recover_snapshot(Some(&cache), cache.text(), cache.revision());
    let SnapshotRecovery::Local(original) = original.recovery() else { panic!("expected cached recovery"); };
    assert!(core::ptr::eq(local.sections()[2].recovered, original.sections()[2].recovered));
    assert_eq!(local.original_list_span(2, 0).unwrap(), {
        let start = current.find("(original)").unwrap();
        start..start + "(original)".len()
    });
    let malformed = format!("{prefix}(new {suffix}");
    for (saved, source, revision) in [
        (Some(&cache), current.as_str(), u64::MAX - 2),
        (Some(&cache), current.as_str(), u64::MAX - 1),
        (Some(&cache), malformed.as_str(), u64::MAX),
        (None, current.as_str(), u64::MAX),
    ] {
        let fallback = recover_snapshot(saved, source, revision);
        assert_eq!(fallback.revision(), revision);
        assert_eq!(fallback.source(), source);
        let SnapshotRecovery::Full(whole) = fallback.recovery() else { panic!("expected full recovery"); };
        assert_eq!(*whole, parse_recovering(source));
    }
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
        "; ) と猫\r\n) (intact) (partial \"invalid\\猫\" (head foo\"text\"))",
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
    let empty = recovery_window(
        &old[..old_end],
        &current[..current_end],
        start,
        old_end,
        current_end,
    );
    assert!(empty.is_some());
    assert_eq!(
        relative_to_tail(parse_recovering(&old[..old_end]), old_end),
        parse_recovering("")
    );
    assert_eq!(
        relative_to_tail(parse_recovering(&current[..current_end]), current_end),
        parse_recovering("")
    );
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
