use circuitgame2_device_timing::{
    FixedIssueError, FixedPrepareError, FixedRequestLedger, HostRequestId, RequestKey, TickPosition,
};

#[test]
fn failed_preparation_preserves_due_response_and_serials_for_retry() {
    let mut ledger = FixedRequestLedger::<u8, 1>::new();
    let original = RequestKey { instance: 0, tag: 7 };
    let first = RequestKey { instance: 1, tag: 8 };
    let second = RequestKey { instance: 2, tag: 9 };
    let issued_at = ledger.advance_tick().unwrap();
    let issued = ledger.issue(original).unwrap();
    let target = TickPosition { tick: issued_at.tick + 1, ..issued_at };
    ledger.receive(issued, target, 123).unwrap();

    assert!(matches!(ledger.prepare_tick(&[], &[]), Err(FixedPrepareError::MissingDelivery)));
    assert!(matches!(ledger.prepare_tick(&[issued, issued], &[]), Err(FixedPrepareError::Delivery(1))));
    assert!(matches!(ledger.prepare_tick(&[issued], &[original]),
        Err(FixedPrepareError::Request(0, FixedIssueError::TagInUse))));
    assert!(matches!(ledger.prepare_tick(&[issued], &[first, second]),
        Err(FixedPrepareError::Request(1, FixedIssueError::Capacity))));
    assert_eq!(ledger.position(), issued_at);
    assert_eq!(ledger.peek_at(issued, target), Some((7, 123)));

    let keys = [first];
    drop(ledger.prepare_tick(&[issued], &keys).unwrap());
    assert_eq!(ledger.position(), issued_at);
    assert_eq!(ledger.peek_at(issued, target), Some((7, 123)));

    let prepared = ledger.prepare_tick(&[issued], &keys).unwrap();
    prepared.cancel();
    assert_eq!(ledger.position(), issued_at);
    assert_eq!(ledger.peek_at(issued, target), Some((7, 123)));

    let committed = ledger.prepare_tick(&[issued], &keys).unwrap().commit();
    assert_eq!(committed.position(), target);
    assert_eq!(ledger.position(), target);
    assert_eq!(ledger.peek_at(issued, target), None);
    assert_eq!(committed.id_at(0), Some(HostRequestId { instance: 1, serial: 1, generation: target.generation }));
    assert_eq!(committed.id_at(1), None);
}

#[test]
fn committed_ids_follow_the_supplied_request_order() {
    let mut ledger = FixedRequestLedger::<(), 2>::new();
    let keys = [RequestKey { instance: 4, tag: 5 }, RequestKey { instance: 9, tag: 1 }];
    let issued = ledger.prepare_tick(&[], &keys).unwrap().commit();
    let target = TickPosition { generation: 0, tick: 1 };
    assert_eq!(issued.position(), target);
    assert_eq!(issued.id_at(0), Some(HostRequestId { instance: 4, generation: 0, serial: 0 }));
    assert_eq!(issued.id_at(1), Some(HostRequestId { instance: 9, generation: 0, serial: 1 }));
    assert_eq!(issued.id_at(2), None);
    let delivery = TickPosition { tick: 2, ..target };
    ledger.receive(issued.id_at(0).unwrap(), delivery, ()).unwrap();
    ledger.receive(issued.id_at(1).unwrap(), delivery, ()).unwrap();
    ledger.prepare_tick(&[issued.id_at(1).unwrap(), issued.id_at(0).unwrap()], &[]).unwrap().commit();
    assert_eq!(ledger.peek_at(issued.id_at(0).unwrap(), delivery), None);
    assert_eq!(ledger.peek_at(issued.id_at(1).unwrap(), delivery), None);
}
