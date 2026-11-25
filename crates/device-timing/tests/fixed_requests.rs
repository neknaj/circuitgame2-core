use circuitgame2_device_timing::{
    ClockError, FixedIssueError, FixedReceiveError, FixedRequestLedger, FixedTickError, HostRequestId,
    HostResponseError, RequestKey, TickPosition,
};

#[test]
fn capacity_returns_at_delivery_without_releasing_the_tag_early() {
    let mut ledger = FixedRequestLedger::<u8, 1>::new();
    let first = RequestKey { instance: 0, tag: 9 };
    let other = RequestKey { instance: 1, tag: 9 };
    assert_eq!(ledger.issue(first), Err(FixedIssueError::BeforeFirstTick));
    let issued = ledger.advance_tick().unwrap();
    let id = ledger.issue(first).unwrap();
    assert_eq!(id.serial, 0);
    assert_eq!(ledger.issue(other), Err(FixedIssueError::Capacity));
    assert_eq!(ledger.issue(first), Err(FixedIssueError::TagInUse));

    let delivery = TickPosition { generation: issued.generation, tick: issued.tick + 1 };
    let unknown = HostRequestId { serial: 1, ..id };
    assert_eq!(ledger.receive(unknown, delivery, 1),
        Err(FixedReceiveError::Response(HostResponseError::UnknownRequest)));
    assert_eq!(ledger.receive(HostRequestId { instance: other.instance, ..id }, delivery, 1),
        Err(FixedReceiveError::Retired));
    assert_eq!(ledger.receive(id, issued, 11),
        Err(FixedReceiveError::Response(HostResponseError::TooEarly)));
    ledger.receive(id, delivery, 42).unwrap();
    assert_eq!(ledger.receive(id, issued, 0),
        Err(FixedReceiveError::Response(HostResponseError::DuplicateResponse)));
    assert_eq!(ledger.peek_at(id, delivery), Some((9, 42)));
    assert_eq!(ledger.consume(id), None);

    assert_eq!(ledger.advance_tick(), Ok(delivery));
    assert_eq!(ledger.advance_tick(), Err(FixedTickError::PendingDelivery));
    assert_eq!(ledger.position(), delivery);
    assert_eq!(ledger.consume(id), Some((9, 42)));
    assert_eq!(ledger.consume(id), None);
    assert_eq!(ledger.receive(id, delivery, 1), Err(FixedReceiveError::Retired));
    assert_eq!(ledger.issue(first), Err(FixedIssueError::TagInUse));
    let later = ledger.issue(other).unwrap();
    assert_eq!(later.serial, 1);
    assert_eq!(ledger.receive(id, delivery, 1), Err(FixedReceiveError::Retired));

    let later_delivery = TickPosition { tick: delivery.tick + 1, ..delivery };
    ledger.receive(later, later_delivery, 5).unwrap();
    ledger.advance_tick().unwrap();
    assert_eq!(ledger.consume(later), Some((9, 5)));
    assert_eq!(ledger.issue(first).unwrap().serial, 2);
}

#[test]
fn reset_discards_the_held_response_and_starts_a_new_serial_sequence() {
    let mut ledger = FixedRequestLedger::<u16, 1>::new();
    let key = RequestKey { instance: 0, tag: 4 };
    let issued = ledger.advance_tick().unwrap();
    let old = ledger.issue(key).unwrap();
    let delivery = TickPosition { tick: issued.tick + 1, ..issued };
    ledger.receive(old, delivery, 1024).unwrap();
    assert_eq!(ledger.reset(delivery), Err(ClockError::StaleChange));
    assert_eq!(ledger.peek_at(old, delivery), Some((4, 1024)));

    let reset = TickPosition { generation: 1, tick: 0 };
    ledger.reset(reset).unwrap();
    assert_eq!(ledger.position(), reset);
    assert_eq!(ledger.peek_at(old, delivery), None);
    assert_eq!(ledger.consume(old), None);
    assert_eq!(ledger.issue(key), Err(FixedIssueError::BeforeFirstTick));
    let tick = ledger.advance_tick().unwrap();
    assert_eq!(ledger.receive(old, tick, 11),
        Err(FixedReceiveError::Response(HostResponseError::DifferentGeneration)));
    assert_eq!(ledger.issue(key), Ok(HostRequestId { instance: 0, generation: 1, serial: 0 }));
}

#[test]
fn zero_capacity_does_not_issue_a_serial() {
    let mut ledger = FixedRequestLedger::<(), 0>::new();
    let tick = ledger.advance_tick().unwrap();
    let key = RequestKey { instance: 0, tag: 1 };
    assert_eq!(ledger.issue(key), Err(FixedIssueError::Capacity));
    let id = HostRequestId { instance: 0, generation: 0, serial: 0 };
    assert_eq!(ledger.receive(id, TickPosition { tick: tick.tick + 1, ..tick }, ()),
        Err(FixedReceiveError::Response(HostResponseError::UnknownRequest)));
}
