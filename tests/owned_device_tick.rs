//! UI の実行枠に分けた評価を、借用を保持せずに同じ tick へ確定する。

use circuitgame2_core::{
    device::{
        CommittedHostRequest, DeviceEvent, DeviceHostRequest, DeviceStateSession, HostRequest,
        OwnedDeviceStateTick,
    },
    netlist::{ClockedNor, ClockedVm, NorNetlist, Wire},
    time::TickPosition,
};

type Session = DeviceStateSession<String, (), usize>;
type Pending = OwnedDeviceStateTick<String, (), usize>;

fn session() -> Session {
    let circuit = ClockedNor::check(NorNetlist {
        input_count: 1,
        gates: Vec::new(),
        outputs: vec![Wire::Input(0)],
    })
    .unwrap();
    let vm = ClockedVm::new(circuit, 1, Vec::new(), 0).unwrap();
    Session::new(vm, vec![10])
}

fn begin(session: Session) -> Pending {
    session
        .prepare_owned_tick()
        .unwrap_or_else(|(_, error)| panic!("tick を準備できない。{error:?}"))
}

// 実行枠1回につき一つのイベントを読み、所有値として次回の継続を返す。
fn run_slice(tick: &Pending, from: usize, total: usize) -> Option<(usize, usize)> {
    let (index, event) = tick.next_event(from)?;
    match &event.payload {
        DeviceEvent::Input { payload, .. } => Some((index + 1, total + payload.len())),
        DeviceEvent::Response(_) => panic!("この試験のイベントは外部入力のみ"),
    }
}

#[test]
fn resumes_with_the_same_input_snapshot_until_commit() {
    let mut session = session();
    let current = TickPosition {
        generation: 0,
        tick: 1,
    };
    let future = TickPosition {
        generation: 0,
        tick: 2,
    };
    for (position, text) in [(current, "ab"), (future, "next"), (current, "c")] {
        session.schedule_input(0, position, text.into()).unwrap();
    }

    let tick = begin(session);
    let first = run_slice(&tick, 0, tick.states()[0]).unwrap();
    let (tick, cursor) = (tick, first);
    assert_eq!(tick.target(), current);
    assert_eq!(tick.previous_output(), &[false]);
    assert_eq!(tick.states(), &[10]);
    let (from, total) = run_slice(&tick, cursor.0, cursor.1).unwrap();
    assert!(run_slice(&tick, from, total).is_none());
    let hosts = [DeviceHostRequest::<(), _> {
        instance: 0,
        request: HostRequest::Request {
            tag: 7,
            payload: "first",
        },
    }];
    let (session, error) = tick.commit(vec![total], &[], &hosts);
    assert!(error.is_err());
    assert_eq!(session.position().tick, 0);
    assert_eq!(session.states(), &[10]);
    assert_eq!(session.output(), &[false]);

    let tick = begin(session);
    assert_eq!(run_slice(&tick, 0, tick.states()[0]), Some(first));
    assert_eq!(run_slice(&tick, cursor.0, cursor.1), Some((from, total)));
    let (session, committed) = tick.commit(vec![total], &[true], &hosts);
    let result = committed.unwrap();
    assert_eq!(result.consumed.len(), 2);
    assert!(
        result
            .consumed
            .iter()
            .all(|event| event.position == current)
    );
    assert_eq!(result.outgoing.len(), 1);
    assert!(matches!(
        result.outgoing.get(0),
        Some(CommittedHostRequest::Request { id, tag: 7, payload: &"first" })
            if id.instance == 0 && id.generation == 0 && id.serial == 0
    ));
    assert_eq!(session.states(), &[13]);
    assert_eq!(session.position(), current);
    assert_eq!(session.output(), &[true]);
    let next = begin(session);
    assert_eq!(run_slice(&next, 0, 0), Some((1, 4)));
}

#[test]
fn cancellation_preserves_events_until_a_successful_reset() {
    let mut session = session();
    let event = TickPosition {
        generation: 0,
        tick: 1,
    };
    session.schedule_input(0, event, "abc".into()).unwrap();
    let tick = begin(session);
    assert_eq!(run_slice(&tick, 0, 0), Some((1, 3)));

    let mut session = tick.cancel();
    assert_eq!(session.position().tick, 0);
    assert_eq!(session.states(), &[10]);
    let reset = session.prepare_reset().unwrap();
    assert!(reset.commit(Vec::new()).is_err());

    let tick = begin(session);
    assert_eq!(run_slice(&tick, 0, 0), Some((1, 3)));
    let mut session = tick.cancel();
    let removed = session.prepare_reset().unwrap().commit(vec![0]).unwrap();
    assert_eq!(removed.len(), 1);
    assert_eq!(removed[0].position, event);
    let tick = begin(session);
    assert_eq!(
        tick.target(),
        TickPosition {
            generation: 1,
            tick: 1
        }
    );
    assert!(tick.next_event(0).is_none());
    assert_eq!(tick.states(), &[0]);
}
