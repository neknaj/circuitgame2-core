//! ボタンのイベントを、回路とデバイスの共通 tick で記録し再生する。

use circuitgame2_core::{
    device::{
        ButtonInput, DeviceEvent, DeviceStateSession, PendingDeviceStateTick, ScheduleInputError,
        StatefulInputError, button_port_request,
    },
    project::{
        ClockedModuleVmLimits, DevicePortMap, ModuleBodyPosition, PortDirection, SourceSnapshot,
        check_use_aliases, index_use_targets, parse_circuit_project,
    },
    time::TickPosition,
};

type Session = DeviceStateSession<ButtonInput, (), bool>;
type RecordedInput = (TickPosition, usize, ButtonInput);

fn fixture() -> (Session, DevicePortMap) {
    let sources = [SourceSnapshot {
        path: "main.ncg2",
        revision: 1,
        text: "(using nor) (module main (in aux left right) (out left right aux))",
    }];
    let project = parse_circuit_project(&sources).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let lowered = aliases
        .lower_clocked_device_vm(
            ModuleBodyPosition { file: 0, entry: 1 },
            ClockedModuleVmLimits {
                width: 1,
                wiring_bits: 3,
                gates: 0,
                state_bits: 0,
            },
            &[button_port_request("left"), button_port_request("right")],
        )
        .unwrap();
    lowered.into_device_state_session(vec![false; 2])
}

// 標準デバイスの評価器を差し込む位置で、レベル式ボタンの状態遷移を再現する。
fn prepare(
    tick: &PendingDeviceStateTick<'_, ButtonInput, (), bool>,
    ports: &DevicePortMap,
    aux: bool,
) -> (Vec<bool>, Vec<bool>) {
    let mut states = tick.states().to_vec();
    let mut from = 0;
    while let Some((index, event)) = tick.next_event(from) {
        let DeviceEvent::Input { instance, payload } = event.payload else {
            panic!("ボタンの応答を予約した");
        };
        states[instance] = payload == ButtonInput::Press;
        from = index + 1;
    }
    let mut input = vec![false; ports.frame_len(PortDirection::Input)];
    input[0] = aux;
    for (index, &state) in states.iter().enumerate() {
        ports.write_input(index, &mut input, &[state]).unwrap();
    }
    (states, input)
}

fn run_tick(session: &mut Session, ports: &DevicePortMap, aux: bool) -> Vec<RecordedInput> {
    let tick = session.prepare_tick().unwrap();
    let (next, input) = prepare(&tick, ports, aux);
    let result = tick.commit::<(), ()>(next, &input, &[]).unwrap();
    assert_eq!(result.outgoing.len(), 0);
    result
        .consumed
        .into_iter()
        .map(|event| {
            let DeviceEvent::Input { instance, payload } = event.payload else {
                panic!("ボタンの応答を消費した");
            };
            (event.position, instance, payload)
        })
        .collect()
}

#[test]
fn records_and_replays_named_buttons_at_committed_ticks() {
    use ButtonInput::{Press, Release};
    let (mut session, ports) = fixture();
    let first = TickPosition {
        generation: 0,
        tick: 1,
    };
    let second = TickPosition {
        generation: 0,
        tick: 2,
    };
    let scheduled = [
        (first, 0, Press),
        (second, 1, Release),
        (first, 0, Release),
        (first, 0, Press),
        (first, 1, Press),
        (second, 1, Release),
    ];
    for &(when, instance, payload) in &scheduled {
        session.schedule_input(instance, when, payload).unwrap();
    }

    assert_eq!(session.output(), &[false, false, false]);
    let tick = session.prepare_tick().unwrap();
    assert_eq!(tick.target(), first);
    assert_eq!(tick.previous_output(), &[false, false, false]);
    let (next, _) = prepare(&tick, &ports, true);
    assert_eq!(next, &[true, true]);
    tick.cancel();
    assert_eq!(
        session.position(),
        TickPosition {
            generation: 0,
            tick: 0
        }
    );
    assert_eq!(session.states(), &[false, false]);

    let invalid = session.prepare_tick().unwrap();
    assert!(invalid.commit::<(), ()>(next, &[], &[]).is_err());
    assert_eq!(
        session.position(),
        TickPosition {
            generation: 0,
            tick: 0
        }
    );
    assert_eq!(session.output(), &[false, false, false]);
    assert_eq!(session.states(), &[false, false]);

    let (mut replay, replay_ports) = fixture();
    for (aux, expecting_output) in [
        (true, [true, true, true]),
        (false, [true, false, false]),
        (true, [true, false, true]),
    ] {
        let recorded = run_tick(&mut session, &ports, aux);
        assert_eq!(
            recorded,
            scheduled
                .iter()
                .copied()
                .filter(|(when, _, _)| *when == session.position())
                .collect::<Vec<_>>()
        );
        for &(position, instance, input) in &recorded {
            replay.schedule_input(instance, position, input).unwrap();
        }
        assert_eq!(run_tick(&mut replay, &replay_ports, aux), recorded);
        assert_eq!(session.output(), &expecting_output);
        assert_eq!(session.output(), replay.output());
        assert_eq!(session.states(), replay.states());
    }
}

#[test]
fn resets_buttons_and_rejects_inputs_from_the_old_generation() {
    let (mut session, ports) = fixture();
    let first = TickPosition {
        generation: 0,
        tick: 1,
    };
    let later = TickPosition {
        generation: 0,
        tick: 2,
    };
    session
        .schedule_input(0, first, ButtonInput::Press)
        .unwrap();
    assert_eq!(run_tick(&mut session, &ports, false).len(), 1);
    session
        .schedule_input(1, later, ButtonInput::Press)
        .unwrap();

    let reset = session.prepare_reset().unwrap();
    assert!(reset.commit(vec![false]).is_err());
    assert_eq!(session.position(), first);
    assert_eq!(session.states(), &[true, false]);
    assert_eq!(session.output(), &[true, false, false]);

    let discarded = session
        .prepare_reset()
        .unwrap()
        .commit(vec![false; 2])
        .unwrap();
    assert_eq!(discarded.len(), 1);
    assert_eq!(discarded[0].position, later);
    assert_eq!(
        session.position(),
        TickPosition {
            generation: 1,
            tick: 0
        }
    );
    assert_eq!(session.states(), &[false, false]);
    assert_eq!(session.output(), &[false, false, false]);
    assert_eq!(
        session.schedule_input(1, later, ButtonInput::Press),
        Err(StatefulInputError::Schedule(
            ScheduleInputError::DifferentGeneration
        ))
    );
    assert!(run_tick(&mut session, &ports, false).is_empty());
    assert_eq!(session.output(), &[false, false, false]);
}
