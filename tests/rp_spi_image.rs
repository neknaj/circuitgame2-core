use circuitgame2_core::backend::rp::{
    AssignmentError, Board, GpioBinding, GpioImageError, GpioOutputPin, PeripheralInputSource,
    Signal, SpiBitOrder, SpiImageError, SpiPortNames, SpiSettingError, SpiSetup,
};
use circuitgame2_core::project::{
    DeviceBindingsError, DevicePortBindingError, ModuleBodyPosition, SourceSnapshot,
    check_use_aliases, index_use_targets, parse_circuit_project,
};

#[test]
fn spi_binding_preserves_port_order_and_reports_the_first_error() {
    let source = [SourceSnapshot {
        path: "spi.ncg2",
        text: "(using nor) (module main (in rv gpio rr s0 s1 s2 d0 d1 d2 d3 d4 d5 d6 d7)
            (out q) (def q (nor gpio rr)))",
        revision: 1,
    }];
    let project = parse_circuit_project(&source).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let valid = SpiSetup {
        instance: 0,
        sck: 18,
        mosi: 19,
        miso: 16,
        cs: 20,
        frequency_hz: 1_000_000,
        mode: 3,
        bit_order: SpiBitOrder::LeastSignificantFirst,
        timeout_micros: 20_000,
    };
    let to = [
        "rr", "rv", "s0", "s1", "s2", "d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
    ];
    let from = ["q"; 18];
    let gpio = [
        GpioBinding::Input {
            port: "gpio",
            pin: 2,
        },
        GpioBinding::Output {
            port: "q",
            pin: 3,
            initial_high: true,
        },
    ];
    let build = |setup, gpio, to, tick_micros| {
        aliases.build_rp_spi_image(
            ModuleBodyPosition { file: 0, entry: 1 },
            Board::Pico2,
            gpio,
            setup,
            SpiPortNames {
                to_circuit: to,
                from_circuit: &from,
            },
            tick_micros,
            64,
            64,
            16,
        )
    };
    let image = build(valid, &gpio, &to, 1000).unwrap();
    assert_eq!(image.setup(), (Board::Pico2, valid, 1000, 1));
    let (inputs, outputs, request) = image.ports();
    assert_eq!(
        inputs[..3],
        [
            PeripheralInputSource::Controller(1),
            PeripheralInputSource::Gpio(2),
            PeripheralInputSource::Controller(0),
        ]
    );
    assert_eq!(inputs.len(), 14);
    assert_eq!(
        outputs,
        [GpioOutputPin {
            port: 0,
            pin: 3,
            initial_high: true,
        }]
    );
    assert_eq!(request, [0; 18]);
    assert!(matches!(
        build(valid, &gpio[1..], &to, 1000),
        Err(SpiImageError::Circuit(GpioImageError::MissingInput {
            port: 1
        }))
    ));
    let mut wrong_direction = to;
    wrong_direction[3] = "q";
    assert!(matches!(
        build(valid, &gpio, &wrong_direction, 1000),
        Err(SpiImageError::Circuit(GpioImageError::Binding(
            DeviceBindingsError::Binding {
                request: 5,
                error: DevicePortBindingError::OppositeDirection(_),
            }
        )))
    ));
    let conflicting_cs = SpiSetup { cs: 3, ..valid };
    assert!(matches!(
        build(conflicting_cs, &gpio, &wrong_direction, 1000),
        Err(SpiImageError::Circuit(GpioImageError::Pin(
            AssignmentError::DuplicatePin { site, pin: 3, .. }
        ))) if site.assignment == 2 && site.signal == Signal::SpiSelect
    ));
    let bad_mode_and_clock = SpiSetup {
        mode: 4,
        frequency_hz: 0,
        ..valid
    };
    assert!(matches!(
        build(bad_mode_and_clock, &gpio, &to, 0),
        Err(SpiImageError::Circuit(GpioImageError::ZeroTickPeriod))
    ));
    assert!(matches!(
        build(bad_mode_and_clock, &gpio, &to, 1000),
        Err(SpiImageError::Setting(SpiSettingError::Mode))
    ));
    assert!(matches!(
        build(
            SpiSetup {
                frequency_hz: 2306,
                ..valid
            },
            &gpio,
            &to,
            1000
        ),
        Err(SpiImageError::Setting(SpiSettingError::Frequency))
    ));
    assert!(matches!(
        build(valid, &gpio, &to[..12], 1000),
        Err(SpiImageError::Setting(SpiSettingError::PortCounts))
    ));
}
