use circuitgame2_core::backend::rp::{
    Board, GpioBinding, GpioImageError, GpioOutputPin, I2cImageError, I2cInputSource, I2cPortNames,
    I2cSetup,
};
use circuitgame2_core::project::{
    DeviceBindingsError, DevicePortBindingError, ModuleBodyPosition, SourceSnapshot,
    check_use_aliases, index_use_targets, parse_circuit_project,
};

#[test]
fn binds_i2c_and_gpio_in_declaration_order_with_source_diagnostics() {
    let text = "(using nor) (module main (in gpio rv rr s0 s1 s2 d0 d1 d2 d3 d4 d5 d6 d7)
        (out q) (def q (nor gpio rr)))";
    let source = [SourceSnapshot {
        path: "i2c.ncg2",
        text,
        revision: 4,
    }];
    let project = parse_circuit_project(&source).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let owner = ModuleBodyPosition { file: 0, entry: 1 };
    let setup = I2cSetup {
        instance: 0,
        sda: 0,
        scl: 1,
        frequency_hz: 100_000,
        timeout_micros: 20_000,
    };
    let to = [
        "rr", "rv", "s0", "s1", "s2", "d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
    ];
    let from = ["q"; 33];
    let build = |gpio, to| {
        aliases.build_rp_i2c_image(
            owner,
            Board::Pico2,
            gpio,
            setup,
            I2cPortNames {
                to_circuit: to,
                from_circuit: &from,
            },
            1000,
            64,
            64,
            16,
        )
    };
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
    let image = build(&gpio, &to).unwrap();
    assert_eq!(image.setup(), (Board::Pico2, setup, 1000, 1));
    let (inputs, outputs, request) = image.ports();
    assert_eq!(
        inputs[..3],
        [
            I2cInputSource::Gpio(2),
            I2cInputSource::Controller(1),
            I2cInputSource::Controller(0)
        ]
    );
    assert_eq!(inputs.len(), 14);
    assert_eq!(
        outputs,
        [GpioOutputPin {
            port: 0,
            pin: 3,
            initial_high: true
        }]
    );
    assert_eq!(request, [0; 33]);

    assert!(matches!(
        build(&gpio[1..], &to),
        Err(I2cImageError::Circuit(GpioImageError::MissingInput {
            port: 0
        }))
    ));
    let mut wrong = to;
    wrong[3] = "q";
    assert!(matches!(
        build(&gpio, &wrong),
        Err(I2cImageError::Circuit(GpioImageError::Binding(
            DeviceBindingsError::Binding {
                request: 5,
                error: DevicePortBindingError::OppositeDirection(_),
            }
        )))
    ));
}
