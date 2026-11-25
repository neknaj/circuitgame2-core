use circuitgame2_core::backend::rp::{AssignmentError, Board, GpioBinding, GpioImageError, GpioOutputPin};
use circuitgame2_core::project::{
    DeviceBindingsError, DevicePortBindingError, ModuleBodyPosition, SourceSnapshot, check_use_aliases,
    index_use_targets, parse_circuit_project,
};

const SOURCE: &str = "(using nor) (module main (in a b) (out a n) (def n (nor a b)))";
const ROOT: ModuleBodyPosition = ModuleBodyPosition { file: 0, entry: 1 };

#[test]
fn builds_one_layout_with_gpio_in_declaration_order() {
    let project = parse_circuit_project(&[SourceSnapshot { path: "main.ncg2", text: SOURCE, revision: 1 }]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let bindings = [
        GpioBinding::Output { port: "n", pin: 18, initial_high: true },
        GpioBinding::Input { port: "b", pin: 3 },
        GpioBinding::Output { port: "a", pin: 19, initial_high: false },
        GpioBinding::Input { port: "a", pin: 2 },
        GpioBinding::Output { port: "n", pin: 27, initial_high: false },
    ];
    let image = aliases.build_rp_gpio_image(ROOT, Board::Pico2, &bindings, 100, 64, 16, 16).unwrap();
    assert_eq!(image.board(), Board::Pico2);
    assert_eq!(image.tick_micros(), 100);
    assert_eq!(image.input_pins(), &[2, 3]);
    assert_eq!(image.output_pins(), &[
        GpioOutputPin { port: 0, pin: 19, initial_high: false },
        GpioOutputPin { port: 1, pin: 18, initial_high: true },
        GpioOutputPin { port: 1, pin: 27, initial_high: false },
    ]);
    assert_eq!(image.layout().input_count(), 2);
    assert_eq!(image.layout().outputs(), &[0, 2]);
    assert_eq!((image.layout().gates()[0].left, image.layout().gates()[0].right), (0, 1));
}

#[test]
fn reports_physical_and_source_binding_diagnostics() {
    let project = parse_circuit_project(&[SourceSnapshot { path: "main.ncg2", text: SOURCE, revision: 1 }]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let build = |bindings| aliases.build_rp_gpio_image(ROOT, Board::Pico, bindings, 100, 64, 16, 16);
    let unexposed = [GpioBinding::Input { port: "a", pin: 23 }];
    assert!(matches!(build(&unexposed),
        Err(GpioImageError::Pin(AssignmentError::UnexposedPin { pin: 23, .. }))));
    let wrong_direction = [GpioBinding::Input { port: "n", pin: 2 }];
    assert!(matches!(build(&wrong_direction), Err(GpioImageError::Binding(DeviceBindingsError::Binding {
        request: 0, error: DevicePortBindingError::OppositeDirection(_),
    }))));
    let second_only = [GpioBinding::Input { port: "b", pin: 3 }];
    assert!(matches!(build(&second_only), Err(GpioImageError::MissingInput { port: 0 })));
}
