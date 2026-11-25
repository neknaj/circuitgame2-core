use circuitgame2_core::backend::rp::{
    Assignment, AssignmentError, Board, Controller, PinSite, Signal, check_assignments,
};

#[test]
fn accepts_disjoint_gpio_uart_spi_and_i2c_on_both_pico_headers() {
    let assignments = [
        Assignment::GpioInput { pin: 22 },
        Assignment::GpioOutput {
            pin: 28,
            initial_high: true,
        },
        Assignment::Uart {
            instance: 0,
            tx: 0,
            rx: 1,
        },
        Assignment::Spi {
            instance: 0,
            clock: 18,
            mosi: 19,
            miso: 16,
            select: 21,
        },
        Assignment::I2c {
            instance: 1,
            data: 6,
            clock: 7,
        },
    ];
    for board in [Board::Pico, Board::Pico2] {
        let checked = check_assignments(board, &assignments).unwrap();
        assert_eq!(checked.board(), board);
        assert_eq!(checked.assignments(), assignments);
    }
}

#[test]
fn pico_2_uart_auxiliary_pins_are_board_specific() {
    let assignments = [Assignment::Uart {
        instance: 1,
        tx: 26,
        rx: 27,
    }];
    assert!(check_assignments(Board::Pico2, &assignments).is_ok());
    assert_eq!(
        check_assignments(Board::Pico, &assignments).unwrap_err(),
        AssignmentError::UnsupportedSignal {
            site: PinSite {
                assignment: 0,
                signal: Signal::UartTx,
            },
            pin: 26,
            instance: 1,
        },
    );
}

#[test]
fn reports_the_first_pin_or_peripheral_violation_with_its_origin() {
    let uart = Assignment::Uart {
        instance: 1,
        tx: 4,
        rx: 5,
    };
    assert_eq!(
        check_assignments(
            Board::Pico2,
            &[
                uart,
                Assignment::Uart {
                    instance: 1,
                    tx: 23,
                    rx: 5
                }
            ],
        )
        .unwrap_err(),
        AssignmentError::DuplicateInstance {
            first_assignment: 0,
            assignment: 1,
            controller: Controller::Uart,
            instance: 1,
        },
    );
    assert_eq!(
        check_assignments(
            Board::Pico,
            &[Assignment::I2c {
                instance: 2,
                data: 0,
                clock: 25
            }]
        )
        .unwrap_err(),
        AssignmentError::UnknownInstance {
            assignment: 0,
            controller: Controller::I2c,
            instance: 2,
        },
    );
    assert_eq!(
        check_assignments(Board::Pico, &[Assignment::GpioInput { pin: 25 }]).unwrap_err(),
        AssignmentError::UnexposedPin {
            site: PinSite {
                assignment: 0,
                signal: Signal::GpioInput
            },
            pin: 25,
        },
    );
    let spi = Assignment::Spi {
        instance: 0,
        clock: 2,
        mosi: 3,
        miso: 0,
        select: 3,
    };
    assert_eq!(
        check_assignments(Board::Pico, &[uart, spi]).unwrap_err(),
        AssignmentError::DuplicatePin {
            first: PinSite {
                assignment: 1,
                signal: Signal::SpiMosi
            },
            site: PinSite {
                assignment: 1,
                signal: Signal::SpiSelect
            },
            pin: 3,
        },
    );
    assert_eq!(
        check_assignments(Board::Pico, &[Assignment::GpioInput { pin: 4 }, uart]).unwrap_err(),
        AssignmentError::DuplicatePin {
            first: PinSite {
                assignment: 0,
                signal: Signal::GpioInput
            },
            site: PinSite {
                assignment: 1,
                signal: Signal::UartTx
            },
            pin: 4,
        },
    );
}
