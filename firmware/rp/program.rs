//! ホストが生成した RP 配線表を検査し、型付きのファームウェア定数へ変換する。

use std::{collections::BTreeSet, fmt::Write, num::NonZeroU64};

use circuitgame2_packed_nor::{PackedClockedNorPlan32, PackedNorGate32};

struct Output {
    port: usize,
    pin: u8,
    high: bool,
}

enum Input {
    Gpio(u8),
    Uart(usize),
}

struct Uart {
    instance: u8,
    tx: u8,
    rx: u8,
    baud: u32,
    outputs: [usize; 11],
}

pub(crate) struct Program {
    period: NonZeroU64,
    inputs: Vec<Input>,
    uart: Option<Uart>,
    gates: Vec<PackedNorGate32>,
    ports: Vec<usize>,
    outputs: Vec<Output>,
}

// 外部ヘッダーに出ている GPIO は Pico と Pico 2 で共通。
fn exposed(pin: u8) -> bool {
    pin <= 22 || (26..=28).contains(&pin)
}

fn number<T: std::str::FromStr>(word: &str) -> Result<T, String> {
    if !word.is_empty()
        && word.bytes().all(|b| b.is_ascii_digit())
        && let Ok(value) = word.parse()
    {
        return Ok(value);
    }
    Err(format!("整数の指定を読めない。{word:?}"))
}

impl Program {
    pub(crate) fn example(board: &str) -> Result<Self, String> {
        Self::parse(
            &format!(
                "ncg2-rp-gpio-v1\nboard {board}\nperiod-us 1000\ninput 2\ngate 0 0\nport 1\noutput 0 3 0\n"
            ),
            board,
        )
    }

    pub(crate) fn parse(text: &str, expected_board: &str) -> Result<Self, String> {
        let mut lines = text.lines();
        let has_uart = match lines.next() {
            Some("ncg2-rp-gpio-v1") => false,
            Some("ncg2-rp-uart-v1") => true,
            _ => return Err("RP 配線表の形式を識別できない。".into()),
        };
        let board = lines.next().and_then(|line| line.strip_prefix("board "));
        if board != Some(expected_board) {
            return Err(format!(
                "2行目のボードは {expected_board} である必要がある。"
            ));
        }
        let period = lines
            .next()
            .and_then(|line| line.strip_prefix("period-us "))
            .ok_or("3行目にマイクロ秒単位の period-us が必要。")
            .and_then(|value| {
                number::<NonZeroU64>(value).map_err(|_| "3行目の period-us は正の整数が必要。")
            })?;
        let mut program = Self {
            period,
            inputs: Vec::new(),
            uart: None,
            gates: Vec::new(),
            ports: Vec::new(),
            outputs: Vec::new(),
        };
        let mut claimed = BTreeSet::new();
        let mut uart_inputs = BTreeSet::new();
        if has_uart {
            let fields: Vec<_> = lines
                .next()
                .unwrap_or_default()
                .split_ascii_whitespace()
                .collect();
            let ["uart", instance, tx, rx, baud] = fields.as_slice() else {
                return Err("4行目に UART 番号、TX/RX ピンとボーレートが必要。".into());
            };
            let instance: u8 = number(instance)?;
            let tx: u8 = claim_pin(tx, &mut claimed)?;
            let rx: u8 = claim_pin(rx, &mut claimed)?;
            let baud: u32 = number(baud)?;
            if instance > 1 || baud == 0 {
                return Err("UART 番号は 0 または 1、ボーレートは正の整数が必要。".into());
            }
            let fields: Vec<_> = lines
                .next()
                .unwrap_or_default()
                .split_ascii_whitespace()
                .collect();
            let Some(("uart-outputs", ports)) =
                fields.split_first().map(|(kind, ports)| (*kind, ports))
            else {
                return Err("5行目に UART の出力ポート指定が必要。".into());
            };
            if ports.len() != 11 {
                return Err("UART には11個の回路出力が必要。".into());
            }
            let mut outputs = [0; 11];
            for (output, value) in outputs.iter_mut().zip(ports) {
                *output = number::<u32>(value)? as usize;
            }
            program.uart = Some(Uart {
                instance,
                tx,
                rx,
                baud,
                outputs,
            });
        }
        for (index, line) in lines.enumerate() {
            let fields: Vec<_> = line.split_ascii_whitespace().collect();
            (|| -> Result<(), String> {
                match fields.as_slice() {
                    ["input", gpio] => program
                        .inputs
                        .push(Input::Gpio(claim_pin(gpio, &mut claimed)?)),
                    ["input-uart", words @ ..] if has_uart => {
                        let signal = uart_input(words)?;
                        if !uart_inputs.insert(signal) {
                            return Err("同じ UART 信号が複数の回路入力を駆動している。".into());
                        }
                        program.inputs.push(Input::Uart(signal));
                    }
                    ["gate", left, right] => program.gates.push(PackedNorGate32 {
                        left: number::<u32>(left)? as usize,
                        right: number::<u32>(right)? as usize,
                    }),
                    ["port", wire] => program.ports.push(number::<u32>(wire)? as usize),
                    ["output", port, gpio, high @ ("0" | "1")] => program.outputs.push(Output {
                        port: number::<u32>(port)? as usize,
                        pin: claim_pin(gpio, &mut claimed)?,
                        high: *high == "1",
                    }),
                    _ => return Err("不明または不正な配線の指定。".into()),
                }
                Ok(())
            })()
            .map_err(|reason| format!("{}行目。{reason}", index + if has_uart { 6 } else { 4 }))?;
        }
        program
            .inputs
            .len()
            .checked_add(program.gates.len())
            .and_then(|count| count.checked_add(2))
            .and_then(|count| u32::try_from(count).ok())
            .ok_or("RP の配線番号の範囲を超えている。")?;
        PackedClockedNorPlan32::new(program.inputs.len(), &program.gates, &program.ports)
            .map_err(|error| format!("配線番号が不正。{error:?}"))?;
        for output in &program.outputs {
            if output.port >= program.ports.len() {
                return Err(format!(
                    "GP{} が参照する出力ポート {} が範囲外。",
                    output.pin, output.port
                ));
            }
        }
        if let Some(uart) = &program.uart {
            if uart_inputs.len() != 14 {
                return Err("UART の回路入力14個を一つずつ指定する必要がある。".into());
            }
            if uart.outputs.iter().any(|&port| port >= program.ports.len()) {
                return Err("UART が参照する出力ポートが範囲外。".into());
            }
        }
        Ok(program)
    }

    pub(crate) fn has_uart(&self) -> bool {
        self.uart.is_some()
    }

    pub(crate) fn rust(&self) -> String {
        let mut result = format!(
            "const PERIOD_US: u64 = {};\nconst INPUT_COUNT: usize = {};\n",
            self.period,
            self.inputs.len(),
        );
        writeln!(
            result,
            "const GATES: [PackedNorGate32; {}] = [",
            self.gates.len()
        )
        .unwrap();
        for gate in &self.gates {
            writeln!(
                result,
                "PackedNorGate32 {{ left: {}, right: {} }},",
                gate.left, gate.right
            )
            .unwrap();
        }
        writeln!(
            result,
            "];\nconst PORTS: [usize; {}] = {:?};",
            self.ports.len(),
            self.ports
        )
        .unwrap();
        write!(
            result,
            "const OUTPUT_PORTS: [usize; {}] = [",
            self.outputs.len()
        )
        .unwrap();
        for output in &self.outputs {
            write!(result, "{},", output.port).unwrap();
        }
        writeln!(result, "];").unwrap();
        if let Some(uart) = &self.uart {
            writeln!(result, "const UART_INSTANCE: u8 = {};", uart.instance).unwrap();
            writeln!(
                result,
                "const UART_OUTPUTS: [usize; 11] = {:?};",
                uart.outputs
            )
            .unwrap();
            let signals: Vec<_> = self
                .inputs
                .iter()
                .map(|input| match input {
                    Input::Gpio(_) => None,
                    Input::Uart(signal) => Some(*signal),
                })
                .collect();
            writeln!(
                result,
                "const UART_INPUTS: [Option<usize>; INPUT_COUNT] = {signals:?};"
            )
            .unwrap();
            writeln!(result, "fn configure_gpio(spawner: Spawner, _pins: embassy_rp::Peripherals) -> Option<([Option<Input<'static>>; INPUT_COUNT], [Output<'static>; OUTPUT_PORTS.len()])> {{").unwrap();
            writeln!(
                result,
                "uart::start(spawner, _pins.UART{}, _pins.PIN_{}, _pins.PIN_{}, {}, {})?;",
                uart.instance, uart.tx, uart.rx, uart.instance, uart.baud
            )
            .unwrap();
            writeln!(result, "Some(([").unwrap();
        } else {
            writeln!(result, "fn configure_gpio(_pins: embassy_rp::Peripherals) -> ([Input<'static>; INPUT_COUNT], [Output<'static>; OUTPUT_PORTS.len()]) {{").unwrap();
            writeln!(result, "([").unwrap();
        }
        for input in &self.inputs {
            match (input, self.has_uart()) {
                (Input::Gpio(pin), false) => {
                    writeln!(result, "Input::new(_pins.PIN_{pin}, Pull::Down),").unwrap()
                }
                (Input::Gpio(pin), true) => {
                    writeln!(result, "Some(Input::new(_pins.PIN_{pin}, Pull::Down)),").unwrap()
                }
                (Input::Uart(_), _) => writeln!(result, "None,").unwrap(),
            }
        }
        writeln!(result, "], [").unwrap();
        for output in &self.outputs {
            let level = if output.high { "High" } else { "Low" };
            writeln!(
                result,
                "Output::new(_pins.PIN_{}, Level::{level}),",
                output.pin
            )
            .unwrap();
        }
        writeln!(result, "]){}\n}}", if self.has_uart() { ")" } else { "" }).unwrap();
        result
    }
}

fn claim_pin(pin: &str, claimed: &mut BTreeSet<u8>) -> Result<u8, String> {
    let pin: u8 = number(pin)?;
    if exposed(pin) && claimed.insert(pin) {
        Ok(pin)
    } else {
        Err(format!(
            "GP{pin} は外部端子に出ていないか、すでに使用されている。"
        ))
    }
}

fn uart_input(words: &[&str]) -> Result<usize, String> {
    match words {
        ["rx-data", bit] => {
            let bit: u8 = number(bit)?;
            if bit < 8 {
                Ok(usize::from(bit))
            } else {
                Err("UART の受信ビット番号は 0 から 7。".into())
            }
        }
        ["rx-valid"] => Ok(8),
        ["rx-framing"] => Ok(9),
        ["rx-overrun"] => Ok(10),
        ["tx-ready"] => Ok(11),
        ["tx-done"] => Ok(12),
        ["tx-ok"] => Ok(13),
        _ => Err("不明な UART 入力。".into()),
    }
}
