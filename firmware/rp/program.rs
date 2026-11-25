//! ホストが生成した GPIO 配線表を検査し、型付きのファームウェア定数へ変換する。

use std::{collections::BTreeSet, fmt::Write, num::NonZeroU64};

use circuitgame2_packed_nor::{PackedClockedNorPlan32, PackedNorGate32};

struct Output {
    port: usize,
    pin: u8,
    high: bool,
}

pub(crate) struct Program {
    period: NonZeroU64,
    inputs: Vec<u8>,
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
        if lines.next() != Some("ncg2-rp-gpio-v1") {
            return Err("配線表の先頭に ncg2-rp-gpio-v1 が必要。".into());
        }
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
            gates: Vec::new(),
            ports: Vec::new(),
            outputs: Vec::new(),
        };
        let mut claimed = BTreeSet::new();
        for (index, line) in lines.enumerate() {
            let fields: Vec<_> = line.split_ascii_whitespace().collect();
            (|| -> Result<(), String> {
                let pin = |pin: &str, claimed: &mut BTreeSet<u8>| {
                    let pin: u8 = number(pin)?;
                    if exposed(pin) && claimed.insert(pin) {
                        Ok(pin)
                    } else {
                        Err(format!(
                            "GP{pin} は外部端子に出ていないか、すでに使用されている。"
                        ))
                    }
                };
                match fields.as_slice() {
                    ["input", gpio] => program.inputs.push(pin(gpio, &mut claimed)?),
                    ["gate", left, right] => program.gates.push(PackedNorGate32 {
                        left: number::<u32>(left)? as usize,
                        right: number::<u32>(right)? as usize,
                    }),
                    ["port", wire] => program.ports.push(number::<u32>(wire)? as usize),
                    ["output", port, gpio, high @ ("0" | "1")] => program.outputs.push(Output {
                        port: number::<u32>(port)? as usize,
                        pin: pin(gpio, &mut claimed)?,
                        high: *high == "1",
                    }),
                    _ => return Err("不明または不正な配線の指定。".into()),
                }
                Ok(())
            })()
            .map_err(|reason| format!("{}行目。{reason}", index + 4))?;
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
        Ok(program)
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
        writeln!(result, "fn configure_gpio(_pins: embassy_rp::Peripherals) -> ([Input<'static>; INPUT_COUNT], [Output<'static>; OUTPUT_PORTS.len()]) {{").unwrap();
        writeln!(result, "([").unwrap();
        for pin in &self.inputs {
            writeln!(result, "Input::new(_pins.PIN_{pin}, Pull::Down),").unwrap();
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
        writeln!(result, "])\n}}").unwrap();
        result
    }
}
