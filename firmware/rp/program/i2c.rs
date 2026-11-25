//! I²C 配線表のヘッダーを検査し、実行側で使う定数と初期化を生成する。

use std::{collections::BTreeSet, fmt, fmt::Write, num::NonZeroU8, num::NonZeroU32};

use super::{Input, claim_pin, number};

const INPUT_HEADER: usize = 5;
const OUTPUT_HEADER: usize = 25;

/// RP が使う I²C コントローラーと回路の信号割り当て。
pub(super) struct I2c {
    instance: u8,
    sda: u8,
    scl: u8,
    frequency_hz: u32,
    timeout_micros: NonZeroU32,
    capacity: NonZeroU8,
    outputs: Vec<usize>,
}

impl I2c {
    /// 4、5行目を読み、I²C のピンを GPIO と同じ割り当て表に登録する。
    ///
    /// # Errors
    ///
    /// ヘッダーの書式、通信設定、ボードで使用可能なピン、容量に対応する出力数を検査する。
    pub(super) fn parse(
        lines: &mut std::str::Lines<'_>,
        claimed: &mut BTreeSet<u8>,
    ) -> Result<Self, String> {
        let setup = lines.next().unwrap_or_default();
        let outputs = lines.next().unwrap_or_default();
        let (instance, sda, scl, frequency_hz, timeout_micros, capacity) = (|| {
            let fields: Vec<_> = setup.split_ascii_whitespace().collect();
            let [
                "i2c",
                instance,
                sda,
                scl,
                frequency_hz,
                timeout_micros,
                capacity,
            ] = fields.as_slice()
            else {
                return Err("I²C 番号、SDA/SCL ピン、周波数、待ち時間、容量が必要。".into());
            };
            let instance: u8 = number(instance)?;
            if instance > 1 {
                return Err("I²C 番号は 0 または 1 が必要。".into());
            }
            let sda = claim_pin(sda, claimed)?;
            let scl = claim_pin(scl, claimed)?;
            // RP2040 と RP2350 の GPIO 機能選択表で、偶数ピンは SDA、奇数ピンは SCL を担当する。
            if sda % 2 != 0 || sda / 2 % 2 != instance {
                return Err(format!(
                    "GP{sda} は I²C{instance} の SDA に割り当てられない。"
                ));
            }
            if scl % 2 != 1 || scl / 2 % 2 != instance {
                return Err(format!(
                    "GP{scl} は I²C{instance} の SCL に割り当てられない。"
                ));
            }
            let frequency_hz = number(frequency_hz)?;
            if !matches!(frequency_hz, 100_000 | 400_000) {
                return Err("I²C の周波数は 100000 Hz または 400000 Hz が必要。".into());
            }
            let timeout_micros = number::<NonZeroU32>(timeout_micros)
                .map_err(|_| "I²C の待ち時間はマイクロ秒単位の正の32ビット整数が必要。")?;
            let capacity = number::<NonZeroU8>(capacity)
                .map_err(|_| "I²C の容量は 1 から 255 バイトが必要。")?;
            Ok((instance, sda, scl, frequency_hz, timeout_micros, capacity))
        })()
        .map_err(|reason: String| format!("4行目。{reason}"))?;

        let outputs = (|| {
            let mut fields = outputs.split_ascii_whitespace();
            if fields.next() != Some("i2c-outputs") {
                return Err("I²C の出力ポート指定が必要。".into());
            }
            let required = OUTPUT_HEADER + usize::from(capacity.get()) * 8;
            let mut outputs = Vec::with_capacity(required);
            for _ in 0..required {
                let field = fields
                    .next()
                    .ok_or_else(|| format!("I²C には{required}個の回路出力が必要。"))?;
                outputs.push(number::<u32>(field)? as usize);
            }
            if fields.next().is_some() {
                return Err(format!("I²C には{required}個の回路出力が必要。"));
            }
            Ok(outputs)
        })()
        .map_err(|reason: String| format!("5行目。{reason}"))?;

        Ok(Self {
            instance,
            sda,
            scl,
            frequency_hz,
            timeout_micros,
            capacity,
            outputs,
        })
    }

    /// 容量ちょうどのデータ領域を含む回路入力の数。
    pub(super) fn input_count(&self) -> usize {
        INPUT_HEADER + usize::from(self.capacity.get()) * 8
    }

    /// 回路出力が出力ポート一覧の範囲内にあることを確認する。
    ///
    /// # Errors
    ///
    /// 最初の範囲外の添字を返す。
    pub(super) fn validate_outputs(&self, output_count: usize) -> Result<(), String> {
        if let Some(port) = self.outputs.iter().find(|&&port| port >= output_count) {
            return Err(format!("5行目。I²C が参照する出力ポート {port} が範囲外。"));
        }
        Ok(())
    }

    /// 配線表で検査した I²C の信号添字と容量を Rust 定数として出す。
    pub(super) fn write_constants(&self, result: &mut String, inputs: &[Input]) -> fmt::Result {
        writeln!(result, "const I2C_INSTANCE: u8 = {};", self.instance)?;
        writeln!(result, "const I2C_CAPACITY: usize = {};", self.capacity)?;
        writeln!(
            result,
            "const I2C_OUTPUTS: [usize; {}] = {:?};",
            self.outputs.len(),
            self.outputs
        )?;
        let signals: Vec<_> = inputs
            .iter()
            .map(|input| match input {
                Input::I2c(signal) => Some(*signal),
                _ => None,
            })
            .collect();
        writeln!(
            result,
            "const I2C_INPUTS: [Option<usize>; INPUT_COUNT] = {signals:?};"
        )
    }

    /// ピンと周辺機能の所有権を、指定されたコントローラーの開始処理に渡す。
    pub(super) fn write_start(&self, result: &mut String) -> fmt::Result {
        writeln!(
            result,
            "i2c::start{}(spawner, _pins.I2C{}, _pins.PIN_{}, _pins.PIN_{}, {}, {})?;",
            self.instance,
            self.instance,
            self.sda,
            self.scl,
            self.frequency_hz,
            self.timeout_micros
        )
    }
}
