//! SPI 配線表のヘッダーを検査し、コントローラーの初期化を生成する。

use std::{collections::BTreeSet, fmt, fmt::Write, num::NonZeroU8, num::NonZeroU32};

use super::{Input, claim_pin, number};

/// RP で使う SPI の通信設定と回路出力。
pub(super) struct Spi {
    /// 配線表で選択した SPI コントローラーの番号。
    pub(super) instance: u8,
    sck: u8,
    mosi: u8,
    miso: u8,
    cs: u8,
    frequency_hz: u32,
    mode: u8,
    least_significant_first: bool,
    timeout_micros: NonZeroU32,
    capacity: NonZeroU8,
    outputs: Vec<usize>,
}

impl Spi {
    /// 4、5行目を読み、通信とピンの割り当て、信号の数を検査する。
    ///
    /// # Errors
    ///
    /// 不正な項目を行番号とともに返す。
    pub(super) fn parse(
        lines: &mut std::str::Lines<'_>,
        claimed: &mut BTreeSet<u8>,
        board: &str,
    ) -> Result<Self, String> {
        let setup = lines.next().unwrap_or_default();
        let outputs = lines.next().unwrap_or_default();
        let mut spi =
            Self::read_setup(setup, claimed, board).map_err(|reason| format!("4行目。{reason}"))?;
        spi.outputs = spi
            .read_outputs(outputs)
            .map_err(|reason| format!("5行目。{reason}"))?;
        Ok(spi)
    }

    fn read_setup(row: &str, claimed: &mut BTreeSet<u8>, board: &str) -> Result<Self, String> {
        let fields: Vec<_> = row.split_ascii_whitespace().collect();
        let [
            "spi",
            instance,
            sck,
            mosi,
            miso,
            cs,
            rate,
            mode,
            order,
            timeout,
            capacity,
        ] = fields.as_slice()
        else {
            return Err(
                "SPI 番号、SCK・MOSI・MISO・CS、周波数、モード、ビット順、待ち時間、容量が必要。"
                    .into(),
            );
        };
        let instance: u8 = number(instance)?;
        if instance > 1 {
            return Err("SPI 番号は 0 または 1 が必要。".into());
        }
        let sck = signal_pin(sck, claimed, instance, 2, "SCK")?;
        let mosi = signal_pin(mosi, claimed, instance, 3, "MOSI")?;
        let miso = signal_pin(miso, claimed, instance, 0, "MISO")?;
        let cs = claim_pin(cs, claimed)?;
        let frequency_hz: u32 = number(rate)?;
        // 既定の clk_peri は Pico で125 MHz、Pico 2 で150 MHz。PL022 は2から65024まで分周できる。
        let clk: u64 = if board == "pico" {
            125_000_000
        } else {
            150_000_000
        };
        let rate = u64::from(frequency_hz);
        if 2 * rate > clk || clk > 65_024 * rate {
            return Err("SPI の周波数が基板の周辺クロックと分周器の範囲外。".into());
        }
        let mode = number(mode)?;
        if mode > 3 {
            return Err("SPI モードは 0 から 3 が必要。".into());
        }
        let least_significant_first = match *order {
            "msb-first" => false,
            "lsb-first" => true,
            _ => return Err("SPI のビット順は msb-first または lsb-first が必要。".into()),
        };
        let timeout_micros = number(timeout)
            .map_err(|_| "SPI の待ち時間はマイクロ秒単位の正の32ビット整数が必要。")?;
        let capacity = number(capacity).map_err(|_| "SPI の容量は 1 から 255 バイトが必要。")?;
        Ok(Self {
            instance,
            sck,
            mosi,
            miso,
            cs,
            frequency_hz,
            mode,
            least_significant_first,
            timeout_micros,
            capacity,
            outputs: Vec::new(),
        })
    }

    fn read_outputs(&self, row: &str) -> Result<Vec<usize>, String> {
        let mut fields = row.split_ascii_whitespace();
        if fields.next() != Some("spi-outputs") {
            return Err("SPI の出力ポート指定が必要。".into());
        }
        let required = 10 + usize::from(self.capacity.get()) * 8;
        let count_error = || format!("SPI には{required}個の回路出力が必要。");
        let mut outputs = Vec::with_capacity(required);
        for _ in 0..required {
            let field = fields.next().ok_or_else(count_error)?;
            outputs.push(number::<u32>(field)? as usize);
        }
        if fields.next().is_some() {
            return Err(count_error());
        }
        Ok(outputs)
    }

    /// 制御信号と受信領域を含む回路入力の数。
    pub(super) fn input_count(&self) -> usize {
        5 + usize::from(self.capacity.get()) * 8
    }

    /// 出力ポート一覧から外れる最初の添字を診断する。
    pub(super) fn validate_outputs(&self, output_count: usize) -> Result<(), String> {
        if let Some(port) = self.outputs.iter().find(|&&port| port >= output_count) {
            return Err(format!("5行目。SPI が参照する出力ポート {port} が範囲外。"));
        }
        Ok(())
    }

    /// 送受信の容量、実際の入出力添字とコントローラー番号を Rust 定数にする。
    pub(super) fn write_constants(&self, result: &mut String, inputs: &[Input]) -> fmt::Result {
        writeln!(result, "const SPI_INSTANCE: u8 = {};", self.instance)?;
        writeln!(result, "const SPI_CAPACITY: usize = {};", self.capacity)?;
        writeln!(
            result,
            "const SPI_OUTPUTS: [usize; {}] = {:?};",
            self.outputs.len(),
            self.outputs
        )?;
        let signals: Vec<_> = inputs
            .iter()
            .map(|input| match input {
                Input::Spi(signal) => Some(*signal),
                _ => None,
            })
            .collect();
        writeln!(
            result,
            "const SPI_INPUTS: [Option<usize>; INPUT_COUNT] = {signals:?};"
        )
    }

    /// 選んだ SPI とピン、DMA チャネルの所有権を開始処理へ渡す。
    pub(super) fn write_start(&self, result: &mut String) -> fmt::Result {
        let Self {
            instance,
            sck,
            mosi,
            miso,
            cs,
            frequency_hz,
            mode,
            least_significant_first,
            timeout_micros,
            ..
        } = self;
        writeln!(
            result,
            "spi::start(spawner, _pins.SPI{instance}, (_pins.PIN_{sck}, _pins.PIN_{mosi}, _pins.PIN_{miso}), (_pins.DMA_CH0, _pins.DMA_CH1), Output::new(_pins.PIN_{cs}, Level::High), spi::Settings {{ frequency_hz: {frequency_hz}, mode: {mode}, least_significant_first: {least_significant_first}, timeout_micros: {timeout_micros} }})?;"
        )
    }
}

fn signal_pin(
    word: &str,
    claimed: &mut BTreeSet<u8>,
    controller: u8,
    offset: u8,
    signal: &str,
) -> Result<u8, String> {
    let pin = claim_pin(word, claimed)?;
    // 両基板の SPI 機能は8ピンごとにコントローラーが切り替わり、同じ信号は4ピンおきに現れる。
    if pin / 8 % 2 != controller || pin % 4 != offset {
        return Err(format!(
            "GP{pin} は SPI{controller} の {signal} に割り当てられない。"
        ));
    }
    Ok(pin)
}
