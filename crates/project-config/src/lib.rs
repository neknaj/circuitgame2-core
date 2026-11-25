//! CLI と GUI が使う TOML の実行設定を、読み込み済みのバイト列から解析する。

use std::{collections::BTreeMap, num::NonZeroU64, ops::Range};

use serde::Deserialize;
pub use toml::{Spanned, Value};

/// プロジェクトの設定ファイル名。
pub const FILE_NAME: &str = "circuitgame2.toml";

/// ソース集合、開始モジュール、外部デバイスや VRAM の設定。
#[derive(Deserialize)]
#[serde(deny_unknown_fields, rename_all = "kebab-case")]
pub struct ProjectConfig {
    /// 設定に書かれた順のソースパスと原文範囲。
    pub sources: Spanned<Vec<Spanned<String>>>,
    /// 実行時の開始モジュールと原文範囲。
    pub entry: Option<Spanned<String>>,
    /// 設定した tick 周期と原文範囲。
    pub tick_ns: Option<Spanned<TickPeriod>>,
    #[serde(default)]
    /// 実行設定に並んだ外部デバイスとその位置。
    pub device: Vec<Spanned<Device>>,
    #[serde(default)]
    /// 設定順に並んだ VRAM の公開指定。
    pub vram: Vec<Vram>,
}

/// TOML に記した正の有理数の tick 周期。
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TickPeriod {
    /// ナノ秒数の分子。
    pub numerator: NonZeroU64,
    /// ナノ秒数の分母。
    pub denominator: NonZeroU64,
}

/// 外部デバイスの種類、配線、種別ごとのオプション。
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Device {
    /// 設定内のインスタンス名と指定箇所。
    pub name: Spanned<String>,
    /// 登録済みデバイス種別と指定箇所。
    pub kind: Spanned<String>,
    /// デバイスポートから回路ポートへの接続先とその原文範囲。
    pub bindings: Spanned<BTreeMap<String, Spanned<String>>>,
    /// 種別ごとのオプションと各値の原文範囲。
    pub options: Option<Spanned<BTreeMap<String, Spanned<Value>>>>,
}

/// 公開名と、RAM の読み出しに対応するルート回路の信号名。
#[derive(Deserialize)]
#[serde(deny_unknown_fields, rename_all = "kebab-case")]
pub struct Vram {
    /// 表示や観測に使う公開名。
    pub name: String,
    /// ルート本体の出力名と、その指定箇所。
    pub read_output: Spanned<String>,
}

/// 設定を読み取れなかった理由。範囲は設定ファイルの原バイト列上の半開区間。
#[derive(Debug, Eq, PartialEq)]
pub enum ConfigError {
    /// 最初に UTF-8 として解釈できなかったバイト範囲。
    InvalidUtf8(Range<usize>),
    /// TOML の文法や項目の型、項目名が設定の形式に合わない。
    InvalidToml {
        /// TOML パーサーが指した設定内の範囲。
        span: Option<Range<usize>>,
        /// TOML パーサーが報告した理由。
        reason: String,
    },
    /// `sources` が空の配列だったときの、その配列の範囲。
    EmptySources(Range<usize>),
}

/// TOML の各値の位置を保存し、実行設定を返す。
///
/// 相対パスや開始モジュール、接続先の解決は呼び出し側が行う。
///
/// # Errors
///
/// UTF-8、TOML の文法や設定項目、空のソース一覧の順に検査し、最初のエラーを返す。
pub fn parse(bytes: &[u8]) -> Result<ProjectConfig, ConfigError> {
    let text = std::str::from_utf8(bytes).map_err(|error| {
        let start = error.valid_up_to();
        let end = error.error_len().map_or(bytes.len(), |width| start + width);
        ConfigError::InvalidUtf8(start..end)
    })?;
    let config: ProjectConfig = toml::from_str(text).map_err(|error| ConfigError::InvalidToml {
        span: error.span(),
        reason: error.message().to_owned(),
    })?;
    if config.sources.get_ref().is_empty() {
        return Err(ConfigError::EmptySources(config.sources.span()));
    }
    Ok(config)
}

#[cfg(test)]
mod tests {
    use super::{ConfigError, parse};

    #[test]
    fn keeps_config_order_and_spans() {
        let source = r#"# 型と位置を確認する
sources = ["main.ncg2", "logic.ncg2"]
entry = "::demo"
tick-ns = { numerator = 9223372036854775807, denominator = 1 }
[[device]]
name = "terminal"
kind = "uart-terminal"
bindings = { tx = "uart-tx" }
options = { baud = 115200 }
[[vram]]
name = "screen"
read-output = "fb-read"
"#;
        let settings = parse(source.as_bytes()).unwrap();
        let paths = settings.sources.get_ref();
        assert_eq!(paths[0].get_ref(), "main.ncg2");
        assert_eq!(paths[1].get_ref(), "logic.ncg2");
        assert_eq!(&source[paths[1].span()], r#""logic.ncg2""#);
        let entry = settings.entry.unwrap();
        assert_eq!(&source[entry.span()], r#""::demo""#);
        assert_eq!(
            settings.tick_ns.unwrap().get_ref().numerator.get(),
            i64::MAX as u64
        );
        let device = &settings.device[0];
        let options = device.get_ref().options.as_ref().unwrap();
        assert_eq!(&source[options.get_ref()["baud"].span()], "115200");
        assert_eq!(&source[settings.vram[0].read_output.span()], r#""fb-read""#);
    }

    #[test]
    fn reports_first_invalid_utf8_or_setting() {
        assert!(matches!(
            parse(b"sources = []\n# \xff"),
            Err(ConfigError::InvalidUtf8(span)) if span == (15..16)
        ));
        assert!(matches!(
            parse(b"sources = []"),
            Err(ConfigError::EmptySources(span)) if span == (10..12)
        ));
        for malformed in [
            "sources = []\nextra = true",
            "sources = [\"x.ncg2\"]\ntick-ns = { numerator = 0, denominator = 1 }",
            "sources = [\"x.ncg2\"]\ntick-ns = { numerator = 9223372036854775808, denominator = 1 }",
            "sources = [\"x.ncg2\"]\n[[device]]\nname = \"d\"\nkind = \"k\"\nbindings = {}\nextra = true",
        ] {
            assert!(matches!(
                parse(malformed.as_bytes()),
                Err(ConfigError::InvalidToml { span: Some(_), .. })
            ));
        }
    }
}
