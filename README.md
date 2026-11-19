# circuitgame2-core

言語仕様と検証方針は [circuitgame2 の設計文書](https://github.com/neknaj/circuitgame2/tree/main/doc)を参照する。

## 検証とビルド

[Verus 0.2026.11.02.8bf68ee](https://github.com/verus-lang/verus/releases/tag/release%2F0.2026.11.02.8bf68ee) の配布物を展開し、`cargo-verus` があるディレクトリを PATH に追加する。Rust のバージョンは `rust-toolchain.toml`、`vstd` のバージョンは `Cargo.toml` で固定している。

```sh
cargo verus verify --locked
cargo test --locked
cargo build --locked --target wasm32-unknown-unknown
```

Verus では数値アトムの数字部分を基数の規則に従って判定することを検証している。空白、行コメント、裸のアトム、文字列内の通常部分は、それぞれの字句規則で定めた最初の境界までを切り出す。括弧は ASCII の1バイトを、エスケープ直後では UTF-8 の文字を1つ消費する。いずれの分割でも元のバイト列を保存する。

文字列走査では、各反復で残りの入力が減ること、返す接尾辞が元の入力の UTF-8 境界から始まること、診断範囲が入力内に収まることを検証している。次の字句区間を切り出す処理では、1バイト以上を消費し、元の入力の UTF-8 境界から始まる正確な接尾辞を返すことを検証している。

厳格解析と回復解析で共用する走査ループでは、字句区間の両端が UTF-8 境界にあり、走査済みの範囲を欠落や重複なく覆うことを検証している。入力末尾まで走査した場合は、全入力が対象となる。厳格解析がエラーで途中終了する場合は、エラーを検出した字句区間までを対象とする。

裸のアトムは名前、パス、数値の分類を検証済みである。文字列の受理条件、構文木の文法適合、診断と回復の契約は引き続き検証対象とする。
