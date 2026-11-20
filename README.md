# circuitgame2-core

NCG2 の CLI と Web で共用する Rust ライブラリ。回路ソースの厳格解析とエラー回復、プロジェクト内の名前解決、回路の型・幅・結線の検査を提供する。構造体宣言の幅とフィールド型名も検査できる。

ビット列を扱う `func` のうち、信号の転送、定数 `0`・`1`、基底 NOR、信号を直接指定する `bit`・`slice` からなるものをネットリストに変換して評価できる。

## 使い方

Rust 1.99.1 を使う。利用側の `Cargo.toml` に次の依存関係を追加する。

```toml
[dependencies]
circuitgame2-core = { version = "0.1.0", git = "https://github.com/neknaj/circuitgame2-core", rev = "d4673b69a92b7b96d194c39e4322c896a4d663fb" }
```

次のコードを `src/main.rs` に置き、`cargo run` を実行する。2入力の NOR を定義し、入力が両方 `false` のときだけ出力が `true` になることを確かめる。

```rust
use circuitgame2_core::project::{
    SourceSnapshot, check_use_aliases, index_use_targets, parse_circuit_project,
};

fn main() {
    let project = parse_circuit_project(&[SourceSnapshot {
        path: "main.ncg2",
        revision: 1,
        text: "(using nor) (func gate (in x y) (out z) (def z (nor x y)))",
    }])
    .unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let function = aliases.check_bit_func(0, 1, 8).unwrap();
    let lowered = function.lower_bit_func(8).unwrap();
    let netlist = lowered.netlist();

    for x in [false, true] {
        for y in [false, true] {
            assert_eq!(netlist.evaluate(&[x, y]).unwrap(), [!(x || y)]);
        }
    }
}
```

`check_bit_func(0, 1, 8)` の `0` はプロジェクト内のファイルの添字、`1` はそのファイルの厳格索引の添字を表す。`8` はビット幅の上限。ソースでは `(using nor)` の次にある `func` を検査する。

- [API リファレンス](https://neknaj.github.io/circuitgame2-core/)
- [NCG2 の設計と仕様](https://neknaj.github.io/circuitgame2/docs/)
- [不具合報告・質問](https://github.com/neknaj/circuitgame2-core/issues)

## 開発

Rust のバージョンは [rust-toolchain.toml](rust-toolchain.toml) に固定している。以下のコマンドはリポジトリのルートで実行する。

変更箇所に対応するテストターゲットを指定できる。例えば、回復パーサーを変更したときは次を実行する。

```sh
cargo check --workspace --locked
cargo test --locked -p circuitgame2-syntax --test circuit_recovery
```

[CI](.github/workflows/ci.yml) では生成入力を使う差分テストとドキュメントテストを含む全テスト、形式検証、WASM 向けビルドを実行する。ローカルで全体を確認する場合は、次のコマンドと下記の形式検証を実行する。

```sh
cargo test --workspace --locked
cargo build --workspace --locked --target wasm32-unknown-unknown
```

形式検証には [Verus 0.2026.11.02.8bf68ee](https://github.com/verus-lang/verus/releases/tag/release%2F0.2026.11.02.8bf68ee) を使う。配布物を展開し、`cargo-verus` のあるディレクトリを PATH に追加する。

```sh
cargo verus verify --workspace --locked
```

[検証設計](https://github.com/neknaj/circuitgame2/blob/main/doc/verification.md)に、各処理で証明する性質を記載している。

## ライセンス

[MIT](LICENSE)
