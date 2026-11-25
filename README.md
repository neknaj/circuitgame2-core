# circuitgame2-core

Neknaj Circuit Game 2 の CLI と GUI で使う Rust ライブラリ。NCG2 の回路ソースを解析し、名前解決と型・ビット幅・結線の検査を行う。組み合わせ回路を評価でき、ラッチや RAM を含む順序回路は tick ごとに実行できる。

編集用の API は構文エラーから回復し、診断を返す。NCG2M ではファイルの構文解析と整数式の評価に加え、条件式やリスト演算などを含む補助関数の本体を型検査できる。

CLI で回路を試す手順をプロジェクトの README にまとめている。 [CLI 入門](https://github.com/neknaj/circuitgame2#cli-で回路を試す)

## Rust から使う

以下の例は Rust 1.99.1 で実行できる。利用側の `Cargo.toml` の `[dependencies]` に次の行を追加する。

```toml
circuitgame2-core = { version = "0.1.0", git = "https://github.com/neknaj/circuitgame2-core", rev = "50227bfd6da7573459c179812d55d8d61ec134d9" }
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

## テストと形式検証

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

各処理で証明する性質は検証設計に、コメントと証明の書き方はコーディング規約に記載している。 [検証設計](https://github.com/neknaj/circuitgame2/blob/main/doc/verification.md) · [コーディング規約](https://github.com/neknaj/circuitgame2/tree/main/doc/coding_standards)

## ライセンス

[MIT](LICENSE)
