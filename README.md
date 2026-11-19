# circuitgame2-core

NCG2 の CLI と Web 向けの共通 Rust ライブラリ。現在は回路ソースの字句解析と構文解析を提供する。エディタ向けには、構文エラーを記録しながら S 式の構文木を返す回復解析も提供する。

## 使い方

開発版を試すには、利用側の `Cargo.toml` に依存関係を追加する。

```toml
[dependencies]
circuitgame2-core = { git = "https://github.com/neknaj/circuitgame2-core.git" }
```

次のコードを `src/main.rs` に置いて `cargo run` を実行すると、回路フォームを検査し、最初の宣言が `func` であることを確かめられる。

```rust
use circuitgame2_core::syntax::circuit::{Head, index_headers};

fn main() {
    let source = "(func identity (in x) (out y) (def y x))";
    let circuit = index_headers(source).expect("valid circuit form");
    assert_eq!(circuit.entries[0].head, Head::Func);
}
```

- [API リファレンス](https://neknaj.github.io/circuitgame2-core/)
- [回路文法](https://github.com/neknaj/circuitgame2/blob/main/doc/grammar.md)
- [NCG2 の設計文書](https://github.com/neknaj/circuitgame2/tree/main/doc)

## 開発

Rust のバージョンは [rust-toolchain.toml](rust-toolchain.toml) に固定している。以下のコマンドはリポジトリのルートで実行する。

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
