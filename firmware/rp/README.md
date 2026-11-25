# Pico・Pico 2 の GPIO ファームウェア

順序 NOR 回路の1 tick を 32 レーンまとめて実行する。物理 GPIO はレーン 0 に接続する。起動時の出力レベルはボード設定で決まり、各 tick の確定後は回路の結果を出力する。

## 回路を選ぶ

NCG2 プロジェクトから配線表を作るには、CLI の `ncg2 rp-plan --project circuitgame2.toml --board board.toml` を使う。配線表を UTF-8 で保存し、環境変数 `NCG2_RP_PROGRAM` にその絶対パスを指定する。ファームウェアのビルドは、ボード名、配線番号、GPIO の範囲と重複を検査する。 [サンプルと設定](https://github.com/neknaj/circuitgame2/tree/main/examples/rp-gpio)

環境変数を指定せずにビルドすると、GP2 の反転を GP3 へ出す組み込み例を使う。この例では起動時の GP3 は Low で、設定周期は 1 ms。

## ビルド

Core リポジトリのルートで、対象のボードに対応するコマンドを実行する。

```sh
rustup target add thumbv6m-none-eabi thumbv8m.main-none-eabihf
cargo build --manifest-path firmware/rp/Cargo.toml --locked --release --target thumbv6m-none-eabi --features pico
cargo build --manifest-path firmware/rp/Cargo.toml --locked --release --target thumbv8m.main-none-eabihf --features pico2
```

出力 ELF は通常 `firmware/rp/target/<ターゲット>/release/ncg2-rp` にある。Pico は UF2 ファミリー `rp2040`、Pico 2 は `rp2350-arm-s` で `elf2uf2-rs convert --family <ファミリー> <ELF> <出力.uf2>` を実行する。ボードを BOOTSEL モードで接続し、UF2 を表示されたドライブにコピーする。 [Raspberry Pi の BOOTSEL 手順](https://www.raspberrypi.com/documentation/microcontrollers/pico-series.html)

組み込み例を確認するときは GND を共通にし、GP2 に 3.3 V ロジックの信号を入れる。GP2 と GP3 をロジックアナライザーで観測すると、次の tick で反転値が現れる設計になっている。端子の位置は、使用するボードのピン配置図で確認する。 [Pico シリーズのピン配置](https://www.raspberrypi.com/documentation/microcontrollers/pico-series.html)

UART・SPI・I²C の接続は実装計画を参照。 [GPU と RP マイコンの実行バックエンド](https://neknaj.github.io/circuitgame2/docs/backends.html)
