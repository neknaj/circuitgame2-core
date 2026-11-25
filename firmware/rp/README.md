# Pico・Pico 2 の GPIO 実行例

GP2 を入力、GP3 を出力として使う。起動時に GP3 を Low に設定し、各 tick で GP2 を読み取る。NOR の両入力に同じ値を渡すので、初回の tick 以降は GP3 に GP2 の反転値が現れる。tick の間隔は 1 ms。端子の位置は、使用するボードのピン配置図で確認する。 [Pico シリーズのピン配置](https://www.raspberrypi.com/documentation/microcontrollers/pico-series.html)

同じ回路を 32 レーンで実行する。GP2 と GP3 はレーン 0 に接続し、残りのレーンには 0 を入力する。証明済みの NOR カーネルと、指定したレーンだけを読み書きする関数を使う。

## ビルド

Core リポジトリのルートから実行する。

```sh
rustup target add thumbv6m-none-eabi thumbv8m.main-none-eabihf
cargo build --manifest-path firmware/rp/Cargo.toml --locked --release --target thumbv6m-none-eabi --features pico
cargo build --manifest-path firmware/rp/Cargo.toml --locked --release --target thumbv8m.main-none-eabihf --features pico2
```

`elf2uf2-rs convert` で ELF を UF2 に変換するときは、Pico に `rp2040`、Pico 2 に `rp2350-arm-s` を指定する。書き込み後は GND を共通にし、GP2 に 3.3 V ロジックの信号を入力する。同じロジックアナライザーで GP2 と GP3 を観測し、次の tick で反転値が現れることを確かめる。

この例ではファームウェアに固定の回路とピンを指定する。プロジェクトからのイメージ生成や UART・SPI・I²C の接続は実装計画を参照。 [GPU と RP マイコンの実行バックエンド](https://neknaj.github.io/circuitgame2/docs/backends.html)
