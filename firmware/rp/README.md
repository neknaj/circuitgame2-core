# Pico・Pico 2 のファームウェア

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

## 名前付き回路を UART につなぐ

`ncg2 rp-plan` に UART と GPIO の設定を渡すと、ファームウェアで使う配線表を生成できる。
UART の回路ポートには単一ビットの名前を指定し、`rx-data` と `tx-data` は最下位ビットから8個並べる。回路の各入力に割り当てる駆動元は一つ。GPIO と UART の両方に同じ入力を指定すると、`rp-plan` が重複を報告する。
UART0 と UART1 のいずれか1系統を選び、TX/RX を指定する。GPIO のみの設定は従来の `ncg2-rp-gpio-v1` を使う。

```sh
ncg2 rp-plan --project circuitgame2.toml --board board.toml > board.rp
NCG2_RP_PROGRAM="$PWD/board.rp" cargo build --manifest-path firmware/rp/Cargo.toml --locked --release --target thumbv6m-none-eabi --features pico,uart --bin ncg2-rp
```

Pico 2 では `--target thumbv8m.main-none-eabihf --features pico2,uart` を使う。配線表には UTF-8 のテキストを指定する。ボーレートがボードの周辺クロックと Embassy の分周値で設定できない場合、ファームウェアは UART を起動せずに停止する。回線は 8N1 で、ハードウェアによるフロー制御は使わない。

tick の開始時に、直前に確定した回路出力と今回のデバイス入力を照合する。`rx-valid` と `rx-ready` がともに1なら、今回の受信イベントを回路に渡す。回路が受け取るまで受信データと異常フラグを保持する。フレーミング等の異常は `rx-framing`、受信列のあふれは `rx-overrun` で示す。受信列のあふれはまとめて通知する。

`tx-valid` と `tx-ready` がともに1の tick が確定すると、送信要求を通信タスクへ渡す。一度に1件を処理し、完了通知を要求 ID と世代で照合する。届いた結果は `tx-done` と `tx-ok` で示し、回路が `tx-done-ready` を1にするまで保持する。異常終了した送信は自動で再試行しない。

tick の期限を超えた場合、候補の回路状態と要求を確定せずに実行を止める。同じ tick を再実行する入口は設けていない。生成したファームウェアはボードの reset で、UART、待ち行列、台帳を初期化する。通信ピンで既にやり取りされたデータは、ボードの状態と別に扱う。

## UART の折り返し例

`ncg2-rp-uart` は UART0 で受信した1バイトを、組み込みの回路のビット入出力を通して送り返す。この実行例では組み込みの配線を使う。Pico と Pico 2 のどちらも 115200 baud、8N1、フロー制御なしで動作する。

```sh
cargo build --manifest-path firmware/rp/Cargo.toml --locked --release --target thumbv6m-none-eabi --features pico,uart --bin ncg2-rp-uart
cargo build --manifest-path firmware/rp/Cargo.toml --locked --release --target thumbv8m.main-none-eabihf --features pico2,uart --bin ncg2-rp-uart
```

出力 ELF の名前は `ncg2-rp-uart`。上の手順と同じ UF2 ファミリーを指定して変換する。3.3 V ロジックの UART アダプターを接続し、1バイトずつ送って折り返しを確認する。

| 端子 | 接続または観測 |
| --- | --- |
| GND | アダプターの GND |
| GP0 | アダプターの RX |
| GP1 | アダプターの TX |
| GP2 | GND に接続すると論理 reset を1回行う |
| GP3 | 診断を検出すると High になり、論理 reset で Low に戻る |
| GP4 | 1 ms 周期の各 tick が確定するたびに反転する |

tick は到着済みのイベントだけを確認する。送信タスクは tick の確定後に受け取った要求を処理し、最大20 ms 待って完了または失敗を返す。完了は要求 ID と reset 世代を照合し、次の tick に渡す。受信エラー、受信列のあふれ、送信失敗、tick の期限超過は GP3 に出る。

論理 reset は取り込み済みの旧世代のイベントと完了通知を破棄し、旧世代の送信データを追加でキューに入れる処理を打ち切る。UART の送信レジスタや割り込みバッファーに渡したバイトは物理ポートから送信され得る。受信バイトの世代は、受信タスクが UART バッファーから取り出した時点で付ける。

## SPI の折り返し例

`ncg2-rp-spi` は SPI0 の MOSI と MISO をつないで、送信したデータを同じ転送で受信する組み込み例である。クロックは 1 MHz を指定する。モード3では、クロックが待機中に High となり、2番目のエッジでデータを取り込む。GPIO の CS は取引中だけ Low にする。RP のハードウェアは MSB-first 固定なので、この例では送信前と受信後に各バイトのビットを反転して LSB-first に対応する。 [Pico SDK の SPI 設定](https://github.com/raspberrypi/pico-sdk/blob/master/src/rp2_common/hardware_spi/include/hardware/spi.h#L247)

| Pico・Pico 2 | 接続または観測 |
| --- | --- |
| GP2 | SCK |
| GP3、GP4 | MOSI と MISO をジャンパーでつなぐ |
| GP5 | CS。転送中は Low |
| GP6 | 転送または tick が失敗すると High |
| GP7 | 1 ms 周期の tick が確定するたびに反転 |
| GP8 | `0x12 0x80` の折り返しを受け取ると High |

以前の手順で環境変数 `NCG2_RP_PROGRAM` を設定した場合は、解除してからビルドする。

```sh
cargo build --manifest-path firmware/rp/Cargo.toml --locked --release --target thumbv6m-none-eabi --features pico,spi --bin ncg2-rp-spi
cargo build --manifest-path firmware/rp/Cargo.toml --locked --release --target thumbv8m.main-none-eabihf --features pico2,spi --bin ncg2-rp-spi
```

出力 ELF は `ncg2-rp-spi`。UF2 への変換は対象ボードの手順に従う。 [ビルド](#ビルド)

回路は 250 tick ごとに要求信号を立てる。次の tick が確定すると、通信タスクが2バイトを同時に送受信する。完了は要求 ID と reset 世代を照合して次の入力に載せる。タイムアウトは 20 ms。折り返しデータの不一致やタイムアウトの後は新しい取引を止め、ボードの reset で再開できる。

## I²C で LM75B の設定を読む

`ncg2-rp-i2c` は I²C0 を 100 kHz で使う組み込み例。LM75B のアドレス端子 A2〜A0 を Low にすると、7ビットアドレスは `0x48` になる。LM75B を 3.3 V で動かし、SDA と SCL を 3.3 V にプルアップする。基板側の内部プルアップは無効にしている。 [LM75B データシート](https://www.nxp.com/docs/en/data-sheet/LM75B.pdf)

| Pico・Pico 2 | LM75B との接続または観測 |
| --- | --- |
| GND | LM75B の GND |
| GP0 | SDA |
| GP1 | SCL |
| GP3 | 通信エラーまたは tick の期限超過で High になる |
| GP4 | 1 ms 周期の tick が確定するたびに反転する |
| GP5 | 最後に読み出した設定レジスタのシャットダウンビットを出す |

以前の手順で環境変数 `NCG2_RP_PROGRAM` を設定した場合は、解除してからビルドする。

```sh
cargo build --manifest-path firmware/rp/Cargo.toml --locked --release --target thumbv6m-none-eabi --features pico,i2c --bin ncg2-rp-i2c
cargo build --manifest-path firmware/rp/Cargo.toml --locked --release --target thumbv8m.main-none-eabihf --features pico2,i2c --bin ncg2-rp-i2c
```

出力 ELF は `ncg2-rp-i2c`。UF2 への変換は対象ボードの手順に従う。 [ビルド](#ビルド)

回路は 250 tick ごとに要求信号を立てる。次の tick が確定すると、通信タスクがポインター `0x01` を送り、反復 START で1バイト読む。完了は要求 ID と世代を照合して回路に渡す。tick の確定後に GP5 に値が出る。LM75B の設定が初期値なら GP5 は Low になる。

通信エラーや 20 ms のタイムアウトが起きると GP3 は High になり、新規の読み出しは停止する。GP4 が反転を続けていれば回路の tick は進んでいる。配線を確認してからボードを reset すると、通信を再開できる。

## 名前付き回路を I²C につなぐ

`ncg2 rp-plan --project circuitgame2.toml --board board.toml` で配線表を作る。ボード設定の `[i2c]` にピンと回路ポートを指定する。配線表を UTF-8 で保存し、その絶対パスを `NCG2_RP_PROGRAM` に指定して `ncg2-rp` をビルドする。Pico の機能指定は `pico,i2c`、Pico 2 は `pico2,i2c`。 [回路・設定・実行手順](https://github.com/neknaj/circuitgame2/tree/main/examples/rp-i2c-lm75b)

次の tick の開始時刻までに処理が終わらないと、基板の LED が点灯して実行が止まる。周期をタイマーで表せない場合も同じように停止する。次の出力を確定する前に期限を検出した場合、GPIO は直前の確定値を保持する。確定後に GPIO への反映が遅れた場合は、その tick の値を保持して停止する。I²C の通信エラーは回路の応答状態に返す。

SPI と I²C の接続仕様を参照する。 [GPU と RP マイコンの実行バックエンド](https://neknaj.github.io/circuitgame2/docs/backends.html)
