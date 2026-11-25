//! ボードに対応するメモリーマップをリンク時に選ぶ。

use std::{env, fs, path::PathBuf};

mod program;

fn main() {
    let pico = env::var_os("CARGO_FEATURE_PICO").is_some();
    let pico2 = env::var_os("CARGO_FEATURE_PICO2").is_some();
    let target = env::var("TARGET").expect("TARGET");
    let (map, file) = match (pico, pico2, target.as_str()) {
        (true, false, "thumbv6m-none-eabi") => (include_bytes!("pico.x").as_slice(), "pico.x"),
        (false, true, "thumbv8m.main-none-eabihf") => {
            (include_bytes!("pico2.x").as_slice(), "pico2.x")
        }
        _ => panic!("pico requires thumbv6m-none-eabi; pico2 requires thumbv8m.main-none-eabihf"),
    };
    let directory = PathBuf::from(env::var_os("OUT_DIR").expect("OUT_DIR"));
    fs::write(directory.join("memory.x"), map).expect("memory.x");
    println!("cargo:rustc-link-search={}", directory.display());
    println!("cargo:rustc-link-arg-bins=--nmagic");
    println!("cargo:rustc-link-arg-bins=-Tlink.x");
    if pico {
        println!("cargo:rustc-link-arg-bins=-Tlink-rp.x");
    }
    println!("cargo:rerun-if-changed={file}");
    println!("cargo:rerun-if-env-changed=NCG2_RP_PROGRAM");
    let board = if pico { "pico" } else { "pico2" };
    let program = if let Some(path) = env::var_os("NCG2_RP_PROGRAM") {
        let path = PathBuf::from(path);
        println!("cargo:rerun-if-changed={}", path.display());
        let text = fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("{} を読み込めない。{error}", path.display()));
        program::Program::parse(&text, board)
            .unwrap_or_else(|error| panic!("{}。{error}", path.display()))
    } else {
        program::Program::example(board).expect("組み込みの GPIO 例")
    };
    println!("cargo:rustc-check-cfg=cfg(rp_uart_program)");
    println!("cargo:rustc-check-cfg=cfg(rp_i2c_program)");
    println!("cargo:rustc-check-cfg=cfg(rp_spi_program)");
    println!("cargo:rustc-check-cfg=cfg(rp_spi_controller, values(\"0\", \"1\"))");
    if program.has_uart() {
        assert!(
            env::var_os("CARGO_FEATURE_UART").is_some(),
            "UART 配線表には uart feature が必要。"
        );
        println!("cargo:rustc-cfg=rp_uart_program");
    }
    if program.has_i2c() {
        assert!(
            env::var_os("CARGO_FEATURE_I2C").is_some(),
            "I²C 配線表には i2c feature が必要。"
        );
        println!("cargo:rustc-cfg=rp_i2c_program");
    }
    if let Some(instance) = program.spi_instance() {
        assert!(
            env::var_os("CARGO_FEATURE_SPI").is_some(),
            "SPI 配線表には spi feature が必要。"
        );
        println!("cargo:rustc-cfg=rp_spi_program");
        println!("cargo:rustc-cfg=rp_spi_controller=\"{instance}\"");
    }
    fs::write(directory.join("program.rs"), program.rust()).expect("program.rs");
}
