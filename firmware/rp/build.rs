//! ボードに対応するメモリーマップをリンク時に選ぶ。

use std::{env, fs, path::PathBuf};

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
}
