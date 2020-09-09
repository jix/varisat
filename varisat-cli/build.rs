use std::{env, path::Path, process::Command, str::from_utf8};

fn main() {
    let rustc = env::var("RUSTC").unwrap();
    let package_version = env::var("CARGO_PKG_VERSION").unwrap();

    let rustc_version = Command::new(rustc)
        .arg("--version")
        .output()
        .ok()
        .filter(|result| result.status.success())
        .expect("Failed to query rustc version");

    let mut use_package_version = true;

    if Path::new("../.git").exists() {
        if let Some(git_revision) = Command::new("git")
            .arg("describe")
            .arg("--tags")
            .arg("--match=v[0-9]*")
            .arg("--dirty=-d")
            .arg("--always")
            .output()
            .ok()
            .filter(|result| result.status.success())
        {
            let version = from_utf8(git_revision.stdout.as_slice()).unwrap();
            println!("cargo:rustc-env=VARISAT_VERSION={}", &version[1..]);
            use_package_version = false;
        }
    }

    if use_package_version {
        println!("cargo:rustc-env=VARISAT_VERSION={}", package_version);
    }

    println!(
        "cargo:rustc-env=VARISAT_RUSTC_VERSION={}",
        from_utf8(rustc_version.stdout.as_slice()).unwrap()
    );
    println!(
        "cargo:rustc-env=VARISAT_PROFILE={}",
        env::var("PROFILE").unwrap()
    );
}
