use failure::{ensure, Error};
use std::env;
use std::process::Command;
use std::str::from_utf8;

fn have_drat_trim() -> Result<(), Error> {
    println!("rerun-if-env-changed=VARISAT_HAVE_DRAT_TRIM");
    if env::var("VARISAT_HAVE_DRAT_TRIM").is_ok() {
        return Ok(());
    }

    let output = Command::new("drat-trim").output()?;
    let stdout = from_utf8(&output.stdout)?;

    ensure!(
        stdout.contains("force binary proof parse mode"),
        "no force binary proof option found"
    );

    Ok(())
}

fn have_rate() -> Result<(), Error> {
    println!("rerun-if-env-changed=VARISAT_HAVE_RATE");
    if env::var("VARISAT_HAVE_RATE").is_ok() {
        return Ok(());
    }

    let _ = Command::new("rate").arg("--version").output()?;

    Ok(())
}

fn main() {
    match have_drat_trim() {
        Ok(_) => println!("cargo:rustc-cfg=test_drat_trim"),
        Err(err) => println!(
            "cargo:warning=drat-trim proof checker not found, some tests will be disabled: {}",
            err
        ),
    }

    match have_rate() {
        Ok(_) => println!("cargo:rustc-cfg=test_rate"),
        Err(err) => println!(
            "cargo:warning=rate proof checker not found, some tests will be disabled: {}",
            err
        ),
    }
}
