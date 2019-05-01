use failure::{ensure, Error};
use std::env;
use std::io::Write;
use std::process::{Command, Stdio};
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

fn have_check_lrat() -> Result<(), Error> {
    println!("rerun-if-env-changed=VARISAT_HAVE_CHECK_LRAT");
    if env::var("VARISAT_HAVE_CHECK_LRAT").is_ok() {
        return Ok(());
    }

    let mut child = Command::new("check-lrat")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()?;
    let stdin = child.stdin.as_mut().unwrap();
    stdin.write_all(b":pc lrat-check\n")?;

    let output = child.wait_with_output()?;
    let stdout = from_utf8(&output.stdout)?;

    ensure!(
        stdout.contains("INCLUDE-BOOK \"projects/sat/lrat/stobj-based/run\""),
        "stobj-based lrat-check not found"
    );

    Ok(())
}

fn have_check_clrat() -> Result<(), Error> {
    println!("rerun-if-env-changed=VARISAT_HAVE_CHECK_LRAT");
    if env::var("VARISAT_HAVE_CHECK_LRAT").is_ok() {
        return Ok(());
    }

    let mut child = Command::new("check-clrat")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()?;
    let stdin = child.stdin.as_mut().unwrap();
    stdin.write_all(b":pc lrat-check\n")?;

    let output = child.wait_with_output()?;
    let stdout = from_utf8(&output.stdout)?;

    ensure!(
        stdout.contains("INCLUDE-BOOK \"projects/sat/lrat/incremental/run\""),
        "incremental lrat-check not found"
    );

    Ok(())
}

fn main() {
    match have_drat_trim() {
        Ok(_) => println!("cargo:rustc-cfg=test_drat_trim"),
        Err(err) => println!(
            "cargo:warning=drat-trim utility not found, some tests will be disabled: {}",
            err
        ),
    }

    match (have_check_lrat(), have_check_clrat()) {
        (Ok(_), Ok(_)) => println!("cargo:rustc-cfg=test_check_lrat"),
        (Err(err), _) => println!(
            "cargo:warning=check-lrat utility not found, some tests will be disabled: {}",
            err
        ),
        (_, Err(err)) => println!(
            "cargo:warning=check-clrat utility not found, some tests will be disabled: {}",
            err
        ),
    }
}
