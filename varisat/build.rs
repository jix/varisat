use std::process::Command;
use std::str::from_utf8;

fn have_drat_trim() -> bool {
    if let Some(drat_trim) = Command::new("drat-trim").output().ok() {
        if let Some(stdout) = from_utf8(&drat_trim.stdout).ok() {
            return stdout.contains("force binary proof parse mode");
        }
    }
    false
}

fn main() {
    if have_drat_trim() {
        println!("cargo:rustc-cfg=test_drat_trim");
    } else {
        println!("cargo:warning=drat-trim utility not found, some tests will be disabled");
    }
}
