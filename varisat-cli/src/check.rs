use std::fs;
use std::io;

use clap::{App, ArgMatches, SubCommand};
use failure::Error;

use varisat::checker::Checker;

use super::{banner, init_logging};

pub fn check_args() -> App<'static, 'static> {
    SubCommand::with_name("--check")
        .arg_from_usage("[INPUT] 'The input file to use (stdin if omitted)'")
        .arg_from_usage("<proof-file> --proof=[FILE] 'The varisat proof file to check.'")
}

pub fn check_main(matches: &ArgMatches) -> Result<i32, Error> {
    init_logging();
    banner();

    let mut checker = Checker::default();

    let stdin = io::stdin();

    let mut locked_stdin;
    let mut opened_file;

    let file = match matches.value_of("INPUT") {
        Some(path) => {
            log::info!("Reading file '{}'", path);
            opened_file = fs::File::open(path)?;
            &mut opened_file as &mut io::Read
        }
        None => {
            log::info!("Reading from stdin");
            locked_stdin = stdin.lock();
            &mut locked_stdin as &mut io::Read
        }
    };

    checker.add_dimacs_cnf(file)?;

    let path = matches.value_of("proof-file").unwrap();

    log::info!("Checking proof file '{}'", path);

    match checker.check_proof(fs::File::open(path)?) {
        Ok(()) => println!("s VERIFIED"),
        Err(err) => {
            log::error!("{}", err);
            println!("s NOT VERIFIED");
            return Ok(1);
        }
    }

    Ok(0)
}
