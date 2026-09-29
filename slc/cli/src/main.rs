//! `slc` — the SL toolchain driver.

use std::path::PathBuf;
use std::process::ExitCode;

mod commands;
mod claim;
mod cputest;
mod gimple;
mod heapcheck;
mod sha256;

fn usage() -> ExitCode {
    eprintln!(
        "usage:
  slc kernel-check PRELUDE.core [FILE.core ...]   check core files (axioms only in the first)
  slc parse PATH...                                parse SL files
  slc check PATH...                                parse and type-check SL files
  slc elab PATH... -o OUT.core                     elaborate SL to core
  slc decode ELF SYMBOL [PATH...]                  disassemble with the spec's table
  slc coverage ELF SYMBOL... [--spec PATH...]      unmodelled instructions reachable from symbols
  slc claim malloc --elf ELF -o OUT.core           state the musl malloc claim
  slc cputest [--n N] [--seed S] [--rows K,..]     compare the instruction table with this CPU
  slc gimple --elf ELF --obj F.o --source F.c DUMP -o OUT.sl   translate a GIMPLE dump
  slc heapcheck [--every N] [--max N] ELF [ARGS...]   check the mallocng invariant on a real run"
    );
    ExitCode::from(2)
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let Some(cmd) = args.first() else { return usage() };
    let rest: Vec<String> = args[1..].to_vec();
    let r = match cmd.as_str() {
        "kernel-check" => commands::kernel_check(&rest.iter().map(PathBuf::from).collect::<Vec<_>>()),
        "parse" => commands::parse(&rest),
        "check" => commands::check(&rest),
        "elab" => commands::elab(&rest),
        "decode" => commands::decode(&rest),
        "coverage" => commands::coverage(&rest),
        "claim" => claim::claim(&rest),
        "cputest" => cputest::cputest(&rest),
        "gimple" => gimple::gimple(&rest),
        "heapcheck" => heapcheck::heapcheck(&rest),
        _ => return usage(),
    };
    match r {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {}", e);
            ExitCode::FAILURE
        }
    }
}
