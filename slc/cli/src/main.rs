//! `slc` — the SL toolchain driver.

use std::process::ExitCode;

mod commands;
mod claim;
mod cputest;
mod gimple;
mod heapcheck;
mod sha256;
mod steps;
mod translate;
mod effects;

fn usage() -> ExitCode {
    eprintln!(
        "usage:
  slc kernel-check [--no-cache] PRELUDE.core [FILE.core ...]   check core files (axioms only in the first);
                                                   a file not newer than its cache entry (build/kernel-cache,
                                                   after the same statements before it) is not checked again,
                                                   its statements taken from the entry; --no-cache: check all
  slc parse PATH...                                parse SL files
  slc check PATH...                                parse and type-check SL files
  slc elab PATH... -o OUT.core                     elaborate SL to core
  slc decode ELF SYMBOL [PATH...]                  disassemble with the spec's table
  slc coverage ELF SYMBOL... [--spec PATH...]      unmodelled instructions reachable from symbols
  slc claim malloc --elf ELF -o OUT.core           state the musl malloc claim
  slc cputest [--n N] [--seed S] [--rows K,..]     compare the instruction table with this CPU
  slc gimple --elf ELF --obj F.o --source F.c DUMP -o OUT.sl   translate a GIMPLE dump
  slc steps ELF CLAIM.core SYMBOL... -o OUT.core    step theorems for the functions' instructions
  slc translate FN SPEC PREFIX -o OUT.core FILE.core...   a function's C1 certificate by statement patterns
  slc heapcheck [--every N] [--max N] ELF [ARGS...]   check the mallocng invariant on a real run"
    );
    ExitCode::from(2)
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let Some(cmd) = args.first() else { return usage() };
    let rest: Vec<String> = args[1..].to_vec();
    let r = match cmd.as_str() {
        "kernel-check" => commands::kernel_check(&rest),
        "parse" => commands::parse(&rest),
        "check" => commands::check(&rest),
        "elab" => commands::elab(&rest),
        "decode" => commands::decode(&rest),
        "coverage" => commands::coverage(&rest),
        "claim" => claim::claim(&rest),
        "cputest" => cputest::cputest(&rest),
        "gimple" => gimple::gimple(&rest),
        "steps" => steps::steps(&rest),
        "heapcheck" => heapcheck::heapcheck(&rest),
        "translate" => translate::translate(&rest),
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
