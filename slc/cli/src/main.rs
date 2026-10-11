//! `slc` — the SL toolchain driver.

use std::process::ExitCode;

mod commands;
mod c1;
mod claim;
mod cputest;
mod gimple;
mod heapcheck;
mod sha256;
mod steps;

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
  slc heapcheck [--every N] [--max N] ELF [ARGS...]   check the mallocng invariant on a real run"
    );
    ExitCode::from(2)
}

/// The commands run on a thread with a large stack (reserved, not used up
/// front): the C1 engine's proof of a path nests one step's in the next,
/// so its depth grows with the path (alloc_group's: over a thousand frames
/// of the proof builder).
const STACK: usize = 1 << 30;

fn main() -> ExitCode {
    match std::thread::Builder::new().name("main".into()).stack_size(STACK).spawn(run).map(|h| h.join()) {
        Ok(Ok(code)) => code,
        Ok(Err(p)) => std::panic::resume_unwind(p),
        Err(e) => {
            eprintln!("error: no thread for the command: {}", e);
            ExitCode::FAILURE
        }
    }
}

fn run() -> ExitCode {
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
