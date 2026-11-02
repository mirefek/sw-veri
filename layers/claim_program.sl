layer claim_program uses claim_malloc

// What is claimed about the whole program (tests/test_malloc.c): its
// process, from exec, runs until it exits or faults -- the machine
// raising an exception ends it (exit / exit_group: `exit(status)`; a
// fault: `segv`, `stack_fault`, `div_error`, `ud`).

// The process: the machine stepping until an exception ends it.
proc[Machine] run_process() {
  while true { step() }
}

// Every run from an unprivileged exec state that ends exits with a
// status in `ok`, or dies of a stack overflow -- the fault abi.sl's
// `abi_function` raises when the stack cannot grow (`overflow_at`, below
// the initial stack pointer, every frame's; or a stack segment fault);
// no other crash. Runs that never end are allowed (no termination claim).
pred program_ok(f: File, ok: Set[nat]) =
  all argv: List[List[bits[8]]], envp: List[List[bits[8]]], m0: Machine, o: Outcome[Machine, ()].
    exec_state(f, argv, envp, m0) && unprivileged(m0.os) && outcome(m0, run_process(), o) ->
      match o {
        ok(_, _)   => true
        exc(m, e)  => (ex s: bits[8]. e = exit(s) && uint(s) in ok) ||
                      (ex a: Addr, c: SegvCode. e = segv(a, c) && overflow_at(m.vm, m.gpr[rsp], m0.gpr[rsp], a)) ||
                      e = stack_fault
        diverge(_) => true
      }
