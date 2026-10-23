layer claim_malloc uses malloc

// What is claimed about a libc binary's allocator. The claim itself is
// assembled by `slc claim malloc`, which supplies the binary, the addresses
// of its symbols, and quantifies over the allocator invariant:
//
//   ex alloc_inv, alloc_owned.  laws(...) && allocator_claim(...)

// Runs the machine until `main` is entered for the first time.
proc[Machine] run_until(target: Addr) {
  while rip != target { step() }
}

// the heap at machine state `m`, with no live blocks, the stack's objects
// `objs` (the program's data on the initial stack)
fn empty_heap(m: Machine, objs: Set[nat]) -> Heap =
  Heap { vm: m.vm, os: m.os, fs_base: m.fs_base, cpu: m.cpu, objs: objs_at(objs, m.fs_base), blocks: (p: Addr) => none }

// Assumption of this claim: the program starts without privileges. musl's
// startup then skips its secure path, whose system calls (poll, open) are
// not modelled yet.
pred unprivileged(os: Os) =
  !os.secure && os.creds.uid = os.creds.euid && os.creds.gid = os.creds.egid

// libc's data on the initial stack: the auxiliary vector (libc keeps a
// pointer to it; musl's allocator reads its AT_RANDOM entry at the first
// allocation) and the 16 random bytes AT_RANDOM points to
fn auxv_addr(m0: Machine, argv: List[List[bits[8]]], envp: List[List[bits[8]]]) -> nat =
  uint(m0.gpr[rsp]) + 24 + 8 * len(argv) + 8 * len(envp)

pred initial_auxv(m0: Machine, argv: List[List[bits[8]]], envp: List[List[bits[8]]], a: nat) =
  ex auxv: List[(nat, nat)].
    auxv_at(m0.vm, auxv_addr(m0, argv, envp), auxv) &&
    ((auxv_addr(m0, argv, envp) <= a && a < auxv_addr(m0, argv, envp) + 16 * len(auxv)) ||
     (ex q: nat. aux(auxv, AT_RANDOM, q) && q <= a && a < q + 16))

// Every unprivileged run from process start that reaches `main` does so in a
// state where the allocator invariant holds with no blocks, and the allocator
// owns only `static` bytes (its code and data), the thread descriptor up to
// errno, and libc's data on the initial stack.
pred init_at_main(f: File, main_at: Addr, static: Set[nat]) =
  all argv: List[List[bits[8]]], envp: List[List[bits[8]]], m0: Machine, m: Machine.
    exec_state(f, argv, envp, m0) && unprivileged(m0.os) &&
    outcome(m0, run_until(main_at), ok(m, ())) ->
      alloc_inv(empty_heap(m, {a: nat | initial_auxv(m0, argv, envp, a)})) &&
      (all a: nat. a in alloc_owned(empty_heap(m, {a: nat | initial_auxv(m0, argv, envp, a)})) ->
         a in static || a in range(m.fs_base, errno_offset(())) || initial_auxv(m0, argv, envp, a))

pred allocator_claim(f: File, main_at: Addr, malloc_at: Addr, free_at: Addr, calloc_at: Addr, static: Set[nat]) =
  init_at_main(f, main_at, static) && allocator_correct(malloc_at, free_at, calloc_at)
