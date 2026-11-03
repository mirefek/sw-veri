layer startup_specs uses gimple, abi, mallocng_specs

// Specs of musl's startup functions (run before main): each a contract --
// a precondition, then a stack overflow or the effect: a frame (what it may
// write: the startup globals `start_writes`, its stack objects' bytes) and
// guarantees (what later code needs: today the allocator's -- the thread
// descriptor at fs_base, its canary, libc.auxv). Other effects (libc's
// page size, __progname, ..) are written but not guaranteed: a guarantee
// is added when a feature needs it. For programs without TLS (no PT_TLS
// segment: the static TLS area musl's own, in builtin_tls) started without
// privileges (the secure path's poll and open not taken).

///////////////////////////////////////////////////////////////////////
//  The startup globals and the frame

// the addresses of the globals the startup code writes or reads
record StartGlobals {
  environ: Addr, hwcap: Addr, sysinfo: Addr, libc: Addr, progname: Addr, progname_full: Addr,
  empty_str: Addr, default_stacksize: Addr, builtin_tls: Addr, main_tls: Addr, stack_chk_guard: Addr
}

fn span(a: Addr, n: nat) -> Set[nat] = {x: nat | uint(a) <= x && x < uint(a) + n}

// what startup may write: libc's fields it sets (can_do_threads, auxv, its
// TLS fields, page size -- not need_locks: single-threaded), the globals
// it sets, the static TLS area (the thread descriptor in it), the stack
// protector's guard
fn start_writes(g: StartGlobals) -> Set[nat] =
  {x: nat | x in span(g.libc, 1) || x in span(g.libc + 8, 48) || x in span(g.environ, 8) || x in span(g.hwcap, 8) || x in span(g.sysinfo, 8) ||
     x in span(g.progname, 8) || x in span(g.progname_full, 8) || x in span(g.default_stacksize, 4) ||
     x in span(g.builtin_tls, 336) || x in span(g.main_tls, 48) || x in span(g.stack_chk_guard, 8)}

// what __init_tls writes: libc's can_do_threads (its first byte) and TLS
// fields, the main TLS module, the default stack size, the static TLS area
fn tls_writes(g: StartGlobals) -> Set[nat] =
  {x: nat | x in span(g.libc, 1) || x in span(g.libc + 16, 32) || x in span(g.default_stacksize, 4) ||
     x in span(g.builtin_tls, 336) || x in span(g.main_tls, 48)}

// what __init_ssp writes: the guard, the canary in the descriptor (in the
// static TLS area)
fn ssp_writes(g: StartGlobals) -> Set[nat] = {x: nat | x in span(g.stack_chk_guard, 8) || x in span(g.builtin_tls, 336)}

// before -> after: only bytes changed, and only those of w or the stack's
// free bytes (the function's stack objects, dead after it)
pred frame(before: Vm, after: Vm, objs: Objs, w: Set[nat]) =
  (after with { bytes: before.bytes }) = before &&
  (all a: Addr. uint(a) notin w -> !stack_free(before, objs, uint(a)) -> after.bytes[a] = before.bytes[a])

///////////////////////////////////////////////////////////////////////
//  The initial stack's data, as the startup code reads it

// envp: n words, nonzero, then a zero word
pred env_at(vm: Vm, objs: Objs, envp: Addr, n: nat) =
  envp != 0 && uint(envp) + 8 * (n + 2) < 2^63 &&
  (all i: nat. i <= n -> usable(vm, objs, uint(envp) + 8 * i, 8, false)) &&
  (all i: nat. i < n -> bytes_at(vm, bits[64](uint(envp) + 8 * i), 8) != 0) &&
  bytes_at(vm, bits[64](uint(envp) + 8 * n), 8) = 0

// the auxiliary vector at a: its pairs, up to AT_NULL's
pred auxv_list(vm: Vm, objs: Objs, a: nat, auxv: List[(nat, nat)]) =
  len(auxv) >= 1 && a + 16 * len(auxv) < 2^63 &&
  (all k: nat. k < len(auxv) ->
     usable(vm, objs, a + 16 * k, 16, false) &&
     bytes_at(vm, bits[64](a + 16 * k), 8) = auxv[k][0] && bytes_at(vm, bits[64](a + 16 * k + 8), 8) = auxv[k][1]) &&
  auxv[len(auxv) - 1][0] = AT_NULL && (all k: nat. k + 1 < len(auxv) -> auxv[k][0] != AT_NULL) &&
  // (each key once -- Linux's vector)
  (all k: nat, j: nat. k < len(auxv) && j < len(auxv) && auxv[k][0] = auxv[j][0] -> k = j)

// aux[key] as musl copies it: the pair's value, or 0 (no pair)
pred aux_is(auxv: List[(nat, nat)], key: nat, v: nat) =
  (ex k: nat. k < len(auxv) && auxv[k][0] = key && auxv[k][1] = v) ||
  (!(ex k: nat. k < len(auxv) && auxv[k][0] = key) && v = 0)

// a C string at p: readable, none of its bytes written by startup
pred cstr(vm: Vm, objs: Objs, p: nat, w: Set[nat]) =
  ex len: nat. p != 0 && p + len + 1 < 2^63 && usable(vm, objs, p, len + 1, false) &&
    (all i: nat. i < len -> bytes_at(vm, bits[64](p + i), 1) != 0) && bytes_at(vm, bits[64](p + len), 1) = 0 &&
    (all i: nat. i <= len -> p + i notin w)

// the program headers (aux[AT_PHDR], aux[AT_PHENT], aux[AT_PHNUM]):
// readable, none of them PT_TLS
const PT_TLS: nat = 7

pred phdrs_ok(vm: Vm, objs: Objs, ph: nat, pe: nat, pn: nat, w: Set[nat]) =
  ph + pe * pn + 56 < 2^63 &&
  (all i: nat. i < pn -> ph + pe * i != 0 && usable(vm, objs, ph + pe * i, 56, false) && bytes_at(vm, bits[64](ph + pe * i), 4) != PT_TLS &&
     (all j: nat. j < 56 -> ph + pe * i + j notin w))

// a stack overflow during startup: as abi's, the thread pointer as a
// callee may have left it (an overflow after __init_tls set it up)
proc[World] overflow_start() {
  havoc fs_base
  overflow()
}

///////////////////////////////////////////////////////////////////////
//  __init_tls(aux), __init_ssp(entropy)

// startup's globals writable and readable, on data pages (mapped,
// readable, writable, off the stack); libc's TLS fields and main_tls still
// zero (in .bss: TLS not yet set up)
pred globals_ok(vm: Vm, objs: Objs, g: StartGlobals) =
  (all x: nat. x in start_writes(g) -> usable(vm, objs, x, 1, true) && usable(vm, objs, x, 1, false) &&
     mapped(vm, x / PAGE) && vm.pages[x / PAGE].value.prot.r && vm.pages[x / PAGE].value.prot.w && !stack_page(vm, x / PAGE)) &&
  uint(g.libc) + 56 < 2^63 && g.builtin_tls != 0 && uint(g.builtin_tls) + 336 < 2^63

pred tls_fresh(vm: Vm, g: StartGlobals) =
  bytes_at(vm, g.libc + 16, 8) = 0 && bytes_at(vm, g.libc + 24, 8) = 0 && bytes_at(vm, g.libc + 32, 8) = 0 &&
  bytes_at(vm, g.libc + 40, 8) = 0 && bytes_at(vm, g.main_tls, 48) = 0

// the descriptor's 200 bytes at fs: in the static TLS area
pred in_tls(g: StartGlobals, fs: Addr) = uint(g.builtin_tls) <= uint(fs) && uint(fs) + 200 <= uint(g.builtin_tls) + 336

// the thread: its descriptor at fs (its own address in its first word), the
// stack protector's word in it
pred thread_set(vm: Vm, fs: Addr) = thread_ok(vm, fs) && canary_ok(vm, fs)

// the thread set up in the static TLS area (the allocator keeps its
// ranges apart from the descriptor)
pred thread_at(g: StartGlobals, vm: Vm, fs: Addr) = thread_set(vm, fs) && in_tls(g, fs)

// __init_tls(aux): aux the 38 words musl copied the vector to; the thread
// pointer set to a descriptor in the static TLS area
pred init_tls_pre(vm: Vm, objs: Objs, g: StartGlobals, aux: Addr) =
  aux != 0 && usable(vm, objs, uint(aux), 304, false) && uint(aux) + 304 <= 2^64 &&
  (all x: nat. uint(aux) <= x && x < uint(aux) + 304 -> x notin start_writes(g)) &&
  globals_ok(vm, objs, g) && tls_fresh(vm, g) &&
  phdrs_ok(vm, objs, bytes_at(vm, aux + 24, 8), bytes_at(vm, aux + 32, 8), bytes_at(vm, aux + 40, 8), start_writes(g))

proc[World] init_tls_spec(g: StartGlobals, aux: Addr) {
  require init_tls_pre(vm, objs, g, aux)
  either { overflow_start() } or {
    let before = vm
    havoc vm where frame(before, vm, objs, tls_writes(g)) && (ex fs: Addr. thread_set(vm, fs) && in_tls(g, fs))
    fs_base := any fs: Addr where thread_set(vm, fs) && in_tls(g, fs)
  }
}

fn init_tls_spec_fun(g: StartGlobals) -> CFun2[World] = (args: Args) => {
  require len(args) >= 1
  init_tls_spec(g, bits[64](args[0]))
  return (any bits[64], any bits[64])
}

// __init_ssp(entropy): the canary from AT_RANDOM's bytes (or from the
// guard's address), stored in the guard and the descriptor
pred init_ssp_pre(vm: Vm, objs: Objs, g: StartGlobals, fs: Addr, entropy: Addr) =
  thread_set(vm, fs) && in_tls(g, fs) && globals_ok(vm, objs, g) &&
  (entropy != 0 -> usable(vm, objs, uint(entropy), 8, false) && uint(entropy) + 8 < 2^63 &&
     (all i: nat. i < 8 -> uint(entropy) + i notin start_writes(g)))

proc[World] init_ssp_spec(g: StartGlobals, entropy: Addr) {
  require init_ssp_pre(vm, objs, g, fs_base, entropy)
  either { overflow_start() } or {
    let before = vm
    havoc vm where frame(before, vm, objs, ssp_writes(g)) && thread_set(vm, fs_base)
  }
}

fn init_ssp_spec_fun(g: StartGlobals) -> CFun2[World] = (args: Args) => {
  require len(args) >= 1
  init_ssp_spec(g, bits[64](args[0]))
  return (any bits[64], any bits[64])
}

///////////////////////////////////////////////////////////////////////
//  __init_libc(envp, pn)

// envp, the vector after it, the program's name; startup's globals; an
// unprivileged start (aux[AT_UID] = aux[AT_EUID], the same for the group,
// aux[AT_SECURE] 0)
pred init_libc_pre(vm: Vm, objs: Objs, g: StartGlobals, envp: Addr, pn: Addr) =
  ex n: nat, auxv: List[(nat, nat)].
    env_at(vm, objs, envp, n) && auxv_list(vm, objs, uint(envp) + 8 * (n + 1), auxv) &&
    (all x: nat. uint(envp) <= x && x < uint(envp) + 8 * (n + 1) + 16 * len(auxv) -> x notin start_writes(g)) &&
    globals_ok(vm, objs, g) && tls_fresh(vm, g) &&
    (pn != 0 -> cstr(vm, objs, uint(pn), start_writes(g))) &&
    (all v: nat. aux_is(auxv, AT_EXECFN, v) -> v != 0 -> cstr(vm, objs, v, start_writes(g))) &&
    cstr(vm, objs, uint(g.empty_str), start_writes(g)) &&
    (ex ph: nat, pe: nat, phn: nat. aux_is(auxv, AT_PHDR, ph) && aux_is(auxv, AT_PHENT, pe) && aux_is(auxv, AT_PHNUM, phn) &&
       phdrs_ok(vm, objs, ph, pe, phn, start_writes(g))) &&
    (all e: nat. aux_is(auxv, AT_RANDOM, e) -> e != 0 ->
       usable(vm, objs, e, 8, false) && e + 8 < 2^63 && (all i: nat. i < 8 -> e + i notin start_writes(g))) &&
    (ex u: nat, gr: nat. aux_is(auxv, AT_UID, u) && aux_is(auxv, AT_EUID, u) && aux_is(auxv, AT_GID, gr) && aux_is(auxv, AT_EGID, gr)) &&
    aux_is(auxv, AT_SECURE, 0)

// the thread set up (in the static TLS area), libc.auxv the vector's
// address (past envp's zero word)
proc[World] init_libc_spec(g: StartGlobals, envp: Addr, pn: Addr) {
  require init_libc_pre(vm, objs, g, envp, pn)
  either { overflow_start() } or {
    let before = vm
    havoc vm where frame(before, vm, objs, start_writes(g)) &&
      (all n: nat. env_at(before, objs, envp, n) -> bytes_at(vm, g.libc + 8, 8) = uint(envp) + 8 * (n + 1)) &&
      (ex fs: Addr. thread_at(g, vm, fs))
    fs_base := any fs: Addr where thread_at(g, vm, fs)
  }
}

fn init_libc_spec_fun(g: StartGlobals) -> CFun2[World] = (args: Args) => {
  require len(args) >= 2
  init_libc_spec(g, bits[64](args[0]), bits[64](args[1]))
  return (any bits[64], any bits[64])
}

///////////////////////////////////////////////////////////////////////
//  main entered: __libc_start_init(), libc_start_main_stage2(main, argc,
//  argv), __libc_start_main(main, argc, argv, ..), _start_c(sp)

// main entered: where startup's runs end (the claim's stop at main), the
// world as startup leaves it
exception at_main

proc[World] main_entered() {
  raise at_main
}

// the program's main as startup sees it
fn main_spec_fun() -> CFun2[World] = (args: Args) => {
  main_entered()
  return (any bits[64], any bits[64])
}

// the program's addresses startup uses: its constructors (the init_array,
// [init_array, init_array_end), each entry `ctor`: crtbegin's frame_dummy,
// a constructor doing nothing -- no clone table to register), main
record StartProgram { init_array: Addr, init_array_end: Addr, ctor: Addr, main: Addr }

// the constructors' table: readable, none of its bytes in w
pred ctors_ok(vm: Vm, objs: Objs, p: StartProgram, w: Set[nat]) =
  ex n: nat. uint(p.init_array_end) = uint(p.init_array) + 8 * n && uint(p.init_array_end) < 2^63 &&
    (all i: nat. i < n -> usable(vm, objs, uint(p.init_array) + 8 * i, 8, false) &&
       bytes_at(vm, p.init_array + 8 * i, 8) = uint(p.ctor) && (all j: nat. j < 8 -> uint(p.init_array) + 8 * i + j notin w))

// __libc_start_init(): _init (crti/crtn's: nothing), then the
// constructors -- this program's do nothing
proc[World] start_init_spec(p: StartProgram) {
  require ctors_ok(vm, objs, p, {x: nat | false})
  either { overflow_start() } or { }
}

fn start_init_spec_fun(p: StartProgram) -> CFun2[World] = (args: Args) => {
  start_init_spec(p)
  return (any bits[64], any bits[64])
}

// libc_start_main_stage2(main, argc, argv): the constructors, then main
// (exit after it, with main's value); envp past argv's words
proc[World] stage2_spec(p: StartProgram, main: Addr, argc: bits[32], argv: Addr) {
  require main = p.main && uint(argc) < 2^31 && uint(argv) + 8 * (uint(argc) + 1) < 2^63 && ctors_ok(vm, objs, p, {x: nat | false})
  either { overflow_start() } or { main_entered() }
}

fn stage2_spec_fun(p: StartProgram) -> CFun2[World] = (args: Args) => {
  require len(args) >= 3
  stage2_spec(p, bits[64](args[0]), bits[32](args[1]), bits[64](args[2]))
  return (any bits[64], any bits[64])
}

// startup's effect: libc set up (as __init_libc's spec: only startup's
// globals written, the thread set up, libc.auxv the vector past envp's
// zero word), then main entered
proc[World] to_main(g: StartGlobals, envp: Addr) {
  let before = vm
  havoc vm where frame(before, vm, objs, start_writes(g)) &&
    (all n: nat. env_at(before, objs, envp, n) -> bytes_at(vm, g.libc + 8, 8) = uint(envp) + 8 * (n + 1)) &&
    (ex fs: Addr. thread_at(g, vm, fs))
  fs_base := any fs: Addr where thread_at(g, vm, fs)
  main_entered()
}

// __libc_start_main(main, argc, argv, ..): argv's words, then envp's
// (argc's count of them, then a null word); __init_libc's precondition at
// envp and argv[0], the constructors apart from what it writes
pred start_main_pre(vm: Vm, objs: Objs, g: StartGlobals, p: StartProgram, argc: nat, argv: Addr) =
  argc < 2^31 && argv != 0 && uint(argv) + 8 * (argc + 1) < 2^63 && usable(vm, objs, uint(argv), 8, false) &&
  init_libc_pre(vm, objs, g, argv + 8 * (argc + 1), bits[64](bytes_at(vm, argv, 8))) &&
  ctors_ok(vm, objs, p, start_writes(g))

proc[World] start_main_spec(g: StartGlobals, p: StartProgram, main: Addr, argc: bits[32], argv: Addr) {
  require main = p.main && start_main_pre(vm, objs, g, p, uint(argc), argv)
  either { overflow_start() } or { to_main(g, argv + 8 * (uint(argc) + 1)) }
}

fn start_main_spec_fun(g: StartGlobals, p: StartProgram) -> CFun2[World] = (args: Args) => {
  require len(args) >= 6
  start_main_spec(g, p, bits[64](args[0]), bits[32](args[1]), bits[64](args[2]))
  return (any bits[64], any bits[64])
}

// _start_c(sp): sp the stack exec set up -- argc's word, then argv
proc[World] start_c_spec(g: StartGlobals, p: StartProgram, sp: Addr) {
  require sp != 0 && uint(sp) + 16 < 2^63 && usable(vm, objs, uint(sp), 8, false) &&
    start_main_pre(vm, objs, g, p, bytes_at(vm, sp, 8), sp + 8)
  either { overflow_start() } or { to_main(g, sp + 8 * (bytes_at(vm, sp, 8) + 2)) }
}

fn start_c_spec_fun(g: StartGlobals, p: StartProgram) -> CFun2[World] = (args: Args) => {
  require len(args) >= 1
  start_c_spec(g, p, bits[64](args[0]))
  return (any bits[64], any bits[64])
}

///////////////////////////////////////////////////////////////////////
//  After main: exit(code)

// the program's addresses exit uses: musl's exit lock, the fini_array's
// one entry (crtbegin's __do_global_dtors_aux: its `completed` byte, the
// weak __cxa_finalize's GOT word -- 0, not linked)
record ExitProgram { lock: Addr, fini_array: Addr, dtors: Addr, completed: Addr, cxa_got: Addr }

// exit's precondition: a sound thread with its id set (not 0) -- its
// word apart from what exit writes --, the lock free, the fini_array's
// entry the dtors', its words readable (the lock and completed byte
// writable)
pred exit_pre(vm: Vm, objs: Objs, p: ExitProgram, fs: Addr) =
  thread_ok(vm, fs) && usable(vm, objs, uint(fs) + 48, 4, false) && bytes_at(vm, fs + 48, 4) != 0 &&
  (uint(fs) + 8 <= uint(p.lock) || uint(p.lock) + 4 <= uint(fs)) &&
  (uint(fs) + 8 <= uint(p.completed) || uint(p.completed) + 1 <= uint(fs)) &&
  usable(vm, objs, uint(p.lock), 4, false) && usable(vm, objs, uint(p.lock), 4, true) && bytes_at(vm, p.lock, 4) = 0 &&
  usable(vm, objs, uint(p.fini_array), 8, false) && bytes_at(vm, p.fini_array, 8) = uint(p.dtors) &&
  usable(vm, objs, uint(p.completed), 1, false) && usable(vm, objs, uint(p.completed), 1, true) &&
  usable(vm, objs, uint(p.cxa_got), 8, false) && bytes_at(vm, p.cxa_got, 8) = 0

// exit(code): a stack overflow, or the process ends with the status
// code's low byte (its memory as it ends: anything -- nothing reads it)
proc[World] exit_spec(p: ExitProgram, code: bits[32]) {
  require exit_pre(vm, objs, p, fs_base)
  either { overflow() } or {
    havoc vm
    raise exit(code[7:0])
  }
}

fn exit_spec_fun(p: ExitProgram) -> CFun2[World] = (args: Args) => {
  require len(args) >= 1
  exit_spec(p, bits[32](args[0]))
  return (any bits[64], any bits[64])
}
